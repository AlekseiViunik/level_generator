#!/usr/bin/env python3
"""
Генератор уровней для Storage Controller
(режимы Standard Crane, Color Matching, Worker).
"""

import json
import math
import os
import random
import threading
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
from collections import deque
from typing import Any, Dict, List, Optional, Set, Tuple

# ─── Константы ───────────────────────────────────────────────────────────────
GRID_W = 6
GRID_H = 5
TRANSPORT_ROW = 5  # виртуальный ряд над сеткой (y=5)

OUTPUT_DIR = os.path.normpath(
    r"C:\Users\vjuni\Documents\__MY_DOCUMENTS\Dev"
    r"\storage_controller\Assets\StorageController\Resources\levels\Levels"
)
COLOR_OUTPUT_DIR = os.path.normpath(
    r"C:\Users\vjuni\Documents\__MY_DOCUMENTS\Dev"
    r"\storage_controller\Assets\StorageController\Resources\levels"
    r"\ColorLevels"
)

SOLUTIONS_DIR = os.path.normpath(
    r"C:\Users\vjuni\Documents\__MY_DOCUMENTS\Dev\level_generator\solutions"
)
COLOR_SOLUTIONS_DIR = os.path.normpath(
    r"C:\Users\vjuni\Documents\__MY_DOCUMENTS\Dev\level_generator"
    r"\solutions\color_matching"
)

WORKER_OUTPUT_DIR = os.path.normpath(
    r"C:\Users\vjuni\Documents\__MY_DOCUMENTS\Dev"
    r"\storage_controller\Assets\StorageController\Resources\levels"
    r"\WorkerLevels"
)
WORKER_SOLUTIONS_DIR = os.path.normpath(
    r"C:\Users\vjuni\Documents\__MY_DOCUMENTS\Dev\level_generator"
    r"\solutions\worker"
)

# Соответствует WorkerGameRules в storage_controller.
WORKER_TIME_LIMIT_SECONDS = 999
# Два разных понятия с одинаковым числовым значением сегодня (как и в
# C#): MAX_COLUMN_HEIGHT - потолок для СТОПКИ ящиков при размещении,
# MAXIMUM_ACTION_ROW - самая верхняя строка, которую может занять тело
# рабочего или переносимый ящик (на неё ничего никогда не кладут, но
# стоять/прыгать через неё можно) - см. WorkerGameRules.MaximumActionRow.
WORKER_MAX_COLUMN_HEIGHT = GRID_H
WORKER_MAXIMUM_ACTION_ROW = GRID_H
WORKER_EMPTY_JUMP_HEIGHT = 2
WORKER_CARRYING_JUMP_HEIGHT = 1
# Issue #153: на сколько колонок вперёд может унести прыжок, "если
# препятствия позволяют" - см. WorkerGameRules.JumpHorizontalReach.
WORKER_JUMP_HORIZONTAL_REACH = 2
# Worker поддерживает только 1x1, широкий (2x1) и высокий (1x2) ящики -
# в отличие от crane/color, 2x2 здесь не разрешён
# (WorkerGameRules.IsAllowedBoxSize).
WORKER_ALLOWED_SIZES: List[Tuple[int, int]] = [(1, 1), (2, 1), (1, 2)]

ALLOWED_SIZES: List[Tuple[int, int]] = [
    (1, 1), (2, 1), (1, 2), (2, 2), (3, 2), (2, 3),
]
TARGET_SIZES: List[Tuple[int, int]] = [(1, 1), (2, 1), (1, 2), (2, 2)]

# Issue #15: at 3-4 colors, extra (non-target) boxes are limited to
# width 1 - empirically, allowing width-2 boxes (let alone the 3-unit
# ALLOWED_SIZES entries) makes color-matching layouts far less likely to
# be solvable at all under the color-support rule, and when solvable,
# shortens the typical solution. Dropping width-2 raised the hit rate
# for 15+/12+-move, 3-4-color levels by roughly 7-20x in testing. Only
# affects extra boxes - the target keeps using TARGET_SIZES as before.
COLOR_RESTRICTED_EXTRA_SIZES: List[Tuple[int, int]] = [(1, 1), (1, 2)]
# Threshold at which the "most boxes must actually move" rule below
# kicks in - empirically the more natural cutoff for capped-size
# color levels turned out to be 12, not the originally proposed 15.
COLOR_LONG_SOLUTION_THRESHOLD = 12
COLOR_MIN_MOVED_FRACTION = 0.8
# How many different colorings to try against the SAME physical layout
# before giving up on it and building a new one from scratch - cheap
# (no re-placement needed) relative to a full re-generation, and was
# the single biggest lever found for making 3-4-color, long-solution
# levels generate at all (0/60000 fresh attempts -> ~1/900 with this).
COLOR_RECOLOR_ATTEMPTS = 30

# Минимальная доля площади (сумма w*h), которую должен занимать каждый
# используемый цвет, от суммарной площади всех ящиков уровня - защита от
# уровней, где один цвет представлен единственным маленьким ящиком.
COLOR_MIN_AREA_FRACTION: Dict[int, float] = {2: 0.30, 3: 0.20, 4: 0.10}
# Минимальное количество ящиков каждого цвета - только при 2 и 3 цветах.
# При 2 цветах порог зависит от общего числа ящиков на уровне; при
# 3 цветах он действует только начиная с 8 ящиков (при меньшем их
# числе действует только комбинированное правило ниже).
COLOR_MIN_BOXES_PER_COLOR_SMALL_LEVEL = 2  # <8 ящиков всего (только 2 цвета)
COLOR_MIN_BOXES_PER_COLOR_LARGE_LEVEL = 3  # >=8 ящиков всего (только 2 цвета)
COLOR_MIN_BOXES_PER_COLOR_3COLORS_LARGE_LEVEL = 2  # >=8 ящиков, 3 цвета
# Комбинированные правила (всегда, независимо от общего числа ящиков):
# любые 2 из 3 цветов вместе - не менее стольки-то ящиков; любые 3 из 4
# цветов вместе - не менее стольки-то ящиков.
COLOR_MIN_BOXES_ANY_2_OF_3_COLORS = 3
COLOR_MIN_BOXES_ANY_3_OF_4_COLORS = 4

# Цвета соответствуют BoxColor в storage_controller (без None).
# Игра поддерживает 2-4 цвета на уровень (ColorMatchingGameRules).
COLOR_PALETTE: List[str] = ["red", "blue", "green", "yellow"]
MIN_COLOR_COUNT = 2
MAX_COLOR_COUNT = 4


def _color_balance_ok(boxes: List["Box"], color_count: int) -> bool:
    """
    Проверяет минимальное представление каждого цвета среди boxes
    (все boxes уже раскрашены и используют ровно color_count разных
    цветов - это гарантируется вызывающим кодом до вызова этой функции).
    См. COLOR_MIN_AREA_FRACTION и COLOR_MIN_BOXES_* выше.
    """
    total_boxes = len(boxes)
    total_area = sum(b.w * b.h for b in boxes)
    counts: Dict[str, int] = {}
    areas: Dict[str, int] = {}
    for b in boxes:
        counts[b.color] = counts.get(b.color, 0) + 1
        areas[b.color] = areas.get(b.color, 0) + b.w * b.h

    min_fraction = COLOR_MIN_AREA_FRACTION[color_count]
    for area in areas.values():
        if area / total_area < min_fraction:
            return False

    if color_count == 2:
        min_count = (
            COLOR_MIN_BOXES_PER_COLOR_LARGE_LEVEL
            if total_boxes >= 8
            else COLOR_MIN_BOXES_PER_COLOR_SMALL_LEVEL
        )
        for count in counts.values():
            if count < min_count:
                return False

    elif color_count == 3:
        if total_boxes >= 8:
            for count in counts.values():
                if count < COLOR_MIN_BOXES_PER_COLOR_3COLORS_LARGE_LEVEL:
                    return False
        colors = list(counts.keys())
        for i in range(len(colors)):
            for j in range(i + 1, len(colors)):
                pair_count = counts[colors[i]] + counts[colors[j]]
                if pair_count < COLOR_MIN_BOXES_ANY_2_OF_3_COLORS:
                    return False

    elif color_count == 4:
        colors = list(counts.keys())
        for i in range(len(colors)):
            for j in range(i + 1, len(colors)):
                for k in range(j + 1, len(colors)):
                    trio_count = (
                        counts[colors[i]] + counts[colors[j]] + counts[colors[k]]
                    )
                    if trio_count < COLOR_MIN_BOXES_ANY_3_OF_4_COLORS:
                        return False

    return True

Occ = Dict[Tuple[int, int], int]  # (x, y) → индекс ящика


# ─── Модель ящика ────────────────────────────────────────────────────────────
class Box:
    __slots__ = ("id", "x", "y", "w", "h", "is_target", "color")

    def __init__(
        self,
        bid: str,
        x: int,
        y: int,
        w: int,
        h: int,
        is_target: bool,
        color: Optional[str] = None,
    ):
        self.id = bid
        self.x = x
        self.y = y
        self.w = w
        self.h = h
        self.is_target = is_target
        self.color = color  # None вне режима Color Matching


# ─── Вспомогательные функции ─────────────────────────────────────────────────
def build_occ(boxes: List[Box], positions: Tuple[Tuple[int, int], ...]) -> Occ:
    """Строит карту занятости (x,y) → индекс ящика."""
    occ: Occ = {}
    for i, b in enumerate(boxes):
        px, py = positions[i]
        for dx in range(b.w):
            for dy in range(b.h):
                occ[(px + dx, py + dy)] = i
    return occ


def col_top(occ: Occ, blocked: Set[Tuple[int, int]], x: int) -> int:
    """Наибольший занятый y в колонне x (или -1, если пусто)."""
    for y in range(GRID_H - 1, -1, -1):
        if (x, y) in occ or (x, y) in blocked:
            return y
    return -1


def placement_y(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    left: int,
    w: int,
    h: int,
) -> Optional[int]:
    """
    Возвращает y, куда приземлится ящик (w×h) при размещении в колоннах
    [left, left+w), или None, если размещение невозможно.
    Проверяет: полная опора снизу, нет переполнения сетки, нет перекрытий.
    """
    py = 0
    for x in range(left, left + w):
        py = max(py, col_top(occ, blocked, x) + 1)

    if py + h > GRID_H:
        return None

    # Полная опора: все ячейки на уровне py-1 должны быть заняты ящиками
    if py > 0:
        for x in range(left, left + w):
            sup = (x, py - 1)
            if sup in blocked or sup not in occ:
                return None

    # Нет перекрытий с существующими объектами
    for x in range(left, left + w):
        for y in range(py, py + h):
            if (x, y) in occ or (x, y) in blocked:
                return None

    return py


def uniform_support_color(
    occ: Occ,
    boxes: List[Box],
    left: int,
    w: int,
    py: int,
) -> Optional[str]:
    """
    Для py>0: цвет опорных ящиков под (left, py) шириной w, если ВСЕ
    опорные ячейки принадлежат ящикам одного цвета, иначе None (в т.ч.
    если py==0 — там опоры нет, вызывать эту функцию для пола бессмысленно).
    """
    if py <= 0:
        return None
    colors = {boxes[occ[(x, py - 1)]].color for x in range(left, left + w)}
    return colors.pop() if len(colors) == 1 else None


def color_fits_support(
    occ: Occ,
    boxes: List[Box],
    left: int,
    w: int,
    py: int,
    color: str,
) -> bool:
    """
    True если ящик данного цвета может приземлиться на (left, py):
    пол (py==0) подходит всегда, иначе все опорные ящики должны быть
    того же цвета.
    """
    if py == 0:
        return True
    return uniform_support_color(occ, boxes, left, w, py) == color


def _transport_clear_at(
    occ_wo: Occ,
    blocked: Set[Tuple[int, int]],
    left: int,
    w: int,
    h: int,
) -> bool:
    """
    True если транспортные строки над ящиком (w×h) в колонне left свободны.
    """
    if h == 1:
        return True
    for y in range(TRANSPORT_ROW - h + 1, TRANSPORT_ROW):
        for x in range(left, left + w):
            if (x, y) in occ_wo or (x, y) in blocked:
                return False
    return True


# ─── BFS-решатель ────────────────────────────────────────────────────────────
def solve(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    max_depth: int = 30,
    max_states: int = 150_000,
) -> int:
    """
    BFS по состояниям. Возвращает минимальное число подъёмов для доставки
    целевого ящика к выходу, или -1 если нет решения.
    Симулирует точную механику крана: anchor = x + (w-1)*0.5 (half-integer
    для width-2), перемещение пошагово влево/вправо с проверкой коридора.
    Прерывается досрочно при превышении max_states.
    """
    initial: Tuple[Tuple[int, int], ...] = tuple((b.x, b.y) for b in boxes)
    queue: deque = deque([(initial, 0)])
    visited: Set[Tuple] = {initial}

    while queue:
        if len(visited) > max_states:
            return -1
        positions, depth = queue.popleft()
        if depth >= max_depth:
            continue

        occ = build_occ(boxes, positions)

        for i, b in enumerate(boxes):
            bx, by = positions[i]

            # Проверка: ничего нет сверху в колоннах ящика
            blocked_above = False
            for x in range(bx, bx + b.w):
                for y in range(by + b.h, GRID_H):
                    if (x, y) in occ or (x, y) in blocked:
                        blocked_above = True
                        break
                if blocked_above:
                    break
            if blocked_above:
                continue

            occ_wo = {k: v for k, v in occ.items() if v != i}

            # Проверка транспортного коридора в точке подъёма
            if not _transport_clear_at(occ_wo, blocked, bx, b.w, b.h):
                continue

            # Пошаговое перемещение крана: anchor = bx + (w-1)*0.5
            center_offset: float = (b.w - 1) * 0.5
            init_anchor: float = bx + center_offset

            seen_lefts: Set[int] = set()
            reachable_lefts: List[int] = []

            def _add(anchor: float) -> None:
                left = int(round(anchor - center_offset))
                if left not in seen_lefts:
                    seen_lefts.add(left)
                    reachable_lefts.append(left)

            _add(init_anchor)

            anchor = init_anchor
            while True:
                next_anchor = anchor - 1
                next_left = int(round(next_anchor - center_offset))
                if next_left < 0:
                    break
                if not _transport_clear_at(
                    occ_wo,
                    blocked,
                    next_left,
                    b.w,
                    b.h
                ):
                    break
                anchor = next_anchor
                _add(anchor)

            anchor = init_anchor
            while True:
                next_anchor = anchor + 1
                next_left = int(round(next_anchor - center_offset))
                if next_left + b.w > GRID_W:
                    break
                if not _transport_clear_at(
                    occ_wo,
                    blocked,
                    next_left,
                    b.w,
                    b.h
                ):
                    break
                anchor = next_anchor
                _add(anchor)

            for left in reachable_lefts:
                to_y = placement_y(occ_wo, blocked, left, b.w, b.h)
                if to_y is None:
                    continue

                # Проверяем доставку цели (в т.ч. когда left == bx)
                if b.is_target and to_y == 0 and left + b.w == GRID_W:
                    return depth + 1

                if left == bx and to_y == by:
                    continue  # та же позиция — бессмысленный ход

                new_pos = list(positions)
                new_pos[i] = (left, to_y)
                state = tuple(new_pos)
                if state not in visited:
                    visited.add(state)
                    queue.append((state, depth + 1))

    return -1


def solve_color(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    max_depth: int = 30,
    max_states: int = 150_000,
) -> int:
    """
    Как solve(), но для режима Color Matching: ящик можно поставить не
    на пол, только если все опорные ящики под ним того же цвета.
    """
    initial: Tuple[Tuple[int, int], ...] = tuple((b.x, b.y) for b in boxes)
    queue: deque = deque([(initial, 0)])
    visited: Set[Tuple] = {initial}

    while queue:
        if len(visited) > max_states:
            return -1
        positions, depth = queue.popleft()
        if depth >= max_depth:
            continue

        occ = build_occ(boxes, positions)

        for i, b in enumerate(boxes):
            bx, by = positions[i]

            blocked_above = False
            for x in range(bx, bx + b.w):
                for y in range(by + b.h, GRID_H):
                    if (x, y) in occ or (x, y) in blocked:
                        blocked_above = True
                        break
                if blocked_above:
                    break
            if blocked_above:
                continue

            occ_wo = {k: v for k, v in occ.items() if v != i}
            if not _transport_clear_at(occ_wo, blocked, bx, b.w, b.h):
                continue

            center_offset: float = (b.w - 1) * 0.5
            init_anchor: float = bx + center_offset
            seen_lefts: Set[int] = set()
            reachable_lefts: List[int] = []

            def _add(anchor: float) -> None:
                left = int(round(anchor - center_offset))
                if left not in seen_lefts:
                    seen_lefts.add(left)
                    reachable_lefts.append(left)

            _add(init_anchor)
            anchor = init_anchor
            while True:
                next_anchor = anchor - 1
                next_left = int(round(next_anchor - center_offset))
                if next_left < 0:
                    break
                if not _transport_clear_at(
                    occ_wo, blocked, next_left, b.w, b.h
                ):
                    break
                anchor = next_anchor
                _add(anchor)

            anchor = init_anchor
            while True:
                next_anchor = anchor + 1
                next_left = int(round(next_anchor - center_offset))
                if next_left + b.w > GRID_W:
                    break
                if not _transport_clear_at(
                    occ_wo, blocked, next_left, b.w, b.h
                ):
                    break
                anchor = next_anchor
                _add(anchor)

            for left in reachable_lefts:
                to_y = placement_y(occ_wo, blocked, left, b.w, b.h)
                if to_y is None:
                    continue
                if b.color is None:
                    continue  # цветной ящик всегда имеет цвет
                if not color_fits_support(
                    occ_wo, boxes, left, b.w, to_y, b.color
                ):
                    continue

                if b.is_target and to_y == 0 and left + b.w == GRID_W:
                    return depth + 1

                if left == bx and to_y == by:
                    continue

                new_pos = list(positions)
                new_pos[i] = (left, to_y)
                state = tuple(new_pos)
                if state not in visited:
                    visited.add(state)
                    queue.append((state, depth + 1))

    return -1


# ─── BFS с восстановлением пути ──────────────────────────────────────────────
Move = Tuple[int, int, int, int, int]  # (box_idx, from_x, from_y, to_x, to_y)


def solve_with_path(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    max_depth: int = 30,
    max_states: int = 150_000,
) -> Optional[List[Move]]:
    """
    BFS идентичный solve(), но дополнительно отслеживает came_from
    для восстановления последовательности ходов.
    Возвращает список (box_idx, from_x, from_y, to_x, to_y) или None.
    Прерывается досрочно при превышении max_states.
    """
    initial: Tuple = tuple((b.x, b.y) for b in boxes)
    came_from: Dict = {initial: None}  # state -> (parent_state, move) | None
    queue: deque = deque([(initial, 0)])

    while queue:
        if len(came_from) > max_states:
            return None
        positions, depth = queue.popleft()
        if depth >= max_depth:
            continue

        occ = build_occ(boxes, positions)

        for i, b in enumerate(boxes):
            bx, by = positions[i]

            blocked_above = False
            for x in range(bx, bx + b.w):
                for y in range(by + b.h, GRID_H):
                    if (x, y) in occ or (x, y) in blocked:
                        blocked_above = True
                        break
                if blocked_above:
                    break
            if blocked_above:
                continue

            occ_wo = {k: v for k, v in occ.items() if v != i}
            if not _transport_clear_at(occ_wo, blocked, bx, b.w, b.h):
                continue

            center_offset: float = (b.w - 1) * 0.5
            init_anchor: float = bx + center_offset
            seen_lefts: Set[int] = set()
            reachable_lefts: List[int] = []

            def _add(anchor: float) -> None:
                left = int(round(anchor - center_offset))
                if left not in seen_lefts:
                    seen_lefts.add(left)
                    reachable_lefts.append(left)

            _add(init_anchor)
            anchor = init_anchor
            while True:
                next_anchor = anchor - 1
                next_left = int(round(next_anchor - center_offset))
                if next_left < 0:
                    break
                if not _transport_clear_at(
                    occ_wo, blocked, next_left, b.w, b.h
                ):
                    break
                anchor = next_anchor
                _add(anchor)

            anchor = init_anchor
            while True:
                next_anchor = anchor + 1
                next_left = int(round(next_anchor - center_offset))
                if next_left + b.w > GRID_W:
                    break
                if not _transport_clear_at(
                    occ_wo, blocked, next_left, b.w, b.h
                ):
                    break
                anchor = next_anchor
                _add(anchor)

            for left in reachable_lefts:
                to_y = placement_y(occ_wo, blocked, left, b.w, b.h)
                if to_y is None:
                    continue

                if b.is_target and to_y == 0 and left + b.w == GRID_W:
                    final_move: Move = (i, bx, by, left, to_y)
                    path: List[Move] = []
                    state = positions
                    while came_from[state] is not None:
                        parent, m = came_from[state]
                        path.append(m)
                        state = parent
                    path.reverse()
                    path.append(final_move)
                    return path

                if left == bx and to_y == by:
                    continue

                new_pos = list(positions)
                new_pos[i] = (left, to_y)
                new_state = tuple(new_pos)
                if new_state not in came_from:
                    came_from[new_state] = (positions, (i, bx, by, left, to_y))
                    queue.append((new_state, depth + 1))

    return None


def solve_color_with_path(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    max_depth: int = 30,
    max_states: int = 150_000,
) -> Optional[List[Move]]:
    """
    Как solve_with_path(), но с проверкой соответствия цвета опоре
    (см. solve_color()).
    """
    initial: Tuple = tuple((b.x, b.y) for b in boxes)
    came_from: Dict = {initial: None}
    queue: deque = deque([(initial, 0)])

    while queue:
        if len(came_from) > max_states:
            return None
        positions, depth = queue.popleft()
        if depth >= max_depth:
            continue

        occ = build_occ(boxes, positions)

        for i, b in enumerate(boxes):
            bx, by = positions[i]

            blocked_above = False
            for x in range(bx, bx + b.w):
                for y in range(by + b.h, GRID_H):
                    if (x, y) in occ or (x, y) in blocked:
                        blocked_above = True
                        break
                if blocked_above:
                    break
            if blocked_above:
                continue

            occ_wo = {k: v for k, v in occ.items() if v != i}
            if not _transport_clear_at(occ_wo, blocked, bx, b.w, b.h):
                continue

            center_offset: float = (b.w - 1) * 0.5
            init_anchor: float = bx + center_offset
            seen_lefts: Set[int] = set()
            reachable_lefts: List[int] = []

            def _add(anchor: float) -> None:
                left = int(round(anchor - center_offset))
                if left not in seen_lefts:
                    seen_lefts.add(left)
                    reachable_lefts.append(left)

            _add(init_anchor)
            anchor = init_anchor
            while True:
                next_anchor = anchor - 1
                next_left = int(round(next_anchor - center_offset))
                if next_left < 0:
                    break
                if not _transport_clear_at(
                    occ_wo, blocked, next_left, b.w, b.h
                ):
                    break
                anchor = next_anchor
                _add(anchor)

            anchor = init_anchor
            while True:
                next_anchor = anchor + 1
                next_left = int(round(next_anchor - center_offset))
                if next_left + b.w > GRID_W:
                    break
                if not _transport_clear_at(
                    occ_wo, blocked, next_left, b.w, b.h
                ):
                    break
                anchor = next_anchor
                _add(anchor)

            for left in reachable_lefts:
                to_y = placement_y(occ_wo, blocked, left, b.w, b.h)
                if to_y is None:
                    continue
                if b.color is None:
                    continue  # цветной ящик всегда имеет цвет
                if not color_fits_support(
                    occ_wo, boxes, left, b.w, to_y, b.color
                ):
                    continue

                if b.is_target and to_y == 0 and left + b.w == GRID_W:
                    final_move: Move = (i, bx, by, left, to_y)
                    path: List[Move] = []
                    state = positions
                    while came_from[state] is not None:
                        parent, m = came_from[state]
                        path.append(m)
                        state = parent
                    path.reverse()
                    path.append(final_move)
                    return path

                if left == bx and to_y == by:
                    continue

                new_pos = list(positions)
                new_pos[i] = (left, to_y)
                new_state = tuple(new_pos)
                if new_state not in came_from:
                    came_from[new_state] = (positions, (i, bx, by, left, to_y))
                    queue.append((new_state, depth + 1))

    return None


# ─── BFS-решатель для режима Worker ──────────────────────────────────────────
# Полная копия правил WorkerRules.cs/WorkerLevelSolver.cs из storage_controller
# (issue #152 - широкие/высокие ящики, блокированные ячейки, потолок действия;
# issue #153 - прыжок с запасом в WORKER_JUMP_HORIZONTAL_REACH колонок и
# затуханием высоты). Решателю нужна только ДИСКРЕТНАЯ версия правил (шаг на
# 1 клетку) - непрерывное скольжение и "перенос по инерции" при падении в
# реальной игре влияют только на рендер, не на решаемость головоломки, так что
# сюда не портируются.
#
# Состояние: позиции установленных ящиков (None у переносимого - он снят с
# сетки, как и в WorkerState.InstalledBoxPositions на стороне игры), позиция и
# направление рабочего, индекс переносимого ящика (-1, если руки пусты). X
# рабочего - float: обычно целое, но ровно X.5 всё время, пока рабочий несёт
# ШИРОКИЙ (2x1) ящик - при подборе он сдвигается на половину клетки между
# своей колонкой и колонкой ящика и остаётся там, пока не положит ящик (тот же
# приём, что уже используется для крана - anchor = x + (w-1)*0.5 в solve()).
WorkerPositions = Tuple[Optional[Tuple[int, int]], ...]
WorkerState = Tuple[WorkerPositions, float, int, int, int]
# ("move"/"jump"/"face", direction, distance) или ("pickup"/"putdown", 0, 0) -
# distance для jump это реально пройденные колонки (1 или 2), для остальных
# не используется (всегда 0 или 1, не влияет на решатель).
WorkerMove = Tuple[str, int, int]


def _worker_occ(positions: WorkerPositions, boxes: List[Box]) -> Occ:
    """Как build_occ(), но positions[i] может быть None (сейчас в руках)."""
    occ: Occ = {}
    for i, b in enumerate(boxes):
        pos = positions[i]
        if pos is None:
            continue
        px, py = pos
        for dx in range(b.w):
            for dy in range(b.h):
                occ[(px + dx, py + dy)] = i
    return occ


def _worker_surface_height(
    occ: Occ, blocked: Set[Tuple[int, int]], x: int
) -> int:
    """Топ ящика/блока в колонне x + 1 (аналог GetSurfaceHeight -
    "приближение сверху", как для прыжка/размещения: плавающее
    препятствие блокирует весь столбец под собой)."""
    return col_top(occ, blocked, x) + 1


def _worker_fall_from(
    occ: Occ, blocked: Set[Tuple[int, int]], x: int, from_y: int
) -> int:
    """Куда рабочий приземлится в колонне x, падая с высоты from_y
    (аналог FallFrom) - в отличие от _worker_surface_height, не видит
    ничего ВЫШЕ from_y, так что даёт пройти под плавающим блоком."""
    y = from_y
    while y > 0 and (x, y - 1) not in occ and (x, y - 1) not in blocked:
        y -= 1
    return y


def _worker_row_occupied(
    occ: Occ, blocked: Set[Tuple[int, int]], y: int, width: int
) -> int:
    """Число занятых клеток (ящик или блок) в ряду y."""
    return sum(1 for x in range(width) if (x, y) in occ or (x, y) in blocked)


def _worker_top_box_at(
    positions: WorkerPositions, boxes: List[Box], x: int
) -> Optional[int]:
    """Индекс установленного ящика с наибольшим верхом среди тех, чей
    [x0, x0+w) содержит колонку x (аналог TryGetTopBox - важно для
    широких ящиков, не только точное совпадение колонны)."""
    best: Optional[int] = None
    best_top = -1
    for i, b in enumerate(boxes):
        pos = positions[i]
        if pos is None:
            continue
        px, py = pos
        if not (px <= x < px + b.w):
            continue
        top = py + b.h
        if top > best_top:
            best_top = top
            best = i
    return best


def _worker_wide_footprint_clear(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    center_x: int,
    row: int,
    width: int,
) -> bool:
    """Свободны ли 3 колонки center_x-1..center_x+1 на высоте row
    (аналог IsWideCarryFootprintClear)."""
    if row >= GRID_H:
        return True
    for x in range(center_x - 1, center_x + 2):
        if x < 0 or x >= width:
            return False
        if (x, row) in occ or (x, row) in blocked:
            return False
    return True


def _worker_is_tall_bottom_row(
    positions: WorkerPositions, boxes: List[Box], row: int
) -> bool:
    """Есть ли уже установленный высокий (h=2) ящик с нижней клеткой в
    этом ряду (аналог IsExistingTallBoxBottomRow - его нижний ряд
    освобождён от row-fill reservation)."""
    for i, b in enumerate(boxes):
        pos = positions[i]
        if pos is not None and b.h == 2 and pos[1] == row:
            return True
    return False


def _worker_row_fill_denied(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    positions: WorkerPositions,
    boxes: List[Box],
    width: int,
    row: int,
    cells_added: int,
    is_this_row_a_tall_bottom_row: bool,
) -> bool:
    """Заполнит ли добавление cells_added клеток в row ряд ПОЛНОСТЬЮ -
    запрещено, кроме нижнего ряда высокого ящика (аналог
    IsRowFillDenied)."""
    if is_this_row_a_tall_bottom_row or _worker_is_tall_bottom_row(
        positions, boxes, row
    ):
        return False
    return _worker_row_occupied(occ, blocked, row, width) + cells_added >= width


def _worker_start_column_max_rise(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    column: int,
    from_y: int,
    carried_height: int,
) -> int:
    """Насколько высоко рабочий (и переносимый ящик над ним) может
    подняться строго вверх в СВОЕЙ колонне, прежде чем что-то сверху
    заблокирует дальнейший подъём (аналог GetStartColumnMaxRise)."""
    rise = 0
    while from_y + rise + 1 <= WORKER_MAXIMUM_ACTION_ROW:
        worker_row = from_y + rise + 1
        if worker_row < GRID_H and (
            (column, worker_row) in occ or (column, worker_row) in blocked
        ):
            break

        box_blocked = False
        for box_row in range(worker_row + 1, worker_row + carried_height + 1):
            if box_row > WORKER_MAXIMUM_ACTION_ROW or (
                box_row < GRID_H
                and ((column, box_row) in occ or (column, box_row) in blocked)
            ):
                box_blocked = True
                break
        if box_blocked:
            break

        rise += 1

    return rise


def _worker_can_move_step(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    boxes: List[Box],
    width: int,
    wx: float,
    wy: int,
    carried: int,
    direction: int,
) -> Optional[Tuple[float, int]]:
    """Один дискретный шаг Move в direction - (new_wx, new_wy) или None
    (аналог WorkerRules.CanMove на 1 клетку/half-клетку)."""
    carried_box = boxes[carried] if carried >= 0 else None
    carried_height = carried_box.h if carried_box is not None else 0

    column = (
        math.floor(wx) + 1 if direction > 0 else math.ceil(wx) - 1
    )
    if column < 0 or column >= width:
        return None

    for row_offset in range(carried_height + 1):
        row = wy + row_offset
        if row < GRID_H and ((column, row) in occ or (column, row) in blocked):
            return None

    landing_y = _worker_fall_from(occ, blocked, column, wy)

    if carried_box is not None and carried_box.w == 2:
        if not _worker_wide_footprint_clear(
            occ, blocked, column, landing_y + 1, width
        ):
            return None

    return (wx + direction, landing_y)


def _worker_can_jump(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    boxes: List[Box],
    width: int,
    wx: float,
    wy: int,
    carried: int,
    direction: int,
) -> Optional[Tuple[int, int, int]]:
    """Прыжок в direction (±1) - (колонка, высота, реальная дистанция
    1 или 2) или None (аналог WorkerRules.CanJump: ближайшая колонка с
    настоящим подъёмом побеждает сразу; колонка не выше старта
    запоминается как fallback, пока есть запас дальше; свес широкого
    переносимого ящика - единственная причина пробовать следующий шаг
    вместо отказа)."""
    start_column = round(wx)
    carried_box = boxes[carried] if carried >= 0 else None
    # "Тяжёлый" переносимый ящик - любой не 1x1 (широкий ИЛИ высокий),
    # как CellCount==2 в C#.
    carried_is_heavy = carried_box is not None and carried_box.w * carried_box.h == 2

    raw_max_rise = (
        0 if carried_is_heavy
        else WORKER_CARRYING_JUMP_HEIGHT if carried_box is not None
        else WORKER_EMPTY_JUMP_HEIGHT
    )
    carried_top_extra = carried_box.h if carried_box is not None else 0
    ceiling_cap = WORKER_MAXIMUM_ACTION_ROW - wy - carried_top_extra
    start_column_cap = _worker_start_column_max_rise(
        occ, blocked, start_column, wy, carried_top_extra
    )

    fallback: Optional[Tuple[int, int, int]] = None

    for step in range(1, WORKER_JUMP_HORIZONTAL_REACH + 1):
        candidate_column = start_column + direction * step
        if candidate_column < 0 or candidate_column >= width:
            break

        step_max_rise = (
            max(0, raw_max_rise - (step - 1))
            if carried_box is None
            else raw_max_rise
        )
        effective_max_rise = min(step_max_rise, ceiling_cap, start_column_cap)

        candidate_height = _worker_surface_height(occ, blocked, candidate_column)
        if candidate_height - wy > effective_max_rise:
            break

        if carried_box is not None and carried_box.w == 2:
            if not _worker_wide_footprint_clear(
                occ, blocked, candidate_column, candidate_height + 1, width
            ):
                continue

        is_genuine_rise = candidate_height > wy
        if (
            carried_box is None
            and not is_genuine_rise
            and step < WORKER_JUMP_HORIZONTAL_REACH
        ):
            fallback = (candidate_column, candidate_height, step)
            continue

        return (candidate_column, candidate_height, step)

    return fallback


def _worker_placement_column(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    wx: float,
    wy: int,
    facing: int,
    width: int,
) -> int:
    """Куда переставится рабочий при выкладывании ящика - "позади"
    (колонка, противоположная facing) если валидна и свободна на
    высоте wy, иначе "спереди" (аналог GetPlacementWorkerColumn)."""
    behind_column = math.floor(wx) if facing > 0 else math.ceil(wx)
    front_column = math.ceil(wx) if facing > 0 else math.floor(wx)

    def is_valid(column: int) -> bool:
        return (
            0 <= column < width
            and (column, wy) not in occ
            and (column, wy) not in blocked
        )

    return behind_column if is_valid(behind_column) else front_column


def _worker_can_pick_up(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    positions: WorkerPositions,
    boxes: List[Box],
    wx: float,
    wy: int,
    adjacent_x: int,
) -> Optional[int]:
    """Индекс ящика, который можно подобрать в колонне adjacent_x, или
    None (аналог CanPickUp: окно досягаемости по высоте + свободна ли
    вся колонка РАБОЧЕГО на высотах, которые займёт переносимый ящик)."""
    box_index = _worker_top_box_at(positions, boxes, adjacent_x)
    if box_index is None:
        return None

    box = boxes[box_index]
    pos = positions[box_index]
    assert pos is not None
    box_y = pos[1]

    reach_ok = (
        wy - 1 <= box_y <= wy + 1 if box.h == 2 else wy <= box_y <= wy + 1
    )
    if not reach_ok:
        return None

    worker_column = round(wx)
    for row_offset in range(1, box.h + 1):
        carried_row = wy + row_offset
        if carried_row < GRID_H and (
            (worker_column, carried_row) in occ
            or (worker_column, carried_row) in blocked
        ):
            return None

    return box_index


def _worker_can_place_single(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    positions: WorkerPositions,
    boxes: List[Box],
    width: int,
    wy: int,
    adjacent_x: int,
    box: Box,
) -> Optional[Tuple[int, int]]:
    column_height = _worker_surface_height(occ, blocked, adjacent_x)
    if column_height + box.h > WORKER_MAX_COLUMN_HEIGHT:
        return None
    if column_height > wy + 1:
        return None

    is_delivery = box.is_target and adjacent_x == width - 1 and column_height == 0
    is_tall = box.h == 2
    if _worker_row_fill_denied(
        occ, blocked, positions, boxes, width, column_height, 1, is_tall
    ) and not is_delivery:
        return None

    if is_tall and _worker_row_fill_denied(
        occ, blocked, positions, boxes, width, column_height + 1, 1, False
    ) and not is_delivery:
        return None

    return (adjacent_x, column_height)


def _worker_can_place_wide(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    positions: WorkerPositions,
    boxes: List[Box],
    width: int,
    wy: int,
    adjacent_x: int,
    facing: int,
    box: Box,
) -> Optional[Tuple[int, int]]:
    other_x = adjacent_x + facing
    left_x = min(adjacent_x, other_x)
    if left_x < 0 or left_x + 1 >= width:
        return None

    left_height = _worker_surface_height(occ, blocked, left_x)
    right_height = _worker_surface_height(occ, blocked, left_x + 1)
    if left_height != right_height:
        return None

    column_height = left_height
    if column_height + 1 > WORKER_MAX_COLUMN_HEIGHT:
        return None
    if column_height > wy + 1:
        return None

    is_delivery = box.is_target and left_x == width - 1 and column_height == 0
    if _worker_row_fill_denied(
        occ, blocked, positions, boxes, width, column_height, 2, False
    ) and not is_delivery:
        return None

    return (left_x, column_height)


def _worker_can_place(
    occ: Occ,
    blocked: Set[Tuple[int, int]],
    positions: WorkerPositions,
    boxes: List[Box],
    width: int,
    wy: int,
    adjacent_x: int,
    facing: int,
    carried: int,
) -> Optional[Tuple[int, int]]:
    """(x, y) куда встанет переносимый ящик, или None (аналог
    CanPlace/CanPlaceSingleColumn/CanPlaceWide)."""
    box = boxes[carried]
    if box.w == 2:
        return _worker_can_place_wide(
            occ, blocked, positions, boxes, width, wy, adjacent_x, facing, box
        )
    return _worker_can_place_single(
        occ, blocked, positions, boxes, width, wy, adjacent_x, box
    )


def _worker_transitions(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    width: int,
    state: WorkerState,
) -> List[Tuple[WorkerState, WorkerMove, bool]]:
    """
    Возвращает список (новое_состояние, действие, доставлена_ли_цель)
    для всех допустимых действий рабочего из state. Точная копия
    структуры WorkerLevelSolver.Expand(): move/jump в направлении,
    противоположном текущему facing, недоступны напрямую - сначала
    нужно развернуться (действие "face", тоже расходует шаг, как в
    реальной игре/решателе). Прыжок на месте (direction=0) решателю не
    нужен - он не меняет состояние.
    """
    positions, wx, wy, facing, carried = state
    occ = _worker_occ(positions, boxes)
    results: List[Tuple[WorkerState, WorkerMove, bool]] = []

    for direction in (-1, 1):
        if facing != direction:
            new_state: WorkerState = (positions, wx, wy, direction, carried)
            results.append((new_state, ("face", direction, 0), False))
            continue

        move_result = _worker_can_move_step(
            occ, blocked, boxes, width, wx, wy, carried, direction
        )
        if move_result is not None:
            new_wx, new_wy = move_result
            new_state = (positions, new_wx, new_wy, facing, carried)
            results.append((new_state, ("move", direction, 1), False))

        jump_result = _worker_can_jump(
            occ, blocked, boxes, width, wx, wy, carried, direction
        )
        if jump_result is not None:
            new_column, new_y, distance = jump_result
            new_state = (positions, float(new_column), new_y, facing, carried)
            results.append((new_state, ("jump", direction, distance), False))

    if carried >= 0:
        placement_column = _worker_placement_column(
            occ, blocked, wx, wy, facing, width
        )
        adjacent_x = placement_column + facing
        if 0 <= adjacent_x < width:
            place_result = _worker_can_place(
                occ, blocked, positions, boxes, width, wy, adjacent_x,
                facing, carried,
            )
            if place_result is not None:
                dest_x, dest_y = place_result
                is_delivery = (
                    boxes[carried].is_target
                    and dest_x == width - 1
                    and dest_y == 0
                )
                new_positions = list(positions)
                new_positions[carried] = (dest_x, dest_y)
                new_state = (
                    tuple(new_positions),
                    float(placement_column),
                    wy,
                    facing,
                    -1,
                )
                results.append(
                    (new_state, ("putdown", facing, 0), is_delivery)
                )
    else:
        adjacent_x = round(wx) + facing
        if 0 <= adjacent_x < width:
            pick_index = _worker_can_pick_up(
                occ, blocked, positions, boxes, wx, wy, adjacent_x
            )
            if pick_index is not None:
                box = boxes[pick_index]
                new_positions = list(positions)
                new_positions[pick_index] = None
                new_wx = round(wx) + facing * 0.5 if box.w == 2 else wx
                new_state = (
                    tuple(new_positions), new_wx, wy, facing, pick_index
                )
                results.append(
                    (new_state, ("pickup", facing, 0), False)
                )

    return results


def solve_worker(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    width: int,
    start_x: int,
    start_y: int,
    facing: int,
    max_depth: int = 60,
    max_states: int = 150_000,
) -> int:
    """
    BFS по состояниям рабочего. Возвращает минимальное число действий
    (move/jump/face/pickup/putdown) для доставки целевого ящика к
    выходу (width-1, 0), или -1 если решения нет. Прерывается досрочно
    при превышении max_states.
    """
    initial_positions: WorkerPositions = tuple((b.x, b.y) for b in boxes)
    initial: WorkerState = (
        initial_positions, float(start_x), start_y, facing, -1
    )
    queue: deque = deque([(initial, 0)])
    visited: Set[WorkerState] = {initial}

    while queue:
        if len(visited) > max_states:
            return -1
        state, depth = queue.popleft()
        if depth >= max_depth:
            continue

        for new_state, _move, delivered in _worker_transitions(
            boxes, blocked, width, state
        ):
            if delivered:
                return depth + 1
            if new_state not in visited:
                visited.add(new_state)
                queue.append((new_state, depth + 1))

    return -1


def solve_worker_with_path(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    width: int,
    start_x: int,
    start_y: int,
    facing: int,
    max_depth: int = 60,
    max_states: int = 150_000,
) -> Optional[List[WorkerMove]]:
    """Как solve_worker(), но восстанавливает последовательность действий."""
    initial_positions: WorkerPositions = tuple((b.x, b.y) for b in boxes)
    initial: WorkerState = (
        initial_positions, float(start_x), start_y, facing, -1
    )
    came_from: Dict[
        WorkerState, Optional[Tuple[WorkerState, WorkerMove]]
    ] = {initial: None}
    queue: deque = deque([(initial, 0)])

    while queue:
        if len(came_from) > max_states:
            return None
        state, depth = queue.popleft()
        if depth >= max_depth:
            continue

        for new_state, move, delivered in _worker_transitions(
            boxes, blocked, width, state
        ):
            if delivered:
                path: List[WorkerMove] = []
                cur = state
                while True:
                    entry = came_from[cur]
                    if entry is None:
                        break
                    parent, m = entry
                    path.append(m)
                    cur = parent
                path.reverse()
                path.append(move)
                return path

            if new_state not in came_from:
                came_from[new_state] = (state, move)
                queue.append((new_state, depth + 1))

    return None


def _moves_word(n: int) -> str:
    """Правильная форма слова 'ход' для числа n."""
    mod100 = n % 100
    mod10 = n % 10
    if 11 <= mod100 <= 19:
        return "ходов"
    if mod10 == 1:
        return "ход"
    if 2 <= mod10 <= 4:
        return "хода"
    return "ходов"


def write_solution(
    lid: str,
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    lift_limit: int,
    path: List[Move],
    solutions_dir: str = SOLUTIONS_DIR,
) -> None:
    """Записывает решение уровня в solutions_dir/<lid>.txt."""
    n = len(path)
    lines = [
        f"{lid}  |  {n} {_moves_word(n)}  |  liftLimit = {lift_limit}",
        "",
        (
            f"Сетка: {GRID_W}x{GRID_H}"
            f" (X: 0-{GRID_W - 1} слева направо,"
            f" Y: 0-{GRID_H - 1} снизу вверх)"
        ),
        "",
        "Начальные позиции:",
    ]
    for b in boxes:
        target_mark = "  [цель]" if b.is_target else ""
        color_mark = f"  [{b.color}]" if b.color else ""
        lines.append(
            f"  {b.id:<10} ({b.w}x{b.h})"
            f"  x={b.x}, y={b.y}{target_mark}{color_mark}"
        )
    lines.append("")
    lines.append("Решение:")
    for step, (bi, fx, fy, tx, ty) in enumerate(path, 1):
        b = boxes[bi]
        suffix = "  <-- ПОБЕДА" if step == n else ""
        lines.append(
            f"    {step}. {b.id:<10} ({b.w}x{b.h})"
            f"  ({fx},{fy}) -> ({tx},{ty}){suffix}"
        )
    os.makedirs(solutions_dir, exist_ok=True)
    out_path = os.path.join(solutions_dir, f"{lid}.txt")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


_WORKER_MOVE_LABELS = {
    ("move", -1): "идёт влево",
    ("move", 1): "идёт вправо",
    ("face", -1): "разворачивается влево",
    ("face", 1): "разворачивается вправо",
    ("jump", -1): "прыжок влево",
    ("jump", 1): "прыжок вправо",
    ("pickup", -1): "берёт ящик",
    ("pickup", 1): "берёт ящик",
    ("putdown", -1): "кладёт ящик",
    ("putdown", 1): "кладёт ящик",
}


def write_solution_worker(
    lid: str,
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    start_x: int,
    start_y: int,
    facing: int,
    path: List[WorkerMove],
    solutions_dir: str = WORKER_SOLUTIONS_DIR,
) -> None:
    """Записывает решение уровня режима Worker в solutions_dir/<lid>.txt."""
    n = len(path)
    lines = [
        f"{lid}  |  {n} {_moves_word(n)}  |  "
        f"timeLimitSeconds = {WORKER_TIME_LIMIT_SECONDS}",
        "",
        (
            f"Сетка: {GRID_W}x{GRID_H}"
            f" (X: 0-{GRID_W - 1} слева направо,"
            f" Y: 0-{GRID_H - 1} снизу вверх)"
        ),
        "",
        (
            f"Рабочий: x={start_x}, y={start_y}, лицом "
            f"{'влево' if facing < 0 else 'вправо'}"
        ),
    ]
    if blocked:
        lines.append(
            "Блокированные ячейки: "
            + ", ".join(f"({x},{y})" for x, y in sorted(blocked))
        )
    lines.append("")
    lines.append("Начальные позиции:")
    for b in boxes:
        target_mark = "  [цель]" if b.is_target else ""
        lines.append(f"  {b.id:<10} ({b.w}x{b.h})  x={b.x}, y={b.y}{target_mark}")
    lines.append("")
    lines.append("Решение:")
    for step, move in enumerate(path, 1):
        move_type, direction, distance = move
        label = _WORKER_MOVE_LABELS[(move_type, direction)]
        if move_type == "jump" and distance > 1:
            label = f"{label} ({distance} клетки)"
        suffix = "  <-- ПОБЕДА" if step == n else ""
        lines.append(f"    {step}. {label}{suffix}")
    os.makedirs(solutions_dir, exist_ok=True)
    out_path = os.path.join(solutions_dir, f"{lid}.txt")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


# ─── Генератор ───────────────────────────────────────────────────────────────
def _sig(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    include_color: bool = False,
) -> str:
    """
    Канонический ключ уровня для проверки уникальности. В режиме
    Color Matching цвет тоже входит в ключ — та же геометрия с другой
    раскраской допускает другие ходы, это другой уровень.
    """
    if include_color:
        key = tuple(sorted(
            (b.w, b.h, b.x, b.y, int(b.is_target), b.color or "")
            for b in boxes
        ))
    else:
        key = tuple(
            sorted((b.w, b.h, b.x, b.y, int(b.is_target)) for b in boxes)
        )
    return f"{key}|{sorted(blocked)}"


def load_existing_signatures(
    output_dir: str,
    include_color: bool = False,
) -> Set[str]:
    """Загружает подписи всех существующих уровней из output_dir."""
    sigs: Set[str] = set()
    if not os.path.isdir(output_dir):
        return sigs
    for fname in os.listdir(output_dir):
        if not (fname.startswith("campaign_") and fname.endswith(".json")):
            continue
        fpath = os.path.join(output_dir, fname)
        try:
            with open(fpath, encoding="utf-8") as f:
                data = json.load(f)
            boxes = [
                Box(
                    b.get("id", ""),
                    b["x"],
                    b["y"],
                    b["width"],
                    b["height"],
                    b.get("isTarget", False),
                    b.get("color"),
                )
                for b in data["boxes"]
            ]
            blocked: Set[Tuple[int, int]] = {
                (c["x"], c["y"]) for c in data.get("blockedCells", [])
            }
            sigs.add(_sig(boxes, blocked, include_color))
        except Exception:
            pass
    return sigs


def get_next_id(output_dir: str = OUTPUT_DIR) -> int:
    """Возвращает следующий номер campaign-уровня в output_dir."""
    existing = []
    if os.path.isdir(output_dir):
        for fname in os.listdir(output_dir):
            if fname.startswith("campaign_") and fname.endswith(".json"):
                try:
                    existing.append(int(fname[9:-5]))
                except ValueError:
                    pass
    return max(existing, default=0) + 1


def _sig_worker(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    start_x: int,
    start_y: int,
    facing: int,
) -> str:
    """
    Канонический ключ уровня режима Worker: геометрия ящиков (включая
    размер - иначе два уровня с одинаковыми якорными клетками, но
    разными размерами ящиков, ложно считались бы дублями) +
    блокированные ячейки + стартовая позиция/направление рабочего — в
    этом режиме от них зависит доступность и сложность решения, в
    отличие от крана, который достаёт любой ящик одинаково откуда
    угодно.
    """
    key = tuple(
        sorted((b.w, b.h, b.x, b.y, int(b.is_target)) for b in boxes)
    )
    return f"{key}|blocked={sorted(blocked)}|worker=({start_x},{start_y},{facing})"


def load_existing_signatures_worker(output_dir: str) -> Set[str]:
    """Загружает подписи всех существующих уровней режима Worker."""
    sigs: Set[str] = set()
    if not os.path.isdir(output_dir):
        return sigs
    for fname in os.listdir(output_dir):
        if not (fname.startswith("campaign_") and fname.endswith(".json")):
            continue
        fpath = os.path.join(output_dir, fname)
        try:
            with open(fpath, encoding="utf-8") as f:
                data = json.load(f)
            boxes = [
                Box(
                    b.get("id", ""), b["x"], b["y"],
                    b.get("width", 1), b.get("height", 1),
                    b.get("isTarget", False),
                )
                for b in data["boxes"]
            ]
            blocked: Set[Tuple[int, int]] = {
                (c["x"], c["y"]) for c in data.get("blockedCells", [])
            }
            facing = -1 if data.get("workerFacing") == "left" else 1
            sigs.add(_sig_worker(
                boxes,
                blocked,
                data.get("workerStartX", 0),
                data.get("workerStartY", 0),
                facing,
            ))
        except Exception:
            pass
    return sigs


def generate_one(
    min_moves: int,
    max_moves: int,
    min_fill: float,
    rng: random.Random,
    seen: Set[str],
    attempts: int = 2000,
) -> Optional[Tuple[List[Box], Set[Tuple[int, int]], int]]:
    """
    Пытается сгенерировать один валидный уровень.
    Возвращает (boxes, blocked, min_sol) или None при неудаче.
    """
    for _ in range(attempts):
        # 1. Выбираем размер и позицию целевого ящика
        tw, th = rng.choice(TARGET_SIZES)
        # Целевой ящик не должен стоять на позиции выхода
        # (x+tw == GRID_W, y==0)
        valid_tx = [x for x in range(GRID_W - tw + 1) if x + tw < GRID_W]
        if not valid_tx:
            continue
        tx = rng.choice(valid_tx)

        target = Box("target", tx, 0, tw, th, True)
        boxes: List[Box] = [target]
        blocked: Set[Tuple[int, int]] = set()

        # 2. Заблокированные клетки (только y=3 или y=4, максимум 2 колонны)
        n_bl = rng.choices([0, 1, 2], weights=[60, 28, 12])[0]
        if n_bl:
            cols = rng.sample(range(GRID_W), min(n_bl, GRID_W))
            for bc in cols:
                blocked.add((bc, rng.choice([3, 4])))

        # 3. Добавляем случайные ящики
        # Потолок поднят с 9 до 19 (issue: генератор долго/безуспешно
        # подбирал раскладку под высокий min_fill, имея всего 10 ящиков
        # в распоряжении). Эмпирически cap=20 - разумный компромисс:
        # заметно расширяет достижимый fill% (60-80% вместо ~60%
        # максимума), а более высокий потолок (25) не помогает и даже
        # замедляет генерацию (BFS дороже на большем числе ящиков) без
        # роста успешности.
        max_extra = rng.randint(2, 19)
        target_cols = set(range(tx, tx + tw))

        for _ in range(max_extra):
            w, h = rng.choice(ALLOWED_SIZES)
            pos_t = tuple((b.x, b.y) for b in boxes)
            occ = build_occ(boxes, pos_t)

            candidates = []
            for x in range(GRID_W - w + 1):
                y = placement_y(occ, blocked, x, w, h)
                if y is not None:
                    candidates.append((x, y))
            if not candidates:
                continue

            # Предпочитаем позиции над целевым ящиком (сложнее головоломка)
            over_target = [
                (x, y) for (x, y) in candidates
                if any(c in target_cols for c in range(x, x + w))
            ]
            pool = (
                over_target
                if over_target and rng.random() < 0.65
                else candidates
            )
            cx, cy = rng.choice(pool)
            boxes.append(Box(f"box_{len(boxes)}", cx, cy, w, h, False))

        # 4. Проверка минимальной заполненности
        fill = sum(b.w * b.h for b in boxes) / (GRID_W * GRID_H) * 100
        if fill < min_fill:
            continue

        # 5. BFS: проверка решаемости и подсчёт минимальных ходов
        min_sol = solve(boxes, blocked, max_depth=max_moves + 6)
        if min_sol < 0 or not (min_moves <= min_sol <= max_moves):
            continue

        # 6. Проверка уникальности
        sig = _sig(boxes, blocked)
        if sig in seen:
            continue
        seen.add(sig)

        return boxes, blocked, min_sol

    return None


def generate_one_color(
    min_moves: int,
    max_moves: int,
    min_fill: float,
    color_count: int,
    rng: random.Random,
    seen: Set[str],
    attempts: int = 2000,
    recolor_attempts: int = COLOR_RECOLOR_ATTEMPTS,
) -> Optional[Tuple[List[Box], Set[Tuple[int, int]], int]]:
    """
    Как generate_one(), но для режима Color Matching. Раскладка (позиции
    и размеры ящиков) строится независимо от цвета, а цвет назначается
    отдельным, внутренним циклом ПОСЛЕ того как раскладка физически
    готова: для одной и той же раскладки перебирается до
    recolor_attempts разных раскрасок, прежде чем раскладка целиком
    отбраковывается и строится заново. Раскраска дёшева (без повторного
    подбора позиций) относительно перестроения раскладки, а подбор
    подходящей раскраски для уже физически готовой раскладки оказался
    на порядки эффективнее, чем откатывать всё целиком при неудаче
    (см. issue #15).

    Правило «класть можно только на ящик своего цвета (или на пол)» —
    это ограничение хода при игре/решении (см. color_fits_support() в
    solve_color()), а не ограничение начальной раскладки: по условию
    задачи ящики разных цветов могут стартово стоять друг на друге как
    угодно, лишь бы уровень был физически корректен (полная опора, без
    пересечений) и решаем.

    При color_count in (3, 4): обычные (не целевые) ящики берутся из
    COLOR_RESTRICTED_EXTRA_SIZES (только ширина 1), а если найденное
    решение требует COLOR_LONG_SOLUTION_THRESHOLD ходов и больше,
    дополнительно требуется, чтобы минимум COLOR_MIN_MOVED_FRACTION
    ящиков (от общего числа, включая цель) были сдвинуты хотя бы раз.

    Каждая раскраска также проверяется на минимальное представление
    каждого цвета (площадь и количество ящиков) - см.
    _color_balance_ok() / COLOR_MIN_AREA_FRACTION / COLOR_MIN_BOXES_*.
    """
    level_colors = rng.sample(COLOR_PALETTE, color_count)
    extra_sizes_pool = (
        COLOR_RESTRICTED_EXTRA_SIZES
        if color_count in (3, 4)
        else ALLOWED_SIZES
    )

    for _ in range(attempts):
        # 1. Выбираем размер и позицию целевого ящика (цвет — позже)
        tw, th = rng.choice(TARGET_SIZES)
        valid_tx = [x for x in range(GRID_W - tw + 1) if x + tw < GRID_W]
        if not valid_tx:
            continue
        tx = rng.choice(valid_tx)

        target = Box("target", tx, 0, tw, th, True, None)
        boxes: List[Box] = [target]
        blocked: Set[Tuple[int, int]] = set()

        # 2. Заблокированные клетки (только y=3 или y=4, максимум 2 колонны)
        n_bl = rng.choices([0, 1, 2], weights=[60, 28, 12])[0]
        if n_bl:
            cols = rng.sample(range(GRID_W), min(n_bl, GRID_W))
            for bc in cols:
                blocked.add((bc, rng.choice([3, 4])))

        # 3. Добавляем случайные ящики (позиция и размер, без цвета)
        # Тот же потолок, что и в generate_one() - см. комментарий там.
        max_extra = rng.randint(2, 19)
        target_cols = set(range(tx, tx + tw))

        for _ in range(max_extra):
            w, h = rng.choice(extra_sizes_pool)
            pos_t = tuple((b.x, b.y) for b in boxes)
            occ = build_occ(boxes, pos_t)

            candidates = []
            for x in range(GRID_W - w + 1):
                y = placement_y(occ, blocked, x, w, h)
                if y is not None:
                    candidates.append((x, y))
            if not candidates:
                continue

            over_target = [
                (x, y) for (x, y) in candidates
                if any(col in target_cols for col in range(x, x + w))
            ]
            pool = (
                over_target
                if over_target and rng.random() < 0.65
                else candidates
            )
            cx, cy = rng.choice(pool)
            boxes.append(
                Box(f"box_{len(boxes)}", cx, cy, w, h, False, None)
            )

        # 4. Проверка минимальной заполненности (не зависит от цвета)
        fill = sum(b.w * b.h for b in boxes) / (GRID_W * GRID_H) * 100
        if fill < min_fill:
            continue

        # 5-8. Раскладка готова физически - перебираем раскраски для
        # НЕЁ ЖЕ, вместо того чтобы откатывать всю раскладку целиком.
        for _ in range(recolor_attempts):
            for b in boxes:
                b.color = rng.choice(level_colors)

            # 5. Уровень должен реально использовать все выбранные цвета
            if len({b.color for b in boxes}) != color_count:
                continue

            # 5.5. Минимальное представление каждого цвета (площадь и
            # количество ящиков) - см. COLOR_MIN_AREA_FRACTION и
            # COLOR_MIN_BOXES_* выше. Дёшево, проверяем до BFS.
            if not _color_balance_ok(boxes, color_count):
                continue

            # 6. BFS: проверка решаемости и подсчёт минимальных ходов
            min_sol = solve_color(boxes, blocked, max_depth=max_moves + 6)
            if min_sol < 0 or not (min_moves <= min_sol <= max_moves):
                continue

            # 7. При 3-4 цветах и длинном решении - доля сдвинутых ящиков
            if (
                color_count in (3, 4)
                and min_sol >= COLOR_LONG_SOLUTION_THRESHOLD
            ):
                path = solve_color_with_path(
                    boxes, blocked, max_depth=max_moves + 6
                )
                if path is None:
                    continue
                moved_fraction = len({m[0] for m in path}) / len(boxes)
                if moved_fraction < COLOR_MIN_MOVED_FRACTION:
                    continue

            # 8. Проверка уникальности (цвет входит в подпись)
            sig = _sig(boxes, blocked, include_color=True)
            if sig in seen:
                continue
            seen.add(sig)

            return boxes, blocked, min_sol

    return None


def _worker_row_would_fill(
    occ: Occ, x: int, w: int, y: int, h: int
) -> bool:
    """True если размещение ящика w×h в (x, y) заполнит целиком хотя бы
    один из затронутых рядов - защита от полностью занятого ряда уже в
    СТАРТОВОЙ раскладке (не то же самое, что рантайм-правило
    WorkerRules.IsRowFillDenied, которое действует только при
    размещении ящика самим рабочим во время решения)."""
    for ry in range(y, y + h):
        existing = sum(1 for (cx, cy) in occ if cy == ry)
        if existing + w >= GRID_W:
            return True
    return False


def generate_one_worker(
    min_moves: int,
    max_moves: int,
    min_fill: float,
    rng: random.Random,
    seen: Set[str],
    attempts: int = 2000,
) -> Optional[Tuple[List[Box], Set[Tuple[int, int]], int, int, int, int]]:
    """
    Пытается сгенерировать один валидный уровень режима Worker.
    Возвращает (boxes, blocked, worker_x, worker_y, worker_facing, min_sol)
    или None при неудаче. worker_facing: -1 (влево) или 1 (вправо).

    Раскладка строится тем же способом, что и опорная геометрия в
    generate_one() (полная опора снизу, без пересечений, через уже общие
    build_occ()/placement_y()) - размер каждого ящика берётся из
    WORKER_ALLOWED_SIZES, а не всегда 1x1. Без выделения целевого ящика
    заранее — им становится случайный уже размещённый ящик (кроме
    перекрывающего клетку выхода), чтобы цель могла естественно
    оказаться погребена под другими ящиками. Каждое размещение также
    обязано соблюдать защиту от заполненного ряда - см.
    _worker_row_would_fill().
    """
    for _ in range(attempts):
        # По решению пользователя: 0-6 блоков, без смещения к малым
        # значениям (в отличие от crane/color). В отличие от них же,
        # клетки выбираются как отдельные (колонка, ряд), а не "1 блок
        # на колонку" - при высоких n_blocked "1 на колонку" размазывал
        # бы препятствие сразу по ВСЕМ 6 колонкам (проверено на
        # практике: при 5-6 блоках так почти всем ящикам отказывает
        # placement_y(), потому что верх КАЖДОЙ колонки уже занят
        # блоком). Разрешая 2 блока в одной колонне, часть колонн
        # остаётся полностью свободной даже при большом n_blocked.
        blocked: Set[Tuple[int, int]] = set()
        n_blocked = rng.randint(0, 6)
        if n_blocked:
            cell_candidates = [
                (x, y) for x in range(GRID_W) for y in (3, 4)
            ]
            rng.shuffle(cell_candidates)
            blocked = set(cell_candidates[:n_blocked])

        occ: Occ = {}
        boxes: List[Box] = []

        # Верхняя граница как в generate_one() - см. комментарий там
        # (потолок 22 при защите "хотя бы 1 свободная клетка в ряду").
        total_boxes = rng.randint(3, 22)
        for _ in range(total_boxes):
            w, h = rng.choice(WORKER_ALLOWED_SIZES)
            candidates = []
            for x in range(GRID_W - w + 1):
                y = placement_y(occ, blocked, x, w, h)
                if y is None:
                    continue
                if _worker_row_would_fill(occ, x, w, y, h):
                    continue
                candidates.append((x, y))
            if not candidates:
                continue
            cx, cy = rng.choice(candidates)
            box = Box(f"box_{len(boxes)}", cx, cy, w, h, False)
            for dx in range(w):
                for dy in range(h):
                    occ[(cx + dx, cy + dy)] = len(boxes)
            boxes.append(box)

        if len(boxes) < 2:
            continue

        # Целью не может быть ящик, чей footprint пересекает клетку
        # выхода (не только якорная клетка - широкий/высокий ящик может
        # накрывать её и другой своей клеткой).
        exit_cell = (GRID_W - 1, 0)
        target_candidates = [
            i for i, b in enumerate(boxes)
            if exit_cell not in {
                (b.x + dx, b.y + dy)
                for dx in range(b.w) for dy in range(b.h)
            }
        ]
        if not target_candidates:
            continue
        target_i = rng.choice(target_candidates)
        boxes[target_i].is_target = True
        boxes[target_i].id = "target"

        # Проверка минимальной заполненности (по площади, а не по числу
        # ящиков - актуально теперь, когда ящики разного размера).
        fill = sum(b.w * b.h for b in boxes) / (GRID_W * GRID_H) * 100
        if fill < min_fill:
            continue

        # Стартовая позиция рабочего: поверх стопки в случайной колонне -
        # но только среди колонн, где стопка не достаёт до потолка
        # видимой сетки (иначе рабочий стартовал бы визуально за
        # пределами игрового поля - редкий, но реальный случай при
        # высоких/частых стопках, который стоило исключить явно).
        column_heights = [0] * GRID_W
        for (cx, cy) in occ:
            column_heights[cx] = max(column_heights[cx], cy + 1)
        start_candidates = [
            x for x in range(GRID_W) if column_heights[x] < GRID_H
        ]
        if not start_candidates:
            continue
        start_x = rng.choice(start_candidates)
        start_y = column_heights[start_x]
        facing = rng.choice([-1, 1])

        # BFS: проверка решаемости и подсчёт минимального числа действий.
        min_sol = solve_worker(
            boxes, blocked, GRID_W, start_x, start_y, facing,
            max_depth=max_moves + 15,
        )
        if min_sol < 0 or not (min_moves <= min_sol <= max_moves):
            continue

        # Проверка уникальности.
        sig = _sig_worker(boxes, blocked, start_x, start_y, facing)
        if sig in seen:
            continue
        seen.add(sig)

        return boxes, blocked, start_x, start_y, facing, min_sol

    return None


def level_to_dict(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    min_sol: int,
    level_id: str,
) -> dict:
    return {
        "schemaVersion": 1,
        "id": level_id,
        "width": GRID_W,
        "height": GRID_H,
        "exitDirection": "right",
        "liftLimit": min_sol + 1,
        "boxes": [
            {
                "id": b.id,
                "x": b.x,
                "y": b.y,
                "width": b.w,
                "height": b.h,
                "isTarget": b.is_target,
                "visualId": "target" if b.is_target else "standard",
            }
            for b in boxes
        ],
        "blockedCells": [{"x": x, "y": y} for (x, y) in sorted(blocked)],
    }


def level_to_dict_color(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    min_sol: int,
    level_id: str,
) -> dict:
    return {
        "schemaVersion": 3,
        "id": level_id,
        "width": GRID_W,
        "height": GRID_H,
        "exitDirection": "right",
        "liftLimit": min_sol + 1,
        "gameMode": "color_matching",
        "boxes": [
            {
                "id": b.id,
                "x": b.x,
                "y": b.y,
                "width": b.w,
                "height": b.h,
                "isTarget": b.is_target,
                "visualId": "target" if b.is_target else "standard",
                "color": b.color,
            }
            for b in boxes
        ],
        "blockedCells": [{"x": x, "y": y} for (x, y) in sorted(blocked)],
    }


def level_to_dict_worker(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    start_x: int,
    start_y: int,
    facing: int,
    level_id: str,
) -> dict:
    return {
        "schemaVersion": 2,
        "id": level_id,
        "width": GRID_W,
        "height": GRID_H,
        "exitDirection": "right",
        "liftLimit": 0,
        "gameMode": "worker",
        "workerStartX": start_x,
        "workerStartY": start_y,
        "workerFacing": "left" if facing < 0 else "right",
        "timeLimitSeconds": WORKER_TIME_LIMIT_SECONDS,
        "boxes": [
            {
                "id": b.id,
                "x": b.x,
                "y": b.y,
                "width": b.w,
                "height": b.h,
                "isTarget": b.is_target,
                "visualId": "target" if b.is_target else "standard",
            }
            for b in boxes
        ],
        "blockedCells": [{"x": x, "y": y} for (x, y) in sorted(blocked)],
    }


# ─── GUI ─────────────────────────────────────────────────────────────────────
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Генератор уровней — Storage Controller")
        self.resizable(False, False)
        self._vars: Dict[str, tk.Variable] = {}
        self._build_ui()

    def _build_ui(self) -> None:
        p: Dict[str, Any] = {"padx": 8, "pady": 4}

        # ── Панель параметров ──
        frm = ttk.LabelFrame(self, text="Параметры", padding=10)
        frm.grid(row=0, column=0, padx=12, pady=8, sticky="ew")

        ttk.Label(frm, text="Режим:").grid(row=0, column=0, sticky="w", **p)
        mode_v = tk.StringVar(value="Standard")
        mode_combo = ttk.Combobox(
            frm, textvariable=mode_v,
            values=["Standard", "Color Matching", "Worker"],
            state="readonly", width=14,
        )
        mode_combo.grid(row=0, column=1, sticky="w", **p)
        mode_combo.bind("<<ComboboxSelected>>", self._on_mode_changed)
        self._vars["mode"] = mode_v

        ttk.Label(frm, text="Количество уровней:").grid(
            row=1,
            column=0,
            sticky="w",
            **p
        )
        count_v = tk.IntVar(value=20)
        ttk.Spinbox(
            frm,
            textvariable=count_v,
            from_=1,
            to=500,
            increment=1,
            width=10
        ).grid(
            row=1, column=1, sticky="w", **p
        )
        self._vars["count"] = count_v

        ttk.Label(
            frm,
            text="Мин. заполненность (%):"
        ).grid(row=2, column=0, sticky="w", **p)
        fill_v = tk.DoubleVar(value=40.0)
        ttk.Spinbox(
            frm, textvariable=fill_v, from_=10.0, to=90.0, increment=5.0,
            width=10, format="%.0f",
        ).grid(row=2, column=1, sticky="w", **p)
        self._vars["fill"] = fill_v

        self._min_moves_label = ttk.Label(frm, text="Мин. ходов:")
        self._min_moves_label.grid(
            row=3, column=0, sticky="w", **p
        )
        min_v = tk.IntVar(value=3)
        ttk.Spinbox(
            frm,
            textvariable=min_v,
            from_=1,
            to=80,
            increment=1,
            width=10
        ).grid(
            row=3, column=1, sticky="w", **p
        )
        self._vars["min_moves"] = min_v

        self._max_moves_label = ttk.Label(frm, text="Макс. ходов:")
        self._max_moves_label.grid(
            row=4, column=0, sticky="w", **p
        )
        max_v = tk.IntVar(value=12)
        ttk.Spinbox(
            frm,
            textvariable=max_v,
            from_=1,
            to=80,
            increment=1,
            width=10
        ).grid(
            row=4, column=1, sticky="w", **p
        )
        self._vars["max_moves"] = max_v

        self._colors_label = ttk.Label(frm, text="Количество цветов:")
        colors_v = tk.StringVar(value=str(MIN_COLOR_COUNT))
        self._colors_combo = ttk.Combobox(
            frm, textvariable=colors_v,
            values=[
                str(n)
                for n in range(MIN_COLOR_COUNT, MAX_COLOR_COUNT + 1)
            ],
            state="readonly", width=10,
        )
        self._colors_row = 5
        self._colors_grid_kwargs = p
        self._vars["colors"] = colors_v
        self._on_mode_changed()  # показать/скрыть по стартовому режиму

        # ── Кнопка ──
        self._gen_btn = ttk.Button(
            self,
            text="Сгенерировать",
            command=self._start
        )
        self._gen_btn.grid(row=1, column=0, pady=6)

        # ── Прогресс-бар ──
        self._prog_v = tk.DoubleVar()
        ttk.Progressbar(
            self, variable=self._prog_v, maximum=100, length=480,
        ).grid(row=2, column=0, padx=12, pady=2, sticky="ew")

        # ── Лог ──
        lf = ttk.LabelFrame(self, text="Лог", padding=4)
        lf.grid(row=3, column=0, padx=12, pady=6, sticky="nsew")
        self._log_box = scrolledtext.ScrolledText(
            lf, width=66, height=22, state="disabled",
        )
        self._log_box.pack(fill="both", expand=True)

    def _on_mode_changed(self, event: Any = None) -> None:
        """
        Показывает поле «Количество цветов» только для Color Matching и
        переключает мин./макс. действий на разумные значения по умолчанию:
        у Worker решение состоит из мелких пошаговых действий рабочего,
        а не укрупнённых ходов крана, поэтому диапазон заметно шире.
        """
        mode = self._vars["mode"].get()
        if mode == "Color Matching":
            self._colors_label.grid(
                row=self._colors_row, column=0, sticky="w",
                **self._colors_grid_kwargs
            )
            self._colors_combo.grid(
                row=self._colors_row, column=1, sticky="w",
                **self._colors_grid_kwargs
            )
        else:
            self._colors_label.grid_remove()
            self._colors_combo.grid_remove()

        if mode == "Worker":
            self._vars["min_moves"].set(10)
            self._vars["max_moves"].set(35)
            self._min_moves_label.configure(text="Мин. действий:")
            self._max_moves_label.configure(text="Макс. действий:")
        else:
            self._vars["min_moves"].set(3)
            self._vars["max_moves"].set(12)
            self._min_moves_label.configure(text="Мин. ходов:")
            self._max_moves_label.configure(text="Макс. ходов:")

    # ── Thread-safe хелперы ──
    def _log(self, msg: str) -> None:
        self.after(0, self._log_ui, msg)

    def _log_ui(self, msg: str) -> None:
        self._log_box.configure(state="normal")
        self._log_box.insert("end", msg + "\n")
        self._log_box.see("end")
        self._log_box.configure(state="disabled")

    def _set_progress(self, val: float) -> None:
        self.after(0, self._prog_v.set, val)

    # ── Запуск ──
    def _start(self) -> None:
        min_moves = self._vars["min_moves"].get()
        max_moves = self._vars["max_moves"].get()
        if min_moves > max_moves:
            messagebox.showerror(
                "Ошибка",
                "Мин. ходов не может быть больше макс. ходов."
            )
            return
        self._gen_btn.configure(state="disabled")
        self._prog_v.set(0)
        self._log_box.configure(state="normal")
        self._log_box.delete("1.0", "end")
        self._log_box.configure(state="disabled")
        threading.Thread(target=self._run, daemon=True).start()

    def _run(self) -> None:
        count: int = self._vars["count"].get()
        min_moves: int = self._vars["min_moves"].get()
        max_moves: int = self._vars["max_moves"].get()
        min_fill: float = self._vars["fill"].get()
        mode: str = self._vars["mode"].get()
        is_color = mode == "Color Matching"
        is_worker = mode == "Worker"
        color_count = int(self._vars["colors"].get()) if is_color else 0

        if is_worker:
            output_dir = WORKER_OUTPUT_DIR
            solutions_dir = WORKER_SOLUTIONS_DIR
        elif is_color:
            output_dir = COLOR_OUTPUT_DIR
            solutions_dir = COLOR_SOLUTIONS_DIR
        else:
            output_dir = OUTPUT_DIR
            solutions_dir = SOLUTIONS_DIR

        rng = random.Random()
        seen: Set[str] = (
            load_existing_signatures_worker(output_dir)
            if is_worker
            else load_existing_signatures(output_dir, include_color=is_color)
        )
        next_id = get_next_id(output_dir)
        ok = 0

        self._log(
            f"Генерация {count} уровней ({mode}),"
            f" начиная с campaign_{next_id:02d}..."
        )
        self._log(
            f"{'Действий' if is_worker else 'Ходов'}: {min_moves}–{max_moves},"
            f" заполненность ≥ {min_fill:.0f}%"
            + (f", цветов: {color_count}" if is_color else "")
        )
        self._log(
            f"Уже существует уровней: {len(seen)} (дубли будут пропущены)\n"
        )

        os.makedirs(output_dir, exist_ok=True)

        for i in range(count):
            # result/sol_path's shape depends on which mode is selected at
            # runtime (worker's 6-tuple vs. crane/color's box+blocked
            # 3-tuple) - typed loosely on purpose rather than unifying two
            # structurally different shapes into one static type.
            result: Any
            if is_worker:
                result = generate_one_worker(
                    min_moves, max_moves, min_fill, rng, seen
                )
            elif is_color:
                result = generate_one_color(
                    min_moves, max_moves, min_fill, color_count, rng, seen
                )
            else:
                result = generate_one(
                    min_moves, max_moves, min_fill, rng, seen
                )

            if result is None:
                self._log(
                    f"[{i + 1}/{count}]  — пропуск"
                    " (не удалось подобрать уровень)"
                )
                self._set_progress((i + 1) / count * 100)
                continue

            lid = f"campaign_{next_id:02d}"

            if is_worker:
                boxes, blocked, start_x, start_y, facing, min_sol = result
                data = level_to_dict_worker(
                    boxes, blocked, start_x, start_y, facing, lid
                )
                out_path = os.path.join(output_dir, f"{lid}.json")
                with open(out_path, "w", encoding="utf-8") as f:
                    json.dump(
                        data, f,
                        ensure_ascii=False,
                        separators=(",", ":"),
                    )
                sol_path: Any = solve_worker_with_path(
                    boxes, blocked, GRID_W, start_x, start_y, facing,
                    max_depth=max_moves + 15,
                )
                if sol_path is not None:
                    write_solution_worker(
                        lid, boxes, blocked, start_x, start_y, facing,
                        sol_path, solutions_dir=solutions_dir,
                    )
                self._log(
                    f"[{i+1}/{count}]  {lid}: {len(boxes)} ящ.,  "
                    f"{len(blocked)} блок.,  "
                    f"{min_sol} действ.,  "
                    f"рабочий=({start_x},{start_y},"
                    f"{'←' if facing < 0 else '→'})"
                )
            else:
                boxes, blocked, min_sol = result
                data = (
                    level_to_dict_color(boxes, blocked, min_sol, lid)
                    if is_color
                    else level_to_dict(boxes, blocked, min_sol, lid)
                )
                out_path = os.path.join(output_dir, f"{lid}.json")
                with open(out_path, "w", encoding="utf-8") as f:
                    json.dump(
                        data, f,
                        ensure_ascii=False,
                        separators=(",", ":"),
                    )
                sol_path = (
                    solve_color_with_path(
                        boxes, blocked, max_depth=max_moves + 6
                    )
                    if is_color
                    else solve_with_path(
                        boxes, blocked, max_depth=max_moves + 6
                    )
                )
                if sol_path is not None:
                    write_solution(
                        lid, boxes, blocked, min_sol + 1, sol_path,
                        solutions_dir=solutions_dir,
                    )
                bl_info = f",  блок={len(blocked)}" if blocked else ""
                self._log(
                    f"[{i+1}/{count}]  {lid}: {len(boxes)} ящ.,  "
                    f"{min_sol} ход.,  liftLimit={min_sol + 1}{bl_info}"
                )

            next_id += 1
            ok += 1
            self._set_progress((i + 1) / count * 100)

        self._log(f"\nГотово.  Создано: {ok},  пропущено: {count - ok}.")
        self.after(0, self._gen_btn.configure, {"state": "normal"})


# ─── Точка входа ─────────────────────────────────────────────────────────────
if __name__ == "__main__":
    App().mainloop()
