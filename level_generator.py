#!/usr/bin/env python3
"""
Генератор уровней для Storage Controller
(режимы Standard Crane, Color Matching, Worker).
"""

import json
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
WORKER_MAX_COLUMN_HEIGHT = GRID_H
WORKER_EMPTY_JUMP_HEIGHT = 2
WORKER_CARRYING_JUMP_HEIGHT = 1

ALLOWED_SIZES: List[Tuple[int, int]] = [
    (1, 1), (2, 1), (1, 2), (2, 2), (3, 2), (2, 3),
]
TARGET_SIZES: List[Tuple[int, int]] = [(1, 1), (2, 1), (1, 2), (2, 2)]

# Цвета соответствуют BoxColor в storage_controller (без None).
# Игра поддерживает 2-4 цвета на уровень (ColorMatchingGameRules).
COLOR_PALETTE: List[str] = ["red", "blue", "green", "yellow"]
MIN_COLOR_COUNT = 2
MAX_COLOR_COUNT = 4

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
# Ящики в этом режиме всегда 1x1, поэтому позиция ящика однозначно задаёт
# занимаемую им единственную клетку. Состояние решателя: позиции
# установленных ящиков (None у переносимого — он снят с сетки, как и в
# WorkerState.InstalledBoxPositions на стороне игры), позиция и направление
# рабочего, индекс переносимого ящика (-1, если руки пусты).
WorkerPositions = Tuple[Optional[Tuple[int, int]], ...]
WorkerState = Tuple[WorkerPositions, int, int, int, int]
WorkerMove = Tuple[str, int]  # ("move"/"jump", ±1) или ("pickup"/"putdown", 0)


def _worker_column_height(positions: WorkerPositions, x: int) -> int:
    """Высота стопки установленных ящиков в колонне x (0, если пусто)."""
    height = 0
    for pos in positions:
        if pos is not None and pos[0] == x:
            height = max(height, pos[1] + 1)
    return height


def _worker_row_count(positions: WorkerPositions, y: int) -> int:
    """Число установленных ящиков в ряду y."""
    return sum(1 for pos in positions if pos is not None and pos[1] == y)


def _worker_top_box(
    positions: WorkerPositions,
    x: int,
) -> Optional[Tuple[int, Tuple[int, int]]]:
    """(индекс, позиция) верхнего установленного ящика в колонне x, либо None."""
    best: Optional[Tuple[int, Tuple[int, int]]] = None
    for i, pos in enumerate(positions):
        if pos is not None and pos[0] == x:
            if best is None or pos[1] > best[1][1]:
                best = (i, pos)
    return best


def _worker_transitions(
    boxes: List[Box],
    width: int,
    state: WorkerState,
) -> List[Tuple[WorkerState, WorkerMove, bool]]:
    """
    Возвращает список (новое_состояние, действие, доставлена_ли_цель)
    для всех допустимых действий рабочего из state. Симулирует точную
    механику WorkerRules.CanMove/CanJump/CanInteract (без прыжка на месте —
    он не меняет состояние и решателю бесполезен).
    """
    positions, wx, wy, facing, carried = state
    results: List[Tuple[WorkerState, WorkerMove, bool]] = []

    # Move: шаг в соседнюю колонну, только если она не выше рабочего.
    for direction in (-1, 1):
        tx = wx + direction
        if tx < 0 or tx >= width:
            continue
        theight = _worker_column_height(positions, tx)
        if theight <= wy:
            new_state: WorkerState = (positions, tx, theight, direction, carried)
            results.append((new_state, ("move", direction), False))

    # Jump: в соседнюю колонну, подъём ограничен в зависимости от переноски.
    for direction in (-1, 1):
        tx = wx + direction
        if tx < 0 or tx >= width:
            continue
        theight = _worker_column_height(positions, tx)
        max_rise = (
            WORKER_CARRYING_JUMP_HEIGHT
            if carried >= 0
            else WORKER_EMPTY_JUMP_HEIGHT
        )
        if theight - wy <= max_rise:
            new_state = (positions, tx, theight, direction, carried)
            results.append((new_state, ("jump", direction), False))

    # Interact: подобрать/положить в колонне, куда смотрит рабочий.
    adjacent_x = wx + facing
    if 0 <= adjacent_x < width:
        col_height = _worker_column_height(positions, adjacent_x)
        if carried >= 0:
            if col_height < WORKER_MAX_COLUMN_HEIGHT:
                dest = (adjacent_x, col_height)
                would_fill = _worker_row_count(positions, dest[1]) >= width - 1
                is_delivery = (
                    boxes[carried].is_target
                    and dest[0] == width - 1
                    and dest[1] == 0
                )
                if (not would_fill or is_delivery) and col_height <= wy + 1:
                    new_positions = list(positions)
                    new_positions[carried] = dest
                    new_state = (tuple(new_positions), wx, wy, facing, -1)
                    results.append((new_state, ("putdown", 0), is_delivery))
        else:
            top = _worker_top_box(positions, adjacent_x)
            if top is not None:
                top_idx, top_pos = top
                if wy <= top_pos[1] <= wy + 1:
                    new_positions = list(positions)
                    new_positions[top_idx] = None
                    new_state = (
                        tuple(new_positions), wx, wy, facing, top_idx
                    )
                    results.append((new_state, ("pickup", 0), False))

    return results


def solve_worker(
    boxes: List[Box],
    width: int,
    start_x: int,
    start_y: int,
    facing: int,
    max_depth: int = 60,
    max_states: int = 150_000,
) -> int:
    """
    BFS по состояниям рабочего. Возвращает минимальное число действий
    (move/jump/pickup/putdown) для доставки целевого ящика к выходу
    (width-1, 0), или -1 если решения нет. Прерывается досрочно при
    превышении max_states.
    """
    initial_positions: WorkerPositions = tuple((b.x, b.y) for b in boxes)
    initial: WorkerState = (initial_positions, start_x, start_y, facing, -1)
    queue: deque = deque([(initial, 0)])
    visited: Set[WorkerState] = {initial}

    while queue:
        if len(visited) > max_states:
            return -1
        state, depth = queue.popleft()
        if depth >= max_depth:
            continue

        for new_state, _move, delivered in _worker_transitions(
            boxes, width, state
        ):
            if delivered:
                return depth + 1
            if new_state not in visited:
                visited.add(new_state)
                queue.append((new_state, depth + 1))

    return -1


def solve_worker_with_path(
    boxes: List[Box],
    width: int,
    start_x: int,
    start_y: int,
    facing: int,
    max_depth: int = 60,
    max_states: int = 150_000,
) -> Optional[List[WorkerMove]]:
    """Как solve_worker(), но восстанавливает последовательность действий."""
    initial_positions: WorkerPositions = tuple((b.x, b.y) for b in boxes)
    initial: WorkerState = (initial_positions, start_x, start_y, facing, -1)
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
            boxes, width, state
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
    ("jump", -1): "прыжок влево",
    ("jump", 1): "прыжок вправо",
    ("pickup", 0): "берёт ящик",
    ("putdown", 0): "кладёт ящик",
}


def write_solution_worker(
    lid: str,
    boxes: List[Box],
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
        "",
        "Начальные позиции:",
    ]
    for b in boxes:
        target_mark = "  [цель]" if b.is_target else ""
        lines.append(f"  {b.id:<10} (1x1)  x={b.x}, y={b.y}{target_mark}")
    lines.append("")
    lines.append("Решение:")
    for step, move in enumerate(path, 1):
        label = _WORKER_MOVE_LABELS[move]
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
    start_x: int,
    start_y: int,
    facing: int,
) -> str:
    """
    Канонический ключ уровня режима Worker: геометрия ящиков + стартовая
    позиция/направление рабочего — в этом режиме от них зависит
    доступность и сложность решения, в отличие от крана, который
    достаёт любой ящик одинаково откуда угодно.
    """
    key = tuple(sorted((b.x, b.y, int(b.is_target)) for b in boxes))
    return f"{key}|worker=({start_x},{start_y},{facing})"


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
                Box(b.get("id", ""), b["x"], b["y"], 1, 1, b.get("isTarget", False))
                for b in data["boxes"]
            ]
            facing = -1 if data.get("workerFacing") == "left" else 1
            sigs.add(_sig_worker(
                boxes,
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
        max_extra = rng.randint(2, 9)
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
) -> Optional[Tuple[List[Box], Set[Tuple[int, int]], int]]:
    """
    Как generate_one(), но для режима Color Matching: каждому ящику
    назначается цвет. Ящик, вставший на пол (y=0) или на цель, получает
    случайный цвет из палитры уровня; ящик, вставший на другие ящики,
    обязан получить их цвет — если опора под кандидатной позицией
    разноцветная, эта позиция для цветного режима отбрасывается.
    """
    level_colors = rng.sample(COLOR_PALETTE, color_count)

    for _ in range(attempts):
        # 1. Выбираем размер, позицию и цвет целевого ящика
        tw, th = rng.choice(TARGET_SIZES)
        valid_tx = [x for x in range(GRID_W - tw + 1) if x + tw < GRID_W]
        if not valid_tx:
            continue
        tx = rng.choice(valid_tx)

        target = Box(
            "target", tx, 0, tw, th, True, rng.choice(level_colors)
        )
        boxes: List[Box] = [target]
        blocked: Set[Tuple[int, int]] = set()

        # 2. Заблокированные клетки (только y=3 или y=4, максимум 2 колонны)
        n_bl = rng.choices([0, 1, 2], weights=[60, 28, 12])[0]
        if n_bl:
            cols = rng.sample(range(GRID_W), min(n_bl, GRID_W))
            for bc in cols:
                blocked.add((bc, rng.choice([3, 4])))

        # 3. Добавляем случайные ящики (цвет зависит от опоры)
        max_extra = rng.randint(2, 9)
        target_cols = set(range(tx, tx + tw))

        for _ in range(max_extra):
            w, h = rng.choice(ALLOWED_SIZES)
            pos_t = tuple((b.x, b.y) for b in boxes)
            occ = build_occ(boxes, pos_t)

            candidates = []
            for x in range(GRID_W - w + 1):
                y = placement_y(occ, blocked, x, w, h)
                if y is None:
                    continue
                if y == 0:
                    candidates.append((x, y, None))
                    continue
                support = uniform_support_color(occ, boxes, x, w, y)
                if support is not None:
                    candidates.append((x, y, support))
            if not candidates:
                continue

            over_target = [
                (x, y, c) for (x, y, c) in candidates
                if any(col in target_cols for col in range(x, x + w))
            ]
            pool = (
                over_target
                if over_target and rng.random() < 0.65
                else candidates
            )
            cx, cy, forced_color = rng.choice(pool)
            color = (
                forced_color
                if forced_color is not None
                else rng.choice(level_colors)
            )
            boxes.append(
                Box(f"box_{len(boxes)}", cx, cy, w, h, False, color)
            )

        # 4. Проверка минимальной заполненности
        fill = sum(b.w * b.h for b in boxes) / (GRID_W * GRID_H) * 100
        if fill < min_fill:
            continue

        # 5. Уровень должен реально использовать все выбранные цвета
        if len({b.color for b in boxes}) != color_count:
            continue

        # 6. BFS: проверка решаемости и подсчёт минимальных ходов
        min_sol = solve_color(boxes, blocked, max_depth=max_moves + 6)
        if min_sol < 0 or not (min_moves <= min_sol <= max_moves):
            continue

        # 7. Проверка уникальности (цвет входит в подпись)
        sig = _sig(boxes, blocked, include_color=True)
        if sig in seen:
            continue
        seen.add(sig)

        return boxes, blocked, min_sol

    return None


def generate_one_worker(
    min_moves: int,
    max_moves: int,
    min_fill: float,
    rng: random.Random,
    seen: Set[str],
    attempts: int = 2000,
) -> Optional[Tuple[List[Box], int, int, int, int]]:
    """
    Пытается сгенерировать один валидный уровень режима Worker.
    Возвращает (boxes, worker_x, worker_y, worker_facing, min_sol) или None
    при неудаче. worker_facing: -1 (влево) или 1 (вправо).

    Ящики всегда 1x1. Раскладка строится тем же способом, что и опорная
    геометрия в generate_one() (полная опора снизу, без пересечений), но
    без выделения целевого ящика заранее — вместо этого им становится
    случайный уже размещённый ящик (кроме стоящего в клетке выхода), чтобы
    цель могла естественно оказаться погребена под другими ящиками. Каждое
    размещение также обязано соблюдать защиту от заполненного ряда: ни один
    ряд не должен остаться заполненным целиком (WorkerRules.CanInteract
    проверяет то же самое при переносе).
    """
    for _ in range(attempts):
        blocked: Set[Tuple[int, int]] = set()  # Worker не поддерживает блоки
        occ: Occ = {}
        placements: List[Tuple[int, int]] = []

        total_boxes = rng.randint(3, 10)
        for _ in range(total_boxes):
            candidates = []
            for x in range(GRID_W):
                y = placement_y(occ, blocked, x, 1, 1)
                if y is None:
                    continue
                if sum(1 for (cx, cy) in occ if cy == y) >= GRID_W - 1:
                    continue
                candidates.append((x, y))
            if not candidates:
                continue
            cx, cy = rng.choice(candidates)
            occ[(cx, cy)] = len(placements)
            placements.append((cx, cy))

        if len(placements) < 2:
            continue

        # Целью не может быть ящик, уже стоящий в клетке выхода.
        target_candidates = [
            i for i, (px, py) in enumerate(placements)
            if (px, py) != (GRID_W - 1, 0)
        ]
        if not target_candidates:
            continue
        target_i = rng.choice(target_candidates)

        tx, ty = placements[target_i]
        boxes: List[Box] = [Box("target", tx, ty, 1, 1, True)]
        for i, (px, py) in enumerate(placements):
            if i == target_i:
                continue
            boxes.append(Box(f"box_{len(boxes)}", px, py, 1, 1, False))

        # Проверка минимальной заполненности (ящики всегда 1x1).
        fill = len(boxes) / (GRID_W * GRID_H) * 100
        if fill < min_fill:
            continue

        # Стартовая позиция рабочего: поверх стопки в случайной колонне.
        start_x = rng.randrange(GRID_W)
        start_y = 0
        for (cx, cy) in occ:
            if cx == start_x:
                start_y = max(start_y, cy + 1)
        facing = rng.choice([-1, 1])

        # BFS: проверка решаемости и подсчёт минимального числа действий.
        min_sol = solve_worker(
            boxes, GRID_W, start_x, start_y, facing,
            max_depth=max_moves + 15,
        )
        if min_sol < 0 or not (min_moves <= min_sol <= max_moves):
            continue

        # Проверка уникальности.
        sig = _sig_worker(boxes, start_x, start_y, facing)
        if sig in seen:
            continue
        seen.add(sig)

        return boxes, start_x, start_y, facing, min_sol

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
                "width": 1,
                "height": 1,
                "isTarget": b.is_target,
                "visualId": "target" if b.is_target else "standard",
            }
            for b in boxes
        ],
        "blockedCells": [],
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

        ttk.Label(frm, text="Мин. ходов:").grid(
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

        ttk.Label(frm, text="Макс. ходов:").grid(
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
            values=[str(n) for n in range(MIN_COLOR_COUNT, MAX_COLOR_COUNT + 1)],
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
        else:
            self._vars["min_moves"].set(3)
            self._vars["max_moves"].set(12)

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
            # runtime (worker's 5-tuple vs. crane/color's box+blocked
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
                result = generate_one(min_moves, max_moves, min_fill, rng, seen)

            if result is None:
                self._log(
                    f"[{i + 1}/{count}]  — пропуск"
                    " (не удалось подобрать уровень)"
                )
                self._set_progress((i + 1) / count * 100)
                continue

            lid = f"campaign_{next_id:02d}"

            if is_worker:
                boxes, start_x, start_y, facing, min_sol = result
                data = level_to_dict_worker(
                    boxes, start_x, start_y, facing, lid
                )
                out_path = os.path.join(output_dir, f"{lid}.json")
                with open(out_path, "w", encoding="utf-8") as f:
                    json.dump(
                        data, f,
                        ensure_ascii=False,
                        separators=(",", ":"),
                    )
                sol_path: Any = solve_worker_with_path(
                    boxes, GRID_W, start_x, start_y, facing,
                    max_depth=max_moves + 15,
                )
                if sol_path is not None:
                    write_solution_worker(
                        lid, boxes, start_x, start_y, facing, sol_path,
                        solutions_dir=solutions_dir,
                    )
                self._log(
                    f"[{i+1}/{count}]  {lid}: {len(boxes)} ящ.,  "
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
