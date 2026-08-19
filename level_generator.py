#!/usr/bin/env python3
"""Генератор уровней для Storage Controller (режим Standard Crane)."""

import json
import os
import random
import threading
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
from collections import deque
from typing import Dict, List, Optional, Set, Tuple

# ─── Константы ───────────────────────────────────────────────────────────────
GRID_W = 6
GRID_H = 5
TRANSPORT_ROW = 5  # виртуальный ряд над сеткой (y=5)

OUTPUT_DIR = os.path.normpath(
    r"C:\Users\vjuni\Documents\__MY_DOCUMENTS\Dev"
    r"\storage_controller\Assets\StorageController\Resources\levels\Levels"
)

SOLUTIONS_DIR = os.path.normpath(
    r"C:\Users\vjuni\Documents\__MY_DOCUMENTS\Dev\level_generator\solutions"
)

ALLOWED_SIZES: List[Tuple[int, int]] = [
    (1, 1), (2, 1), (1, 2), (2, 2), (3, 2), (2, 3),
]
TARGET_SIZES: List[Tuple[int, int]] = [(1, 1), (2, 1), (1, 2), (2, 2)]

Occ = Dict[Tuple[int, int], int]  # (x, y) → индекс ящика


# ─── Модель ящика ────────────────────────────────────────────────────────────
class Box:
    __slots__ = ("id", "x", "y", "w", "h", "is_target")

    def __init__(
        self,
        bid: str,
        x: int,
        y: int,
        w: int,
        h: int,
        is_target: bool
    ):
        self.id = bid
        self.x = x
        self.y = y
        self.w = w
        self.h = h
        self.is_target = is_target


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
) -> int:
    """
    BFS по состояниям. Возвращает минимальное число подъёмов для доставки
    целевого ящика к выходу, или -1 если нет решения.
    Симулирует точную механику крана: anchor = x + (w-1)*0.5 (half-integer
    для width-2), перемещение пошагово влево/вправо с проверкой коридора.
    """
    initial: Tuple[Tuple[int, int], ...] = tuple((b.x, b.y) for b in boxes)
    queue: deque = deque([(initial, 0)])
    visited: Set[Tuple] = {initial}

    while queue:
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


# ─── BFS с восстановлением пути ──────────────────────────────────────────────
Move = Tuple[int, int, int, int, int]  # (box_idx, from_x, from_y, to_x, to_y)


def solve_with_path(
    boxes: List[Box],
    blocked: Set[Tuple[int, int]],
    max_depth: int = 30,
) -> Optional[List[Move]]:
    """
    BFS идентичный solve(), но дополнительно отслеживает came_from
    для восстановления последовательности ходов.
    Возвращает список (box_idx, from_x, from_y, to_x, to_y) или None.
    """
    initial: Tuple = tuple((b.x, b.y) for b in boxes)
    came_from: Dict = {initial: None}  # state -> (parent_state, move) | None
    queue: deque = deque([(initial, 0)])

    while queue:
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
) -> None:
    """Записывает решение уровня в SOLUTIONS_DIR/<lid>.txt."""
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
        lines.append(
            f"  {b.id:<10} ({b.w}x{b.h})"
            f"  x={b.x}, y={b.y}{target_mark}"
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
    os.makedirs(SOLUTIONS_DIR, exist_ok=True)
    out_path = os.path.join(SOLUTIONS_DIR, f"{lid}.txt")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


# ─── Генератор ───────────────────────────────────────────────────────────────
def _sig(boxes: List[Box], blocked: Set[Tuple[int, int]]) -> str:
    """Канонический ключ уровня для проверки уникальности."""
    key = tuple(sorted((b.w, b.h, b.x, b.y, int(b.is_target)) for b in boxes))
    return f"{key}|{sorted(blocked)}"


def get_next_id() -> int:
    """Возвращает следующий номер campaign-уровня."""
    existing = []
    if os.path.isdir(OUTPUT_DIR):
        for fname in os.listdir(OUTPUT_DIR):
            if fname.startswith("campaign_") and fname.endswith(".json"):
                try:
                    existing.append(int(fname[9:-5]))
                except ValueError:
                    pass
    return max(existing, default=0) + 1


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


# ─── GUI ─────────────────────────────────────────────────────────────────────
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Генератор уровней — Storage Controller")
        self.resizable(False, False)
        self._vars: dict = {}
        self._build_ui()

    def _build_ui(self) -> None:
        p = {"padx": 8, "pady": 4}

        # ── Панель параметров ──
        frm = ttk.LabelFrame(self, text="Параметры", padding=10)
        frm.grid(row=0, column=0, padx=12, pady=8, sticky="ew")

        ttk.Label(frm, text="Режим:").grid(row=0, column=0, sticky="w", **p)
        mode_v = tk.StringVar(value="Standard")
        ttk.Combobox(
            frm, textvariable=mode_v, values=["Standard"],
            state="readonly", width=14,
        ).grid(row=0, column=1, sticky="w", **p)
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

        ttk.Label(frm, text="Мин. ходов:").grid(row=3, column=0, sticky="w", **p)
        min_v = tk.IntVar(value=3)
        ttk.Spinbox(
            frm,
            textvariable=min_v,
            from_=1,
            to=40,
            increment=1,
            width=10
        ).grid(
            row=3, column=1, sticky="w", **p
        )
        self._vars["min_moves"] = min_v

        ttk.Label(frm, text="Макс. ходов:").grid(row=4, column=0, sticky="w", **p)
        max_v = tk.IntVar(value=12)
        ttk.Spinbox(
            frm,
            textvariable=max_v,
            from_=1,
            to=40,
            increment=1,
            width=10
        ).grid(
            row=4, column=1, sticky="w", **p
        )
        self._vars["max_moves"] = max_v

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

        rng = random.Random()
        seen: Set[str] = set()
        next_id = get_next_id()
        ok = 0

        self._log(f"Генерация {count} уровней, начиная с campaign_{next_id:02d}...")
        self._log(
            f"Ходов: {min_moves}–{max_moves},"
            f"заполненность ≥ {min_fill:.0f}%\n"
        )

        os.makedirs(OUTPUT_DIR, exist_ok=True)

        for i in range(count):
            result = generate_one(min_moves, max_moves, min_fill, rng, seen)
            if result is None:
                self._log(
                    f"[{i+1}/{count}]  — пропуск (не удалось подобрать уровень)"
                )
            else:
                boxes, blocked, min_sol = result
                lid = f"campaign_{next_id:02d}"
                data = level_to_dict(boxes, blocked, min_sol, lid)
                out_path = os.path.join(OUTPUT_DIR, f"{lid}.json")
                with open(out_path, "w", encoding="utf-8") as f:
                    json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
                sol_path = solve_with_path(
                    boxes, blocked, max_depth=max_moves + 6
                )
                if sol_path is not None:
                    write_solution(
                        lid, boxes, blocked, min_sol + 1, sol_path
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


# ─── Точка входа ──────────────────────────────────────────────────────────────
if __name__ == "__main__":
    App().mainloop()
