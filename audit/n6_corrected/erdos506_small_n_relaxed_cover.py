from __future__ import annotations

import argparse
import json
import math
from functools import lru_cache
from itertools import combinations
from pathlib import Path


def bit(index: int) -> int:
    return 1 << index


def triples(n: int) -> list[tuple[int, int, int]]:
    return [tuple(combo) for combo in combinations(range(n), 3)]


def subsets(n: int, min_size: int, max_size: int) -> list[tuple[int, ...]]:
    return [
        tuple(combo)
        for size in range(min_size, max_size + 1)
        for combo in combinations(range(n), size)
    ]


def triple_mask_for_block(block: tuple[int, ...], triple_index: dict[tuple[int, int, int], int]) -> int:
    mask = 0
    for triple in combinations(block, 3):
        mask |= bit(triple_index[tuple(triple)])
    return mask


def line_patterns(n: int) -> list[tuple[tuple[int, ...], ...]]:
    candidates = subsets(n, 3, n - 1)
    patterns: list[tuple[tuple[int, ...], ...]] = [()]

    def compatible(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
        return len(set(a) & set(b)) <= 1

    def dfs(start: int, chosen: list[tuple[int, ...]]) -> None:
        for idx in range(start, len(candidates)):
            line = candidates[idx]
            if all(compatible(line, existing) for existing in chosen):
                next_chosen = chosen + [line]
                patterns.append(tuple(next_chosen))
                dfs(idx + 1, next_chosen)

    dfs(0, [])
    return patterns


def min_exact_cover_count(universe_mask: int, block_masks: list[int], stop_at: int | None = None) -> int | None:
    if universe_mask == 0:
        return 0
    block_masks = sorted(set(mask & universe_mask for mask in block_masks if mask & universe_mask), key=lambda m: -m.bit_count())
    if not block_masks:
        return None

    coverers: dict[int, list[int]] = {}
    mask = universe_mask
    while mask:
        b = mask & -mask
        coverers[b.bit_length() - 1] = [bm for bm in block_masks if bm & b]
        mask ^= b

    best = stop_at if stop_at is not None else math.inf

    @lru_cache(maxsize=None)
    def dfs(remaining: int, used: int) -> int:
        nonlocal best
        if remaining == 0:
            best = min(best, used)
            return used
        if used >= best:
            return math.inf
        # Pick the remaining triple with the fewest candidate blocks.
        bits = []
        tmp = remaining
        while tmp:
            b = tmp & -tmp
            idx = b.bit_length() - 1
            bits.append((len([bm for bm in coverers[idx] if bm & remaining]), idx))
            tmp ^= b
        _, triple_idx = min(bits)
        answer = math.inf
        for bm in coverers[triple_idx]:
            answer = min(answer, dfs(remaining & ~bm, used + 1))
        return answer

    value = dfs(universe_mask, 0)
    return None if value == math.inf else int(value)


def analyze_n(n: int, target: int) -> dict[str, object]:
    ts = triples(n)
    triple_index = {triple: idx for idx, triple in enumerate(ts)}
    all_triples_mask = (1 << len(ts)) - 1
    circle_blocks = subsets(n, 3, n - 1)
    circle_masks = [triple_mask_for_block(block, triple_index) for block in circle_blocks]
    rows = []
    best_relaxed_at_most_target = math.inf
    witness_pattern = None
    for pattern in line_patterns(n):
        collinear_mask = 0
        for line in pattern:
            collinear_mask |= triple_mask_for_block(line, triple_index)
        universe = all_triples_mask & ~collinear_mask
        # A circle block cannot contain a collinear triple.
        admissible_circle_masks = [mask for mask in circle_masks if mask & collinear_mask == 0]
        min_cover = min_exact_cover_count(universe, admissible_circle_masks, stop_at=target)
        if min_cover is None:
            continue
        best_relaxed_at_most_target = min(best_relaxed_at_most_target, min_cover)
        if witness_pattern is None or min_cover < witness_pattern["relaxed_min_circle_count"]:
            witness_pattern = {
                "line_blocks": [list(line) for line in pattern],
                "collinear_triple_count": collinear_mask.bit_count(),
                "relaxed_min_circle_count": min_cover,
            }
        rows.append(
            {
                "line_blocks": [list(line) for line in pattern],
                "collinear_triple_count": collinear_mask.bit_count(),
                "relaxed_min_circle_count": min_cover,
            }
        )
    return {
        "n": n,
        "target_to_exclude": target,
        "line_pattern_count": len(line_patterns(n)),
        "best_relaxed_circle_count_at_most_target": (
            None if best_relaxed_at_most_target == math.inf else int(best_relaxed_at_most_target)
        ),
        "relaxed_model_rules_out_target": best_relaxed_at_most_target > target,
        "best_witness_pattern": witness_pattern,
        "rows_with_count_at_most_target": [row for row in rows if row["relaxed_min_circle_count"] <= target][:20],
        "claim_boundary": (
            "Relaxed incidence cover only. It ignores algebraic realizability and "
            "some circle-intersection constraints; if it rules out a target, that "
            "is useful, but if it has survivors they may be unrealizable."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Relaxed small-n incidence cover diagnostic for Erdos 506.")
    parser.add_argument("--n", type=int, action="append")
    parser.add_argument("--output-json", type=Path)
    args = parser.parse_args()
    ns = args.n or [4, 5, 6, 7]
    targets = {4: 2, 5: 4, 6: 7, 7: 10}
    payload = {
        "packet": "erdos506 small-n relaxed cover diagnostic",
        "rows": [analyze_n(n, targets[n]) for n in ns],
    }
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.output_json:
        args.output_json.write_text(text + "\n", encoding="utf-8")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
