from __future__ import annotations

import argparse
import json
import math
from functools import lru_cache
from pathlib import Path

from erdos506_small_n_relaxed_cover import line_patterns, subsets, triple_mask_for_block, triples


TARGETS = {4: 2, 5: 4, 6: 7, 7: 10}
CANDIDATES = {4: 3, 5: 5, 6: 8, 7: 11}


def _mask_indices(mask: int) -> list[int]:
    indices = []
    while mask:
        bit = mask & -mask
        indices.append(bit.bit_length() - 1)
        mask ^= bit
    return indices


def _block_payload(blocks: list[tuple[int, ...]]) -> list[list[int]]:
    return [list(block) for block in blocks]


def _feasible_circle_cover(
    n: int,
    line_pattern: tuple[tuple[int, ...], ...],
    target: int,
) -> tuple[bool, list[tuple[int, ...]] | None]:
    triple_list = triples(n)
    triple_index = {triple: idx for idx, triple in enumerate(triple_list)}
    all_triples_mask = (1 << len(triple_list)) - 1

    collinear_mask = 0
    for line in line_pattern:
        collinear_mask |= triple_mask_for_block(line, triple_index)
    universe_mask = all_triples_mask & ~collinear_mask

    circle_blocks: list[tuple[tuple[int, ...], int, set[int]]] = []
    for block in subsets(n, 3, n - 1):
        mask = triple_mask_for_block(block, triple_index)
        if mask & collinear_mask:
            continue
        if mask & universe_mask:
            circle_blocks.append((block, mask, set(block)))

    compatibility_masks = []
    for _, _, block_set in circle_blocks:
        compatible = 0
        for idx, (_, _, other_set) in enumerate(circle_blocks):
            if len(block_set & other_set) <= 2:
                compatible |= 1 << idx
        compatibility_masks.append(compatible)

    coverers = []
    for triple_idx in range(len(triple_list)):
        triple_bit = 1 << triple_idx
        mask = 0
        for block_idx, (_, block_mask, _) in enumerate(circle_blocks):
            if block_mask & triple_bit:
                mask |= 1 << block_idx
        coverers.append(mask)

    full_available = (1 << len(circle_blocks)) - 1
    choice: dict[tuple[int, int, int], int] = {}

    @lru_cache(maxsize=None)
    def dfs(remaining: int, available: int, slots: int) -> bool:
        if remaining == 0:
            return True
        if slots == 0:
            return False

        union_mask = 0
        for block_idx in _mask_indices(available):
            union_mask |= circle_blocks[block_idx][1]
        if remaining & ~union_mask:
            return False

        best_options: int | None = None
        best_option_count = math.inf
        for triple_idx in _mask_indices(remaining):
            options = coverers[triple_idx] & available
            option_count = options.bit_count()
            if option_count == 0:
                return False
            if option_count < best_option_count:
                best_option_count = option_count
                best_options = options

        assert best_options is not None
        option_indices = _mask_indices(best_options)
        option_indices.sort(key=lambda idx: -circle_blocks[idx][1].bit_count())
        for block_idx in option_indices:
            next_remaining = remaining & ~circle_blocks[block_idx][1]
            next_available = available & compatibility_masks[block_idx] & ~(1 << block_idx)
            if dfs(next_remaining, next_available, slots - 1):
                choice[(remaining, available, slots)] = block_idx
                return True
        return False

    if not dfs(universe_mask, full_available, target):
        return False, None

    witness = []
    remaining = universe_mask
    available = full_available
    slots = target
    while remaining:
        block_idx = choice[(remaining, available, slots)]
        witness.append(circle_blocks[block_idx][0])
        remaining &= ~circle_blocks[block_idx][1]
        available = available & compatibility_masks[block_idx] & ~(1 << block_idx)
        slots -= 1
    return True, witness


def audit_n(n: int, max_survivor_examples: int = 5) -> dict[str, object]:
    target = TARGETS[n]
    patterns = line_patterns(n)
    survivor_examples = []
    survivor_count = 0
    for pattern in patterns:
        feasible, witness = _feasible_circle_cover(n, pattern, target)
        if not feasible:
            continue
        survivor_count += 1
        if len(survivor_examples) < max_survivor_examples:
            survivor_examples.append(
                {
                    "line_blocks": _block_payload(list(pattern)),
                    "circle_blocks": _block_payload(witness or []),
                    "circle_block_count": len(witness or []),
                }
            )

    return {
        "n": n,
        "candidate_exact_value": CANDIDATES[n],
        "target_to_exclude": target,
        "line_pattern_count": len(patterns),
        "incidence_survivor_count_at_target": survivor_count,
        "rules_out_target_by_incidence_axioms": survivor_count == 0,
        "candidate_promoted_by_this_audit": survivor_count == 0,
        "survivor_examples": survivor_examples,
    }


def small_n_incidence_audit(ns: list[int] | None = None, max_survivor_examples: int = 5) -> dict[str, object]:
    ns = ns or [4, 5, 6, 7]
    rows = [audit_n(n, max_survivor_examples=max_survivor_examples) for n in ns]
    return {
        "packet": "erdos506 small-n incidence audit",
        "variant": "distinct real points, not all on one line and not all on one circle",
        "incidence_axioms": [
            "collinear triples do not determine circles",
            "a circle block cannot contain a collinear triple",
            "two distinct circle blocks share at most two points",
            "all non-collinear triples must be covered by circle blocks",
            "circle blocks are proper subsets, so the excluded all-on-one-circle case is not used",
        ],
        "rows": rows,
        "proved_candidates": [row["n"] for row in rows if row["candidate_promoted_by_this_audit"]],
        "unproved_candidates": [row["n"] for row in rows if not row["candidate_promoted_by_this_audit"]],
        "claim_boundary": (
            "This is a necessary-condition incidence audit, not a full realization theorem. "
            "Rows with survivors are open in this packet: a survivor may still be algebraically unrealizable."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Small-n incidence audit for Erdos 506 candidates.")
    parser.add_argument("--n", type=int, action="append", choices=sorted(TARGETS))
    parser.add_argument("--max-survivor-examples", type=int, default=5)
    parser.add_argument("--output-json", type=Path)
    args = parser.parse_args()

    payload = small_n_incidence_audit(args.n, max_survivor_examples=args.max_survivor_examples)
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.output_json:
        args.output_json.write_text(text + "\n", encoding="utf-8")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
