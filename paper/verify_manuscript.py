"""Static integrity checks for the canonical Erdős 506 manuscript.

This is an expository/source-boundary checker.  It does not verify the
mathematics and does not search configurations.
"""

from __future__ import annotations

from collections import Counter
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
MAIN = HERE / "erdos506_v1_review_manuscript.tex"
BIB = HERE / "references.bib"
SECTIONS = (
    HERE / "sections/01_foundations_small_cases.tex",
    HERE / "sections/02_finite_n10_n12.tex",
    HERE / "sections/02a_c39_router_v2.tex",
    HERE / "sections/03_n13_infinity_certificates.tex",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def tex_sources() -> tuple[Path, ...]:
    paths = (MAIN, *SECTIONS)
    for path in paths:
        require(path.is_file(), f"missing manuscript source: {path}")
        require(path.stat().st_size > 500, f"empty manuscript source: {path}")
    return paths


def arguments(text: str, command: str) -> list[str]:
    pattern = re.compile(rf"\\{command}\s*\{{([^}}]+)\}}")
    return [item.strip() for value in pattern.findall(text) for item in value.split(",")]


def check_balanced_environments(path: Path, text: str) -> None:
    """Reject crossed or unclosed TeX environments before invoking TeX."""

    stack: list[tuple[str, int]] = []
    token_pattern = re.compile(r"\\(begin|end)\{([^}]+)\}")
    for match in token_pattern.finditer(text):
        command, environment = match.groups()
        line = text.count("\n", 0, match.start()) + 1
        if command == "begin":
            stack.append((environment, line))
            continue
        require(bool(stack), f"unmatched \\end{{{environment}}} at {path}:{line}")
        opened, opened_line = stack.pop()
        require(
            opened == environment,
            f"crossed environments at {path}:{line}: "
            f"opened {opened} on line {opened_line}, closed {environment}",
        )
    require(not stack, f"unclosed environments in {path}: {stack}")


def main() -> None:
    paths = tex_sources()
    texts = {path: path.read_text(encoding="utf-8") for path in paths}
    joined = "\n".join(texts.values())
    main_text = texts[MAIN]

    for path, text in texts.items():
        check_balanced_environments(path, text)
        bad_controls = sorted({ord(char) for char in text if ord(char) < 32 and char not in "\n\t"})
        require(not bad_controls, f"control characters in {path}: {bad_controls}")

    malformed_tex = {
        r",[ \t]*,": "doubled comma",
        r"(?<![\\A-Za-z])quad\b": "missing backslash before quad",
        r"(?<![\\A-Za-z])qquad\b": "missing backslash before qquad",
        r"\\label\{[^}]+\}\\\s*$": "single trailing backslash after label",
        r"\\tag\{\d": "manual numeric equation tag",
    }
    for pattern, message in malformed_tex.items():
        for path, text in texts.items():
            match = re.search(pattern, text, flags=re.MULTILINE)
            line = text.count("\n", 0, match.start()) + 1 if match else -1
            require(match is None, f"{message} at {path}:{line}")

    expected_inputs = {
        "sections/01_foundations_small_cases",
        "sections/02_finite_n10_n12",
        "sections/03_n13_infinity_certificates",
    }
    found_inputs = set(arguments(main_text, "input"))
    require(found_inputs == expected_inputs, f"unexpected input set: {found_inputs}")
    for raw in found_inputs:
        require((HERE / f"{raw}.tex").is_file(), f"missing input: {raw}")

    supplement_paths = set(re.findall(r"\\path\{(supplement/[^}]+)\}", joined))
    for raw in supplement_paths:
        path = HERE / raw
        require(path.is_file(), f"missing named supplement: {raw}")
        require(path.stat().st_size > 100, f"empty named supplement: {raw}")

    forbidden = {
        "% REVIEW GAP:": "unresolved review gap",
        "scratch/": "research-dossier path leaked into article",
        "docs/": "operational-doc path leaked into article",
        "C:\\Users": "local absolute path leaked into article",
        "sixteen-point base case": "obsolete n=16 architecture",
        "parametric deletion": "obsolete deletion architecture",
        "uniform deletion": "obsolete deletion architecture",
        "solver infeasibility": "historical solver narrative",
        "CP-SAT": "historical solver narrative",
        "MILP": "historical solver narrative",
    }
    lowered = joined.lower()
    for token, message in forbidden.items():
        require(token.lower() not in lowered, f"{message}: {token}")

    labels = re.findall(r"\\label\{([^}]+)\}", joined)
    duplicate_labels = sorted(label for label, count in Counter(labels).items() if count > 1)
    require(not duplicate_labels, f"duplicate labels: {duplicate_labels}")
    label_set = set(labels)

    references: set[str] = set()
    for command in ("ref", "eqref", "cref", "Cref"):
        references.update(arguments(joined, command))
    missing_refs = sorted(references - label_set)
    require(not missing_refs, f"undefined references: {missing_refs}")

    bib_text = BIB.read_text(encoding="utf-8")
    bib_keys = set(re.findall(r"@\w+\s*\{\s*([^,\s]+)", bib_text))
    citation_keys = set(arguments(joined, "cite"))
    missing_citations = sorted(citation_keys - bib_keys)
    require(not missing_citations, f"undefined citations: {missing_citations}")

    expected_labels = {
        "thm:main",
        "sec:foundations-small",
        "thm:small-values",
        "sec:finite-n10-n12",
        "thm:finite-n10-n12",
        "sec:n13-infinity",
        "thm:n13-value",
        "thm:large-range",
    }
    require(expected_labels <= label_set, f"missing canonical labels: {sorted(expected_labels-label_set)}")

    required_phrases = (
        "f(7)=11",
        "f(8)=17",
        "n\\ge15",
        "No optimizer",
        "not a Lean",
    )
    for phrase in required_phrases:
        require(phrase.lower() in lowered, f"missing publication boundary: {phrase}")

    theorem_count = len(re.findall(r"\\begin\{(?:theorem|lemma|proposition|corollary)\}", joined))
    proof_count = len(re.findall(r"\\begin\{proof\}", joined))
    require(theorem_count >= 25, f"too few named claims: {theorem_count}")
    require(proof_count >= 20, f"too few written proofs: {proof_count}")

    print(
        "PASS_CANONICAL_MANUSCRIPT_STATIC_INTEGRITY "
        f"files={len(paths)} labels={len(labels)} refs={len(references)} "
        f"citations={len(citation_keys)} supplements={len(supplement_paths)} "
        f"claims={theorem_count} proofs={proof_count}"
    )
    print("PASS_NO_MISSING_INPUT_REFERENCE_OR_CITATION")
    print("PASS_NO_RESEARCH_PATH_OR_OBSOLETE_DELETION_ARCHITECTURE")


if __name__ == "__main__":
    main()
