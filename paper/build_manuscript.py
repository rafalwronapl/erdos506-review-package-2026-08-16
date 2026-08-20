"""Build and gate the canonical V1 review manuscript reproducibly."""

from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import os
import re
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MAIN = HERE / "erdos506_v1_review_manuscript.tex"
PDF = MAIN.with_suffix(".pdf")
LOG = MAIN.with_suffix(".log")
TECTONIC = ROOT / ".tools/tectonic-0.17.0/tectonic.exe"
TECTONIC_SHA256 = "99ffcfdbf1ebf8bdda9e791942e3d06aedb12463fddc33f07de6f5211c8bf08d"
SOURCE_DATE_EPOCH = "1785888000"  # 2026-08-05 00:00:00 UTC
MAX_OVERFULL_PT = 0.5


def digest(path: Path) -> str:
    value = sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            value.update(chunk)
    return value.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> None:
    require(TECTONIC.is_file(), f"missing pinned Tectonic binary: {TECTONIC}")
    require(digest(TECTONIC) == TECTONIC_SHA256, "unexpected Tectonic binary hash")

    subprocess.run([sys.executable, "verify_manuscript.py"], cwd=HERE, check=True)
    build_environment = os.environ.copy()
    build_environment["SOURCE_DATE_EPOCH"] = SOURCE_DATE_EPOCH
    subprocess.run(
        [str(TECTONIC), MAIN.name, "--keep-logs", "--keep-intermediates"],
        cwd=HERE,
        env=build_environment,
        check=True,
    )

    require(PDF.is_file() and PDF.stat().st_size > 100_000, "missing or implausibly small PDF")
    log = LOG.read_text(encoding="utf-8", errors="replace")
    forbidden_log = (
        "There were undefined references",
        "Citation `",
        "multiply defined",
        "Emergency stop",
        "LaTeX Warning:",
        "Package hyperref Warning:",
    )
    for token in forbidden_log:
        require(token not in log, f"TeX log contains: {token}")

    excesses = [
        float(value)
        for value in re.findall(r"Overfull \\hbox \(([0-9.]+)pt too wide\)", log)
        if float(value) > MAX_OVERFULL_PT
    ]
    require(not excesses, f"overfull boxes above {MAX_OVERFULL_PT}pt: {excesses}")

    sources = [
        MAIN,
        *sorted((HERE / "sections").glob("*.tex")),
        HERE / "references.bib",
        *sorted(path for path in (HERE / "supplement").glob("*") if path.is_file()),
    ]
    source_fingerprint = sha256(
        "\n".join(
            f"{path.relative_to(HERE).as_posix()}:{digest(path)}" for path in sources
        ).encode()
    ).hexdigest()
    print(
        "PASS_CANONICAL_V1_ARTICLE_BUILD "
        f"source_files={len(sources)} source_fingerprint={source_fingerprint} "
        f"pdf_sha256={digest(PDF)}"
    )


if __name__ == "__main__":
    main()
