"""Render a panel-question JSON file into a LaTeX prompt.

Reads a JSON file produced by `lake exe panelquestion_export` for an active
panel question and emits a complete LaTeX prompt by filling the appropriate
per-question Jinja2 template under this directory.

CLI:
    python3 render.py <json_path> [--out output.tex]

Per-question template selection: the `questionId` prefix (`Q1_`, `Q2_`,
`Q3_`, `Q5_`, or `Q6_`) selects the corresponding `q*_prompt.tex.j2`.
Each per-question template extends `common_prompt.tex.j2`.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from jinja2 import Environment, FileSystemLoader, select_autoescape

TEMPLATE_DIR = Path(__file__).resolve().parent
QID_RE = re.compile(r"^(Q[12356])_")


def render(json_path: Path, out_path: Path) -> None:
    data = json.loads(json_path.read_text())
    summary = data["summary"]
    qid = summary["questionId"]
    match = QID_RE.match(qid)
    if not match:
        raise ValueError(f"Cannot infer template for questionId {qid!r}")
    template_name = f"{match.group(1).lower()}_prompt.tex.j2"

    env = Environment(
        loader=FileSystemLoader(str(TEMPLATE_DIR)),
        autoescape=select_autoescape(disabled_extensions=("j2",), default=False),
        trim_blocks=True,
        lstrip_blocks=True,
    )
    template = env.get_template(template_name)
    out_path.write_text(template.render(**summary))


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json_path", type=Path, help="Input JSON file.")
    parser.add_argument(
        "--out", type=Path, default=None,
        help="Output .tex path (default: alongside the JSON, same stem).",
    )
    args = parser.parse_args(argv)
    out = args.out or args.json_path.with_suffix(".tex")
    render(args.json_path, out)
    print(f"Wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
