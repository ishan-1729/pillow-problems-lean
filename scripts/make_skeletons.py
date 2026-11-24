#!/usr/bin/env python3
"""Generate PillowProblems/PNN.lean for each of the 72 problems from data/problems.json.

Each file quotes Carroll's question (and his separate answer, if any) verbatim, followed by
placeholders that the formalization replaces. Run once; refuses to overwrite existing files.
"""
import json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def quote(t: str) -> str:
    t = t.replace('-/', '- /').replace('/-', '/ -')
    return '\n>\n'.join('> ' + p for p in t.split('\n\n') if p.strip())


def main() -> int:
    data = json.loads((ROOT / 'data' / 'problems.json').read_text(encoding='utf-8'))
    for p in data['problems']:
        n = p['n']
        path = ROOT / 'PillowProblems' / f'P{n:02d}.lean'
        if path.exists():
            print('exists, skipping', path.name); continue
        lines = [
            'import PillowProblems.Basic', '',
            '/-!',
            f'# Problem {n}' + (f' ({", ".join(p["subjects"])})' if p['subjects'] else ''), '',
            '**Question.**' + (f' *(dated {p["date"]})*' if p['date'] else ''), '',
            quote(p['question']), '',
        ]
        if p['answer']:
            lines += ['**Answer.**', '', quote(p['answer']), '']
        lines += [
            "*(Carroll's solution: Chapter III, problem " + str(n) + '; text in `data/problems.json`.)*', '',
            '**Lean reading.** TODO', '',
            '**Status.** TODO',
            '-/', '',
            f'namespace PillowProblems.P{n:02d}', '',
            f'-- TODO(problem {n})', '',
            f'end PillowProblems.P{n:02d}', '',
        ]
        path.write_text('\n'.join(lines), encoding='utf-8')
    print('done')
    return 0


if __name__ == '__main__':
    sys.exit(main())
