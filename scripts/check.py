#!/usr/bin/env python3
"""Type-check individual problem files with `lake env lean`, at most N Lean processes at a time.

Usage: python scripts/check.py PillowProblems/P05.lean [more files] [--slots 3]

Problem files import only `PillowProblems.Basic`, so after `lake build PillowProblems.Basic`
each one can be checked on its own. The slot limit keeps memory use bounded when several
checks run in parallel on one machine.
"""
import argparse, os, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SLOT_DIR = Path(os.environ.get('TEMP', '/tmp')) / 'pillow_lean_slots'


def acquire_slot(n: int) -> Path:
    SLOT_DIR.mkdir(parents=True, exist_ok=True)
    while True:
        for i in range(n):
            p = SLOT_DIR / f'slot{i}'
            try:
                if p.exists() and time.time() - p.stat().st_mtime > 1800:  # stale
                    p.unlink()
            except OSError:
                pass
            try:
                fd = os.open(p, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
                os.write(fd, str(os.getpid()).encode())
                os.close(fd)
                return p
            except FileExistsError:
                continue
        time.sleep(2)


def main() -> int:
    sys.stdout.reconfigure(encoding='utf-8')  # Lean diagnostics contain non-ASCII
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+')
    ap.add_argument('--slots', type=int, default=3)
    a = ap.parse_args()
    rc = 0
    for f in a.files:
        slot = acquire_slot(a.slots)
        try:
            t0 = time.time()
            r = subprocess.run(['lake', 'env', 'lean', str(Path(f))], cwd=ROOT, capture_output=True,
                               text=True, encoding='utf-8', errors='replace')
        finally:
            slot.unlink(missing_ok=True)
        msg = (r.stdout + r.stderr).strip()
        sorries = msg.count("declaration uses `sorry`") + msg.count("declaration uses 'sorry'")
        print(f"[{'OK' if r.returncode == 0 else 'FAIL'}] {f} ({time.time() - t0:.0f}s, sorry warnings: {sorries})")
        if msg:
            print(msg)
        rc |= r.returncode != 0
    return rc


if __name__ == '__main__':
    sys.exit(main())
