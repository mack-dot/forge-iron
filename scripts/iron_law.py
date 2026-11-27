#!/usr/bin/env python3
"""Compatibility wrapper delegating to canonical `runtime/iron_law.py`."""
from __future__ import annotations

import sys
from pathlib import Path

_RUNTIME = Path(__file__).resolve().parent.parent / "runtime"
if str(_RUNTIME) not in sys.path:
    sys.path.insert(0, str(_RUNTIME))

import iron_law as _rt_iron_law  # noqa: E402

if __name__ == "__main__":
    sys.exit(_rt_iron_law.main(sys.argv))
