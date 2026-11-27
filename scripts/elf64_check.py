#!/usr/bin/env python3
"""Compatibility wrapper delegating to canonical `runtime/elf64_check.py`."""
from __future__ import annotations

import sys
from pathlib import Path

_RUNTIME = Path(__file__).resolve().parent.parent / "runtime"
if str(_RUNTIME) not in sys.path:
    sys.path.insert(0, str(_RUNTIME))

from elf64_check import *  # noqa: F401,F403,E402
