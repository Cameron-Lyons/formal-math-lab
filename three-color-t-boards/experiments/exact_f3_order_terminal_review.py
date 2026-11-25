#!/usr/bin/env python3
"""Strict terminal audit of the long minimum-fill full F3 trial."""

from exact_f3_terminal_review import main

if __name__ == "__main__":
    main("exact_msolve_full_native3_minfill_symbolic_3g", translated=True, ordered=True)
