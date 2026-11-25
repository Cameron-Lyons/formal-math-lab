#!/usr/bin/env python3
"""Audit only terminal artifacts of the checked-byte full minimum-fill trial.

Requires both completed backend and outer result JSONs. Does not poll, start,
restart, terminate or assign a status to any still-running solver.
"""
from exact_f3_terminal_review import main

if __name__ == '__main__':
    main('exact_msolve_full_native3_minfill_byte_4g', translated=True, ordered=True)
