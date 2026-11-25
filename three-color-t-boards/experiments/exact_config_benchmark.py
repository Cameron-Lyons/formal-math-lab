#!/usr/bin/env python3
"""Three bounded deterministic Ganak configurations on the original model."""

import hashlib
import json
import os
import re
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from exact_count_cnf import make_cnf
from exact_phase import board_model, default_board, normalize_board, rephase, write_cnf

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments"
CONFIGS = {
    "fast_pipeline": ["--fast"],
    "structural": [
        "--fast",
        "--allindep",
        "1",
        "--arjunprobe",
        "0",
        "--arjunsimplev",
        "0",
        "--arjunbackwmaxc",
        "0",
        "--arjunoraclefindbins",
        "0",
        "--arjunextend",
        "0",
        "--coverdrop",
        "0",
        "--puurabackbone",
        "0",
        "--puuraautarky",
        "0",
        "--puuraoraclevivif",
        "0",
        "--puuraoraclesparsify",
        "0",
        "--extraoracle",
        "0",
        "--tditers",
        "50",
    ],
    "td_only": ["--arjun", "0", "--puura", "0", "--td", "1", "--tditers", "50"],
}


def prepare():
    for colors, prefix_rows, seed, mode, name in [
        (2, 0, 0, "orbit", "binary"),
        (3, 7, 1, "none", "prefix_C"),
    ]:
        board = normalize_board(default_board(colors, seed), colors, mode)
        prefix = board[:prefix_rows]
        cnf, cells = make_cnf(colors, prefix, mode != "none", "tree", mode == "orbit")
        model = board_model(cnf, cells, board)
        write_cnf(OUT / f"exact_config_{name}.cnf", rephase(cnf, model), cells)


def run(config, scope, seconds):
    path = OUT / (
        "exact_phase_ternary.cnf" if scope == "ternary" else f"exact_config_{scope}.cnf"
    )
    log = OUT / f"exact_config_{config}_{scope}.log"
    command = [
        "timeout",
        "--kill-after=2s",
        str(seconds),
        str(OUT / "exact_count_tools/ganak"),
        "--prob",
        "0",
        "--maxcache",
        "512",
        "--polar",
        "3",
        "--verb",
        "2",
        *CONFIGS[config],
        str(path),
    ]
    started = time.monotonic()
    with log.open("w") as output:
        process = subprocess.Popen(
            command, stdout=output, stderr=subprocess.STDOUT, start_new_session=True
        )
        _, status, usage = os.wait4(process.pid, 0)
        code = os.waitstatus_to_exitcode(status)
        process.returncode = code
    text = log.read_text()
    count = re.search(r"^c s exact arb int (\d+)$", text, re.MULTILINE)
    rdb = re.findall(r"^c o \[rdb\].*rdb: (\d+)", text, re.MULTILINE)
    sizes = re.findall(r"^c o ind size: (\d+) nvars: (\d+)", text, re.MULTILINE)
    terminal = [line for line in text.splitlines() if line.strip()][-1:]
    result = {
        "configuration": config,
        "scope": scope,
        "command": command,
        "input": str(path.relative_to(ROOT)),
        "input_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "log": str(log.relative_to(ROOT)),
        "status": "complete"
        if code == 0 and count
        else ("timeout" if code in (124, 137, -9) else "failed"),
        "exit_code": code,
        "exact_count": int(count[1]) if code == 0 and count else None,
        "wall_seconds": round(time.monotonic() - started, 3),
        "limit_wall_seconds": seconds,
        "user_seconds": round(usage.ru_utime, 3),
        "system_seconds": round(usage.ru_stime, 3),
        "max_rss_kb": usage.ru_maxrss,
        "preprocessing_completed": "Arjun T:" in text if config != "td_only" else None,
        "counter_initialization_observed": "blk vars from:" in text,
        "counter_search_observed": bool(rdb),
        "last_recorded_rdb": int(rdb[-1]) if rdb else None,
        "counter_support_size": int(sizes[-1][0]) if sizes else None,
        "counter_variables": int(sizes[-1][1]) if sizes else None,
        "terminal_log_line": re.sub(r"\x1b\[[0-9;]*m", "", terminal[0])
        if terminal
        else None,
    }
    print(json.dumps(result), flush=True)
    return result


def main():
    prepare()
    results = []
    with ThreadPoolExecutor(max_workers=3) as pool:
        binary = list(pool.map(lambda config: run(config, "binary", 20), CONFIGS))
    results.extend(binary)
    valid = []
    for result in binary:
        if result["exact_count"] is not None and result["exact_count"] != 42:
            raise AssertionError(result)
        valid.append(result["configuration"])
    tasks = [(config, scope) for scope in ("prefix_C", "ternary") for config in valid]
    with ThreadPoolExecutor(max_workers=3) as pool:
        results.extend(pool.map(lambda task: run(*task, 60), tasks))
    (OUT / "exact_config_results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
