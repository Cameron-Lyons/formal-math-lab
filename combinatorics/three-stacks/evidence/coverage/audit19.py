"""Audit the original length-19 ordered join, all closure counts and physical schedules."""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import itertools
import json
import math
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import IO, Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify.replay import replay

EVIDENCE_DIR = Path(__file__).resolve().parents[1]
RESULTS = Path(__file__).resolve().parent / "results"
RESULTS_ARCHIVE = EVIDENCE_DIR / "results.tar.gz"
PER_ORDER = math.comb(18, 7) * math.factorial(11)
WIDTH = len("Hard 1 " + " ".join(map(str, range(1, 20))) + "\n")
JOIN_KEYS = (
    "order",
    "decks",
    "delegated_or_bond",
    "owned",
    "group_count",
    "head_visits",
    "leaf",
    "mirror",
    "dual",
    "extra",
    "late",
    "late_dual",
    "pending",
)
RECUTS = [(10, False), (9, False), (10, True), (9, True), (8, False), (8, True)]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def open_text(path: Path) -> IO[str]:
    if path.suffix == ".gz":
        return gzip.open(path, "rt", encoding="utf-8")
    return path.open(encoding="utf-8")


def hashfile(path: Path) -> str:
    with path.open("rb") as src:
        return hashlib.file_digest(src, "sha256").hexdigest()


def count(x: object) -> bool:
    return type(x) is int and x >= 0


@dataclass
class Job:
    name: str
    ranks: Path
    log: Path
    raw: Path | None
    receipt: dict[str, Any] | None = None


def live_jobs(manifest: Path) -> list[Job]:
    jobs: list[Job] = []
    base = manifest.resolve().parent
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if line.strip() and not line.startswith("#"):
            name, ranks, stop, stride, log, raw = line.split()
            require(
                bool(re.fullmatch(r"[A-Za-z0-9_-]+", name))
                and ranks.startswith("@")
                and (stop, stride) == ("5040", "1"),
                f"Invalid manifest row {line}",
            )
            jobs.append(Job(name, base / ranks[1:], base / log, base / raw))
    return jobs


def policy_and_domains(
    priority_path: Path, domains_path: Path
) -> tuple[dict[int, int], dict[int, dict[str, int]]]:
    with open_text(priority_path) as f:
        prio_rows = [tuple(map(int, line.split())) for line in f]
    require(
        len(prio_rows) == 5040 and sorted(prio_rows) == [(i, 0) for i in range(5040)],
        "Invalid fresh priority policy",
    )
    priority = {t: i for i, (t, _) in enumerate(prio_rows)}
    with open_text(domains_path) as f:
        dom_rows = [{k: int(v) for k, v in r.items()} for r in csv.DictReader(f)]
    require(
        len(dom_rows) == 5040
        and sorted(r["order"] for r in dom_rows) == list(range(5040)),
        "Missing or duplicate expected-domain rank",
    )
    for r in dom_rows:
        require(
            all(count(v) for v in r.values())
            and r["owned"] == r["full"] + r["lex"]
            and r["owned"] + r["delegated_or_bond"] == PER_ORDER,
            f"Invalid expected domain {r}",
        )
    return priority, {r["order"]: r for r in dom_rows}


def verify_domains(priority: Path, domains: Path) -> None:
    with tempfile.TemporaryDirectory() as temp:
        work = Path(temp)
        with (
            open_text(priority) as src,
            (work / "priority.txt").open("w", encoding="utf-8") as out,
        ):
            shutil.copyfileobj(src, out)
        source = Path(__file__).with_name("check_ordered_ownership.cpp")
        subprocess.run(
            ["c++", "-O3", "-std=c++23", source, "-o", work / "domains"], check=True
        )
        verified = subprocess.run(
            [work / "domains", work / "priority.txt", "900"],
            check=True,
            capture_output=True,
            text=True,
        )
        with open_text(domains) as expected:
            require(
                verified.stdout == expected.read(),
                "Independent physical ownership enumeration differs from archived domains",
            )


def read_progress(
    job: Job,
    partial: bool,
    priority: dict[int, int],
    domains: dict[int, dict[str, int]],
) -> tuple[list[int], dict[int, dict[str, int]]]:
    with open_text(job.ranks) as f:
        ranks = [int(x) for x in f.read().split()]
    with open_text(job.log) as f:
        text = f.read()
    if text and not text.endswith("\n"):
        require(partial, f"{job.name} has an unfinished progress line")
        text = text[: text.rfind("\n") + 1]
    rows: dict[int, dict[str, int]] = {}
    for line in text.splitlines():
        bits = line.split()
        if not bits:
            continue
        require(
            len(bits) == 2 * (len(JOIN_KEYS) + 2)
            and bits[::2] == [*JOIN_KEYS, "prepare", "seconds"],
            f"{job.name} unexpected progress record {line[:120]}",
        )
        row = dict(
            zip(JOIN_KEYS, map(int, bits[1 : 2 * len(JOIN_KEYS) : 2]), strict=True)
        )
        t = row["order"]
        require(
            all(count(x) for x in row.values())
            and len(rows) < len(ranks)
            and t == ranks[len(rows)]
            and t not in rows,
            f"{job.name} out-of-order rank {t}",
        )
        d = domains[t]
        require(
            row["decks"] == PER_ORDER
            and row["owned"] == d["owned"]
            and row["delegated_or_bond"] == d["delegated_or_bond"],
            f"{job.name} rank {t} differs from independent ownership count",
        )
        hard = priority[t] >= 4140
        if hard:
            require(
                bool(row["group_count"]) == bool(row["owned"])
                and row["head_visits"] >= row["group_count"],
                f"Invalid grouped pass at {t}",
            )
        else:
            require(
                row["group_count"]
                == row["head_visits"]
                == row["mirror"]
                == row["delegated_or_bond"]
                == 0,
                f"Unexpected symmetry reduction on a full scan at {t}",
            )
        # The live logger combines the final two nested cuts. Their sum is
        # determined by the leaf balance, their individual counts are unavailable.
        row["bulk"] = row["owned"] - row["leaf"]
        row["nested"] = row["leaf"] - sum(
            row[k] for k in ("mirror", "dual", "extra", "late", "late_dual", "pending")
        )
        require(
            row["bulk"] >= 0 and row["nested"] >= 0 and row["mirror"] <= d["lex"],
            f"{job.name} negative category or invalid lex count at {t}",
        )
        rows[t] = row
    require(
        partial or len(rows) == len(ranks),
        f"{job.name}: {len(rows)}/{len(ranks)} primary ranks",
    )
    return ranks, rows


def suffix_order(p: tuple[int, ...] | list[int]) -> int:
    r = 0
    for i in range(11, 18):
        r = (i - 10) * r + sum(x > p[i] for x in p[11:i])
    return r


def residual(
    p: tuple[int, ...], ranks: dict[int, int], priority: dict[int, int]
) -> None:
    require(
        sorted(p) == list(range(1, 20))
        and p[-1] == 1
        and all(x != y + 1 for x, y in itertools.pairwise(p)),
        "Invalid final residual deck",
    )
    t = suffix_order(p)
    require(ranks.get(t, 0) > 0, "Final residual has incorrect source rank")
    if priority[t] >= 4140:
        d = [0] * 19
        for i, x in enumerate(p):
            d[19 - x] = 19 - i
        v = suffix_order(d)
        require(
            priority[t] < priority[v] or (v == t and p <= tuple(d)),
            "Final residual violates ownership",
        )


def close_batch(
    directory: Path,
    ranks: dict[int, dict[str, int]],
    priority: dict[int, int],
    totals: Counter[str],
    needed: set[bytes],
) -> list[int]:
    entry = json.loads((directory / "closure.json").read_text(encoding="utf-8"))
    requests = entry["ranks"]
    require(
        bool(requests)
        and all(
            isinstance(x, list) and len(x) == 2 and all(count(i) for i in x)
            for x in requests
        ),
        f"{directory}: invalid rank list",
    )
    seen = dict(requests)
    require(
        len(seen) == len(requests)
        and all(t in ranks and ranks[t]["pending"] == c for t, c in requests),
        f"{directory}: incorrect or repeated primary count",
    )
    previous = sum(seen.values())
    require(
        count(entry.get("checked_rows")) and entry["checked_rows"] == previous,
        f"{directory}: missing or incorrect independent raw-stream report",
    )
    totals["raw_closed"] += previous
    require(len(entry["steps"]) == len(RECUTS), f"{directory}: missing a recut stage")
    for record, (cut, dual) in zip(entry["steps"], RECUTS, strict=True):
        k, flipped, accepted, left = record
        require(
            k == cut
            and flipped is dual
            and count(accepted)
            and count(left)
            and left + accepted == previous,
            f"{directory}: invalid cut {cut} {dual}",
        )
        totals[f"cut{cut}_{'dual' if dual else 'forward'}"] += accepted
        previous = left
    accepted, left = entry["flex"]
    require(
        count(accepted) and count(left) and accepted + left == previous,
        f"{directory}: invalid flexible-cut accounting",
    )
    totals["flex"] += accepted
    individuals: set[tuple[int, ...]] = set()
    with (directory / "individual.txt").open(encoding="utf-8") as src:
        for line in src:
            tag, status, *cards = line.split()
            p = tuple(map(int, cards))
            require(
                (tag, status) == ("Hard", "1") and p not in individuals,
                "Bad individual record",
            )
            residual(p, seen, priority)
            individuals.add(p)
            needed.add(("Hard 1 " + " ".join(map(str, p))).encode())
    require(len(individuals) == left, f"{directory}: incorrect individual count")
    with gzip.open(directory / "words.txt.gz", "rt", encoding="utf-8") as src:
        for line in src:
            *cards, word = line.split()
            p = tuple(map(int, cards))
            require(
                p in individuals and len(word) == 76 and replay(p, word),
                f"{directory}: invalid or unexpected physical schedule",
            )
            individuals.remove(p)
    require(not individuals, f"{directory}: a physical sorting word is missing")
    totals["words"] += left
    return [t for t, _ in requests]


def raw_receipt(
    job: Job,
    rows: dict[int, dict[str, int]],
    required: set[bytes],
    checker: Path,
    priority: Path,
    tmp: Path,
) -> dict[str, Any]:
    # The C++ validator checks each physical deck's permutation, descending
    # bonds, exact source rank, uniqueness within that rank and ownership.
    expect = tmp / "counts.txt"
    expect.write_text(
        "".join(f"{t} {r['pending']}\n" for t, r in rows.items()), encoding="utf-8"
    )
    total = sum(r["pending"] for r in rows.values())
    name = job.raw
    assert name is not None
    missing = required.copy()
    digest = hashlib.sha256()
    size = 0
    with subprocess.Popen(
        [checker, "/dev/stdin", expect, priority, "900"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
    ) as proc:
        assert proc.stdin is not None
        assert proc.stdout is not None
        opener = gzip.open if name.suffix == ".gz" else Path.open
        with opener(name, "rb") as src:
            carry = b""
            for block in iter(lambda: src.read(2**21), b""):
                proc.stdin.write(block)
                size += len(block)
                digest.update(block)
                if missing:
                    lines = (carry + block).split(b"\n")
                    carry = lines.pop()
                    missing.difference_update(lines)
            require(
                not missing,
                f"{job.name}: final verified inputs absent from raw stream",
            )
        proc.stdin.close()
        message = proc.stdout.read().decode().strip()
        require(
            proc.wait() == 0
            and message == f"Checked {total} distinct, correctly assigned candidates",
            f"{job.name}: failed final physical raw-stream check",
        )
    require(size == total * WIDTH, f"{job.name}: wrong raw byte count")
    return {"rows": total, "bytes": size, "sha256": digest.hexdigest()}


def compress(src: Path, dest: Path) -> None:
    with (
        src.open("rb") as inp,
        dest.open("wb") as raw,
        gzip.GzipFile(
            filename="", mode="wb", fileobj=raw, compresslevel=1, mtime=0
        ) as out,
    ):
        shutil.copyfileobj(inp, out, length=2**21)


def write_archive(
    dst: Path,
    jobs: list[Job],
    receipts: dict[str, dict[str, Any]],
    chunks: list[Path],
    priority: Path,
    domains: Path,
    include_raw: bool,
) -> None:
    require(not dst.exists(), f"Archive destination already exists: {dst}")
    dst.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=dst.parent) as stage_str:
        stage = Path(stage_str) / "archive"
        (stage / "workers").mkdir(parents=True)
        (stage / "closures").mkdir()
        for source, name in ((priority, "priority.txt"), (domains, "domains.csv")):
            with (
                open_text(source) as a,
                (stage / name).open("w", encoding="utf-8") as b,
            ):
                shutil.copyfileobj(a, b)
        names: list[str] = []
        for job in jobs:
            d = stage / "workers" / job.name
            d.mkdir()
            shutil.copyfile(job.ranks, d / "ranks.txt")
            compress(job.log, d / "progress.txt.gz")
            (d / "raw.json").write_text(
                json.dumps(receipts[job.name], indent=2) + "\n", encoding="utf-8"
            )
            if include_raw:
                assert job.raw is not None
                compress(job.raw, d / "raw.txt.gz")
            names.append(job.name)
        for chunk in chunks:
            target = stage / "closures" / chunk.name
            target.mkdir()
            for file in ("closure.json", "individual.txt", "words.txt.gz"):
                shutil.copyfile(chunk / file, target / file)
        (stage / "run.json").write_text(
            json.dumps({"version": 1, "hard": 900, "workers": names}, indent=2) + "\n",
            encoding="utf-8",
        )
        entries = {
            str(p.relative_to(stage)): hashfile(p)
            for p in sorted(stage.rglob("*"))
            if p.is_file()
        }
        (stage / "sha256.json").write_text(
            json.dumps(entries, indent=2) + "\n", encoding="utf-8"
        )
        # Validate what was copied, then publish the complete directory at once.
        audit_archive(stage, None, False)
        stage.rename(dst)


def audit(
    jobs: list[Job],
    chunks: list[Path],
    priority_path: Path,
    domains_path: Path,
    partial: bool,
    check_raw: Path | None = None,
    archive: Path | None = None,
    include_raw: bool = False,
) -> dict[str, Any]:
    priority, domains = policy_and_domains(priority_path, domains_path)
    require(
        len({job.name for job in jobs}) == len(jobs) and bool(jobs),
        "Missing or repeated worker name",
    )
    rank_owner: dict[int, str] = {}
    rows_by_job: dict[str, dict[int, dict[str, int]]] = {}
    needs: dict[str, set[bytes]] = {job.name: set() for job in jobs}
    processed: set[int] = set()
    totals: Counter[str] = Counter()
    for job in jobs:
        order, rows = read_progress(job, partial, priority, domains)
        require(
            len(order) == len(set(order)) and all(t not in rank_owner for t in order),
            f"Overlapping scheduled ranks at {job.name}",
        )
        rank_owner.update(dict.fromkeys(order, job.name))
        processed.update(rows)
        rows_by_job[job.name] = rows
        total = sum(r["pending"] for r in rows.values())
        if job.receipt is not None:
            receipt = job.receipt
            require(
                receipt["rows"] == total
                and receipt["bytes"] == total * WIDTH
                and bool(re.fullmatch(r"[0-9a-f]{64}", receipt["sha256"])),
                f"{job.name}: invalid raw-stream receipt",
            )
        elif job.raw is not None:
            size = job.raw.stat().st_size
            require(
                size >= total * WIDTH if partial else size == total * WIDTH,
                f"{job.name} raw length mismatch",
            )
        for row in rows.values():
            totals.update(
                {
                    k: row[k]
                    for k in (
                        "decks",
                        "owned",
                        "delegated_or_bond",
                        "bulk",
                        "leaf",
                        "mirror",
                        "dual",
                        "extra",
                        "late",
                        "late_dual",
                        "nested",
                        "pending",
                    )
                }
            )
    require(
        set(rank_owner) == set(range(5040)),
        "Scheduled ranks do not partition all 5,040 orders",
    )
    closed: set[int] = set()
    positions = {
        name: {t: i for i, t in enumerate(rows)} for name, rows in rows_by_job.items()
    }
    for directory in chunks:
        name, part = directory.name.split("--")
        require(name in rows_by_job, f"Unknown closure worker {directory}")
        batch = close_batch(directory, rows_by_job[name], priority, totals, needs[name])
        pos = [positions[name][t] for t in batch]
        require(
            part == f"{batch[0]}-{batch[-1]}"
            and pos == list(range(pos[0], pos[0] + len(pos)))
            and closed.isdisjoint(batch),
            f"{directory}: overlapping or noncontiguous closure",
        )
        closed.update(batch)
    require(
        partial or closed == processed == set(range(5040)),
        f"Incomplete length-19 run: {len(processed)} primary and {len(closed)} closed",
    )
    require(
        totals["decks"] == len(processed) * PER_ORDER
        and totals["owned"] + totals["delegated_or_bond"] == totals["decks"]
        and totals["raw_closed"]
        == sum(
            totals[k]
            for k in (
                "words",
                "flex",
                *(f"cut{k}_{'dual' if d else 'forward'}" for k, d in RECUTS),
            )
        ),
        "Totals do not conserve primary or closing domains",
    )
    if not partial:
        require(
            totals["decks"] == math.factorial(18)
            and totals["raw_closed"] == totals["pending"],
            "Final domain total differs from 18! or pending totals differ",
        )
    if check_raw is not None or archive:
        require(not partial, "Full raw-stream verification requires a complete run")
        require(
            all(job.raw for job in jobs),
            "Original raw streams not present; use the live manifest or a full archive",
        )
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            flat_priority = tmp / "priority.txt"
            with (
                open_text(priority_path) as src,
                flat_priority.open("w", encoding="utf-8") as dst,
            ):
                shutil.copyfileobj(src, dst)
            if check_raw is None:
                check_raw = tmp / "check-stream"
                source = Path(__file__).with_name("check_ordered_stream.cpp")
                subprocess.run(
                    ["c++", "-std=c++23", "-O2", source, "-o", check_raw], check=True
                )
            receipts: dict[str, dict[str, Any]] = {}
            for job in jobs:
                receipt = raw_receipt(
                    job,
                    rows_by_job[job.name],
                    needs[job.name],
                    check_raw,
                    flat_priority,
                    tmp,
                )
                require(
                    job.receipt is None or job.receipt == receipt,
                    f"{job.name}: raw digest differs",
                )
                receipts[job.name] = receipt
            if archive is not None:
                write_archive(
                    archive,
                    jobs,
                    receipts,
                    chunks,
                    priority_path,
                    domains_path,
                    include_raw,
                )
    return {
        "status": "partial" if partial else "complete",
        "primary_ranks": len(processed),
        "closed_ranks": len(closed),
        **dict(sorted(totals.items())),
    }


def audit_archive(
    path: Path, checker: Path | None, verify_files: bool = True
) -> dict[str, Any]:
    meta = json.loads((path / "run.json").read_text(encoding="utf-8"))
    require(meta["version"] == 1 and meta["hard"] == 900, "Unknown archived run format")
    if verify_files:
        digests = json.loads((path / "sha256.json").read_text(encoding="utf-8"))
        names = {
            str(p.relative_to(path))
            for p in path.rglob("*")
            if p.is_file() and p != path / "sha256.json"
        }
        require(
            names == set(digests),
            "Archive file list differs from preservation manifest",
        )
        for name, digest in digests.items():
            require(hashfile(path / name) == digest, f"Corrupt preserved file {name}")
    jobs: list[Job] = []
    for name in meta["workers"]:
        d = path / "workers" / name
        raw = d / "raw.txt.gz"
        jobs.append(
            Job(
                name,
                d / "ranks.txt",
                d / "progress.txt.gz",
                raw if raw.exists() else None,
                json.loads((d / "raw.json").read_text(encoding="utf-8")),
            )
        )
    return audit(
        jobs,
        sorted(p.parent for p in (path / "closures").glob("*/closure.json")),
        path / "priority.txt",
        path / "domains.csv",
        False,
        check_raw=checker,
    )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("archive", nargs="?", type=Path, default=None)
    ap.add_argument("--live", nargs=2, type=Path, metavar=("MANIFEST", "CLOSURES"))
    ap.add_argument("--priority", type=Path, default=None)
    ap.add_argument("--domains", type=Path, default=None)
    ap.add_argument("--partial", action="store_true")
    ap.add_argument(
        "--save",
        type=Path,
        help="Save a complete, raw-audited live run to a new directory",
    )
    ap.add_argument(
        "--include-raw",
        action="store_true",
        help="Also preserve complete compressed raw worker streams",
    )
    ap.add_argument(
        "--stream-checker",
        type=Path,
        help="Recheck full raw streams with this compiled check_ordered_stream",
    )
    ap.add_argument(
        "--recompute-ownership",
        action="store_true",
        help="Compile and rerun the independent per-rank ownership enumeration",
    )
    args = ap.parse_args()
    require(
        not args.include_raw or args.save is not None,
        "--include-raw requires --save",
    )
    require(
        not args.partial
        or (bool(args.live) and not args.save and not args.stream_checker),
        "--partial requires live read-only auditing",
    )

    def _run_with_results(results_dir: Path) -> dict[str, Any]:
        archive_path = args.archive or (results_dir / "n19-ordered")
        priority_path = args.priority or (results_dir / "n19-fresh-priority.txt.gz")
        domains_path = args.domains or (results_dir / "n19-ordered-domains.csv.gz")
        if args.live:
            if args.save or args.recompute_ownership:
                verify_domains(priority_path, domains_path)
            manifest, closed = args.live
            require(
                closed.is_dir() and not list(closed.glob("*.result")),
                "Missing closures or reported unsortable candidate",
            )
            # Snapshot complete closure reports before reading the advancing join logs.
            chunks = sorted(p.parent for p in closed.glob("*/closure.json"))
            return audit(
                live_jobs(manifest),
                chunks,
                priority_path,
                domains_path,
                args.partial,
                args.stream_checker,
                args.save,
                args.include_raw,
            )
        require(args.save is None, "--save requires --live")
        if args.recompute_ownership:
            verify_domains(archive_path / "priority.txt", archive_path / "domains.csv")
        return audit_archive(archive_path, args.stream_checker)

    if (
        args.archive is not None
        or RESULTS.is_dir()
        or (args.live and args.priority is not None and args.domains is not None)
    ):
        stats = _run_with_results(RESULTS)
    else:
        with tempfile.TemporaryDirectory(prefix="three-stacks-results-") as tmp:
            with tarfile.open(RESULTS_ARCHIVE, "r:gz") as tf:
                tf.extractall(tmp, filter="data")
            stats = _run_with_results(Path(tmp) / "coverage" / "results")
    print(json.dumps(stats, indent=2))


if __name__ == "__main__":
    main()
