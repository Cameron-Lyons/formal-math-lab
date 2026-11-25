"""Optional deterministic rediscovery; requires g++, not required by Lean."""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=int, default=120)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    seeds = json.loads((root/'sources/anc/certificates.json').read_text())['ternary_seeds']
    known = set()
    for rows in seeds:
        for perm in itertools.permutations('012'):
            for reflected in [False, True]:
                known.add(''.join(perm[int(c)] for row in rows
                                  for c in (row[::-1] if reflected else row)))
    with tempfile.TemporaryDirectory(prefix='tboard-search-') as tmp:
        directory = Path(tmp)
        binary = directory/'search'
        subprocess.run(['g++', '-O3', '-std=c++23', '-Wall', '-Wextra', '-Wpedantic', '-Werror', str(root/'search_prefix.cpp'),
                        '-o', str(binary)], check=True)
        (directory/'prefix_known.txt').write_text('\n'.join(sorted(known))+'\n')
        completed = subprocess.run([str(binary), ''.join(seeds[0]), '6', str(args.seconds)],
                                   cwd=directory)
        if completed.returncode:
            raise SystemExit('Search ended without a new board; a timeout proves nothing.')
        result = json.loads((directory/'prefix_result.json').read_text())
        expected = json.loads((root/'prefix_result.json').read_text())
        if result['rows'] != expected['rows']:
            raise ValueError('Rediscovery differs from the recorded witness')
        print(json.dumps(result, indent=2))
        print('Rediscovered the recorded new board.')


if __name__ == '__main__':
    main()
