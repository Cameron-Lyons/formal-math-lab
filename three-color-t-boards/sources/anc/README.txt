Explicit Three- and Four-Color Prismatic T-Tetrominoes
Qiyuan Ma, Shanghai Jiao Tong University
Correspondence: mqyqwerty@sjtu.edu.cn

All Python programs require Python 3.10 or later and use only its standard
library. No SAT solver, LaTeX installation, network connection, or original
research workspace is needed for certificate verification.

Keep the programs and all data files in this directory together. Run:

    python verify.py
    python count_extensions.py
    python search_model.py

verify.py checks the main T and L certificates by planar translation,
checks the inverse pattern CSV tables, checks the five disjoint ternary
orbits (60 colorings), checks the 24 four-color label permutations, and
independently obtains the binary total 168 by whole-row dynamic programming.
If main.tex is one directory above the program, its color tables are also
compared with certificates.json. Three deliberate invalid-data controls
must be rejected. Checks remain active under python -O. Typical run time
on the preparation machine was below one second.

count_extensions.py independently performs cell-by-cell enumeration. It
returns 168 in the binary case and two extensions for each of prefixes C
and P (rows 0 through 6 fixed). It checks the returned arrays geometrically.
The preparation run took about ten seconds; times vary by machine and load.
Neither program claims to count all ternary colorings.

search_model.py checks the fixed binary high-bit mask and the displayed
four-color certificate against every clause of a solver-independent CNF.
To generate files for another SAT implementation:

    python search_model.py --dimacs model.cnf --witness model.sol

The files must not already exist. The encoding has 2747 variables, 11754
clauses, and 1920 within-group window comparisons. It is a restricted
construction model; an unsatisfiable instance would not establish
unrestricted nonexistence. The program itself never invokes a SAT solver.

search_n3.py is an optional discovery search, rather than a validator:

    python search_n3.py --colors 3 --seconds 600
    python search_n3.py --colors 2 --all --seconds 30

The ternary discovery run can time out. The binary command returns 84
canonical labelings, corresponding to 168 labeled colorings. The supplied
certificates can be checked without repeating a discovery run.

FILES
    certificates.json   main colorings, five ternary seeds, two prefixes
    n3_patterns.csv     all 81 patterns and their unique window locations
    n4_patterns.csv     all 256 patterns and their unique window locations
    verify.py           geometric and independent row-DP verification
    count_extensions.py exact binary and prescribed-prefix enumeration
    search_model.py     fixed-mask Boolean model and witness check
    search_n3.py        optional row-first discovery search
    *_stdout.txt        actual outputs from the preparation run
    SHA256SUMS.txt       hashes of the submitted source and ancillary files,
                        excluding the hash list itself

CONVENTIONS
    A row is a string of color labels, read from left to right.
    Row r has length 2r+1 and its cell j has T coordinate (j-r,-r).
    The apex is fixed at (0,0); colors are labeled; only translations of
    the chosen small shape are counted. Horizontal reflections of the
    entire colored board are counted as different unless their arrays
    coincide. Window order is (top,left,middle,right).

The counts 60 and 24 are lower bounds. The five-color case, the general
existence problem, and the exact ternary total are not settled here.

The programs and manuscript were developed with substantial assistance
from OpenAI Codex, as disclosed in the manuscript. The author separately
verified the two main certificates using an independently written
coordinate-based checker. The original author's checker is not required
by, and is not included in, this ancillary package.
