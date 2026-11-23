Explicit Three- and Four-Color Prismatic T-Tetrominoes
Qiyuan Ma (马启渊), Shanghai Jiao Tong University
Correspondence: mqyqwerty@sjtu.edu.cn
Manuscript date: 24 October 2026. Release preparation: 2026-10-25.

CONTENTS
t_tetrominoes_preprint_v1.pdf: the complete seven-page manuscript, including figures,
color tables, references, and the disclosure of substantial OpenAI Codex use.
t_tetrominoes_source_code_data_v1.zip: LaTeX source, Python programs, JSON certificates,
inverse pattern CSV tables, recorded outputs, and SHA-256 checksums.

REPRODUCE
Extract the ZIP to an empty folder. From the extracted folder run:
    python anc/verify.py
    python anc/count_extensions.py
    python anc/search_model.py
Python 3.10+ and its standard library are sufficient. Certificate checking
does not require a SAT solver, LaTeX, or network access. See anc/README.txt
for program details. main.tex can be compiled with XeLaTeX or Tectonic.
SHA256SUMS.txt covers all other files within the archive.

SCOPE
The three-color certificate has 100 cells and 81 T-windows; the four-color
certificate has 289 cells and 256 T-windows. Every ordered color pattern
occurs exactly once. The row-shift yields corresponding L certificates.
The supplied ternary family has 60 distinct labeled colorings; 60 is a
lower bound, not the full ternary count. The binary count 168 is reproduced
by independent row-wise and cell-wise enumerations. No five-color or
arbitrary-color construction is claimed. Only material supporting the
three- and four-color manuscript is included in this release.

LICENSING AND ATTRIBUTION
Copyright (c) 2026 Qiyuan Ma (马启渊).

The manuscript (PDF and main.tex), figures, color tables, JSON/CSV
certificate data, documentation, recorded computational outputs and
checksums are licensed under the Creative Commons Attribution 4.0
International license (SPDX identifier: CC-BY-4.0).
Full terms: LICENSES/CC-BY-4.0.txt
https://creativecommons.org/licenses/by/4.0/

The Python source files below are licensed under the MIT License:
    anc/verify.py
    anc/count_extensions.py
    anc/search_model.py
    anc/search_n3.py
Full terms and copyright notice: LICENSES/MIT.txt

The two licenses apply to the stated file categories, respectively;
they are not alternatives offered for every file. License texts are
reproduced as standard terms and retain their own notices.
The separately uploaded t_tetrominoes_preprint_v1.pdf and README.txt
are covered by CC-BY-4.0. Attribution: Qiyuan Ma, "Explicit Three- and
Four-Color Prismatic T-Tetrominoes", Shanghai Jiao Tong University, 2026.
Use the Zenodo record DOI in citations once published.
