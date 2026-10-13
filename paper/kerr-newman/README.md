# A Machine-Checked Proof that the Kerr–Newman Spacetime Solves the Einstein–Maxwell Equations

LaTeX source of the paper describing the Lean 4 formalization in `../../prove2me/nohair/`.

## Building

```
make            # latexmk -pdf → main.pdf
make arxiv      # kerr-newman-arxiv.tar.gz with main.tex, stats.tex, refs.bib, main.bbl
```

Requires a TeX Live with `latexmk`, `natbib`, `listings`, `tikz`, `booktabs`, `cleveref`.
The build uses pdflatex; Unicode in the Lean listings is handled by `literate` replacements.

## Files

- `main.tex` – the paper.
- `stats.tex` – measured numbers used in the text (file sizes, counts).
- `refs.bib` – bibliography. Every entry was checked against a publisher page, an index record
  (ADS, INSPIRE, OSTI, arXiv) or the Mathlib source; fields that could not be confirmed were left out.
- `closure/` – single-environment axiom check (see below).
- `supplementary/` – the measurement and audit scripts and their reports:
  - `stats.md` – statistics and timings of the formalization (Table 1 of the paper).
  - `conventions_audit.md` – independent SymPy/mpmath audit of the platform definitions and of every
    formula displayed in the paper.
  - `audit_*.py`, `static_stats.py`, `cert_stats.py` – the scripts behind those two reports.

## The single-environment axiom check (`closure/`)

On Prove2Me each theorem is checked against `sorry` stubs of the theorems it imports.
`closure/mk_closure.py` rewrites the accepted solution files so that each proves its theorem under the
platform name, with the stub imports replaced by the corresponding proof modules, and
`closure/build.sh` compiles the chain in dependency order and prints the axioms of the milestone and of
its three conjuncts. With a workspace holding the platform definition blocks (`Definitions/`) and
Mathlib:

```
python3 closure/mk_closure.py
python3 closure/cmp_stmt.py /path/to/workspace    # every statement equals its platform stub
WORKSPACE=/path/to/workspace closure/build.sh
```

Output of the last step (Lean 4.33.1, Mathlib `0df444a3`):

```
'NoHair.kerrNewman_einsteinMaxwell' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoHair.kerrNewman_einstein' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoHair.kerrNewman_maxwell' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoHair.kerrNewman_field_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
```
