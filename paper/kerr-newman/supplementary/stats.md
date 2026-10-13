# Formalization statistics: Kerr–Newman solves Einstein–Maxwell (Lean 4 + Mathlib)

Generated from the repository files on 2026-10-13. Machine: x86_64 Intel Xeon @ 2.10GHz, 4 vCPUs, 15.7 GiB RAM, Linux 6.18.44-fc-v114. All numbers below are exact counts unless marked otherwise.

## Toolchain

- Lean: `Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)`
- Mathlib commit: `0df444a360eaa60ab8c11dca51a86af692955474` (commit date 2026-08-21T12:04:53+00:00; toolchain `leanprover/lean4:v4.33.1`)
- Other packages (lake-manifest.json): plausible `b7eb3304aeae`, LeanSearchClient `5f4d51b81cbd`, importGraph `16f02aa76428`, proofwidgets `4be2e3d5087e`, aesop `3448c0bcc5ce`, Qq `92c15be17b7c`, batteries `4488d40d070b`, Cli `6130a47896ce`
- Python 3.13.16, SymPy 1.14.0 (generators).

## 1. Static statistics per file

Counts are on comment-stripped source; `theorems` = top-level `theorem`/`lemma`, `defs` = `def`/`abbrev` (incl. `noncomputable def`). `ring` counts the `ring` tactic only (not `ring_nf`).

| File | Lines | Bytes | Thms | Defs | linear_combination | field_simp | ring | fin_cases | simp only | positivity |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Def_NoHair_KerrNewmanEinstein_Base` | 798 | 245,123 | 51 | 120 | 4 | 6 | 4 | 6 | 20 | 11 |
| `Def_NoHair_KerrNewmanEinstein_Atoms` | 256 | 20,126 | 12 | 0 | 28 | 29 | 30 | 9 | 9 | 24 |
| `Def_NoHair_KerrNewmanEinstein_Christoffel` | 310 | 96,312 | 46 | 0 | 40 | 0 | 1 | 11 | 41 | 0 |
| `Def_NoHair_KerrNewmanEinstein_Div1` | 142 | 35,513 | 8 | 0 | 4 | 0 | 0 | 0 | 4 | 0 |
| `Def_NoHair_KerrNewmanEinstein_Div2` | 150 | 82,153 | 6 | 0 | 6 | 0 | 0 | 0 | 6 | 0 |
| `Def_NoHair_KerrNewmanEinstein_Div3` | 238 | 85,199 | 10 | 0 | 10 | 0 | 0 | 0 | 10 | 0 |
| `Def_NoHair_KerrNewmanEinstein_Div4` | 238 | 63,059 | 10 | 0 | 10 | 0 | 0 | 0 | 10 | 0 |
| `Def_NoHair_KerrNewmanEinstein_Ricci1` | 30 | 26,799 | 2 | 0 | 2 | 0 | 0 | 0 | 4 | 0 |
| `Def_NoHair_KerrNewmanEinstein_Ricci2` | 30 | 31,115 | 2 | 0 | 2 | 0 | 0 | 0 | 4 | 0 |
| `Def_NoHair_KerrNewmanEinstein_Ricci3` | 24 | 33,045 | 1 | 0 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Def_NoHair_KerrNewmanEinstein_Ricci4` | 24 | 33,073 | 1 | 0 | 1 | 0 | 0 | 0 | 2 | 0 |
| `Def_NoHair_KerrNewmanEinstein_Ricci5` | 30 | 57,911 | 2 | 0 | 2 | 0 | 0 | 0 | 4 | 0 |
| `Def_NoHair_KerrNewmanEinstein_Ricci6` | 30 | 49,991 | 2 | 0 | 2 | 0 | 0 | 0 | 4 | 0 |
| `Def_NoHair_KerrNewmanEinstein_MaxwellF` | 223 | 19,196 | 35 | 0 | 33 | 0 | 0 | 4 | 33 | 0 |
| `Def_NoHair_KerrNewmanEinstein_MaxwellT` | 118 | 69,636 | 17 | 0 | 16 | 0 | 0 | 2 | 16 | 0 |
| `Sol_NoHair_KNE_thm_christoffel` | 12 | 473 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `Sol_NoHair_KNE_thm_div_one` | 45 | 2,279 | 1 | 0 | 0 | 0 | 0 | 4 | 3 | 0 |
| `Sol_NoHair_KNE_thm_div_two` | 37 | 1,808 | 1 | 0 | 0 | 0 | 0 | 3 | 2 | 0 |
| `Sol_NoHair_KNE_thm_div_three` | 37 | 1,808 | 1 | 0 | 0 | 0 | 0 | 3 | 2 | 0 |
| `Sol_NoHair_KNE_thm_ricci_a` | 16 | 844 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `Sol_NoHair_KNE_thm_ricci_b` | 14 | 618 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `Sol_NoHair_KNE_thm_ricci_c` | 16 | 844 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `Sol_NoHair_KNE_thm_maxwell` | 16 | 988 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `Sol_NoHair_kerrNewman_einstein` | 251 | 17,437 | 28 | 0 | 5 | 1 | 4 | 15 | 15 | 2 |
| `Sol_NoHair_kerrNewman_field_closed` | 88 | 4,115 | 7 | 0 | 0 | 0 | 1 | 1 | 3 | 3 |
| `Sol_NoHair_kerrNewman_flat_maxwell` | 720 | 35,138 | 79 | 17 | 5 | 7 | 20 | 1 | 42 | 32 |
| `Sol_NoHair_kerrNewman_maxwell` | 460 | 23,170 | 48 | 5 | 11 | 7 | 7 | 7 | 23 | 12 |
| `Sol_NoHair_kerrNewman_einsteinMaxwell` | 15 | 717 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

### Totals

| Group | Files | Lines | Bytes | Thms | Defs | linear_combination | field_simp | ring | fin_cases |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Einstein: 15 Def blocks | 15 | 2,641 | 948,251 | 205 | 120 | 161 | 35 | 35 | 32 |
| Einstein: 8 intermediate Sol_NoHair_KNE_thm_* | 8 | 193 | 9,662 | 8 | 0 | 0 | 0 | 0 | 10 |
| Einstein: final Sol_NoHair_kerrNewman_einstein | 1 | 251 | 17,437 | 28 | 0 | 5 | 1 | 4 | 15 |
| **(a) Einstein part total** | 24 | 3,085 | 975,350 | 241 | 120 | 166 | 36 | 39 | 57 |
| **(b) Maxwell parts** (field_closed, flat_maxwell, maxwell, einsteinMaxwell glue) | 4 | 1,283 | 63,140 | 135 | 22 | 16 | 14 | 28 | 9 |
| **All proof files (a)+(b)** | 28 | 4,368 | 1,038,490 | 376 | 142 | 182 | 50 | 67 | 66 |
| Thm_ statement stubs (`sorry`), for reference | 13 | 200 | 7,499 | 13 | 0 | 0 | 0 | 0 | 0 |

- `sorry` occurrences in all proof files: 0. No `admit`, `native_decide`, `axiom` declarations, or `set_option maxHeartbeats` anywhere (default heartbeat limit 200000).
- Thm_ stub files in the repo: 13 (4 in `nohair/`, 9 in `nohair/einstein/`; `Thm_NoHair_kerrNewman_einstein.lean` appears in both, differing only in its docstring → 12 distinct statements). The milestone statement `Thm_NoHair_kerrNewman_einsteinMaxwell.lean` lives only in the workspace `Theorems/`.
- Trusted platform definitions: `Def_NoHair_coordinates.lean` 144 lines, `Def_NoHair_kerrNewman.lean` 43 lines, `Def_NoHair_spacetime.lean` 249 lines (436 lines, 22,769 bytes; the Einstein–Maxwell statement uses only the coordinate-level definitions in `Def_NoHair_coordinates.lean`).
- All 15 Def blocks, 8 Thm stubs, 8 intermediate solutions and the final solution in the repo are byte-identical to the copies in `/root/prove2me_workspace` (Definitions/, Theorems/, Solutions/), except the docstring difference noted above.

### What each Einstein definition block contains

| Block | Thms | Certificates | Content |
|---|---:|---:|---|
| Base | 51 | 0 | Kerr–Schild radius facts, line derivatives of r and k_i, the HasCP calculus (closed under const/+/−/·/÷/pow, time shift), relations k1²+k2²+k3²=1 and W(r²+a²k3²)=1, and all 120 closed-form definitions (G***, DD***, Ric**, Fc/Fu**, FFA, atom partials, tables, algebraic builders chrS/RicS/FS/TS). |
| Atoms | 12 | 28 | HasCP for the atoms r, k1, k2, k3, W, the profile f and potential factor H (28 rational-cofactor certificates, normalised by field_simp; ring); metric/inverse-metric/Christoffel bridge lemmas (cp_metric, invMetric_eq, chr_eq). |
| Christoffel | 46 | 40 | 40 polynomial identities chrS = Gam (one per independent Γ^i_{jk}); chr_closed: Γ of the platform metric equals Gam on r>0; symmetry facts. |
| Div1 | 8 | 4 | Differentiability of Γ^0_{0σ} (time direction, 4) and ∂_1 Γ^1_{0σ} = DD10σ (4). |
| Div2 | 6 | 6 | ∂_1 Γ^1_{νσ} = DD1νσ for νσ ∈ {11,12,13,22,23,33} (6). |
| Div3 | 10 | 10 | ∂_2 Γ^2_{νσ} = DD2νσ (10). |
| Div4 | 10 | 10 | ∂_3 Γ^3_{νσ} = DD3νσ (10). |
| Ricci1 | 2 | 2 | RicS = RicA for components (0,0), (0,1). |
| Ricci2 | 2 | 2 | RicS = RicA for components (0,2), (0,3). |
| Ricci3 | 1 | 1 | RicS = RicA for component (1,1). |
| Ricci4 | 1 | 1 | RicS = RicA for component (1,2). |
| Ricci5 | 2 | 2 | RicS = RicA for components (1,3), (2,2). |
| Ricci6 | 2 | 2 | RicS = RicA for components (2,3), (3,3). |
| MaxwellF | 35 | 33 | F = dA in closed form (FS = FA, 16), raised F^{μν} (FupA, 16), invariant F_{αβ}F^{αβ} (FFA, 1). |
| MaxwellT | 17 | 16 | Maxwell source tensor TS = RicA (16 components). |

Intermediate platform theorems (each a short `Sol_NoHair_KNE_thm_*` file that only cites block lemmas): `thm_christoffel` (← Christoffel), `thm_div_one` (← Div1, Div2), `thm_div_two` (← Div3), `thm_div_three` (← Div4), `thm_ricci_a` (← Ricci1, Ricci2), `thm_ricci_b` (← Ricci3, Ricci4), `thm_ricci_c` (← Ricci5, Ricci6), `thm_maxwell` (← MaxwellF, MaxwellT). The final `Sol_NoHair_kerrNewman_einstein` (28 theorems) imports Base, Atoms and the 8 theorem statements: trace of Γ vanishes (`trGam_0..3`, 5 certificates incl. `scal_zero`), its derivative vanishes, Ricci formula at y, R = 0, G = Ric, closed form of `maxwellSource`, and `solution`.

### Maxwell parts

| File | Thms | Defs | Content |
|---|---:|---:|---|
| `Sol_NoHair_kerrNewman_field_closed` | 7 | 0 | dF = 0: F = dA with A of class C² on r>0, so the cyclic sum of ∂_μF_{νρ} vanishes by symmetry of second derivatives. |
| `Sol_NoHair_kerrNewman_flat_maxwell` | 79 | 17 | Flat-space Maxwell ∂_μ(η η F) = 0 via Appell-type potentials: harmonicity ΔH = 0 and curl A = ∇ψ for the spatial part; line-derivative calculus, translation invariance in t. |
| `Sol_NoHair_kerrNewman_maxwell` | 48 | 5 | Curved Maxwell ∂_μ(√|det g| F^{μν}) = 0 reduced to the flat one: det g = −1, g⁻¹ = η − f k♯k♯ᵀ, alignment F k♯ = λ k (so F^{μν} = η η F); uses the flat_maxwell statement. |
| `Sol_NoHair_kerrNewman_einsteinMaxwell` | 1 | 0 | Milestone glue: EinsteinMaxwellAt = ⟨kerrNewman_einstein, kerrNewman_maxwell, kerrNewman_field_closed⟩. |

## 2. `linear_combination` certificates (Gröbner cofactors)

Certificates of the form `linear_combination (c1) * hrel + (c2) * hW` with hrel: k1²+k2²+k3² = 1, hW: W(r²+a²k3²) = 1, in the 15 Def blocks **plus** the final solution file (5 more). Variables: a, m, e, R, K1, K2, K3, W. Parsed exactly with SymPy `ring` over QQ (no sampling; 0.8 s).

- Number of certificates: **162** (157 in the Def blocks + 5 in the final solution). Other `linear_combination` calls (hand-written, Base): 4.
- Polynomial cofactors: 141 (of which 23 have both cofactors 0, i.e. the identity holds by `ring` after unfolding; 118 non-trivial). Rational cofactors (Atoms block, `(norm := (field_simp; ring))`): 21.
- Cofactor text: total 464,768 chars; mean 2869, median 1046, max 28,293 chars (Ricci4:ricS_12).
- Monomials (c1 + c2, polynomial certificates): total 6,478; mean 54.9 / median 31.5 over the non-trivial ones; **max 356** (Ricci4:ricS_12: c1 has 326 monomials of total degree 24, c2 has 30).
- Max total degree of a cofactor (all 8 variables): **27**; max degree in the atoms R,K1,K2,K3,W: 18; max exponent of W: 7; max |integer coefficient|: 72.

| Block | Certificates | zero | rational | cofactor chars | monomials (sum) | max monomials | max total degree |
|---|---:|---:|---:|---:|---:|---:|---:|
| Atoms | 28 | 7 | 21 | 6,814 | 0 | 0 | 0 |
| Christoffel | 40 | 0 | 0 | 68,598 | 1,098 | 62 | 16 |
| Div1 | 4 | 0 | 0 | 13,568 | 208 | 66 | 18 |
| Div2 | 6 | 0 | 0 | 49,051 | 718 | 199 | 19 |
| Div3 | 10 | 0 | 0 | 41,608 | 615 | 181 | 19 |
| Div4 | 10 | 0 | 0 | 25,249 | 395 | 119 | 19 |
| Ricci1 | 2 | 0 | 0 | 21,950 | 300 | 190 | 23 |
| Ricci2 | 2 | 0 | 0 | 25,794 | 340 | 173 | 23 |
| Ricci3 | 1 | 0 | 0 | 28,155 | 354 | 354 | 24 |
| Ricci4 | 1 | 0 | 0 | 28,293 | 356 | 356 | 24 |
| Ricci5 | 2 | 0 | 0 | 49,682 | 615 | 324 | 24 |
| Ricci6 | 2 | 0 | 0 | 42,596 | 535 | 284 | 24 |
| MaxwellF | 33 | 16 | 0 | 4,433 | 73 | 15 | 22 |
| MaxwellT | 16 | 0 | 0 | 55,550 | 808 | 117 | 27 |
| Sol_NoHair_kerrNewman_einstein | 5 | 0 | 0 | 3,427 | 63 | 23 | 12 |

## 3. Closed-form definitions (Base block)

Base contains **120 `def`s**: 40 Christoffel closed forms G000..G333 + table Gam; 30 divergence closed forms DD100..DD333 + table dDivT; 10 Ricci components Ric00..Ric33 + table RicA; 6 Fc + 6 Fu + tables FA, FupA + invariant FFA; 5 atom-partial tables dRt, dKt, dWt, dfA, dHA; Wf (=W); 4 line-derivative helpers drf, dk1f, dk2f, dk3f; 12 algebraic builders etaT, Kv, Ks, fA, dgA, ginvA, chrS, RicS, HA, FS, gA, TS (41+31+11+15+5+1+4+12 = 120).

| Family | Count | Monomials (sum) | Max monomials | Max total degree | Max W-exponent |
|---|---:|---:|---:|---:|---:|
| Γ^i_{jk} closed forms G000..G333 | 40 | 574 | 23 (G122) | 13 | 3 |
| divergence terms ∂_ρΓ^ρ_{νσ} DD100..DD333 | 30 | 1825 | 101 (DD122) | 21 | 5 |
| Ricci components Ric00..Ric33 | 10 | 55 | 13 (Ric11) | 9 | 3 |
| F_{μν} components Fc01..Fc23 | 6 | 24 | 4 (Fc01) | 12 | 3 |
| F^{μν} components Fu01..Fu23 | 6 | 24 | 4 (Fu01) | 12 | 3 |
| invariant F_{αβ}F^{αβ} | 1 | 3 | 3 (FFA) | 14 | 4 |
| atom partials `dRt` (3 non-zero entries) | 1 | 6 | 2 | 4 | – |
| atom partials `dKt` (9 non-zero entries) | 1 | 18 | 2 | 4 | – |
| atom partials `dWt` (3 non-zero entries) | 1 | 11 | 4 | 9 | – |
| atom partials `dfA` (3 non-zero entries) | 1 | 23 | 8 | 11 | – |
| atom partials `dHA` (3 non-zero entries) | 1 | 12 | 4 | 11 | – |

Largest closed-form polynomial: **DD122** with 101 monomials (total degree 21, atom degree 16, W^5, 7,654 chars).

HasCP derivation terms in Div1–Div4: 34 terms, 5,286 `HasCP.*` constructor applications (mul 2486, cst 1238, pow 1123, add 439), largest term 4,346 chars.

## 4. Generation pipeline

| Script | Lines | Role |
|---|---:|---|
| `ks_atoms.py` | 101 | Independent SymPy model of the Lean definitions in atoms r,k1,k2,k3 (partials of the atoms from implicit differentiation of r⁴−(ρ²−a²)r²−a²z²=0; canonical form = cancel + remainder of the numerator mod k1²+k2²+k3²−1). Builds g, g⁻¹ (checked), ∂g, Γ, ∂Γ, Riemann/Ricci, R, A=(er/Σ)k, F=dA, F², T; asserts G_{μν}=T_{μν} for all 16 components and R=0; pickles Γ, ∂Γ, Ric, F, T (ks_atoms.pkl). |
| `gen.py` | 112 | First-generation generator (rational closed forms with denominators Σ=r²+a²k3², Q=r²+a²; single relation k1²+k2²+k3²=1): Lean pretty-printers poly_str/frac_str/den_str and single-relation cofactors. Superseded by gen4.py; still imported by the scratch-only gen2.py/gen3.py. |
| `gen4.py` | 412 | Production generator (v4). Adds the atom W=1/Σ so every closed form is a polynomial; converts the pickled Γ, ∂_ρΓ^ρ, Ric, F to polynomials (choosing the shortest representative mod the sphere relation), computes F^{♯♯} and F²; prints g4_defs.lean (114 defs), g4_atoms.lean (7 HasCP lemmas for r,k1,k2,k3,W,f,H with rational cofactors) and g4_lemmas.lean (138 lemmas: chrS_Gam×40, dG×34 with explicit HasCP derivation trees, trGam×4, ricS×10, scal_zero, fS×16, fU×16, fF, tS×16). Every cofactor pair comes from sympy.reduced(numerator, [k1²+k2²+k3²−1, W(r²+a²k3²)−1], lex W>k1>r>k2>k3>a>m>e) with an assertion that the remainder is 0. |
| `mkparts2.py` | 75 | Earlier splitter into 13 blocks (Base, Atoms, Christoffel, Div1–4, Ricci1–4, a single Maxwell block, Assembly) written into the workspace Definitions/; its Base, Atoms, Christoffel, Div1–Div3 are the published versions (header '(n of 13)'); superseded by mkparts4.py for the rest. |
| `mkparts4.py` | 77 | Final splitter: concatenates generated fragments (g4_*.lean) with hand-written glue (infra_copied, mulinv, core_new, glue4_W/defs/metric/disp/final) into 16 blocks — the 15 published ones plus an all-in-one Assembly block that was never published — adds header/imports/options, writes parts_meta3.json. |
| `mkthms.py` | 73 | Generates the 8 intermediate platform statements (Thm_NoHair_KNE_thm_*.lean, `sorry` stubs over block Base) and their solutions (Sol_NoHair_KNE_thm_*.lean, each citing block lemmas; the three divergence proofs dispatch with fin_cases), plus titles and natural-language statements. |
| `publish_parts.py` | 84 | Resumable publisher: submits the 15 blocks in dependency order through the platform CLI (scripts/p2m.py), polls the publish job, retries on compile time-outs/internal errors and records state (publish_state.json). Not run for this report. |

- Data flow: ks_atoms.py → ks_atoms.pkl → gen4.py → g4_defs.lean (349 lines), g4_atoms.lean (186), g4_lemmas.lean (1225); total 914,369 bytes of generated Lean → mkparts4.py (+ 866 lines of hand-written glue in gen/*.lean: core_new.lean 126, glue4_W.lean 9, glue4_defs.lean 57, glue4_disp.lean 266, glue4_final.lean 119, glue4_metric.lean 51, infra_copied.lean 231, mulinv.lean 7) → 15 Def blocks; mkthms.py → 8 Thm stubs + 8 Sol files; final Sol_NoHair_kerrNewman_einstein.lean = glue4_final.lean + generated trGam_0..3/scal_zero.
- All 114 generated defs, 7 generated atom lemmas and 138 generated lemmas occur verbatim in the published blocks / final solution (checked by substring search); the generated fragments (914,369 bytes) are 93.7% of the 975,350 bytes of the Einstein part (15 blocks + 8 intermediate + final); hand-written glue: 866 lines / 43,050 bytes.
- Reproducibility: re-running ks_atoms.py then gen4.py from copies in a fresh directory (this machine, shared load) took 3:05.35 (user 181.46 s, max RSS 98 MB) and 1:23.21 (user 82.18 s, max RSS 74 MB); outputs byte-identical to the originals: {'ks_atoms.pkl': True, 'g4_defs.lean': True, 'g4_atoms.lean': True, 'g4_lemmas.lean': True}. The original ks_atoms run logged 136 s and 'EINSTEIN OK'.
- The 15 published blocks equal the mkparts4.py output (scratch parts3/) except that the first six (Base, Atoms, Christoffel, Div1–Div3) were published from the earlier 13-block split (mkparts2.py) and carry its header line '(n of 13)'; only that comment line differs (mkparts3.py, scratch-only, was an intermediate 19-block variant with Div2–Div4 halved).
- gen4.py imports only ks_atoms (and reads ks_atoms.pkl); gen3 is not needed for the production pipeline. Scratch-only scripts (earlier iterations / size experiments, nh_ein/): gen2.py (149), gen3.py (295), gen3b.py (96), mkparts.py (61), mkparts3.py (78), size1.py (14), size2.py (28), size3.py (22), test_poly.py (13), wcheck.py (51).
- Publication record (publish_state.json): all 15 blocks PUBLISHED; Div2 was re-submitted once (the script re-submits only after a 'timed out'/'Internal error' failure); the all-in-one Assembly block has two submission records and was never published — its content was moved into the 8 intermediate theorems + the final solution.

## 5. Check times and memory

`/usr/bin/time -v lake env lean <file>` from `/root/prove2me_workspace`, one file at a time, two full sequential passes (run 1, run 2). This re-elaborates each file against the existing .olean files of its imports; nothing is rebuilt or written. The intermediate/final/Maxwell solution copies had `#print axioms solution` appended (negligible cost). Baseline file containing only `import Mathlib`: cold page cache 226.6 s (first run of the session, reading ~6 GB of Mathlib .olean files from disk); warm 7.97, 7.79, 7.55, 7.91 s. **Net = min(run1, run2) wall − min warm baseline (7.55 s).** No `set_option maxHeartbeats` is used anywhere (default 200000). Max RSS includes the memory-mapped .olean files of Mathlib and of the imported blocks (~6.4 GB for `import Mathlib` alone), so it is dominated by imports, not by the proof.

Caveat: the machine (4 vCPUs, 15 GB) was shared with other jobs during the measurements (1-min load average between 1.0–4.3); wall-clock times can be inflated by contention. User CPU time is the more robust figure. Run 1 and run 2 are reported separately.

| File | Wall run 1 (s) | Wall run 2 (s) | Net of baseline (s) | User CPU (s, min) | Max RSS (MB) | Exit |
|---|---:|---:|---:|---:|---:|---:|
| *Einstein Def blocks* | | | | | | |
| Def_Base | 38.01 | 35.32 | 27.8 | 30.0 | 6,748 | 0,0 |
| Def_Atoms | 33.41 | 35.57 | 25.9 | 27.2 | 6,867 | 0,0 |
| Def_Christoffel | 81.83 | 82.61 | 74.3 | 68.2 | 8,422 | 0,0 |
| Def_Div1 | 29.11 | 27.67 | 20.1 | 21.7 | 6,954 | 0,0 |
| Def_Div2 | 80.11 | 87.20 | 72.6 | 64.8 | 7,799 | 0,0 |
| Def_Div3 | 83.64 | 87.69 | 76.1 | 67.9 | 7,832 | 0,0 |
| Def_Div4 | 56.40 | 56.65 | 48.9 | 45.6 | 7,365 | 0,0 |
| Def_Ricci1 | 33.79 | 31.58 | 24.0 | 24.4 | 7,316 | 0,0 |
| Def_Ricci2 | 36.58 | 35.68 | 28.1 | 27.9 | 7,364 | 0,0 |
| Def_Ricci3 | 36.47 | 36.65 | 28.9 | 27.5 | 7,487 | 0,0 |
| Def_Ricci4 | 36.70 | 37.75 | 29.2 | 28.3 | 7,507 | 0,0 |
| Def_Ricci5 | 60.16 | 59.58 | 52.0 | 47.4 | 8,045 | 0,0 |
| Def_Ricci6 | 53.69 | 50.12 | 42.6 | 40.1 | 7,803 | 0,0 |
| Def_MaxwellF | 26.85 | 25.57 | 18.0 | 20.1 | 6,933 | 0,0 |
| Def_MaxwellT | 50.97 | 48.33 | 40.8 | 38.7 | 7,655 | 0,0 |
| **sum Einstein Def blocks** | **737.7** | **738.0** | **609.2** | **579.9** | | |
| *Einstein intermediate solutions* | | | | | | |
| Sol_KNE_thm_christoffel | 6.71 | 6.12 | -1.4 | 3.8 | 6,409 | 0,0 |
| Sol_KNE_thm_div_one | 8.05 | 8.62 | 0.5 | 4.3 | 6,426 | 0,0 |
| Sol_KNE_thm_div_two | 7.54 | 7.74 | -0.0 | 4.1 | 6,427 | 0,0 |
| Sol_KNE_thm_div_three | 8.38 | 7.57 | 0.0 | 4.0 | 6,428 | 0,0 |
| Sol_KNE_thm_ricci_a | 7.49 | 7.55 | -0.1 | 4.0 | 6,405 | 0,0 |
| Sol_KNE_thm_ricci_b | 7.83 | 7.03 | -0.5 | 3.7 | 6,405 | 0,0 |
| Sol_KNE_thm_ricci_c | 7.38 | 7.40 | -0.2 | 3.7 | 6,406 | 0,0 |
| Sol_KNE_thm_maxwell | 8.40 | 7.37 | -0.2 | 3.8 | 6,406 | 0,0 |
| **sum Einstein intermediate solutions** | **61.8** | **59.4** | **-1.8** | **31.4** | | |
| *Einstein final* | | | | | | |
| Sol_kerrNewman_einstein | 10.59 | 10.41 | 2.9 | 11.3 | 6,646 | 0,0 |
| **sum Einstein final** | **10.6** | **10.4** | **2.9** | **11.3** | | |
| *Maxwell parts* | | | | | | |
| Sol_kerrNewman_field_closed | 8.93 | 8.63 | 1.1 | 6.1 | 6,447 | 0,0 |
| Sol_kerrNewman_flat_maxwell | 16.94 | 15.03 | 7.5 | 26.7 | 6,700 | 0,0 |
| Sol_kerrNewman_maxwell | 25.58 | 23.63 | 16.1 | 32.1 | 6,808 | 0,0 |
| Sol_kerrNewman_einsteinMaxwell | 7.03 | 6.83 | -0.7 | 3.8 | 6,404 | 0,0 |
| **sum Maxwell parts** | **58.5** | **54.1** | **23.9** | **68.6** | | |
| *Baselines (import Mathlib only)* | | | | | | |
| baseline1 | 226.62 | – | 219.1 | 13.3 | 6,275 | 0 |
| baseline2 | 7.97 | 7.55 | 0.0 | 4.1 | 6,391 | 0,0 |
| baseline3 | 7.79 | 7.91 | 0.2 | 4.0 | 6,391 | 0,0 |
| **sum of all proof files (28)** | **868.6** | **861.9** | **634.1** | **691.3** | | |

Reading the table: the per-file elaboration cost beyond loading Mathlib is the *Net* column; the four warm baselines spread over 7.55–7.97 s, so net values within about ±0.5 s of zero (all 8 intermediate solutions, the glue) mean "no measurable cost beyond the imports". The 15 Def blocks account for essentially all of the work: net 609 s ≈ 10.2 min of the 634 s total net. The heaviest single files are Div3 (76 s), Christoffel (74 s) and Div2 (73 s) net; no single file exceeds 88 s wall-clock here (the platform's per-compile limit is 300 s; the never-published all-in-one Assembly block is not timed). User CPU can exceed wall time for the solution files (flat_maxwell, maxwell, final), presumably because those files do not set `Elab.async false` (the Def blocks do) and Lean elaborates some proofs in parallel threads.

Earlier `lake build` times printed by Lake when the blocks were first compiled (scratch logs `nh_ein/part_*.log`; same machine, other load, includes writing .olean): Base 65 s, Atoms 33 s, Christoffel 93 s, Div1 31 s, Div2 94 s, Div3 96 s, Div4 88 s, Ricci1 39 s, Ricci2 45 s, Ricci3 45 s, Ricci4 47 s, Ricci5 75 s, Ricci6 65 s, MaxwellF 29 s, MaxwellT 61 s, Assembly 16 s, Maxwell 83 s (`Maxwell` = the superseded single Maxwell block; `Assembly` = the never-published all-in-one block, built on top of all others).

## 6. Axiom checks (exact output)

**Sol_KNE_thm_christoffel**

```
'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sol_KNE_thm_div_one**

```
'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sol_KNE_thm_div_two**

```
'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sol_KNE_thm_div_three**

```
'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sol_KNE_thm_ricci_a**

```
'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sol_KNE_thm_ricci_b**

```
'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sol_KNE_thm_ricci_c**

```
'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sol_KNE_thm_maxwell**

```
'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sol_kerrNewman_einstein**

```
'solution' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

**Sol_kerrNewman_field_closed**

```
'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sol_kerrNewman_flat_maxwell**

```
'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sol_kerrNewman_maxwell**

```
'solution' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

**Sol_kerrNewman_einsteinMaxwell**

```
'solution' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

**axcheck_stubs**

```
'NoHair.KNE.thm_christoffel' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.KNE.thm_div_one' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.KNE.thm_div_two' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.KNE.thm_div_three' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.KNE.thm_ricci_a' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.KNE.thm_ricci_b' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.KNE.thm_ricci_c' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.KNE.thm_maxwell' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.kerrNewman_einstein' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.kerrNewman_maxwell' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.kerrNewman_field_closed' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.kerrNewman_flat_maxwell' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NoHair.kerrNewman_einsteinMaxwell' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

**axcheck3_einstein**

```
'solution' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
closure of `solution`: 31146 constants; constants mentioning sorryAx directly: [NoHair.KNE.thm_maxwell,
 NoHair.KNE.thm_ricci_c,
 NoHair.KNE.thm_ricci_b,
 NoHair.KNE.thm_ricci_a,
 NoHair.KNE.thm_christoffel,
 NoHair.KNE.thm_div_three,
 NoHair.KNE.thm_div_two,
 NoHair.KNE.thm_div_one]
```

**axcheck3_einsteinMaxwell**

```
'solution' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
closure of `solution`: 14499 constants; constants mentioning sorryAx directly: [NoHair.kerrNewman_field_closed,
 NoHair.kerrNewman_maxwell,
 NoHair.kerrNewman_einstein]
```

**axcheck3_maxwell**

```
'solution' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
closure of `solution`: 31279 constants; constants mentioning sorryAx directly: [NoHair.kerrNewman_flat_maxwell]
```

- Each `Sol_*` file was elaborated as-is with `#print axioms solution` appended (outputs above, run 1; run 2 byte-identical). The 8 intermediate Einstein solutions and the field_closed / flat_maxwell solutions depend only on [propext, Classical.choice, Quot.sound].
- `sorryAx` in the final einstein, maxwell and einsteinMaxwell outputs comes only from the imported platform statement stubs (Theorems/Thm_*.lean, `:= by sorry`, axioms shown under axcheck_stubs). The axcheck3_* files (= the solution + a small metaprogram walking the type/value of every constant in the dependency closure of `solution`) list exactly which constants mention `sorryAx` directly: for the final Einstein solution exactly the 8 stubs NoHair.KNE.thm_{christoffel, div_one, div_two, div_three, ricci_a, ricci_b, ricci_c, maxwell}; for the curved Maxwell solution exactly NoHair.kerrNewman_flat_maxwell; for the einsteinMaxwell glue exactly NoHair.kerrNewman_{einstein, maxwell, field_closed}.
- Since every one of those stubs has a solution whose axioms are [propext, Classical.choice, Quot.sound], the full chain (15 Def blocks → 8 intermediate theorems → kerrNewman_einstein; flat_maxwell → maxwell; field_closed; → kerrNewman_einsteinMaxwell) uses no axioms beyond propext, Classical.choice, Quot.sound. (This is a compositional argument; a single-environment re-check with the stubs replaced by their proofs was not run here.)
- Static check: no `sorry`, `admit`, `native_decide` or `axiom` in any of the 28 proof files or the 15 Def blocks.

