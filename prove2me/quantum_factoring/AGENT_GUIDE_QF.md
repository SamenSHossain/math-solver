# Guide for proof agents (Prove2Me workspace): unitarity of circuits (exact quantum factoring mission)

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. `export PATH="$HOME/.elan/bin:$PATH"`.
- Definitions (READ IN FULL FIRST): `Definitions/Def_ExactQuantumFactoring.lean` (namespace `OAI.ExactQuantumFactoring`): Primitive (not, cnot, toffoli, hadamard, phase) with arity and `Primitive.matrix : List Bool → List Bool → ℂ` (entries on ill-sized lists are 0); `Gate` (primitive, inverse, controlled), `Gate.baseMatrix` (conjugate transpose when inverse), `Gate.matrix` (controlled: the first bit is the control; block-diagonal identity ⊕ base); `Instruction q` (gate, injective `wire : Fin gate.arity → Fin q`); `Instruction.matrix a b = if (a and b agree off the wires) then gate.matrix (List.ofFn (a ∘ wire)) (List.ofFn (b ∘ wire)) else 0`; `Circuit.apply` = foldl of `mulVec`; `Circuit.outputState c ℓ N` = apply to the basis vector of `inputBasis`.
- Target: `Theorems/Thm_OAI_ExactQuantumFactoring_outputState_normSq_sum.lean`: ∑ x, normSq (c.outputState ℓ N x) = 1.
- Type-check: `./check.sh Solutions/<file>.lean`. Scratch: `Solutions/Scratch_QF_<key>*.lean`. Never `lake build`; never edit Theorems/, Definitions/, .lake/.
- File layout: `import Mathlib`, `import Definitions.Def_ExactQuantumFactoring`, `set_option autoImplicit false`, `open scoped BigOperators`, `open OAI.ExactQuantumFactoring`, helpers in `namespace OAI.ExactQuantumFactoring.QF_U … end`, then a TOP-LEVEL `theorem solution` copying the target's binders and conclusion exactly (only the name changes). No Theorems.* imports.
- No sorry/admit/native_decide/axioms; keep compile time well under 200 s.

## Plan
1. Gate unitarity on lists of the right length. For every gate g and all v v' : Fin g.arity → Bool,
   ∑ u : Fin g.arity → Bool, star (g.matrix (List.ofFn u) (List.ofFn v)) * g.matrix (List.ofFn u) (List.ofFn v') = if v = v' then 1 else 0.
   - Primitives: NOT, CNOT, Toffoli are permutation matrices; Hadamard entries ±1/√2 (use (√2)² = 2, `Complex.ofReal`, `Real.sq_sqrt`/`Real.mul_self_sqrt`); phase is diag(1, i). Arity ≤ 3, so sums are over ≤ 8 terms: `Fintype.sum` over `Fin k → Bool` can be expanded (e.g. `Fin.sum_univ_succ`/`Fintype.sum_pi`-style lemmas, or an equivalence with `Bool × …`), then `decide`/`simp`/`fin_cases` on the Booleans and `ring_nf`/`norm_num` with `Complex.ext_iff` for the complex arithmetic.
   - Inverse: baseMatrix is the conjugate transpose, and the conjugate transpose of a unitary matrix is unitary (for finite square matrices UᴴU = 1 ↔ UUᴴ = 1: `Matrix.mul_eq_one_comm`).
   - Controlled: the first bit is the control (the arity is primitive.arity + 1; `Fin (n+1) → Bool` splits as `Bool × (Fin n → Bool)` via `Fin.consEquiv`/`Fin.cons`, and `List.ofFn (Fin.cons b u) = b :: List.ofFn u`); the matrix is block diagonal (identity on control false, base on control true).
   It is convenient to define the finite matrix G g : Matrix (Fin g.arity → Bool) (Fin g.arity → Bool) ℂ := fun u v => g.matrix (List.ofFn u) (List.ofFn v) and prove `Gᴴ * G = 1` (`Matrix.mem_unitaryGroup_iff'` etc.).
2. Instruction unitarity: (o.matrix)ᴴ * o.matrix = 1. Entry (b, b'): ∑ a, star(o.matrix a b) * o.matrix a b'. Both factors require a ≡ b and a ≡ b' off the wires; if b and b' differ off the wires every term is 0. Otherwise reindex the sum over {a | a ≡ b off wires} by u = a ∘ wire (a bijection with Fin k → Bool, since `wire` is injective: a is determined by u on the wires and by b elsewhere; use `Function.Injective.extend`-style reconstruction or `Equiv`s built from `wire`) to get (Gᴴ G)(b ∘ wire, b' ∘ wire) = [b ∘ wire = b' ∘ wire], and b ≡ b' off wires plus b ∘ wire = b' ∘ wire means b = b'.
3. Norm preservation: for a unitary U (UᴴU = 1), ∑ x, normSq ((U.mulVec v) x) = ∑ x, normSq (v x) (expand normSq as conj·z, or use `Matrix.UnitaryGroup` / `EuclideanSpace` isometry facts: `Matrix.UnitaryGroup.toLinearEquiv`/`unitary.norm_map`-style lemmas after identifying the state with `EuclideanSpace ℂ (Basis q)`; ‖v‖² = ∑ normSq).
4. `Circuit.apply` preserves ∑ normSq by induction on the instruction list (`List.foldl`, generalize the initial vector), and the initial basis vector has ∑ normSq = 1 (`Finset.sum_ite_eq`).

## Return
Structured result: status OK/PARTIAL, file, check_tail, proof_description, remaining.
