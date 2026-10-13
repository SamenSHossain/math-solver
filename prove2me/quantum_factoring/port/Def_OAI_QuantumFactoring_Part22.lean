/-
Exact quantum factoring development (port of OpenAI's formalization), part 22 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: RetainedNodeFilter.lean, RetrospectiveTree.lean, RetainedTreeFilter.lean, VerifiedRoot.lean, TreePadding.lean, QuarterPreparation.lean, TreeRootOutput.lean, TreePhysicalPreparation.lean, TreeQuarterPhysical.lean, RetainedQuarterFilter.lean, ExactnessFurther2.lean, OracleReadOnly.lean, TreeReadOnly.lean, ZeroOutside.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part21

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedNodeFilter.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def nodePrefixFilter (hn : 0<n) (T : ℕ) : (s : ℕ)→
    BooleanNetwork (M.width T) ((PhysicalNode.machine n (2*n)).width s)→BooleanNetwork (M.width T) 1
  | 0,_=>constant true
  | s+1,v=>(nodePrefixFilter hn T s (v.comp ((PhysicalNode.machine n (2*n)).previousNet s))).band
      (M.retainedSplitFilter hn T (v.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s)))

def retainedNodeFilter (hn : 0<n) (T : ℕ)
    (raw : BooleanNetwork (M.width T) (NodeKernel.width n)) : BooleanNetwork (M.width T) 1 :=
  M.nodePrefixFilter hn T (2*n) raw

lemma nodePrefixFilter_passed {N : ℕ} (hn : 128≤n) (T s : ℕ)
    (raw : BooleanNetwork (M.width T) ((PhysicalNode.machine n (2*n)).width s))
    (x : Basis c) (h : Trace n T) (q : Basis n) (r : SplitMachine.Trace n s)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x T h))
    (hq : (bitsValue q).toNat=0 ∨ 2≤(bitsValue q).toNat)
    (hP : (bitsValue q).toNat≠0 → (bitsValue q).toNat∈(M.dataLog x T h).map Prod.fst)
    (hr : raw.eval (M.encoded x T h)=
      (PhysicalNode.machine n (2*n)).encoded (NodeKernel.start q) s r) :
    (M.nodePrefixFilter (by omega) T s raw).eval (M.encoded x T h) 0=true ↔
      (PhysicalNode.machine n (2*n)).passed (NodeKernel.start q) s r := by
  induction s with
  | zero=>simp [nodePrefixFilter,SplitMachine.passed]
  | succ s ih=>
    rw [nodePrefixFilter,eval_band,Bool.and_eq_true]
    apply and_congr
    · apply ih _ r.1
      rw [eval_comp,hr,SplitMachine.previousNet_encoded]
    · have hraw : (raw.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s)).eval
          (M.encoded x T h)= FixedSplit.encoding
          ((PhysicalNode.query n (2*n)).eval ((PhysicalNode.machine n (2*n)).config
            (NodeKernel.start q) s r.1)) r.2 := by
        rw [eval_comp,hr,SplitMachine.lastSplitNet_encoded]
        rfl
      rcases hq with hz | hpos
      · apply M.retainedSplitFilter_nonhard hn T _ _ _ r.2 _ hraw
        have hzero:=PhysicalNode.query_zero hn q hz s r.1
        intro hh
        have hh':=hh.1
        omega
      · apply M.retainedSplitFilter_passed hn T _ x h _ r.2 hc (hP (by omega)) (by omega) _ hraw
        intro hh
        have hs:=PhysicalNode.query_safe hn hpos (bitsValue q).isLt s r.1
        rw [←PhysicalNode.startNet_eval n q] at hs
        change (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat=0 ∨
          (2 ≤ (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat ∧
          (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat<2^n ∧
          (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat∣(bitsValue q).toNat) at hs
        rcases hs with hz | hs
        · have hh':=hh.1
          omega
        · exact hs.2.2

/-- Every split in the actual retained node history is tested against the final
read-only verified table. No fresh random experiment or ideal flag is inserted. -/
theorem retainedNodeFilter_passed {N : ℕ} (hn : 128≤n) (T : ℕ)
    (raw : BooleanNetwork (M.width T) (NodeKernel.width n))
    (x : Basis c) (h : Trace n T) (q : Basis n) (r : NodeKernel.Raw n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x T h))
    (hq : (bitsValue q).toNat=0 ∨ 2≤(bitsValue q).toNat)
    (hP : (bitsValue q).toNat≠0 → (bitsValue q).toNat∈(M.dataLog x T h).map Prod.fst)
    (hr : raw.eval (M.encoded x T h)=NodeKernel.encoding q r) :
    (M.retainedNodeFilter (by omega) T raw).eval (M.encoded x T h) 0=true ↔ NodeKernel.passed q r :=
  M.nodePrefixFilter_passed hn T (2*n) raw x h q r hc hq hP hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetrospectiveTree.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree
namespace PhysicalTree

lemma verified_query_safe {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (r : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t r) :
    let m:=(bitsValue ((query n).eval ((machine n).config (initialQueue n N) t r))).toNat
    m=0 ∨ 2 ≤ m := by
  dsimp only
  rw [verified_query_value hn hN hb t r hv]
  have hh:=run_bounds (xs:=[N]) (B:=2^n) (by
    intro a ha
    have he : a=N := List.mem_singleton.mp ha
    subst a
    exact ⟨hN,hb⟩) t
  cases he : run t [N] with
  | nil=>exact Or.inl rfl
  | cons a as=>exact Or.inr (hh a (by rw [he];simp)).1
end PhysicalTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Read-only postprocessing of the retained actual history. Each node receives
only the flat row data at its actual runtime label. Occurrences are retained;
lookup selects the first matching verified record, not a factorization oracle. -/
noncomputable def dataTests (rows : List (ℕ×List ℕ)) (x : Basis c) (hn : 0<n) :
    (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,r=>dataTests rows x hn t r.1 ∧
    let q:=M.query.eval (M.config x t r.1)
    NodeKernel.dataPassed q (PhysicalTree.flatData rows (bitsValue q).toNat) hn r.2
end NodeMachine
namespace PhysicalTree

lemma dataTests_correct {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (rows : List (ℕ×List ℕ)) (hc : CompleteLog n N rows)
    (t : ℕ) (r : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t r)
    (hr : ∀ a∈(machine n).dataLog (initialQueue n N) t r,a∈rows) :
    (machine n).dataTests rows (initialQueue n N) (by omega) t r ↔
      (machine n).passed (initialQueue n N) t r := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    apply and_congr (ih r.1 hv.1 (fun a ha=>hr a (List.mem_cons_of_mem _ ha)))
    apply NodeKernel.dataPassed_correct hn _ _ (verified_query_safe hn hN hb t r.1 hv.1)
    intro hpos
    apply completeLog_view hc _ hpos
    apply List.mem_map.mpr
    refine ⟨_,hr _ (List.mem_cons_self),rfl⟩

/-- Literal event specification for completed-data retrospective checking.
The Boolean implementation of the arithmetic and the whole polynomial-time
compiler are separate obligations, not consequences of this definition. -/
noncomputable def accepted {n N : ℕ} (hn : 0<n) (r : NodeMachine.Trace n (2*n^2)) : Prop :=
  (machine n).verified (initialQueue n N) (2*n^2) r ∧
    (machine n).dataTests ((machine n).dataLog (initialQueue n N) (2*n^2) r)
      (initialQueue n N) hn (2*n^2) r

/-- Same-history retrospective equivalence, with the actual physical data tree
and actual divisibility-safe node controller. Unverified factor data is rejected
first; no comparison to a counterfactual run is used. -/
theorem accepted_iff_passed {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (r : NodeMachine.Trace n (2*n^2)) :
    accepted (N:=N) (by omega) r ↔ (machine n).passed (initialQueue n N) (2*n^2) r := by
  constructor
  · rintro ⟨hv,hd⟩
    exact (dataTests_correct hn hN hb _ (verified_complete_log hn hN hb r hv)
      _ r hv (fun _ ha=>ha)).mp hd
  · intro hp
    have hv:=passed_verified hn hN hb _ r hp
    exact ⟨hv,(dataTests_correct hn hN hb _ (verified_complete_log hn hN hb r hv)
      _ r hv (fun _ ha=>ha)).mpr hp⟩

/-- Exact accepted mass, after the actual complete-data checks. This is still
an event theorem: using it as a physical phase flag requires the missing fully
assembled retrospective Boolean network, rather than an arbitrary predicate. -/
theorem accepted_mass {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n) :
    Exactness.outcomeMass (accepted (n:=n) (N:=N) (by omega))
      ((machine n).state (initialQueue n N) (2*n^2))=
        (((Completion.target n:ℝ)^(n^5+1))^(2*n))^(2*n^2) := by
  have he : accepted (n:=n) (N:=N) (by omega)=
      (machine n).passed (initialQueue n N) (2*n^2) := by
    funext r
    exact propext (accepted_iff_passed hn hN hb r)
  rw [he]
  exact (machine n).passed_mass hn _ _
end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedTreeFilter.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def treePrefixFilter (hn : 0<n) (T : ℕ) : (s : ℕ)→
    BooleanNetwork (M.width T) (M.width s)→BooleanNetwork (M.width T) 1
  | 0,_=>constant true
  | s+1,v=>(treePrefixFilter hn T s (v.comp (M.previousNet s))).band
      (M.retainedNodeFilter hn T (v.comp (M.lastNodeNet s)))

def acceptedNet (hn : 0<n) (T : ℕ) : BooleanNetwork (M.width T) 1 :=
  (M.verifiedNet T).band (M.treePrefixFilter hn T T (select id))
end NodeMachine
namespace PhysicalTree

lemma treePrefixFilter_passed {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (T s : ℕ) (h : NodeMachine.Trace n T) (r : NodeMachine.Trace n s)
    (raw : BooleanNetwork ((machine n).width T) ((machine n).width s))
    (hc : CompleteLog n N ((machine n).dataLog (initialQueue n N) T h))
    (hv : (machine n).verified (initialQueue n N) s r)
    (hsub : ∀ a∈(machine n).dataLog (initialQueue n N) s r,
      a∈(machine n).dataLog (initialQueue n N) T h)
    (hr : raw.eval ((machine n).encoded (initialQueue n N) T h)=
      (machine n).encoded (initialQueue n N) s r) :
    ((machine n).treePrefixFilter (by omega) T s raw).eval
      ((machine n).encoded (initialQueue n N) T h) 0=true ↔
      (machine n).passed (initialQueue n N) s r := by
  induction s with
  | zero=>simp [NodeMachine.treePrefixFilter,NodeMachine.passed]
  | succ s ih=>
    rw [NodeMachine.treePrefixFilter,eval_band,Bool.and_eq_true]
    apply and_congr
    · apply ih r.1 _ hv.1 (fun a ha=>hsub a (List.mem_cons_of_mem _ ha))
      rw [eval_comp,hr,NodeMachine.previousNet_encoded]
    · apply (machine n).retainedNodeFilter_passed hn T _ (initialQueue n N) h _ r.2 hc
        (verified_query_safe hn hN hb s r.1 hv.1)
      · intro _
        apply List.mem_map.mpr
        refine ⟨_,hsub _ (List.mem_cons_self),rfl⟩
      · rw [eval_comp,hr,NodeMachine.lastNodeNet_encoded]
        rfl

/-- A fully assembled same-history Boolean flag on the actual physical tree.
Completeness of the factor table is derived from its literal verification;
it is not a hypothesis of this flag specification. -/
theorem acceptedNet_iff_passed {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (h : NodeMachine.Trace n (2*n^2)) :
    ((machine n).acceptedNet (by omega) (2*n^2)).eval
      ((machine n).encoded (initialQueue n N) (2*n^2) h) 0=true ↔
      (machine n).passed (initialQueue n N) (2*n^2) h := by
  rw [NodeMachine.acceptedNet,eval_band,Bool.and_eq_true,(machine n).verifiedNet_encoded hn]
  constructor
  · rintro ⟨hv,hf⟩
    exact (treePrefixFilter_passed hn hN hb (2*n^2) (2*n^2) h h (select id)
      (verified_complete_log hn hN hb h hv) hv (fun _ ha=>ha) (by rfl)).mp hf
  · intro hp
    have hv:=passed_verified hn hN hb (2*n^2) h hp
    refine ⟨hv,?_⟩
    exact (treePrefixFilter_passed hn hN hb (2*n^2) (2*n^2) h h (select id)
      (verified_complete_log hn hN hb h hv) hv (fun _ ha=>ha) (by rfl)).mpr hp

lemma acceptedNet_iff_accepted {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (h : NodeMachine.Trace n (2*n^2)) :
    ((machine n).acceptedNet (by omega) (2*n^2)).eval
      ((machine n).encoded (initialQueue n N) (2*n^2) h) 0=true ↔ accepted (N:=N) (by omega) h :=
  (acceptedNet_iff_passed hn hN hb h).trans (accepted_iff_passed hn hN hb h).symm
end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/VerifiedRoot.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)
lemma first_verified (x : Basis c) (t : ℕ) (h : Trace n (t+1))
    (hp : M.verified x (t+1) h) :
    PhysicalTree.NodeVerified (M.query.eval x) (firstRaw t h) := by
  induction t with
  | zero=>exact hp.2
  | succ t ih=>exact ih h.1 hp.1
end NodeMachine
namespace PhysicalTree
lemma nodeWords_layout (n : ℕ) (z : Basis (NodeKernel.width n)) :
    SortedWords.layout n n (nodeWords n z)=(nodeResult n).eval z := by
  simp only [nodeWords,SortedWords.layout_ofFn,resultFields,eval_comp,tensorSelect_inverse]
  exact (tensorLayout n n).apply_symm_apply _

/-- The literal data-verifier flag implies a correct root readout on arbitrary
raw histories, not just on histories assumed successful in the analysis. -/
theorem verified_root {n N : ℕ} (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n (t+1))
    (hp : (machine n).verified (initialQueue n N) (t+1) h) :
    ∃ zs : List (Basis n), zs.length=n ∧ CorrectEncoding N n (SortedWords.numbers zs) ∧
      (rootResult n t).eval ((machine n).encoded (initialQueue n N) (t+1) h)=
        SortedWords.layout n n zs := by
  have hp0:=(machine n).first_verified (initialQueue n N) t h hp
  change NodeVerified ((query n).eval (initialQueue n N)) (NodeMachine.firstRaw t h) at hp0
  rw [query_initial] at hp0
  have hv : (bitsValue (natBasis n N)).toNat=N := by rw [natBasis_value,Nat.mod_eq_of_lt hb]
  rcases hp0 with hz | hc
  · rw [hv] at hz
    omega
  · refine ⟨nodeWords n (NodeKernel.encoding (natBasis n N) (NodeMachine.firstRaw t h)),
      nodeWords_length _ _,?_,?_⟩
    · simpa only [hv] using hc
    · rw [rootResult,eval_comp,NodeMachine.firstNodeNet_encoded,nodeWords_layout]
      change (nodeResult n).eval (NodeKernel.encoding ((query n).eval (initialQueue n N)) _) = _
      rw [query_initial]

/-- Exact equivalence of the physical data-verifier bit with the explicit
retrospective data predicate, and its unconditional root-output soundness. -/
theorem verifier_readout {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n (t+1))
    (hp : ((machine n).verifiedNet (t+1)).eval
      ((machine n).encoded (initialQueue n N) (t+1) h) 0=true) :
    ∃ zs : List (Basis n), zs.length=n ∧ CorrectEncoding N n (SortedWords.numbers zs) ∧
      (rootResult n t).eval ((machine n).encoded (initialQueue n N) (t+1) h)=
        SortedWords.layout n n zs :=
  verified_root hN hb t h (((machine n).verifiedNet_encoded hn _ _ _).mp hp)
end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreePadding.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials
namespace PhysicalTree

/-- The actual tree has 2n² nodes, 2n split clocks per node, one list slot and
n^5 padded base/order slots per split. This is not the n^10 padding cap. -/
def slots (n : ℕ) : ℕ := ((n^5+1)*(2*n))*(2*n^2)
def padding (n : ℕ) : ℕ := n^10-slots n

lemma slots_le {n : ℕ} (hn : 128≤n) : slots n≤n^10 := by
  have hp : 1≤n^5 := Nat.one_le_pow _ _ (by omega)
  have h₂ : 8≤n^2 := by nlinarith
  calc
    slots n ≤ ((2*n^5)*(2*n))*(2*n^2) := by
      unfold slots
      gcongr
      omega
    _ = 8*n^8 := by ring
    _ ≤ n^2*n^8 := Nat.mul_le_mul_right _ h₂
    _ = n^10 := by ring

lemma slots_add_padding {n : ℕ} (hn : 128≤n) : slots n+padding n=n^10 :=
  Nat.add_sub_of_le (slots_le hn)

abbrev PadRaw (n : ℕ) := Fin (padding n)→Basis n
noncomputable def padState (n : ℕ) : PadRaw n→ℂ := tensorState (fairState n) (padding n)
def padPassed {n : ℕ} (x : PadRaw n) : Prop := ∀ i, ¬ Completion.rare (x i)

def padProgram (n : ℕ) : List (Instruction (tensorWidth n (padding n))) :=
  tensorProgram (hadamardPrefix n n le_rfl) (padding n)

lemma padProgram_length (n : ℕ) : (padProgram n).length=padding n*n := by
  rw [padProgram,tensorProgram_length,hadamardPrefix_length]

lemma padProgram_state (n : ℕ) :
    (programMatrix (padProgram n)).mulVec
      (basisVector (tensorLayout n (padding n) (fun _ _=>false)))=
    encodeState (tensorLayout n (padding n)) (padState n) := by
  rw [padProgram,tensorProgram_state,hadamards_zero]
  rfl

lemma pad_normalized (n : ℕ) : ∑ x,Complex.normSq (padState n x)=1 :=
  tensor_normalized _ _ (fairState_normalized n)

lemma pad_mass (n : ℕ) : outcomeMass (padPassed (n:=n)) (padState n)=
    (Completion.target n:ℝ)^(padding n) := by
  change outcomeMass (fun x : PadRaw n=>∀ i,¬Completion.rare (x i))
    (tensorState (fairState n) (padding n))=_
  rw [tensor_all_mass (fairState n) (padding n) (fun y=>¬Completion.rare y),mass_compl _ _ (fairState_normalized n)]
  have hr : outcomeMass (fun x : Basis n=>Completion.rare x) (fairState n)=
      1/(2:ℝ)^n := by
    exact fair_value_mass (by positivity)
  rw [hr]
  simp only [Completion.target,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
    Rat.cast_pow,Rat.cast_ofNat]

abbrev PaddedRaw (n : ℕ) := NodeMachine.Trace n (2*n^2)×PadRaw n
noncomputable def paddedState (n N : ℕ) : PaddedRaw n→ℂ :=
  independentState ((machine n).state (initialQueue n N) (2*n^2)) (padState n)
noncomputable def paddedAccepted {n N : ℕ} (hn : 0<n) (x : PaddedRaw n) : Prop :=
  accepted (N:=N) hn x.1 ∧ padPassed x.2

lemma padded_normalized (n N : ℕ) : ∑ x,Complex.normSq (paddedState n N x)=1 :=
by
  change ∑ x : NodeMachine.Trace n (2*n^2)×PadRaw n,
    Complex.normSq (independentState ((machine n).state (initialQueue n N) (2*n^2))
      (padState n) x)=1
  simp only [independentState,Complex.normSq_mul,Fintype.sum_prod_type]
  simp_rw [←Finset.mul_sum,pad_normalized,mul_one]
  exact (machine n).state_normalized _ _

/-- Exact manuscript P_n, now for the actual chronological physical tree,
retrospective checks on its own data log, and literal nonzero-word padding. -/
theorem padded_mass {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (paddedAccepted (n:=n) (N:=N) (by omega)) (paddedState n N)=
      (knownProbability n:ℝ) := by
  change outcomeMass (fun x : PaddedRaw n => accepted (N:=N) (by omega) x.1 ∧
    padPassed x.2) (independentState ((machine n).state (initialQueue n N) (2*n^2))
      (padState n))=_
  rw [independent_mass,accepted_mass hn hN hb,pad_mass,
    ←pow_mul,←pow_mul,←pow_add]
  have he : (n^5+1)*(2*n*(2*n^2))+padding n=n^10 := by
    simpa only [slots,Nat.mul_assoc] using slots_add_padding hn
  rw [he]
  simp only [knownProbability,Completion.target,Rat.cast_pow,Rat.cast_sub,
    Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/QuarterPreparation.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness OrderTrial

lemma knownProbability_at (n : ℕ) : DyadicAt (n^11) (knownProbability n) := by
  have hd : DyadicAt n (1-1/(2:ℚ)^n) := (DyadicAt.integer n 1).sub ⟨1,by simp⟩
  convert hd.pow (n^10) using 1 <;> first | rfl | ring

namespace Quarter
/-- The second rounding uses EXACTLY J+2, not the transition completion's
slightly finer W+t+2 grid. One surplus fair retention bit is harmless. -/
def retention (n : ℕ) : ℚ := quarterCoeff (n*n) (knownProbability n)
def guessRetention (n : ℕ) : ℚ := (2:ℚ)^(n*n+1)*quarterRemainder (n*n) (knownProbability n)
abbrev D (n : ℕ) : ℕ := Completion.coinBits (n*n) 1 (n^11)
abbrev Raw (α : Type*) (n : ℕ) := Completion.Raw α (n*n) 1 (n^11)
noncomputable def fresh {α : Type*} (ψ : α→ℂ) (n : ℕ) : Raw α n→ℂ :=
  Completion.fresh ψ (n*n) 1 (n^11)

lemma retention_at (n : ℕ) : DyadicAt (D n) (retention n) := by
  apply (show DyadicAt (n*n+2) (retention n) from ⟨_,rfl⟩).mono
  unfold D Completion.coinBits
  omega
lemma guessRetention_at (n : ℕ) : DyadicAt (D n) (guessRetention n) := by
  have hC : DyadicAt (n*n+2) (retention n) := ⟨_,rfl⟩
  have hP := (knownProbability_at n).mul hC
  have hhalf : DyadicAt 1 (1/2) := ⟨1,by norm_num⟩
  have hprod := hP.mul hhalf
  have hprod' : DyadicAt (D n) (knownProbability n*retention n/2) := by
    simpa only [div_eq_mul_inv,one_div,one_mul] using hprod.mono (l:=D n) (by unfold D Completion.coinBits; omega)
  have hquarter : DyadicAt (D n) (1/4) :=
    (show DyadicAt 2 (1/4) from ⟨1,by norm_num⟩).mono (by unfold D Completion.coinBits; omega)
  have h := (hquarter.sub hprod').int_mul (2^(n*n+1))
  simpa only [guessRetention,quarterRemainder,retention,Int.cast_pow,Int.cast_ofNat] using h

def ordinaryPass {α : Type*} {n : ℕ} (success : α→Prop) (r : Raw α n) : Prop :=
  ¬Completion.rare r.1 ∧ (success r.2.1 ∧ Completion.threshold (retention n) r.2.2.2)
def guessPass {α : Type*} {n : ℕ} (N : ℕ) (r : Raw α n) : Prop :=
  Completion.rare r.1 ∧ (CorrectEncoding N n (guessWords n r.2.2.1) ∧
    Completion.threshold (guessRetention n) r.2.2.2)
def passed {α : Type*} {n : ℕ} (N : ℕ) (success : α→Prop) (r : Raw α n) : Prop :=
  ordinaryPass success r ∨ guessPass N r

theorem passed_mass {α : Type*} [Fintype α] {N n : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (ψ : α→ℂ) (success : α→Prop) (hψ : ∑ x,Complex.normSq (ψ x)=1)
    (hs : outcomeMass success ψ=(knownProbability n:ℝ)) :
    outcomeMass (passed N success) (fresh ψ n)=1/4 := by
  obtain ⟨hp₀,hp₁⟩ := knownProbability_bounds hn
  obtain ⟨hC₀,hC₁,hG₀,hG₁⟩ := quarter_retention_bounds (n*n) hp₀ hp₁
  have hC := dyadic_fair_threshold (retention_at n) hC₀ hC₁
  have hG := dyadic_fair_threshold (guessRetention_at n) hG₀ (hG₁.le.trans (by norm_num))
  have hr : outcomeMass (fun b : Basis 1 => Completion.rare b) (fairState 1)=1/2 := by
    simpa only [Completion.rare,pow_one] using (fair_value_mass (by norm_num : 0<2^1))
  have hnr : outcomeMass (fun b : Basis 1 => ¬Completion.rare b) (fairState 1)=1/2 := by
    rw [RepeatedTrials.mass_compl _ _ (fair_normalized 1),hr]
    norm_num
  have ho : outcomeMass (ordinaryPass (n:=n) success) (fresh ψ n)=
      (1/2)*(knownProbability n:ℝ)*(retention n:ℝ) := by
    change outcomeMass (fun r : Raw α n => ¬Completion.rare r.1 ∧
      (success r.2.1 ∧ Completion.threshold (retention n) r.2.2.2))
      (Completion.fresh ψ (n*n) 1 (n^11))=_
    rw [Completion.fresh,independent_mass (fairState 1)
      (independentState ψ (independentState (fairState (n*n)) (fairState (D n))))
      (fun b => ¬Completion.rare b) (fun r => success r.1 ∧ Completion.threshold (retention n) r.2.2),
      independent_mass ψ (independentState (fairState (n*n)) (fairState (D n)))
      success (fun r => Completion.threshold (retention n) r.2),
      independent_mass_right _ _ _ (fair_normalized (n*n))]
    rw [hnr,hs]
    rw [show outcomeMass (Completion.threshold (D:=D n) (retention n)) (fairState (D n))=
      (retention n:ℝ) from hC]
    ring
  have hg : outcomeMass (guessPass (n:=n) N) (fresh ψ n)=
      (1/2)*(1/(2:ℝ)^(n*n))*(guessRetention n:ℝ) := by
    change outcomeMass (fun r : Raw α n => Completion.rare r.1 ∧
      (CorrectEncoding N n (guessWords n r.2.2.1) ∧ Completion.threshold (guessRetention n) r.2.2.2))
      (Completion.fresh ψ (n*n) 1 (n^11))=_
    rw [Completion.fresh,independent_mass (fairState 1)
      (independentState ψ (independentState (fairState (n*n)) (fairState (D n))))
      Completion.rare (fun r => CorrectEncoding N n (guessWords n r.2.1) ∧
        Completion.threshold (guessRetention n) r.2.2),
      independent_mass_right ψ (independentState (fairState (n*n)) (fairState (D n)))
      (fun r => CorrectEncoding N n (guessWords n r.1) ∧ Completion.threshold (guessRetention n) r.2) hψ,
      independent_mass (fairState (n*n)) (fairState (D n))
      (fun x => CorrectEncoding N n (guessWords n x)) (Completion.threshold (guessRetention n)),
      hr,fair_guess_mass hN hb]
    rw [show outcomeMass (Completion.threshold (D:=D n) (guessRetention n)) (fairState (D n))=
      (guessRetention n:ℝ) from hG]
    simp only [one_div,inv_pow]
    ring
  change outcomeMass (fun r => ordinaryPass success r ∨ guessPass N r) (fresh ψ n)=1/4
  rw [outcomeMass_disjoint_or _ _ _ (by intro r h; exact h.1.1 h.2.1),ho,hg]
  have h := congrArg (fun q : ℚ => (q:ℝ)) (quarter_mass (n*n) (knownProbability n))
  push_cast at h
  simpa only [retention,guessRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using h

/-- The flagged output always has the same canonical root encoding. -/
theorem passed_correct {α : Type*} {N n : ℕ} (ordinary : α→Basis (n*n)) (success : α→Prop)
    (hsound : ∀ a,success a → CorrectEncoding N n (guessWords n (ordinary a)))
    (r : Raw α n) (h : passed N success r) :
    CorrectEncoding N n (guessWords n (Completion.output ordinary r)) := by
  rcases h with h | h
  · simpa only [Completion.output,ite_eq_right h.1] using hsound r.2.1 h.2.1
  · simpa only [Completion.output,ite_eq_left h.1] using h.2.1

/-- No probability or canonical factor list occurs in the raw unitary. -/
def program {q : ℕ} (P : List (Instruction q)) (n : ℕ) := Completion.program P (n*n) 1 (n^11)
lemma program_entry {q : ℕ} (P : List (Instruction q)) (n : ℕ) (a : Basis q) (r : Raw (Basis q) n) :
    (programMatrix (program P n)).mulVec
      (basisVector (Completion.layout q (n*n) 1 (n^11) ((fun _ => false),a,(fun _ => false),(fun _ => false))))
      (Completion.layout q (n*n) 1 (n^11) r)=fresh ((programMatrix P).mulVec (basisVector a)) n r :=
  Completion.program_entry P (n*n) 1 (n^11) a r
lemma program_length {q : ℕ} (P : List (Instruction q)) (n : ℕ) :
    (program P n).length=P.length+1+n*n+D n := Completion.program_length P (n*n) 1 (n^11)

end Quarter
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeRootOutput.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

/-- Only a fixed rearrangement of output wires, from tensor grouping to the
source's consecutive n-bit fields. No factor search is present. -/
def flattenWords (n : ℕ) : BooleanNetwork (tensorWidth n n) (n*n) :=
  wordBlocks (fun i=>tensorSelect n n i)

lemma flattenWords_numbers {n : ℕ} (zs : List (Basis n)) (hl : zs.length=n) :
    guessWords n ((flattenWords n).eval (SortedWords.layout n n zs))=SortedWords.numbers zs := by
  let f : Fin n→Basis n := fun i=>zs[i.val]'(by omega)
  have hf : List.ofFn f=zs := by
    apply List.ext_getElem
    · simp only [List.length_ofFn,hl]
    · intro i hi hj
      simp only [List.getElem_ofFn,f]
  rw [←hf,SortedWords.layout_ofFn]
  simp only [guessWords,flattenWords,wordBlocks_eval,tensorSelect_eval,
    SortedWords.numbers,List.map_ofFn,Function.comp_def]

/-- A literal bounded readout for every clock count, with a harmless zero case. -/
def rootFlat (n : ℕ) : (t : ℕ)→BooleanNetwork ((machine n).width t) (n*n)
  | 0=>Completion.zeros _ _
  | t+1=>(rootResult n t).comp (flattenWords n)

lemma rootFlat_correct {n N : ℕ} (hN : 2≤N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n (t+1))
    (hv : (machine n).verified (initialQueue n N) (t+1) h) :
    CorrectEncoding N n (guessWords n ((rootFlat n (t+1)).eval
      ((machine n).encoded (initialQueue n N) (t+1) h))) := by
  obtain ⟨zs,hl,hc,he⟩:=verified_root hN hb t h hv
  rw [rootFlat,eval_comp,he,flattenWords_numbers zs hl]
  exact hc

noncomputable def ordinaryOutput (n N : ℕ) (r : PaddedRaw n) : Basis (n*n) :=
  (rootFlat n (2*n^2)).eval ((machine n).encoded (initialQueue n N) (2*n^2) r.1)

/-- Soundness uses verifier success on this raw history, not ideal quantum
success or an externally supplied prime-factorization list. -/
theorem padded_output {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : PaddedRaw n) (hp : paddedAccepted (N:=N) (by omega) r) :
    CorrectEncoding N n (guessWords n (ordinaryOutput n N r)) := by
  have hh : ∀ (t : ℕ) (h : NodeMachine.Trace n t), 0<t →
      (machine n).verified (initialQueue n N) t h →
      CorrectEncoding N n (guessWords n ((rootFlat n t).eval
        ((machine n).encoded (initialQueue n N) t h))) := by
    intro t
    cases t with
    | zero=>intro _ ht; omega
    | succ t=>intro h _ hv; exact rootFlat_correct hN hb t h hv
  apply hh _ _ _ hp.1.1
  have : 0<n := by omega
  positivity

/-- Both branches of Section 6's final quarter-probability preparation now
use the actual chronological tree. This is an event/output theorem; it does
not assert the missing efficient Boolean implementation of the full flag. -/
theorem quarter_mass {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (Quarter.passed N (paddedAccepted (n:=n) (N:=N) (by omega)))
      (Quarter.fresh (paddedState n N) n)=1/4 := by
  exact Quarter.passed_mass hn hN hb _ _ (padded_normalized n N) (padded_mass hn hN hb)

theorem quarter_output {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : Quarter.Raw (PaddedRaw n) n)
    (hp : Quarter.passed N (paddedAccepted (n:=n) (N:=N) (by omega)) r) :
    CorrectEncoding N n (guessWords n (Completion.output (ordinaryOutput n N) r)) :=
  Quarter.passed_correct _ _ (fun r hr=>padded_output hn hN hb r hr) r hp

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreePhysicalPreparation.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork BitArithmetic Exactness OrderTrial

lemma parallelProgram_encoded_state {α β : Type*} [Fintype α] [Fintype β] {p q : ℕ}
    (A : List (Instruction p)) (B : List (Instruction q)) (x : Basis p) (y : Basis q)
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (χ : β→ℂ)
    (hA : (programMatrix A).mulVec (basisVector x)=encodeState e ψ)
    (hB : (programMatrix B).mulVec (basisVector y)=encodeState f χ) :
    (programMatrix (parallelProgram A B)).mulVec (basisVector (Fin.append x y))=
      encodeState (fun ab : α×β=>Fin.append (e ab.1) (f ab.2)) (independentState ψ χ) := by
  rw [parallelProgram,programMatrix_append,←Matrix.mulVec_mulVec,leftProgram_basis,hA,
    encodeState_comp,encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,rightProgram_basis,hB,encodeState_comp,Function.comp_def]
  exact (encode_independent e f ψ χ).symm

namespace PhysicalTree
abbrev launchWork (n : ℕ) := (initialNet n).net.count
abbrev launchWidth (n : ℕ) := n+width n+launchWork n

def launchProgram (n : ℕ) : List (Instruction (launchWidth n)) :=
  preparedOracle (initialNet n) le_rfl ((machine n).program (steps n))
def launchEncoding (n N : ℕ) (r : NodeMachine.Trace n (steps n)) : Basis (launchWidth n) :=
  packed (launchWork n) (natBasis n N) ((machine n).encoded (initialQueue n N) (steps n) r)
def launchZero (n N : ℕ) : Basis (launchWidth n) :=
  packed (launchWork n) (natBasis n N) (fun _=>false)

lemma launchProgram_state (n N : ℕ) :
    (programMatrix (launchProgram n)).mulVec (basisVector (launchZero n N))=
      encodeState (launchEncoding n N) ((machine n).state (initialQueue n N) (steps n)) := by
  rw [launchProgram,launchZero,preparedOracle_basis,initialNet_eval,
    NodeMachine.program_state,encodeState_comp]
  rfl
lemma launchEncoding_injective (n N : ℕ) : Function.Injective (launchEncoding n N) := by
  intro a b h
  apply (machine n).encoded_injective (initialQueue n N) (steps n)
  have he:=congrArg (fun x=>x ∘ targetRegister n (width n) (launchWork n)) h
  simpa only [launchEncoding,packed_targetRegister] using he

abbrev paddedWidth (n : ℕ) := launchWidth n+tensorWidth n (padding n)
def paddedProgram (n : ℕ) : List (Instruction (paddedWidth n)) :=
  parallelProgram (launchProgram n) (padProgram n)
def paddedZero (n N : ℕ) : Basis (paddedWidth n) :=
  Fin.append (launchZero n N) (tensorLayout n (padding n) (fun _ _=>false))
def paddedEncoding (n N : ℕ) (r : PaddedRaw n) : Basis (paddedWidth n) :=
  Fin.append (launchEncoding n N r.1) (tensorLayout n (padding n) r.2)

lemma paddedProgram_state (n N : ℕ) :
    (programMatrix (paddedProgram n)).mulVec (basisVector (paddedZero n N))=
      encodeState (paddedEncoding n N) (paddedState n N) :=
  parallelProgram_encoded_state _ _ _ _ _ _ _ _ (launchProgram_state n N) (padProgram_state n)

lemma paddedEncoding_injective (n N : ℕ) : Function.Injective (paddedEncoding n N) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have he : (launchEncoding n N a,tensorLayout n (padding n) b)=
      (launchEncoding n N c,tensorLayout n (padding n) d) := (appendEquiv _ _).injective h
  have hac:=launchEncoding_injective n N (congrArg Prod.fst he)
  have hbd:=(tensorLayout n (padding n)).injective (congrArg Prod.snd he)
  cases hac
  cases hbd
  rfl

lemma launchProgram_length (n : ℕ) : (launchProgram n).length≤
    4*launchWork n+2*width n+((machine n).program (steps n)).length :=
  preparedOracle_length _ _ _
lemma paddedProgram_length (n : ℕ) : (paddedProgram n).length≤
    4*launchWork n+2*width n+((machine n).program (steps n)).length+padding n*n := by
  rw [paddedProgram,parallelProgram_length,padProgram_length]
  exact Nat.add_le_add_right (launchProgram_length n) _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeQuarterPhysical.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

lemma hadamards_zero_encoded (q : ℕ) :
    (programMatrix (hadamardPrefix q q le_rfl)).mulVec (basisVector (fun _=>false))=
      encodeState id (fairState q) := by
  funext x
  rw [hadamards_zero]
  exact (encodeState_at id Function.injective_id (fairState q) x).symm

namespace Completion
/-- The actual four-register completion, when the ordinary preparation has
retained and injectively encoded its full history. -/
def extendEncoding {α : Type*} {q : ℕ} (e : α→Basis q) (W t d : ℕ) :
    Raw α W t d→Basis (t+(q+(W+coinBits W t d))) :=
  fun r=>Fin.append r.1 (Fin.append (e r.2.1) (Fin.append r.2.2.1 r.2.2.2))

lemma extendEncoding_injective {α : Type*} {q : ℕ} (e : α→Basis q)
    (he : Function.Injective e) (W t d : ℕ) : Function.Injective (extendEncoding e W t d) := by
  rintro ⟨a,b,c,h⟩ ⟨a',b',c',h'⟩ hh
  have H : (a,Fin.append (e b) (Fin.append c h))=
      (a',Fin.append (e b') (Fin.append c' h')) :=
    (appendEquiv t (q+(W+coinBits W t d))).injective hh
  have ha:=congrArg Prod.fst H
  have H' : (e b,Fin.append c h)=(e b',Fin.append c' h') :=
    (appendEquiv q (W+coinBits W t d)).injective (congrArg Prod.snd H)
  have hb:=he (congrArg Prod.fst H')
  have H'' : (c,h)=(c',h') :=
    (appendEquiv W (coinBits W t d)).injective (congrArg Prod.snd H')
  have hc:=congrArg Prod.fst H''
  have hd:=congrArg Prod.snd H''
  cases ha; cases hb; cases hc; cases hd; rfl

lemma program_encoded_state {α : Type*} [Fintype α] {q : ℕ}
    (P : List (Instruction q)) (e : α→Basis q) (ψ : α→ℂ) (z : Basis q)
    (hP : (programMatrix P).mulVec (basisVector z)=encodeState e ψ) (W t d : ℕ) :
    (programMatrix (program P W t d)).mulVec
      (basisVector (layout q W t d ((fun _=>false),z,(fun _=>false),(fun _=>false))))=
      encodeState (extendEncoding e W t d) (fresh ψ W t d) := by
  let D:=coinBits W t d
  have hG := parallelProgram_encoded_state
    (hadamardPrefix W W le_rfl) (hadamardPrefix D D le_rfl)
    (fun _=>false) (fun _=>false) id id (fairState W) (fairState D)
    (hadamards_zero_encoded W) (hadamards_zero_encoded D)
  have hO := parallelProgram_encoded_state P
    (parallelProgram (hadamardPrefix W W le_rfl) (hadamardPrefix D D le_rfl))
    z (Fin.append (fun _ : Fin W=>false) (fun _ : Fin D=>false)) e
    (fun r : Basis W×Basis D=>Fin.append r.1 r.2) ψ
    (independentState (fairState W) (fairState D)) hP hG
  have hT := parallelProgram_encoded_state
    (hadamardPrefix t t le_rfl)
    (parallelProgram P (parallelProgram (hadamardPrefix W W le_rfl) (hadamardPrefix D D le_rfl)))
    (fun _=>false) (Fin.append z (Fin.append (fun _ : Fin W=>false) (fun _ : Fin D=>false)))
    id (fun r : α×(Basis W×Basis D)=>Fin.append (e r.1) (Fin.append r.2.1 r.2.2))
    (fairState t) (independentState ψ (independentState (fairState W) (fairState D)))
    (hadamards_zero_encoded t) hO
  exact hT
end Completion

namespace PhysicalTree
abbrev quarterWidth (n : ℕ) := 1+(paddedWidth n+(n*n+Quarter.D n))
def quarterProgram (n : ℕ) : List (Instruction (quarterWidth n)) :=
  Quarter.program (paddedProgram n) n
def quarterZero (n N : ℕ) : Basis (quarterWidth n) :=
  Completion.layout (paddedWidth n) (n*n) 1 (n^11)
    ((fun _=>false),paddedZero n N,(fun _=>false),(fun _=>false))
def quarterEncoding (n N : ℕ) : Quarter.Raw (PaddedRaw n) n→Basis (quarterWidth n) :=
  Completion.extendEncoding (paddedEncoding n N) (n*n) 1 (n^11)

lemma quarterProgram_state (n N : ℕ) :
    (programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))=
      encodeState (quarterEncoding n N) (Quarter.fresh (paddedState n N) n) :=
  Completion.program_encoded_state _ _ _ _ (paddedProgram_state n N) _ _ _
lemma quarterEncoding_injective (n N : ℕ) : Function.Injective (quarterEncoding n N) :=
  Completion.extendEncoding_injective _ (paddedEncoding_injective n N) _ _ _
lemma quarterProgram_length (n : ℕ) :
    (quarterProgram n).length=(paddedProgram n).length+1+n*n+Quarter.D n :=
  Quarter.program_length _ _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedQuarterFilter.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

def launchHistory (n : ℕ) : BooleanNetwork (launchWidth n) (width n) :=
  select (targetRegister n (width n) (launchWork n))
def launchInput (n : ℕ) : BooleanNetwork (launchWidth n) n :=
  select (firstRegister n (width n) (launchWork n))
def paddedHistory (n : ℕ) : BooleanNetwork (paddedWidth n) (width n) :=
  (select (Fin.castAdd (tensorWidth n (padding n)))).comp (launchHistory n)
def paddedInput (n : ℕ) : BooleanNetwork (paddedWidth n) n :=
  (select (Fin.castAdd (tensorWidth n (padding n)))).comp (launchInput n)
def paddedPad (n : ℕ) : BooleanNetwork (paddedWidth n) (tensorWidth n (padding n)) :=
  select (Fin.natAdd (launchWidth n))

lemma paddedHistory_eval (n N : ℕ) (r : PaddedRaw n) :
    (paddedHistory n).eval (paddedEncoding n N r)=
      (machine n).encoded (initialQueue n N) (2*n^2) r.1 := by
  simp only [paddedHistory,eval_comp,eval_select,Function.comp_def,paddedEncoding,
    Fin.append_left,launchHistory,launchEncoding]
  exact packed_targetRegister _ _
lemma paddedInput_eval (n N : ℕ) (r : PaddedRaw n) :
    (paddedInput n).eval (paddedEncoding n N r)=natBasis n N := by
  simp only [paddedInput,eval_comp,eval_select,Function.comp_def,paddedEncoding,
    Fin.append_left,launchInput,launchEncoding]
  exact packed_first _ _
lemma paddedPad_eval (n N : ℕ) (r : PaddedRaw n) :
    (paddedPad n).eval (paddedEncoding n N r)=tensorLayout n (padding n) r.2 := by
  funext i
  simp only [paddedPad,eval_select,Function.comp_apply,paddedEncoding,Fin.append_right]

def padFlag (n : ℕ) : BooleanNetwork (tensorWidth n (padding n)) 1 :=
  all (List.ofFn (fun i : Fin (padding n)=>(zeroWord (tensorSelect n (padding n) i)).bnot))
lemma padFlag_eval (n : ℕ) (r : PadRaw n) :
    (padFlag n).eval (tensorLayout n (padding n) r) 0=true ↔ padPassed r := by
  simp only [padFlag,all_eval,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,
    bnot_value,zeroWord_value,tensorSelect_eval,padPassed,Completion.rare]

def paddedFlag (n : ℕ) (hn : 0<n) : BooleanNetwork (paddedWidth n) 1 :=
  ((paddedHistory n).comp ((machine n).acceptedNet hn (2*n^2))).band
    ((paddedPad n).comp (padFlag n))
lemma paddedFlag_eval {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : PaddedRaw n) :
    (paddedFlag n (by omega)).eval (paddedEncoding n N r) 0=true ↔
      paddedAccepted (N:=N) (by omega) r := by
  rw [paddedFlag,eval_band,Bool.and_eq_true,eval_comp,paddedHistory_eval,
    acceptedNet_iff_accepted hn hN hb,eval_comp,paddedPad_eval,padFlag_eval]
  rfl

def quarterOrd (n : ℕ) := Completion.ordinaryWires (paddedWidth n) (n*n) 1 (n^11)
def quarterGuess (n : ℕ) := Completion.guessWires (paddedWidth n) (n*n) 1 (n^11)
def quarterCoin (n : ℕ) := Completion.retentionWires (paddedWidth n) (n*n) 1 (n^11)
def quarterRare (n : ℕ) := Completion.rareNet (paddedWidth n) (n*n) 1 (n^11)

lemma quarterOrd_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterOrd n).eval (quarterEncoding n N r)=paddedEncoding n N r.2.1 :=
  Completion.ordinaryWires_eval (r.1,paddedEncoding n N r.2.1,r.2.2)
lemma quarterGuess_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterGuess n).eval (quarterEncoding n N r)=r.2.2.1 :=
  Completion.guessWires_eval (r.1,paddedEncoding n N r.2.1,r.2.2)
lemma quarterCoin_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterCoin n).eval (quarterEncoding n N r)=r.2.2.2 :=
  Completion.retentionWires_eval (r.1,paddedEncoding n N r.2.1,r.2.2)
lemma quarterRare_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterRare n).eval (quarterEncoding n N r) 0=true ↔ Completion.rare r.1 :=
  Completion.rareNet_eval (r.1,paddedEncoding n N r.2.1,r.2.2)

def quarterKeep (n : ℕ) (p : ℚ) : BooleanNetwork (quarterWidth n) 1 :=
  retentionNet (Quarter.D n) (.const p) (.var ()) (fun _ : Unit=>quarterCoin n)
lemma quarterKeep_eval (n N : ℕ) (p : ℚ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterKeep n p).eval (quarterEncoding n N r) 0=true ↔
      Completion.threshold p r.2.2.2 := by
  rw [quarterKeep,retentionNet_value]
  simp only [RatExpr.eval_const,NatExpr.eval,quarterCoin_eval,Completion.threshold]

def quarterGuessFlag (n : ℕ) : BooleanNetwork (quarterWidth n) 1 :=
  ((((quarterOrd n).comp (paddedInput n)).pair (quarterGuess n))).comp (guessVerifier n)
lemma quarterGuessFlag_eval {n N : ℕ} (hn : 128≤n) (hb : N<2^n)
    (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterGuessFlag n).eval (quarterEncoding n N r) 0=true ↔
      CorrectEncoding N n (guessWords n r.2.2.1) := by
  rw [quarterGuessFlag,eval_comp,eval_pair,eval_comp,quarterOrd_eval,paddedInput_eval,
    quarterGuess_eval,guessVerifier_correct hn,natBasis_value,Nat.mod_eq_of_lt hb]

def quarterFlag (n : ℕ) (hn : 0<n) : BooleanNetwork (quarterWidth n) 1 :=
  ((quarterRare n).bnot.band
    (((quarterOrd n).comp (paddedFlag n hn)).band (quarterKeep n (Quarter.retention n)))).bor
    ((quarterRare n).band ((quarterGuessFlag n).band (quarterKeep n (Quarter.guessRetention n))))

/-- The literal Boolean flag for the source's exact quarter event. All factor
and order tests read the actual retained history, not an ideal initialized table. -/
theorem quarterFlag_eval {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterFlag n (by omega)).eval (quarterEncoding n N r) 0=true ↔
      Quarter.passed N (paddedAccepted (N:=N) (by omega)) r := by
  simp only [quarterFlag,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    bnot_value,quarterRare_eval,eval_comp,quarterOrd_eval,
    paddedFlag_eval hn hN hb,quarterKeep_eval,quarterGuessFlag_eval hn hb,
    Quarter.passed,Quarter.ordinaryPass,Quarter.guessPass]

def paddedOutputNet (n : ℕ) : BooleanNetwork (paddedWidth n) (n*n) :=
  (paddedHistory n).comp (rootFlat n (2*n^2))
def quarterOutputNet (n : ℕ) : BooleanNetwork (quarterWidth n) (n*n) :=
  Completion.outputNet (paddedOutputNet n) 1 (n^11)
lemma quarterOutputNet_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterOutputNet n).eval (quarterEncoding n N r)=
      Completion.output (ordinaryOutput n N) r := by
  rw [quarterOutputNet]
  change (Completion.outputNet (paddedOutputNet n) 1 (n^11)).eval
    (Completion.layout _ _ _ _ (r.1,paddedEncoding n N r.2.1,r.2.2))=_
  rw [Completion.outputNet_eval]
  simp only [Completion.output,paddedOutputNet,eval_comp,paddedHistory_eval,ordinaryOutput]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExactnessFurther2.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace ExactQuantumFactoring
open scoped BigOperators

namespace Exactness

lemma RespectsSector.one {ι : Type*} [DecidableEq ι] (S : ι→Prop) :
    RespectsSector S (1 : Matrix ι ι ℂ) := by
  intro x y h
  have hxy : x≠y := fun he => h (he ▸ Iff.rfl)
  simp [hxy]

lemma RespectsSector.mul {ι : Type*} [Fintype ι] (S : ι→Prop)
    (U V : Matrix ι ι ℂ) (hU : RespectsSector S U) (hV : RespectsSector S V) :
    RespectsSector S (U*V) := by
  classical
  intro x y hxy
  apply Finset.sum_eq_zero
  intro z _
  change U x z*V z y=0
  by_cases hxz : S x↔S z
  · rw [hV z y (fun hzy => hxy (hxz.trans hzy)),mul_zero]
  · rw [hU x z hxz,zero_mul]

end Exactness
open Exactness

/-- A syntactic read-only rule suffices; no hypothesis about the state prepared
by the algorithm or its unknown factors occurs here. -/
def ReadOnly {q : ℕ} (inputs : Finset (Fin q)) (P : List (Instruction q)) : Prop :=
  ∀ o∈P,o.target∉inputs

def inputSector {q : ℕ} (inputs : Finset (Fin q)) (z x : Basis q) : Prop :=
  ∀ i∈inputs,x i=z i

lemma Instruction.respects_input {q : ℕ} (o : Instruction q) (inputs : Finset (Fin q))
    (ht : o.target∉inputs) (z : Basis q) : RespectsSector (inputSector inputs z) o.matrix := by
  intro x y hxy
  by_contra hne
  apply hxy
  have he (i : Fin q) (hi : i∈inputs) : x i=y i :=
    o.nonzero_eq x y hne i (fun h => ht (h ▸ hi))
  constructor
  · intro hx i hi
    rw [←he i hi]
    exact hx i hi
  · intro hy i hi
    rw [he i hi]
    exact hy i hi

lemma program_respects_input {q : ℕ} (inputs : Finset (Fin q))
    (P : List (Instruction q)) (hP : ReadOnly inputs P) (z : Basis q) :
    RespectsSector (inputSector inputs z) (programMatrix P) := by
  induction P with
  | nil => exact RespectsSector.one _
  | cons o P ih =>
    rw [programMatrix_cons]
    exact RespectsSector.mul _ _ _
      (ih (fun p hp => hP p (by simp [hp])))
      (o.respects_input inputs (hP o (by simp)) z)

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OracleReadOnly.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

@[simp] lemma Instruction.target_reverse {q : ℕ} (o : Instruction q) : o.reverse.target=o.target := rfl
@[simp] lemma Instruction.target_place {p q : ℕ} (w : Register p q) (o : Instruction p) :
    (o.place w).target=w o.target := rfl
@[simp] lemma notAt_target {q : ℕ} (t : Fin q) : (notAt t).target=t := rfl
@[simp] lemma cnotAt_target {q : ℕ} (a t : Fin q) (ha : a≠t) : (cnotAt a t ha).target=t := rfl
@[simp] lemma toffoliAt_target {q : ℕ} (a b t : Fin q) (hab : a≠b) (hat : a≠t) (hbt : b≠t) :
    (toffoliAt a b t hab hat hbt).target=t := rfl

lemma BooleanOp.compile_target {q : ℕ} {t : Fin q} (b : BooleanOp q t) :
    ∀ o∈b.compile,o.target=t := by
  cases b with
  | constant b=>cases b <;> simp [BooleanOp.compile]
  | copy=>simp [BooleanOp.compile]
  | neg=>simp [BooleanOp.compile]
  | conj a b ha hb=>simp only [BooleanOp.compile];split_ifs <;> simp

lemma BooleanProgram.compile_target {q n : ℕ} (P : BooleanProgram q)
    (h : ∀ a∈P,n≤a.1.val) : ∀ o∈P.compile,n≤o.target.val := by
  intro o ho
  obtain ⟨a,ha,ho⟩:=List.mem_flatMap.mp ho
  rw [a.2.compile_target o ho]
  exact h a ha

lemma BoolNet.program_target {n k q : ℕ} (p : BoolNet n k) (h : k≤q) :
    ∀ a∈p.program h,n≤a.1.val := by
  induction p with
  | input=>simp [BoolNet.program]
  | @add k p b ih=>
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact ih (by omega) a ha
    · have he:=List.mem_singleton.mp ha
      subst a
      exact p.input_le

lemma BooleanNetwork.copyPrefix_target {k m : ℕ} (f : Fin m→Fin k) (t : ℕ) (h : t ≤ m) :
    ∀ a∈copyPrefix f t h,k≤a.1.val := by
  induction t with
  | zero=>simp [copyPrefix]
  | succ t ih=>
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact ih (by omega) a ha
    · have he:=List.mem_singleton.mp ha
      subst a
      simp

lemma BooleanNetwork.oracle_target {n m : ℕ} (c : BooleanNetwork n m) :
    ∀ o∈c.oracle,n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · rcases List.mem_append.mp ho with ho|ho
    · exact BooleanProgram.compile_target _ (c.net.program_target _) o ho
    · exact c.net.input_le.trans (BooleanProgram.compile_target _
        (copyPrefix_target _ _ _) o ho)
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
    rw [Instruction.target_reverse]
    exact BooleanProgram.compile_target _ (c.net.program_target _) a (List.mem_reverse.mp ha)

/-- Compute/copy/uncompute never targets a read-only input, including on
malformed scratch states. This global property is what reflection needs. -/
lemma BooleanNetwork.oracleOn_target {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count≤r) :
    ∀ o∈oracleOn c hr,n≤o.target.val := by
  intro o ho
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
  rw [Instruction.target_place,oraclePlacement_val]
  have hn:=c.oracle_target a ha
  simp only [oracleIndex,ite_eq_right (Nat.not_lt.mpr hn)]
  split_ifs <;> omega

lemma targetProgram_target {n m r : ℕ} (P : List (Instruction m)) :
    ∀ o∈targetProgram n r P,n≤o.target.val := by
  intro o ho
  obtain ⟨a,_ha,rfl⟩:=List.mem_map.mp ho
  rw [Instruction.target_place,targetRegister_val]
  omega

lemma preparedOracle_target {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count≤r)
    (P : List (Instruction m)) : ∀ o∈preparedOracle c hr P,n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · exact c.oracleOn_target hr o ho
  · exact targetProgram_target P o ho

/-- The bit prefix is preserved for every input sector, without any data
correctness or clean-work premise. -/
lemma preparedOracle_readOnly {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count≤r)
    (P : List (Instruction m)) :
    ReadOnly (Finset.univ.filter (fun i : Fin (n+m+r)=>i.val<n)) (preparedOracle c hr P) := by
  intro o ho hi
  have hn:=preparedOracle_target c hr P o ho
  have hl:=(Finset.mem_filter.mp hi).2
  omega

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeReadOnly.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork Exactness

/-- Parallel fresh work does not alter the prefix protected by the left program. -/
lemma parallelProgram_prefix_target {p q n : ℕ} (P : List (Instruction p))
    (Q : List (Instruction q)) (hn : n≤p) (hP : ∀ o∈P,n≤o.target.val) :
    ∀ o∈parallelProgram P Q,n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
    have ha':=hP a ha
    simpa only [Instruction.target_place,leftRegister,Function.Embedding.coeFn_mk,
      Fin.val_castAdd] using ha'
  · obtain ⟨a,_ha,rfl⟩:=List.mem_map.mp ho
    change n≤p+a.target.val
    omega

/-- The branch register preceding an otherwise read-only prefix introduces
only targets before that prefix, never in it. -/
lemma parallelProgram_interval_target {p q n : ℕ} (P : List (Instruction p))
    (Q : List (Instruction q)) (hQ : ∀ o∈Q,n≤o.target.val) :
    ∀ o∈parallelProgram P Q,o.target.val<p ∨ p+n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · obtain ⟨a,_ha,rfl⟩:=List.mem_map.mp ho
    exact Or.inl a.target.isLt
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
    exact Or.inr (Nat.add_le_add_left (hQ a ha) p)

namespace PhysicalTree
lemma paddedProgram_prefix_target (n : ℕ) : ∀ o∈paddedProgram n,n≤o.target.val := by
  apply parallelProgram_prefix_target
  · dsimp only [launchWidth]
    omega
  · exact preparedOracle_target _ _ _

lemma quarterProgram_interval_target (n : ℕ) :
    ∀ o∈quarterProgram n,o.target.val<1 ∨ 1+n≤o.target.val := by
  apply parallelProgram_interval_target
  apply parallelProgram_prefix_target
  · dsimp only [paddedWidth,launchWidth]
    omega
  · exact paddedProgram_prefix_target n

/-- The original input is the n-wire interval immediately following the
fresh branch coin. This definition is independent of N. -/
def inputWires (n : ℕ) : Finset (Fin (quarterWidth n)) :=
  Finset.univ.filter (fun i => 1 ≤ i.val ∧ i.val < 1+n)

lemma quarterProgram_readOnly (n : ℕ) : ReadOnly (inputWires n) (quarterProgram n) := by
  intro o ho hi
  have ht:=quarterProgram_interval_target n o ho
  have hi':=(Finset.mem_filter.mp hi).2
  omega

/-- This is global input invariance, not merely a clean-input statement. -/
lemma quarterProgram_respects_input (n N : ℕ) :
    RespectsSector (inputSector (inputWires n) (quarterZero n N)) (programMatrix (quarterProgram n)) :=
  program_respects_input _ _ (quarterProgram_readOnly n) _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ZeroOutside.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork Exactness

/-- A linear-size clean-work flag, leaving every protected input bit alone. -/
def zeroOutside {q : ℕ} (I : Finset (Fin q)) : BooleanNetwork q 1 :=
  all (List.ofFn (fun i : Fin q => if i∈I then constant true else (bit i).bnot))

lemma zeroOutside_value {q : ℕ} (I : Finset (Fin q)) (x : Basis q) :
    (zeroOutside I).eval x 0=true ↔ ∀ i, i∉I → x i=false := by
  simp only [zeroOutside,all_eval,List.mem_ofFn]
  constructor
  · intro h i hi
    have hh:=h _ ⟨i,rfl⟩
    simpa only [ite_eq_right hi,eval_bnot,eval_bit,Bool.not_eq_true'] using hh
  · intro h c hc
    obtain ⟨i,rfl⟩:=hc
    by_cases hi : i∈I
    · simp only [ite_eq_left hi,eval_constant]
    · simp only [ite_eq_right hi,eval_bnot,eval_bit,h i hi,Bool.not_false]

lemma zeroOutside_count {q : ℕ} (I : Finset (Fin q)) : (zeroOutside I).net.count≤2*q+1 := by
  have h : ∀ c∈List.ofFn (fun i : Fin q => if i∈I then constant true else (bit i).bnot),
      c.net.count≤1 := by
    intro c hc
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc
    by_cases hi : i∈I
    · rw [ite_eq_left hi]
      exact le_rfl
    · rw [ite_eq_right hi]
      exact le_rfl
  simpa only [zeroOutside,List.length_ofFn,Nat.reduceAdd,Nat.mul_comm] using all_count _ h

lemma zeroOutside_sector {q : ℕ} (I : Finset (Fin q)) (z : Basis q)
    (hz : ∀ i, i∉I → z i=false) (x : Basis q) (hx : inputSector I z x) :
    (zeroOutside I).eval x 0=true ↔ x=z := by
  rw [zeroOutside_value]
  constructor
  · intro h
    funext i
    by_cases hi : i∈I
    · exact hx i hi
    · rw [h i hi,hz i hi]
  · rintro rfl
    exact hz

lemma tensorLayout_zero (q k : ℕ) :
    tensorLayout q k (fun _ _=>false)=(fun _=>false) := by
  induction k with
  | zero=>funext i;exact Fin.elim0 i
  | succ k ih=>
    rw [tensorLayout_succ]
    change Fin.append (fun _=>false) (tensorLayout q k (fun _ _=>false))=_
    rw [ih]
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [Fin.append_left,Fin.append_right]

namespace PhysicalTree
lemma launchZero_suffix (n N : ℕ) (i : Fin (launchWidth n)) (hi : n ≤ i.val) :
    launchZero n N i=false := by
  simp only [launchZero,packed,dite_eq_right (Nat.not_lt.mpr hi)]
  split_ifs <;> rfl

lemma paddedZero_suffix (n N : ℕ) (i : Fin (paddedWidth n)) (hi : n ≤ i.val) :
    paddedZero n N i=false := by
  revert hi
  refine Fin.addCases ?_ ?_ i
  · intro j hj
    simpa only [paddedZero,Fin.append_left] using launchZero_suffix n N j hj
  · intro j _hj
    simp only [paddedZero,Fin.append_right]
    change tensorLayout n (padding n) (fun _ _=>false) j=false
    rw [tensorLayout_zero]

lemma quarterZero_clean (n N : ℕ) (i : Fin (quarterWidth n)) (hi : i∉inputWires n) :
    quarterZero n N i=false := by
  revert hi
  refine Fin.addCases ?_ ?_ i
  · intro j _hj
    simp only [quarterZero,Completion.layout,productLayout_apply,Equiv.refl_apply,Fin.append_left]
  · intro j hj
    simp only [quarterZero,Completion.layout,productLayout_apply,Equiv.refl_apply,Fin.append_right]
    change Fin.append (paddedZero n N) (Fin.append (fun _ : Fin (n*n)=>false)
      (fun _ : Fin (Quarter.D n)=>false)) j=false
    have hn : n ≤ j.val := by
      have hh : ¬(1 ≤ 1+j.val ∧ 1+j.val < 1+n) := by
        simpa only [inputWires,Finset.mem_filter,Finset.mem_univ,true_and,
          Fin.val_natAdd] using hj
      omega
    clear hj
    revert hn
    refine Fin.addCases ?_ ?_ j
    · intro a ha
      simpa only [Fin.append_left] using paddedZero_suffix n N a ha
    · intro a _ha
      simp only [Fin.append_right]
      refine Fin.addCases ?_ ?_ a <;> intro j <;> simp only [Fin.append_left,Fin.append_right]

/-- The zero reflection's flag depends only on the length and the actual clean
work coordinates, never on the unknown integer or its factorization. -/
def zeroNet (n : ℕ) : BooleanNetwork (quarterWidth n) 1 := zeroOutside (inputWires n)

lemma zeroNet_count (n : ℕ) : (zeroNet n).net.count≤2*quarterWidth n+1 :=
  zeroOutside_count _

lemma zeroNet_sector (n N : ℕ) (x : Basis (quarterWidth n))
    (hx : inputSector (inputWires n) (quarterZero n N) x) :
    (zeroNet n).eval x 0=true ↔ x=quarterZero n N :=
  zeroOutside_sector _ _ (quarterZero_clean n N) _ hx

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
