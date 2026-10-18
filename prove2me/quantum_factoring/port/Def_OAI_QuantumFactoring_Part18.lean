/-
Exact quantum factoring development (port of OpenAI's formalization), part 18 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: OccurrenceQueue.lean, CanonicalWords.lean, PhysicalTreeCompletion.lean, TreeInitialization.lean, TreeHistoryAccess.lean, PhysicalTreeLaunch.lean, DivisorData.lean, RetrospectiveStatistics.lean, RetrospectiveResidues.lean, RetrospectiveLists.lean, RetrospectiveSlots.lean, NodeVerifiedCircuit.lean, VerifiedTreeCompletion.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part17

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OccurrenceQueue.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.AuxiliaryTree

/-- The full occurrence preorder; equal labels under different parents are
retained as different list elements. This is only a correctness invariant,
never used as the modulus-input physical circuit's initializer. -/
def preorder (m : ℕ) : List ℕ :=
  m::((children m).attach.flatMap (fun d=>preorder d.val))
termination_by m
decreasing_by exact (child_bounds d.property).2

lemma preorder_eq (m : ℕ) : preorder m=m::(children m).flatMap preorder := by
  rw [preorder]
  congr 1
  rw [List.flatMap_subtype (g:=preorder) (fun _ _=>rfl),List.unattach_attach]

lemma visits_eq_preorder {m depth : ℕ} (hd : level m depth=[]) :
    visits depth m=preorder m := by
  induction depth generalizing m with
  | zero=>simp only [level,List.cons_ne_self] at hd
  | succ d ih=>
    rw [visits,preorder_eq]
    congr 1
    apply List.flatMap_congr
    intro a ha
    exact ih (DataProducer.child_level_empty hd ha)

lemma preorder_length_le {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) :
    (preorder m).length ≤ 2*n^2 := by
  rw [←visits_eq_preorder (level_empty hm hb)]
  simpa only [pow_two,Nat.mul_assoc] using visits_length_le hm hb (2*n)

lemma preorder_nonempty (m : ℕ) : preorder m≠[] := by
  rw [preorder_eq]
  exact List.cons_ne_nil _ _

def forest (xs : List ℕ) : List ℕ := xs.flatMap preorder

def advance : List ℕ→List ℕ
  | []=>[]
  | m::ms=>children m++ms

lemma forest_advance (m : ℕ) (ms : List ℕ) :
    forest (m::ms)=m::forest (advance (m::ms)) := by
  simp only [forest,List.flatMap_cons,preorder_eq,List.cons_append,advance,List.flatMap_append]

lemma queue_length_le (xs : List ℕ) : xs.length ≤ (forest xs).length := by
  induction xs with
  | nil=>simp [forest]
  | cons m ms ih=>
    rw [forest_advance,List.length_cons,List.length_cons]
    have he : (forest (advance (m::ms))).length=
        ((children m).flatMap preorder).length+(forest ms).length := by
      simp only [forest,advance,List.flatMap_append,List.length_append]
    rw [he]
    omega

def run : ℕ→List ℕ→List ℕ
  | 0,xs=>xs
  | t+1,xs=>run t (advance xs)

lemma forest_run (t : ℕ) (xs : List ℕ) : forest (run t xs)=(forest xs).drop t := by
  induction t generalizing xs with
  | zero=>rfl
  | succ t ih=>
    rw [run,ih]
    cases xs with
    | nil=>simp [advance,forest]
    | cons m ms=>rw [forest_advance,List.drop_succ_cons]

lemma forest_eq_nil_iff {xs : List ℕ} : forest xs=[] ↔ xs=[] := by
  constructor
  · intro h
    have hh := queue_length_le xs
    rw [h,List.length_nil] at hh
    exact List.eq_nil_of_length_eq_zero (by omega)
  · rintro rfl
    rfl

/-- Exactly the polynomial clock used by the physical queue suffices for EVERY
occurrence, not just every distinct label. -/
theorem run_complete {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) : run (2*n^2) [m]=[] := by
  apply forest_eq_nil_iff.mp
  rw [forest_run]
  have he : forest [m]=preorder m := by simp [forest]
  rw [he]
  exact List.drop_eq_nil_of_le (preorder_length_le hm hb)

lemma run_queue_length {m n t : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) :
    (run t [m]).length ≤ 2*n^2 := by
  have h := queue_length_le (run t [m])
  rw [forest_run] at h
  have he : forest [m]=preorder m := by simp [forest]
  rw [he,List.length_drop] at h
  exact h.trans ((Nat.sub_le _ _).trans (preorder_length_le hm hb))

lemma advance_bounds {xs : List ℕ} {B : ℕ} (hx : ∀ a∈xs,2 ≤ a ∧ a < B) :
    ∀ a∈advance xs,2 ≤ a ∧ a < B := by
  cases xs with
  | nil=>simp [advance]
  | cons m ms=>
    intro a ha
    have hm := hx m (by simp)
    rcases List.mem_append.mp ha with hd | ht
    · have hb := child_bounds hd
      exact ⟨hb.1,hb.2.trans hm.2⟩
    · exact hx a (by simp [ht])

lemma run_bounds {xs : List ℕ} {B : ℕ} (hx : ∀ a∈xs,2 ≤ a ∧ a < B) (t : ℕ) :
    ∀ a∈run t xs,2 ≤ a ∧ a < B := by
  induction t generalizing xs with
  | zero=>exact hx
  | succ t ih=>exact ih (advance_bounds hx)

lemma run_succ_right (t : ℕ) (xs : List ℕ) : run (t+1) xs=advance (run t xs) := by
  induction t generalizing xs with
  | zero=>rfl
  | succ t ih=>rw [run,ih];rfl

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CanonicalWords.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open OrderTrial SortedWords

def canonicalWords (n : ℕ) (xs : List ℕ) : List (Basis n) := xs.map (natBasis n)

lemma natBasis_number {n : ℕ} (a : Basis n) : natBasis n (bitsValue a).toNat=a := by
  apply (bitsEquiv n).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue (natBasis n (bitsValue a).toNat)).toNat=(bitsValue a).toNat
  rw [natBasis_value,Nat.mod_eq_of_lt (bitsValue a).isLt]

lemma canonical_numbers {n : ℕ} (xs : List (Basis n)) : canonicalWords n (numbers xs)=xs := by
  simp only [canonicalWords,numbers,List.map_map,Function.comp_def,natBasis_number]
  exact List.map_id xs

lemma numbers_canonical {n : ℕ} (xs : List ℕ) (hb : ∀ a∈xs,a < 2^n) :
    numbers (canonicalWords n xs)=xs := by
  simp only [canonicalWords,numbers,List.map_map]
  calc
    _ = xs.map id := List.map_congr_left (fun a ha=>by
      simp only [Function.comp_apply,natBasis_value,Nat.mod_eq_of_lt (hb a ha),id_eq])
    _ = xs := List.map_id xs

lemma canonical_length (n : ℕ) (xs : List ℕ) : (canonicalWords n xs).length=xs.length := List.length_map (natBasis n)
lemma canonical_append (n : ℕ) (xs ys : List ℕ) :
    canonicalWords n (xs++ys)=canonicalWords n xs++canonicalWords n ys := List.map_append

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalTreeCompletion.lean =====
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

def machine (n : ℕ) : NodeMachine n (configWidth n) := ⟨query n,update n⟩
def initialQueue (n N : ℕ) : Basis (configWidth n) :=
  stackEncoding (capacity n) n (canonicalWords n [N])

/-- On the actual all-passed raw history, the literal physical pending queue is
exactly the remaining canonical occurrence preorder. This is a proof invariant,
not a precomputed queue or advice to the circuit. -/
theorem queue_invariant {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hp : (machine n).passed (initialQueue n N) t h) :
    (machine n).config (initialQueue n N) t h=
      stackEncoding (capacity n) n (canonicalWords n (AuxiliaryTree.run t [N])) := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    obtain ⟨h,r⟩ := h
    have hi := ih h hp.1
    have hbounds := AuxiliaryTree.run_bounds (xs:=[N]) (B:=2^n)
      (by
        intro a ha
        have he : a=N := by simpa using ha
        subst a
        exact ⟨hN,hb⟩) t
    have hlen := AuxiliaryTree.run_queue_length (t:=t) hN hb
    rw [NodeMachine.config,NodeMachine.next,hi]
    change (update n).eval (Fin.append _ (NodeKernel.encoding ((query n).eval _) r))=_
    cases he : AuxiliaryTree.run t [N] with
    | nil=>
      change (update n).eval (Fin.append (stackEncoding (capacity n) n []) _)=_
      rw [update_nil,AuxiliaryTree.run_succ_right,he]
      rfl
    | cons m ms=>
      have hm := hbounds m (by rw [he];simp)
      have hv : (bitsValue (natBasis n m)).toNat=m := by rw [natBasis_value,Nat.mod_eq_of_lt hm.2]
      have hc : (natBasis n m::canonicalWords n ms).length ≤ capacity n := by
        rw [he,List.length_cons] at hlen
        simp only [List.length_cons,canonical_length]
        unfold capacity
        omega
      have hr : NodeKernel.passed (natBasis n m) r := by
        have hh := hp.2
        change NodeKernel.passed ((query n).eval ((machine n).config (initialQueue n N) t h)) r at hh
        rw [hi,he] at hh
        change NodeKernel.passed ((query n).eval (stackEncoding (capacity n) n
          (natBasis n m::canonicalWords n ms))) r at hh
        rw [query_encoding] at hh
        exact hh
      obtain ⟨ks,hk,hu⟩ := update_passed hn (natBasis n m) (canonicalWords n ms) hc
        (by rw [hv];exact hm.1) r hr
      have hks : ks=canonicalWords n (AuxiliaryTree.children m) := by
        rw [hv] at hk
        rw [←canonical_numbers ks,hk]
      change (update n).eval (Fin.append (stackEncoding (capacity n) n
        (natBasis n m::canonicalWords n ms))
          (NodeKernel.encoding ((query n).eval (stackEncoding (capacity n) n
            (natBasis n m::canonicalWords n ms))) r))=_
      rw [query_encoding,hu,hks,AuxiliaryTree.run_succ_right,he]
      change stackEncoding (capacity n) n
        (canonicalWords n (AuxiliaryTree.children m)++canonicalWords n ms)=
        stackEncoding (capacity n) n (canonicalWords n (AuxiliaryTree.children m++ms))
      rw [canonical_append]

/-- The full actual tree controller terminates in the source's polynomial
occurrence cap, with no truncation on a passing history. The circuit nevertheless
has fixed worst-case dimensions on all other histories as well. -/
theorem complete {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (h : NodeMachine.Trace n (2*n^2))
    (hp : (machine n).passed (initialQueue n N) (2*n^2) h) :
    (machine n).config (initialQueue n N) (2*n^2) h=stackEncoding (capacity n) n [] := by
  rw [queue_invariant hn hN hb _ h hp,AuxiliaryTree.run_complete hN hb]
  rfl

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeInitialization.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Literal clean initialization: retain the runtime controller word and create
only zero history/output/scratch fields. No query result is precomputed. -/
def initialNet : (t : ℕ) → BooleanNetwork c (M.width t)
  | 0 => select id
  | t+1 => packNet M.updateWork
      (packNet M.initWork (initialNet t) (Completion.zeros c (NodeKernel.width n)))
      (Completion.zeros c c)

lemma initialNet_eval (t : ℕ) (x : Basis c) :
    (M.initialNet t).eval x=M.initial t x := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    rw [initialNet,packNet_eval,packNet_eval,Completion.zeros_eval,Completion.zeros_eval,ih]
    rfl

lemma initialNet_count (t : ℕ) : (M.initialNet t).net.count=
    t*(NodeKernel.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [initialNet, count_select]
  | succ t ih=>
    simp only [initialNet,packNet_count,Completion.zeros_count,ih]
    ring

/-- A whole fixed-period machine can itself be launched coherently from a
Boolean-computed runtime controller state, retaining earlier history exactly. -/
theorem launch_on_history {α : Type*} [Fintype α] {p r : ℕ}
    (e : α→Basis p) (ψ : α→ℂ) (v : BooleanNetwork p c) (t : ℕ)
    (hc : (v.comp (M.initialNet t)).net.count ≤ r) :
    (programMatrix (preparedOracle (v.comp (M.initialNet t)) hc (M.program t))).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
      encodeState (fun ar : α×Trace n t => packed r (e ar.1)
        (M.encoded (v.eval (e ar.1)) t ar.2))
        (RecordedHistory.appendState ψ (fun a=>M.state (v.eval (e a)) t)) := by
  apply preparedOracle_encode_dependent e (fun a=>M.encoded (v.eval (e a)) t) ψ
    (fun a=>M.state (v.eval (e a)) t) (v.comp (M.initialNet t)) hc (M.program t)
  intro a
  rw [eval_comp,M.initialNet_eval,M.program_state]

end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeHistoryAccess.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Access only retained earlier wires. No history is recomputed. -/
def previousNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (M.width t) :=
  (select (firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork)).comp
    (select (firstRegister (M.width t) (NodeKernel.width n) M.initWork))
def lastNodeNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (NodeKernel.width n) :=
  (select (firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork)).comp
    (select (targetRegister (M.width t) (NodeKernel.width n) M.initWork))

lemma previousNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.previousNet t).eval (M.encoded x (t+1) (h,r))=M.encoded x t h := by
  rw [previousNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (NodeKernel.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) ∘
      firstRegister (M.width t) (NodeKernel.width n) M.initWork=_
  rw [packed_first,packed_first]
lemma lastNodeNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.lastNodeNet t).eval (M.encoded x (t+1) (h,r))=
      NodeKernel.encoding (M.query.eval (M.config x t h)) r := by
  rw [lastNodeNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (NodeKernel.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) ∘
      targetRegister (M.width t) (NodeKernel.width n) M.initWork=_
  rw [packed_first,packed_targetRegister]

def firstNodeNet : (t : ℕ)→BooleanNetwork (M.width (t+1)) (NodeKernel.width n)
  | 0=>M.lastNodeNet 0
  | t+1=>(M.previousNet (t+1)).comp (firstNodeNet t)
def firstRaw : (t : ℕ)→Trace n (t+1)→NodeKernel.Raw n
  | 0,h=>h.2
  | t+1,h=>firstRaw t h.1
lemma firstNodeNet_encoded (x : Basis c) (t : ℕ) (h : Trace n (t+1)) :
    (M.firstNodeNet t).eval (M.encoded x (t+1) h)=NodeKernel.encoding (M.query.eval x) (firstRaw t h) := by
  induction t with
  | zero=>exact M.lastNodeNet_encoded x 0 h.1 h.2
  | succ t ih=>
    rw [firstNodeNet,eval_comp,M.previousNet_encoded,ih]
    rfl
lemma first_passed (x : Basis c) (t : ℕ) (h : Trace n (t+1))
    (hp : M.passed x (t+1) h) : NodeKernel.passed (M.query.eval x) (firstRaw t h) := by
  induction t with
  | zero=>exact hp.2
  | succ t ih=>exact ih h.1 hp.1
lemma firstNodeNet_count (t : ℕ) : (M.firstNodeNet t).net.count=0 := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [firstNodeNet,count_comp,previousNet,count_comp,count_select,ih,add_zero]

end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalTreeLaunch.lean =====
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

def startNet (n : ℕ) : BooleanNetwork n (configWidth n) :=
  stackPush (select id) (Completion.zeros n (configWidth n))
lemma startNet_eval (n : ℕ) (a : Basis n) :
    (startNet n).eval a=stackEncoding (capacity n) n [a] := by
  rw [startNet,stackPush_encoding _ _ _ [] (by rw [Completion.zeros_eval];rfl)]
  rfl
lemma startNet_nat {n N : ℕ} : (startNet n).eval (natBasis n N)=initialQueue n N := by
  rw [startNet_eval]
  rfl
abbrev steps (n : ℕ) := 2*n^2
abbrev width (n : ℕ) := (machine n).width (steps n)
def initialNet (n : ℕ) : BooleanNetwork n (width n) :=
  (startNet n).comp ((machine n).initialNet (steps n))
lemma initialNet_eval {n N : ℕ} : (initialNet n).eval (natBasis n N)=
    (machine n).initial (steps n) (initialQueue n N) := by
  rw [initialNet,eval_comp,NodeMachine.initialNet_eval,startNet_nat]

/-- Literal runtime-input initialization and physical chronological tree
construction, coherently over all input words. No factors initialize the input. -/
theorem launch {n p r : ℕ} {α : Type*} [Fintype α] (e : α→Basis p) (ψ : α→ℂ)
    (input : BooleanNetwork p n) (hc : (input.comp (initialNet n)).net.count ≤ r) :
    (programMatrix (preparedOracle (input.comp (initialNet n)) hc
      ((machine n).program (steps n)))).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun ar : α×NodeMachine.Trace n (steps n)=>packed r (e ar.1)
      ((machine n).encoded ((startNet n).eval (input.eval (e ar.1))) (steps n) ar.2))
      (RecordedHistory.appendState ψ (fun a=>(machine n).state
        ((startNet n).eval (input.eval (e a))) (steps n))) := by
  apply preparedOracle_encode_dependent e
    (fun a=>(machine n).encoded ((startNet n).eval (input.eval (e a))) (steps n)) ψ
    (fun a=>(machine n).state ((startNet n).eval (input.eval (e a))) (steps n))
    (input.comp (initialNet n)) hc ((machine n).program (steps n))
  intro a
  rw [eval_comp,initialNet,eval_comp,NodeMachine.initialNet_eval,NodeMachine.program_state]

/-- Actual root readout from earlier retained wires, not a factor-table lookup. -/
def rootResult (n t : ℕ) : BooleanNetwork ((machine n).width (t+1)) (tensorWidth n n) :=
  ((machine n).firstNodeNet t).comp (nodeResult n)

lemma query_initial (n N : ℕ) : (query n).eval (initialQueue n N)=natBasis n N :=
  query_encoding n (natBasis n N) []

/-- Every flagged chronological raw history has the literal sorted and padded
root encoding in the fixed root-output network. No other run supplies it. -/
theorem root_correct {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n (t+1))
    (hp : (machine n).passed (initialQueue n N) (t+1) h) :
    ∃ zs : List (Basis n), zs.length=n ∧ CorrectEncoding N n (SortedWords.numbers zs) ∧
      (rootResult n t).eval ((machine n).encoded (initialQueue n N) (t+1) h)=
        SortedWords.layout n n zs := by
  have hp0 := (machine n).first_passed (initialQueue n N) t h hp
  change NodeKernel.passed ((query n).eval (initialQueue n N)) (NodeMachine.firstRaw t h) at hp0
  rw [query_initial] at hp0
  have hv : (bitsValue (natBasis n N)).toNat=N := by rw [natBasis_value,Nat.mod_eq_of_lt hb]
  have hp' : (PhysicalNode.machine n (2*n)).passed
      (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) (NodeMachine.firstRaw t h) := by
    simpa only [NodeKernel.passed,NodeKernel.start,PhysicalNode.startNet_eval,hv] using hp0
  obtain ⟨zs,hl,hc,he⟩ := PhysicalNode.complete_output hn hN hb (NodeMachine.firstRaw t h) hp'
  refine ⟨zs,hl,hc,?_⟩
  rw [rootResult,eval_comp,NodeMachine.firstNodeNet_encoded]
  change (nodeResult n).eval (NodeKernel.encoding ((query n).eval (initialQueue n N))
    (NodeMachine.firstRaw t h))=_
  rw [query_initial,nodeResult,eval_comp,NodeKernel.encoding,SplitMachine.current_encoded,
    NodeKernel.start,PhysicalNode.startNet_eval,hv]
  exact he

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/DivisorData.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

/-- Expand ONLY the supplied exponent record. No factoring operation is hidden
in the list used by the retrospective controller. -/
def recordPrimes (f : FactorRecord) : List ℕ :=
  (f.support.sort (· ≤ ·)).flatMap (fun p => List.replicate (f p) p)

lemma recordPrimes_prime {f : FactorRecord} (hp : ∀ p∈f.support,p.Prime) :
    ∀ p∈recordPrimes f,p.Prime := by
  intro p h
  obtain ⟨q,hq,hp'⟩ := List.mem_flatMap.mp h
  have he : p=q := (List.mem_replicate.mp hp').2
  subst p
  exact hp q ((Finset.mem_sort (· ≤ ·)).mp hq)

lemma recordPrimes_prod (f : FactorRecord) : (recordPrimes f).prod=f.prod (·^·) := by
  rw [recordPrimes,prod_flatMap]
  simp only [List.prod_replicate]
  rw [←List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
  rfl

lemma recordPrimes_length (f : FactorRecord) : (recordPrimes f).length=f.sum (fun _ e => e) := by
  rw [recordPrimes,List.length_flatMap]
  simp only [List.length_replicate]
  rw [←List.sum_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
  rfl

/-- Divide a subfactor from the parent's prime list, in bounded time: there is
at most one division per prime occurrence in the already supplied list. -/
def divisorPrimes : ℕ→List ℕ→List ℕ
  | _, [] => []
  | m, p::ps => if p∣m then p::divisorPrimes (m/p) ps else divisorPrimes m ps

lemma divisorPrimes_length (m : ℕ) (ps : List ℕ) : (divisorPrimes m ps).length ≤ ps.length := by
  induction ps generalizing m with
  | nil => simp [divisorPrimes]
  | cons p ps ih =>
    rw [divisorPrimes]
    split_ifs
    · exact Nat.succ_le_succ (ih _)
    · exact (ih _).trans (by simp)

lemma divisorPrimes_prime (m : ℕ) (ps : List ℕ) (hp : ∀ p∈ps,p.Prime) :
    ∀ p∈divisorPrimes m ps,p.Prime := by
  induction ps generalizing m with
  | nil => simp [divisorPrimes]
  | cons p ps ih =>
    have htail : ∀ q∈ps,q.Prime := fun q hq => hp q (by simp [hq])
    rw [divisorPrimes]
    split_ifs
    · intro q hq
      rcases List.mem_cons.mp hq with he | hq
      · subst q; exact hp p (by simp)
      · exact ih _ htail q hq
    · exact ih _ htail

lemma divisorPrimes_prod (ps : List ℕ) (hp : ∀ p∈ps,p.Prime) {m : ℕ} (hd : m∣ps.prod) :
    (divisorPrimes m ps).prod=m := by
  induction ps generalizing m with
  | nil =>
    have hm := Nat.dvd_one.mp hd
    simp [divisorPrimes,hm]
  | cons p ps ih =>
    have hprime := hp p (by simp)
    have htail : ∀ q∈ps,q.Prime := fun q hq => hp q (by simp [hq])
    rw [divisorPrimes]
    split_ifs with hdiv
    · rw [List.prod_cons,ih htail (quotient_dvd_tail hprime.pos hdiv hd),Nat.mul_div_cancel' hdiv]
    · exact ih htail ((hprime.coprime_iff_not_dvd.mpr hdiv).symm.dvd_of_dvd_mul_left hd)

/-- Literal stored record projection, used only after complete-data validation. -/
def FactorData.factors : FactorData→FactorRecord
  | .node _ f _ => f

def FactorData.descendants : FactorData→List FactorData
  | .node _ _ ds => ds

@[simp] lemma trueData_factors (m : ℕ) : (trueData m).factors=m.factorization := by
  rw [trueData_eq]; rfl
@[simp] lemma trueData_descendants (m : ℕ) : (trueData m).descendants=(children m).map trueData := by
  rw [trueData_eq]; rfl

def dataDivisorPrimes (data : FactorData) (m : ℕ) : List ℕ :=
  divisorPrimes m (recordPrimes data.factors)

lemma dataDivisorPrimes_correct {M m : ℕ} (hM : 0<M) (hd : m∣M) :
    (∀ p∈dataDivisorPrimes (trueData M) m,p.Prime) ∧
      (dataDivisorPrimes (trueData M) m).prod=m := by
  have hp : ∀ p∈recordPrimes M.factorization,p.Prime :=
    recordPrimes_prime (fun _ => Nat.prime_of_mem_primeFactors)
  have hprod : (recordPrimes M.factorization).prod=M := by
    rw [recordPrimes_prod,Nat.prod_factorization_pow_eq_self hM.ne']
  refine ⟨?_,?_⟩
  · simpa only [dataDivisorPrimes,trueData_factors] using divisorPrimes_prime m _ hp
  · simpa only [dataDivisorPrimes,trueData_factors] using divisorPrimes_prod _ hp (show m∣(recordPrimes M.factorization).prod by rw [hprod]; exact hd)

/-- Child lookup takes the first matching stored occurrence. It does not compute
new children. Distinct parents deliberately retain separate occurrence data. -/
def dataChildPrimes (data : FactorData) (label : ℕ) : List ℕ :=
  match data.descendants.find? (fun d => decide (d.label=label)) with
  | none => []
  | some d => recordPrimes d.factors

lemma dataChildPrimes_correct {M label : ℕ} (h : label∈children M) :
    (∀ p∈dataChildPrimes (trueData M) label,p.Prime) ∧
      (dataChildPrimes (trueData M) label).prod=label := by
  have hex : ∃ d, ((children M).map trueData).find? (fun d => decide (d.label=label))=some d := by
    cases hf : ((children M).map trueData).find? (fun d => decide (d.label=label)) with
    | none =>
      have hh := List.find?_eq_none.mp hf (trueData label) (List.mem_map.mpr ⟨label,h,rfl⟩)
      simp only [trueData_label,decide_true] at hh
      contradiction
    | some d => exact ⟨d,rfl⟩
  obtain ⟨d,hd⟩ := hex
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hd)
  have he : l=label := by simpa only [trueData_label,decide_eq_true_eq] using List.find?_some hd
  subst l
  have hlabel := (child_bounds h).1
  simp only [dataChildPrimes,trueData_descendants,hd,trueData_factors]
  refine ⟨recordPrimes_prime (fun _ => Nat.prime_of_mem_primeFactors),?_⟩
  rw [recordPrimes_prod,Nat.prod_factorization_pow_eq_self (by omega)]

/-- phi factors are reconstructed from division against the supplied parent
record and the supplied p−1 children. The p=2 contribution requires no child. -/
noncomputable def dataTotientPrimes (data : FactorData) (m : ℕ) : List ℕ :=
  let f := primeRecord (dataDivisorPrimes data m)
  (f.support.sort (· ≤ ·)).flatMap (fun p =>
    List.replicate (f p-1) p ++ if p=2 then [] else dataChildPrimes data (p-1))

lemma dataTotientPrimes_correct {M m : ℕ} (hM : 0<M) (hm : 0 < m) (hd : m∣M) :
    (∀ p∈dataTotientPrimes (trueData M) m,p.Prime) ∧
      (dataTotientPrimes (trueData M) m).prod=m.totient := by
  obtain ⟨hprime,hprod⟩ := dataDivisorPrimes_correct hM hd
  have hf : primeRecord (dataDivisorPrimes (trueData M) m)=m.factorization := by
    rw [primeRecord_eq_factorization _ hprime,hprod]
  have hchild (p : ℕ) (hp : p∈m.factorization.support) (h2 : p≠2) :
      p-1∈children M := by
    have hpm : p.Prime ∧ p∣m ∧ m≠0 := Nat.mem_primeFactors.mp hp
    exact mem_children.mpr ⟨p,hpm.1,hpm.2.1.trans hd,hM.ne',by have := hpm.1.two_le; omega,rfl⟩
  rw [dataTotientPrimes,hf]
  refine ⟨?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
    have hq' := (Finset.mem_sort (· ≤ ·)).mp hq
    rcases List.mem_append.mp hp with hp | hp
    · have he := (List.mem_replicate.mp hp).2
      subst p
      exact Nat.prime_of_mem_primeFactors hq'
    · split_ifs at hp with h2
      · simp at hp
      · exact (dataChildPrimes_correct (hchild q hq' h2)).1 p hp
  · rw [prod_flatMap]
    calc
      _ = ((m.factorization.support.sort (· ≤ ·)).map
          (fun p => p^(m.factorization p-1)*(p-1))).prod := by
        congr 1
        apply List.map_congr_left
        intro p hp
        rw [List.prod_append,List.prod_replicate]
        split_ifs with h2
        · subst p
          simp
        · rw [(dataChildPrimes_correct (hchild p ((Finset.mem_sort (· ≤ ·)).mp hp) h2)).2]
      _ = m.factorization.prod (fun p e => p^(e-1)*(p-1)) := by
        rw [←List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
        rfl
      _ = m.totient := (Nat.totient_eq_prod_factorization hm.ne').symm

/-- Section5's retrospective order algorithm instantiated with the **actual
supplied auxiliary data**, not with a hypothesized factorization of phi. -/
theorem data_strip_order {M m : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hd : m∣M)
    (a : (ZMod m)ˣ) :
    stripOrderFactors a (dataTotientPrimes (trueData M) m) m.totient=orderOf a := by
  obtain ⟨hp,hprod⟩ := dataTotientPrimes_correct hM (by omega) hd
  exact strip_totient_factors hm a _ hp hprod

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetrospectiveStatistics.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

/-- The closed statistics are evaluated over the supplied exponent record,
not by enumerating residues or invoking a factorization oracle. -/
noncomputable def recordPhi (f : FactorRecord) : ℕ :=
  ∏ p∈f.support, primePowerUnitCount p (f p)

noncomputable def recordFavorable (n : ℕ) (f : FactorRecord) : ℕ :=
  recordPhi f - ∑ t : Fin (n+1), ∏ p∈f.support,
    closedLevelCount (primePowerUnitCount p (f p)) t.val

lemma recordPhi_factorization {m : ℕ} (hm : m≠0) : recordPhi m.factorization=m.totient := by
  rw [Nat.totient_eq_prod_factorization hm]
  apply Finset.prod_congr rfl
  intro p hp
  exact Nat.mul_comm _ _

lemma recordFavorable_factorization {m : ℕ} (hm : m≠0) (n : ℕ) :
    recordFavorable n m.factorization=favorableCount m n := by
  rw [recordFavorable,recordPhi_factorization hm,favorableCount]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  exact (Finset.prod_coe_sort _ _).symm

noncomputable def dataRecord (data : FactorData) (m : ℕ) : FactorRecord :=
  primeRecord (dataDivisorPrimes data m)

lemma dataRecord_correct {M m : ℕ} (hM : 0 < M) (hd : m∣M) :
    dataRecord (trueData M) m = m.factorization := by
  have hh := dataDivisorPrimes_correct hM hd
  rw [dataRecord,primeRecord_eq_factorization _ hh.1,hh.2]

noncomputable def dataPhi (data : FactorData) (m : ℕ) : ℕ := recordPhi (dataRecord data m)
noncomputable def dataFavorable (data : FactorData) (m n : ℕ) : ℕ := recordFavorable n (dataRecord data m)

lemma dataPhi_correct {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (hd : m∣M) :
    dataPhi (trueData M) m=m.totient := by
  rw [dataPhi,dataRecord_correct hM hd,recordPhi_factorization hm.ne']

lemma dataFavorable_correct {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (hd : m∣M) (n : ℕ) :
    dataFavorable (trueData M) m n=favorableCount m n := by
  rw [dataFavorable,dataRecord_correct hM hd,recordFavorable_factorization hm.ne']

/-- Literal prime stripping in natural modular arithmetic. This is exactly the
scan compiled by `stripScan`; its inputs come only from the supplied data. -/
def stripFactorsNat (a m : ℕ) : List ℕ→ℕ→ℕ
  | [], v => v
  | q::qs, v => stripFactorsNat a m qs (stripPrimeNat a m q v)

lemma stripFactorsNat_unit {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (qs : List ℕ) (v : ℕ) :
    stripFactorsNat a m qs v=stripOrderFactors u qs v := by
  induction qs generalizing v with
  | nil => rfl
  | cons q qs ih => rw [stripFactorsNat,stripPrimeNat_unit hm u ha,ih]; rfl

noncomputable def dataOrder (data : FactorData) (a m : ℕ) : ℕ :=
  stripFactorsNat a m (dataTotientPrimes data m) (dataPhi data m)

/-- The retrospective order used for EVERY actual requested cofactor is the
true order, without calling an order oracle during execution. -/
lemma dataOrder_correct {M m a : ℕ} (hM : 0 < M) (hm : 2 ≤ m) (hd : m∣M)
    (u : (ZMod m)ˣ) (ha : (a : ZMod m)=(u : ZMod m)) :
    dataOrder (trueData M) a m=orderOf u := by
  have hh := dataTotientPrimes_correct hM (by omega : 0 < m) hd
  rw [dataOrder,dataPhi_correct hM (by omega) hd,stripFactorsNat_unit hm u ha]
  exact strip_totient_factors hm u _ hh.1 hh.2

noncomputable def dataListSuccess (data : FactorData) (m n K : ℕ) : ℚ :=
  1-(1-(dataFavorable data m n : ℚ)/(2:ℚ)^(Nat.clog 2 m))^K
noncomputable def dataOrderSuccess (data : FactorData) (a m K : ℕ) : ℚ :=
  Completion.orderSuccess (dataOrder data a m) K

lemma dataListSuccess_correct {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (hd : m∣M) (n K : ℕ) :
    dataListSuccess (trueData M) m n K=Completion.listSuccess m n K := by
  rw [dataListSuccess,dataFavorable_correct hM hm hd]
  rfl

lemma dataOrderSuccess_correct {M m a : ℕ} (hM : 0 < M) (hm : 2 ≤ m) (hd : m∣M)
    (u : (ZMod m)ˣ) (ha : (a : ZMod m)=(u : ZMod m)) (K : ℕ) :
    dataOrderSuccess (trueData M) a m K=Completion.orderSuccess (orderOf u) K := by
  rw [dataOrderSuccess,dataOrder_correct hM hm hd u ha]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetrospectiveResidues.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

/-- The distinguished component is selected from the supplied record, not by
factoring the requested integer a second time. -/
def recordFirst (f : FactorRecord) : ℕ :=
  if h : f.support.Nonempty then f.support.min' h else 0

lemma recordFirst_factorization {m : ℕ} (hm : 2 ≤ m) :
    recordFirst m.factorization=m.minFac := by
  have hp : m.minFac∈m.factorization.support :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd m,by omega⟩
  rw [recordFirst,dite_eq_left ⟨_,hp⟩]
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨hp,?_⟩
  intro p h
  obtain ⟨hprime,hd,_⟩ := Nat.mem_primeFactors.mp h
  exact Nat.minFac_le_of_dvd hprime.two_le hd

lemma component_two_le {m : ℕ} (p : Component m) : 2 ≤ p.val^m.factorization p.val := by
  have hp := Nat.mem_primeFactors.mp p.property
  exact hp.1.two_le.trans (Nat.le_pow (hp.1.factorization_pos_of_dvd hp.2.2 hp.2.1))

lemma equivPi_natCast {m : ℕ} (hm : m≠0) (p : Component m) (a : ℕ) :
    ZMod.equivPi m hm (a : ZMod m) p=(a : ZMod (p.val^m.factorization p.val)) := by
  exact map_natCast ((Pi.evalRingHom _ p).comp (ZMod.equivPi m hm).toRingHom) a

lemma unitCRT_natCast {m : ℕ} (hm : m≠0) (p : Component m) (u : (ZMod m)ˣ) (a : ℕ)
    (ha : (a : ZMod m)=u) :
    ((unitCRT m hm u p : ComponentUnits m p) : ZMod (p.val^m.factorization p.val))=a := by
  change ZMod.equivPi m hm (u : ZMod m) p=_
  rw [←ha,equivPi_natCast]

noncomputable def dataResidueGood (data : FactorData) (a m : ℕ) : Prop :=
  a < m ∧ Nat.Coprime a m ∧
    ¬∀ p∈(dataRecord data m).support,
      padicValNat 2 (dataOrder data a (p^(dataRecord data m) p))=
      padicValNat 2 (dataOrder data a
        ((recordFirst (dataRecord data m))^((dataRecord data m) (recordFirst (dataRecord data m)))))

lemma data_component_order {M m a : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hd : m∣M)
    (u : (ZMod m)ˣ) (ha : (a : ZMod m)=u) (p : Component m) :
    dataOrder (trueData M) a (p.val^m.factorization p.val)=
      orderOf (unitCRT m (by omega) u p) := by
  exact dataOrder_correct hM (component_two_le p) ((Nat.ordProj_dvd m p.val).trans hd)
    (unitCRT m (by omega) u p) (unitCRT_natCast (by omega) p u a ha).symm

/-- The retrospective favorable test is a scan of supplied prime-power factors
and prime-stripping computations. It agrees with the CRT event on every actual
requested cofactor, including those below a node of the auxiliary tree. -/
lemma dataResidueGood_correct {M m n a : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) (u : (ZMod m)ˣ) (ha : a=(u : ZMod m).val) :
    dataResidueGood (trueData M) a m ↔
      FavorableUnit (by omega) hb (UniversalSplit.firstComponent hm) u := by
  let : NeZero m := ⟨by omega⟩
  have haz : (a : ZMod m)=u := by rw [ha,ZMod.natCast_zmod_val]
  have hac : a.Coprime m := (ZMod.isUnit_iff_coprime a m).mp (haz ▸ u.isUnit)
  have hal : a < m := ha ▸ (u : ZMod m).val_lt
  rw [dataResidueGood,and_iff_right hal,and_iff_right hac,dataRecord_correct hM hd,
    recordFirst_factorization hm]
  apply not_congr
  constructor
  · intro h p
    apply Fin.ext
    change padicValNat 2 (orderOf (unitCRT m _ u p))=_
    have he := h p.val p.property
    change padicValNat 2 (dataOrder (trueData M) a (p.val^m.factorization p.val))=
      padicValNat 2 (dataOrder (trueData M) a
        ((UniversalSplit.firstComponent hm).val^m.factorization (UniversalSplit.firstComponent hm).val)) at he
    rw [data_component_order hM hm hd u haz p,
      data_component_order hM hm hd u haz (UniversalSplit.firstComponent hm)] at he
    exact he
  · intro h p hp
    let pp : Component m := ⟨p,hp⟩
    change padicValNat 2 (dataOrder (trueData M) a (pp.val^m.factorization pp.val))=
      padicValNat 2 (dataOrder (trueData M) a
        ((UniversalSplit.firstComponent hm).val^m.factorization (UniversalSplit.firstComponent hm).val))
    rw [data_component_order hM hm hd u haz pp,
      data_component_order hM hm hd u haz (UniversalSplit.firstComponent hm)]
    exact congrArg Fin.val (h pp)

/-- Checking the uniquely specified CRT residue needs only congruences against
the supplied prime powers; no CRT search is hidden in the guess validator. -/
noncomputable def dataCanonicalResidue (data : FactorData) (a m : ℕ) : Prop :=
  a < m ∧ ∀ p∈(dataRecord data m).support,
    a%(p^(dataRecord data m) p)=
      if p=recordFirst (dataRecord data m) then 1 else p^(dataRecord data m) p-1

lemma canonical_component_val {m : ℕ} (hm : m≠0) (p₀ p : Component m) :
    ((unitCRT m hm (canonicalUnit hm p₀) p : ComponentUnits m p) :
      ZMod (p.val^m.factorization p.val)).val=
      if p.val=p₀.val then 1 else p.val^m.factorization p.val-1 := by
  classical
  rw [canonicalUnit_component]
  by_cases h : p=p₀
  · subst p
    simp only [ite_true,Units.val_one]
    exact ZMod.val_one'' (n:=p₀.val^m.factorization p₀.val) (by have := component_two_le p₀; omega)
  · have hn : p.val≠p₀.val := fun hh=>h (Subtype.ext hh)
    simp only [ite_eq_right h,ite_eq_right hn,Units.val_neg,Units.val_one]
    have hq := component_two_le p
    generalize p.val^m.factorization p.val=q at *
    cases q with
    | zero => omega
    | succ q => simpa only [Nat.add_sub_cancel] using ZMod.val_neg_one q

lemma dataCanonicalResidue_correct {M m : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hd : m∣M) (a : ℕ) :
    dataCanonicalResidue (trueData M) a m ↔
      a=(canonicalUnit (by omega) (UniversalSplit.firstComponent hm) : ZMod m).val := by
  let : NeZero m := ⟨by omega⟩
  let u := canonicalUnit (by omega : m≠0) (UniversalSplit.firstComponent hm)
  rw [dataCanonicalResidue,dataRecord_correct hM hd,recordFirst_factorization hm]
  constructor
  · rintro ⟨hal,h⟩
    have hz : (a : ZMod m)=u := by
      apply (ZMod.equivPi m (by omega : m≠0)).injective
      funext p
      apply ZMod.val_injective
      rw [equivPi_natCast,ZMod.val_natCast]
      change _=((unitCRT m (by omega) u p : ComponentUnits m p) :
        ZMod (p.val^m.factorization p.val)).val
      rw [canonical_component_val]
      exact h p.val p.property
    have he := congrArg (fun z : ZMod m=>z.val) hz
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hal] using he
  · intro ha
    refine ⟨ha ▸ (u : ZMod m).val_lt,?_⟩
    intro p hp
    let pp : Component m := ⟨p,hp⟩
    have haz : (a : ZMod m)=u := by rw [ha,ZMod.natCast_zmod_val]
    have he := congrArg (fun z : ZMod (p^m.factorization p)=>z.val)
      (unitCRT_natCast (by omega) pp u a haz)
    rw [ZMod.val_natCast,canonical_component_val] at he
    exact he.symm

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetrospectiveLists.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree OrderTrial

lemma dataResidueGood_exists {M m n a : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) : dataResidueGood (trueData M) a m ↔
      ∃ u : (ZMod m)ˣ,a=(u : ZMod m).val ∧
        FavorableUnit (by omega) hb (UniversalSplit.firstComponent hm) u := by
  let : NeZero m := ⟨by omega⟩
  constructor
  · intro h
    have hu : IsUnit (a : ZMod m) := (ZMod.isUnit_iff_coprime a m).mpr h.2.1
    have hv : a=(hu.unit : ZMod m).val := by
      rw [hu.unit_spec,ZMod.val_natCast,Nat.mod_eq_of_lt h.1]
    exact ⟨hu.unit,hv,(dataResidueGood_correct hM hm hb hd hu.unit hv).mp h⟩
  · rintro ⟨u,ha,h⟩
    exact (dataResidueGood_correct hM hm hb hd u ha).mpr h

noncomputable def dataGoodList (data : FactorData) (m n : ℕ)
    (y : Basis (Completion.transitionWidth n)) : Prop :=
  ∃ i : Fin (n^5),dataResidueGood data (bitsValue (TransitionWords.read y i)).toNat m
lemma dataGoodList_correct {M m n : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) (y : Basis (Completion.transitionWidth n)) :
    dataGoodList (trueData M) m n y ↔
      ListSlots.GoodOutput (by omega) hb (UniversalSplit.firstComponent hm) y := by
  unfold dataGoodList ListSlots.GoodOutput
  apply exists_congr
  intro i
  exact dataResidueGood_exists hM hm hb hd

/-- The source canonical list has the CRT unit in the first field and zero in
all remaining fields (including the final unused word). -/
lemma canonical_list_words {m n : ℕ} (hm : m≠0) (hb : m < 2^n) (p₀ : Component m) :
    ListSlots.canonical hm hb p₀=TransitionWords.encode
      (fun i : Fin (n^5) => natBasis n (if i.val=0 then (canonicalUnit hm p₀ : ZMod m).val else 0)) := by
  let : NeZero m := ⟨hm⟩
  unfold ListSlots.canonical ListSlots.ordinary
  congr 1
  funext i
  apply (bitsEquiv n).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue (padBits _ (canonicalList hm p₀ (n^5) i))).toNat=_
  rw [padBits_value]
  simp only [canonicalList,bitsEquiv,Equiv.coe_fn_symm_mk,bitsValue_bits,BitVec.toNat_ofNat,
    ]
  have hv : (if i.val=0 then (canonicalUnit hm p₀ : ZMod m).val else 0) < m := by
    split_ifs
    · exact ZMod.val_lt _
    · omega
  change _=(bitsValue (natBasis n _)).toNat
  rw [natBasis_value,Nat.mod_eq_of_lt (hv.trans_le (Nat.le_pow_clog (by decide) m)),Nat.mod_eq_of_lt (hv.trans hb)]

/-- A direct fixed-field validator: read field zero, test its supplied-factor CRT
congruences, and check every other field and the unused word is zero. -/
noncomputable def dataCanonicalList (data : FactorData) (m n : ℕ) (hn : 0<n)
    (y : Basis (Completion.transitionWidth n)) : Prop :=
  let a := TransitionWords.read y ⟨0,pow_pos hn 5⟩
  dataCanonicalResidue data (bitsValue a).toNat m ∧
    y=TransitionWords.encode (fun i : Fin (n^5) => if i.val=0 then a else natBasis n 0)

lemma basis_eq_natBasis {n a : ℕ} (ha : a<2^n) (x : Basis n) :
    (bitsValue x).toNat=a ↔ x=natBasis n a := by
  constructor
  · intro hx
    apply (bitsEquiv n).injective
    apply BitVec.eq_of_toNat_eq
    change (bitsValue x).toNat=(bitsValue (natBasis n a)).toNat
    rw [hx,natBasis_value,Nat.mod_eq_of_lt ha]
  · intro hx
    rw [hx,natBasis_value,Nat.mod_eq_of_lt ha]

lemma dataCanonicalList_correct {M m n : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) (hn : 0<n) (y : Basis (Completion.transitionWidth n)) :
    dataCanonicalList (trueData M) m n hn y ↔
      y=ListSlots.canonical (by omega) hb (UniversalSplit.firstComponent hm) := by
  let : NeZero m := ⟨by omega⟩
  let u := canonicalUnit (by omega : m≠0) (UniversalSplit.firstComponent hm)
  have hu : (u : ZMod m).val<2^n := (ZMod.val_lt _).trans hb
  rw [dataCanonicalList,dataCanonicalResidue_correct hM hm hd,basis_eq_natBasis hu,
    canonical_list_words]
  have hshape : (fun i : Fin (n^5) => natBasis n (if i.val=0 then (u : ZMod m).val else 0))=
      (fun i : Fin (n^5) => if i.val=0 then natBasis n (u : ZMod m).val else natBasis n 0) := by
    funext i
    split_ifs <;> rfl
  change (_=natBasis n (u : ZMod m).val ∧ _) ↔ y=TransitionWords.encode _
  rw [hshape]
  constructor
  · rintro ⟨ha,hy⟩
    simpa only [ha] using hy
  · intro hy
    rw [hy,TransitionWords.read_encode]
    simp only [ite_true,eq_self]
    exact ⟨trivial,rfl⟩

namespace Completion
/-- Equivalent form of dyadic completion for a retrospective, data-based test
of the guessed string. No canonical output is used during preparation. -/
def test {α : Type*} {W t d : ℕ} (good : α→Prop) (guessGood : Basis W→Prop)
    (s z : ℚ) (r : Raw α W t d) : Prop :=
  ordinaryPass good s z r ∨ rare r.1 ∧ guessGood r.2.2.1 ∧
    threshold (guessRetention W t s z) r.2.2.2
lemma test_eq_passed {α : Type*} {W t d : ℕ} (good : α→Prop) (guessGood : Basis W→Prop)
    (y₀ : Basis W) (s z : ℚ) (hg : ∀ y,guessGood y ↔ y=y₀) (r : Raw α W t d) :
    test good guessGood s z r ↔ passed good y₀ s z r := by
  simp only [test,passed,guessPass,hg]
end Completion

noncomputable def dataListPassed {n : ℕ} (data : FactorData) (m : Basis n) (hn : 0<n)
    (r : PhysicalListSlots.Result n) : Prop :=
  Completion.test (fun x => dataGoodList data (bitsValue m).toNat n (PhysicalListSlots.ordinary x))
    (dataCanonicalList data (bitsValue m).toNat n hn)
    (dataListSuccess data (bitsValue m).toNat n (n^5)) (Completion.target n) r

/-- Same integer, same raw outcome, same retention coin. A verified occurrence
record suffices even when the request is only a divisor of that occurrence. -/
lemma dataListPassed_correct {M n : ℕ} (hM : 0<M) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat∣M) (hn : 0<n)
    (r : PhysicalListSlots.Result n) :
    dataListPassed (trueData M) m hn r ↔
      PhysicalListSlots.passed m (by omega) (UniversalSplit.firstComponent hm) r := by
  have hg : (fun x => dataGoodList (trueData M) (bitsValue m).toNat n (PhysicalListSlots.ordinary x))=
      (ListSlots.GoodOutput (by omega) (bitsValue m).isLt (UniversalSplit.firstComponent hm) ∘
        PhysicalListSlots.ordinary) := by
    funext x
    exact propext (dataGoodList_correct hM hm (bitsValue m).isLt hd _)
  rw [dataListPassed,hg,dataListSuccess_correct hM (by omega) hd]
  exact Completion.test_eq_passed _ _ _ _ _
    (dataCanonicalList_correct hM hm (bitsValue m).isLt hd hn) r

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetrospectiveSlots.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree OrderTrial

/-- The usable-slot test is just range plus Euclidean gcd, not an order oracle. -/
def residueUsable (a m : ℕ) : Prop := a < m ∧ a.Coprime m
lemma residueUsable_iff {n : ℕ} (a m : Basis n) :
    residueUsable (bitsValue a).toNat (bitsValue m).toNat ↔ OrderSlots.Usable a m := by
  simp only [residueUsable,OrderSlots.Usable,ZMod.isUnit_iff_coprime]

/-- Test the same completed order slot using the later supplied node record.
Unusable list entries (including out-of-range words) use the source dummy test. -/
noncomputable def dataOrderPassed {n : ℕ} (data : FactorData) (a m : Basis n)
    (r : OrderSlots.Result n) : Prop := by
  classical
  exact
  if residueUsable (bitsValue a).toNat (bitsValue m).toNat then
    Completion.test
      (fun x => orderResult (OrderSlots.sampleExponent n) n a m (n^5) x=
        dataOrder data (bitsValue a).toNat (bitsValue m).toNat)
      (fun y => y=natBasis _ (dataOrder data (bitsValue a).toNat (bitsValue m).toNat))
      (dataOrderSuccess data (bitsValue a).toNat (bitsValue m).toNat (n^5)) (Completion.target n) r
  else Completion.test (fun _=>True) (fun y=>y=natBasis _ 0) 1 (Completion.target n) r

lemma dataOrderPassed_correct {M n : ℕ} (hM : 0<M) (a m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat∣M)
    (r : OrderSlots.Result n) :
    dataOrderPassed (trueData M) a m r ↔ OrderSlots.passed a m r := by
  classical
  rw [dataOrderPassed,residueUsable_iff]
  by_cases h : OrderSlots.Usable a m
  · rw [ite_eq_left h,OrderSlots.passed,dite_eq_left h,
      dataOrder_correct hM hm hd h.2.unit h.2.unit_spec.symm,
      dataOrderSuccess_correct hM hm hd h.2.unit h.2.unit_spec.symm]
    change Completion.test _ _ _ _ r ↔ Completion.passed _ (natBasis _ (OrderSlots.unitOrder a m)) _ _ r
    rw [OrderSlots.unitOrder,dite_eq_left h]
    exact Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) r
  · rw [ite_eq_right h,OrderSlots.passed,dite_eq_right h]
    change Completion.test _ _ _ _ r ↔ Completion.passed _ (natBasis _ (OrderSlots.unitOrder a m)) _ _ r
    rw [OrderSlots.unitOrder,dite_eq_right h]
    exact Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) r

noncomputable def dataSplitPassed {n : ℕ} (data : FactorData) (m : Basis n) (hn : 0<n)
    (r : UniversalSplit.Raw n) : Prop := by
  classical
  exact
  if UniversalSplit.Hard (bitsValue m).toNat then
    dataListPassed data m hn r.1 ∧ ∀ i,dataOrderPassed data (FixedSplit.bases r.1 i) m (r.2 i)
  else UniversalSplit.dummy r

/-- All list/order/retention decisions are on the actual retained raw block.
The record may be that of any actual node whose label is divisible by m. -/
lemma dataSplitPassed_correct {M n : ℕ} (hM : 0<M) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat∣M) (hn : 0<n)
    (r : UniversalSplit.Raw n) :
    dataSplitPassed (trueData M) m hn r ↔ UniversalSplit.passed m r := by
  classical
  rw [dataSplitPassed,UniversalSplit.passed]
  split_ifs with hh
  · change (_ ∧ ∀ i,_) ↔ (_ ∧ ∀ i,_)
    exact and_congr (dataListPassed_correct hM m hm hd hn r.1)
      (forall_congr' (fun i=>dataOrderPassed_correct hM _ m hm hd (r.2 i)))
  · rfl

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeVerifiedCircuit.lean =====
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

def resultFields (n : ℕ) : Fin n→BooleanNetwork (NodeKernel.width n) n :=
  fun i=>(nodeResult n).comp (tensorSelect n n i)
def nodeWords (n : ℕ) (z : Basis (NodeKernel.width n)) : List (Basis n) :=
  List.ofFn (fun i=>(resultFields n i).eval z)
lemma fields_nodeWords (n : ℕ) (z : Basis (NodeKernel.width n)) :
    (fields n).map (fun a=>a.eval z)=nodeWords n z := by
  rw [fields,List.map_ofFn]
  rfl
lemma nodeWords_length (n : ℕ) (z : Basis (NodeKernel.width n)) : (nodeWords n z).length=n :=
  List.length_ofFn
lemma numbers_nodeWords (n : ℕ) (z : Basis (NodeKernel.width n)) :
    SortedWords.numbers (nodeWords n z)=candidateWords (resultFields n) z := by
  simp only [SortedWords.numbers,nodeWords,candidateWords,List.map_ofFn,Function.comp_def]

def NodeVerified {n : ℕ} (q : Basis n) (r : NodeKernel.Raw n) : Prop :=
  (bitsValue q).toNat=0 ∨ CorrectEncoding (bitsValue q).toNat n
    (SortedWords.numbers (nodeWords n (NodeKernel.encoding q r)))

lemma node_verified_of_passed {n : ℕ} (hn : 128 ≤ n) (q : Basis n)
    (hq : (bitsValue q).toNat=0 ∨ 2 ≤ (bitsValue q).toNat)
    (r : NodeKernel.Raw n) (hp : NodeKernel.passed q r) : NodeVerified q r := by
  rcases hq with hz | ha
  · exact Or.inl hz
  · right
    have hp' : (PhysicalNode.machine n (2*n)).passed
        (NodeStateCircuit.pack [natBasis (n+1) (bitsValue q).toNat] [] false) (2*n) r := by
      simpa only [NodeKernel.passed,NodeKernel.start,PhysicalNode.startNet_eval] using hp
    obtain ⟨zs,hl,hc,he⟩ := PhysicalNode.complete_output hn ha (bitsValue q).isLt r hp'
    have hf : nodeWords n (NodeKernel.encoding q r)=zs := by
      rw [←fields_nodeWords]
      apply fields_eval _ zs hl
      rw [nodeResult,eval_comp,NodeKernel.encoding,SplitMachine.current_encoded,
        NodeKernel.start,PhysicalNode.startNet_eval]
      exact he
    rw [hf]
    exact hc

/-- The queue remains canonical for ANY retrospectively verified local result,
not only for results obtained on the all-good event. -/
theorem update_verified {n : ℕ} (hn : 128 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (ha : 2 ≤ (bitsValue a).toNat)
    (r : NodeKernel.Raw n) (hv : NodeVerified a r) :
    ∃ kids : List (Basis n), SortedWords.numbers kids=AuxiliaryTree.children (bitsValue a).toNat ∧
      (update n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) (NodeKernel.encoding a r))=
        stackEncoding (capacity n) n (kids++as) := by
  rcases hv with hz | hc
  · omega
  · refine ⟨ChildQueue.kids (nodeWords n (NodeKernel.encoding a r)),
      ChildQueue.kids_correct (by omega) ha _ hc,?_⟩
    rw [update_eval (by omega : 2 ≤ n) a as hlen ha,fields_nodeWords]

end PhysicalTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def verified (x : Basis c) : (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,h=>verified x t h.1 ∧ PhysicalTree.NodeVerified
      (M.query.eval (M.config x t h.1)) h.2

def rowQuery (t : ℕ) : BooleanNetwork (M.width (t+1)) n :=
  ((M.previousNet t).comp (M.currentNet t)).comp M.query
def rowFields (t : ℕ) (i : Fin n) : BooleanNetwork (M.width (t+1)) n :=
  (M.lastNodeNet t).comp (PhysicalTree.resultFields n i)
def rowVerifiedNet (t : ℕ) : BooleanNetwork (M.width (t+1)) 1 :=
  (zeroWord (M.rowQuery t)).bor (factorVerifierOn (M.rowQuery t) (M.rowFields t))
def verifiedNet : (t : ℕ)→BooleanNetwork (M.width t) 1
  | 0=>constant true
  | t+1=>((M.previousNet t).comp (verifiedNet t)).band (M.rowVerifiedNet t)

lemma rowQuery_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.rowQuery t).eval (M.encoded x (t+1) (h,r))=M.query.eval (M.config x t h) := by
  rw [rowQuery,eval_comp,eval_comp,M.previousNet_encoded,M.current_encoded]
lemma rowFields_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) (i : Fin n) :
    (M.rowFields t i).eval (M.encoded x (t+1) (h,r))=
      (PhysicalTree.resultFields n i).eval (NodeKernel.encoding (M.query.eval (M.config x t h)) r) := by
  rw [rowFields,eval_comp,M.lastNodeNet_encoded]
lemma rowVerifiedNet_encoded (hn : 128 ≤ n) (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.rowVerifiedNet t).eval (M.encoded x (t+1) (h,r)) 0=true ↔
      PhysicalTree.NodeVerified (M.query.eval (M.config x t h)) r := by
  rw [rowVerifiedNet,eval_bor,Bool.or_eq_true,zeroWord_value,
    factorVerifierOn_correct hn,M.rowQuery_encoded,PhysicalTree.NodeVerified,
    PhysicalTree.numbers_nodeWords]
  simp only [candidateWords,M.rowFields_encoded]

/-- A literal, bounded Boolean verifier of every actual retained root/node
factor list. No predicate is silently converted to an oracle gate. -/
theorem verifiedNet_encoded (hn : 128 ≤ n) (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.verifiedNet t).eval (M.encoded x t h) 0=true ↔ M.verified x t h := by
  induction t with
  | zero=>simp [verifiedNet,verified]
  | succ t ih=>
    rw [verifiedNet,eval_band,Bool.and_eq_true,eval_comp,M.previousNet_encoded,
      ih,M.rowVerifiedNet_encoded hn]
    rfl

end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/VerifiedTreeCompletion.lean =====
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

/-- On any retrospectively verified raw history, the literal physical pending queue is
exactly the remaining canonical occurrence preorder. This is a proof invariant,
not a precomputed queue or advice to the circuit. -/
theorem verified_queue_invariant {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hp : (machine n).verified (initialQueue n N) t h) :
    (machine n).config (initialQueue n N) t h=
      stackEncoding (capacity n) n (canonicalWords n (AuxiliaryTree.run t [N])) := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    obtain ⟨h,r⟩ := h
    have hi := ih h hp.1
    have hbounds := AuxiliaryTree.run_bounds (xs:=[N]) (B:=2^n)
      (by
        intro a ha
        have he : a=N := by simpa using ha
        subst a
        exact ⟨hN,hb⟩) t
    have hlen := AuxiliaryTree.run_queue_length (t:=t) hN hb
    rw [NodeMachine.config,NodeMachine.next,hi]
    change (update n).eval (Fin.append _ (NodeKernel.encoding ((query n).eval _) r))=_
    cases he : AuxiliaryTree.run t [N] with
    | nil=>
      change (update n).eval (Fin.append (stackEncoding (capacity n) n []) _)=_
      rw [update_nil,AuxiliaryTree.run_succ_right,he]
      rfl
    | cons m ms=>
      have hm := hbounds m (by rw [he];simp)
      have hv : (bitsValue (natBasis n m)).toNat=m := by rw [natBasis_value,Nat.mod_eq_of_lt hm.2]
      have hc : (natBasis n m::canonicalWords n ms).length ≤ capacity n := by
        rw [he,List.length_cons] at hlen
        simp only [List.length_cons,canonical_length]
        unfold capacity
        omega
      have hr : NodeVerified (natBasis n m) r := by
        have hh := hp.2
        change NodeVerified ((query n).eval ((machine n).config (initialQueue n N) t h)) r at hh
        rw [hi,he] at hh
        change NodeVerified ((query n).eval (stackEncoding (capacity n) n
          (natBasis n m::canonicalWords n ms))) r at hh
        rw [query_encoding] at hh
        exact hh
      obtain ⟨ks,hk,hu⟩ := update_verified hn (natBasis n m) (canonicalWords n ms) hc
        (by rw [hv];exact hm.1) r hr
      have hks : ks=canonicalWords n (AuxiliaryTree.children m) := by
        rw [hv] at hk
        rw [←canonical_numbers ks,hk]
      change (update n).eval (Fin.append (stackEncoding (capacity n) n
        (natBasis n m::canonicalWords n ms))
          (NodeKernel.encoding ((query n).eval (stackEncoding (capacity n) n
            (natBasis n m::canonicalWords n ms))) r))=_
      rw [query_encoding,hu,hks,AuxiliaryTree.run_succ_right,he]
      change stackEncoding (capacity n) n
        (canonicalWords n (AuxiliaryTree.children m)++canonicalWords n ms)=
        stackEncoding (capacity n) n (canonicalWords n (AuxiliaryTree.children m++ms))
      rw [canonical_append]

/-- The full actual tree controller terminates in the fixed polynomial
occurrence cap, with no truncation on a passing history. The circuit nevertheless
has fixed worst-case dimensions on all other histories as well. -/
theorem verified_complete {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (h : NodeMachine.Trace n (2*n^2))
    (hp : (machine n).verified (initialQueue n N) (2*n^2) h) :
    (machine n).config (initialQueue n N) (2*n^2) h=stackEncoding (capacity n) n [] := by
  rw [verified_queue_invariant hn hN hb _ h hp,AuxiliaryTree.run_complete hN hb]
  rfl


/-- Every good chronological run passes the literal complete-node verification.
The converse is deliberately NOT asserted: local filters still must be checked. -/
theorem passed_verified {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hp : (machine n).passed (initialQueue n N) t h) :
    (machine n).verified (initialQueue n N) t h := by
  induction t with
  | zero=>trivial
  | succ t ih=>
    refine ⟨ih h.1 hp.1,?_⟩
    apply node_verified_of_passed hn _ _ h.2 hp.2
    have hi := queue_invariant hn hN hb t h.1 hp.1
    change (bitsValue ((query n).eval ((machine n).config (initialQueue n N) t h.1))).toNat=0 ∨
      2 ≤ (bitsValue ((query n).eval ((machine n).config (initialQueue n N) t h.1))).toNat
    rw [hi]
    have hbounds := AuxiliaryTree.run_bounds (xs:=[N]) (B:=2^n) (by
      intro a ha
      have he : a=N := by simpa using ha
      subst a
      exact ⟨hN,hb⟩) t
    cases he : AuxiliaryTree.run t [N] with
    | nil=>
      left
      change (bitsValue ((query n).eval (stackEncoding (capacity n) n []))).toNat=0
      rw [query,blockNet_eval,block_stackEncoding]
      simp only [List.getElem?_nil,Option.getD_none,zeroBasis_value]
      rfl
    | cons a as=>
      right
      have ha := hbounds a (by rw [he];simp)
      change 2 ≤ (bitsValue ((query n).eval (stackEncoding (capacity n) n
        (natBasis n a::canonicalWords n as)))).toNat
      rw [query_encoding,natBasis_value,Nat.mod_eq_of_lt ha.2]
      exact ha.1

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
