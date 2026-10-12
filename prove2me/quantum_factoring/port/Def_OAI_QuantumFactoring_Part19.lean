/-
Exact quantum factoring development (port of OpenAI's formalization), part 19 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: QueueCoverage.lean, PhysicalDataLog.lean, FlatVerifiedData.lean, FlatDataView.lean, FlatDataPredicates.lean, NodeStateFailure.lean, PhysicalNodeSafety.lean, RetrospectiveNode.lean, SplitHistoryAccess.lean, HardFilterCircuit.lean, RationalPowerCircuit.lean, CompletionFilterCircuit.lean, CompletionPredicateCircuit.lean, TwoAdicCircuit.lean, TableOrder.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part18

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/QueueCoverage.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.AuxiliaryTree

/-- Chronological node heads, in reverse recording order. Zero denotes a dummy
slot after the pending queue has become empty. Duplicate occurrences remain. -/
def seen (xs : List ℕ) : ℕ→List ℕ
  | 0=>[]
  | t+1=>(run t xs).headD 0::seen xs t

lemma head_or_advance {xs : List ℕ} {a : ℕ} (ha : a∈xs) :
    a=xs.headD 0 ∨ a∈advance xs := by
  cases xs with
  | nil=>simp at ha
  | cons b bs=>
    rcases List.mem_cons.mp ha with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_append_right _ h)
lemma children_head (xs : List ℕ) {a : ℕ} (ha : a∈children (xs.headD 0)) : a∈advance xs := by
  cases xs with
  | nil=>simp [children] at ha
  | cons b bs=>exact List.mem_append_left _ ha

/-- Everything pending before a step is either the recorded head or remains
pending afterwards. This assertion does not search the mathematical tree. -/
lemma seen_or_pending_step {xs : List ℕ} {t a : ℕ}
    (h : a∈seen xs t ∨ a∈run t xs) : a∈seen xs (t+1) ∨ a∈run (t+1) xs := by
  rcases h with h | h
  · exact Or.inl (List.mem_cons_of_mem _ h)
  · rcases head_or_advance h with h | h
    · exact Or.inl (List.mem_cons.mpr (Or.inl h))
    · exact Or.inr (by rw [run_succ_right];exact h)

lemma original_covered (xs : List ℕ) (t : ℕ) {a : ℕ} (ha : a∈xs) :
    a∈seen xs t ∨ a∈run t xs := by
  induction t with
  | zero=>exact Or.inr ha
  | succ t ih=>exact seen_or_pending_step ih

/-- Every required p−1 child of every already visited node is itself either
visited or still on the actual occurrence queue. -/
lemma children_covered (xs : List ℕ) (t : ℕ) {m a : ℕ}
    (hm : m∈seen xs t) (ha : a∈children m) : a∈seen xs t ∨ a∈run t xs := by
  induction t with
  | zero=>simp [seen] at hm
  | succ t ih=>
    rcases List.mem_cons.mp hm with hm | hm
    · have hx : a∈advance (run t xs) := children_head _ (by simpa only [←hm] using ha)
      exact Or.inr (by rw [run_succ_right];exact hx)
    · exact seen_or_pending_step (ih hm)

lemma completed_root {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) : m∈seen [m] (2*n^2) := by
  have h:=original_covered [m] (2*n^2) (by simp : m∈[m])
  rw [run_complete hm hb] at h
  simpa only [List.not_mem_nil,or_false] using h
lemma completed_children {m n a b : ℕ} (hm : 2 ≤ m) (hb : m < 2^n)
    (ha : a∈seen [m] (2*n^2)) (hc : b∈children a) : b∈seen [m] (2*n^2) := by
  have h:=children_covered [m] (2*n^2) ha hc
  rw [run_complete hm hb] at h
  simpa only [List.not_mem_nil,or_false] using h
lemma seen_length (xs : List ℕ) (t : ℕ) : (seen xs t).length=t := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [seen,List.length_cons,ih]
end ExactQuantumFactoring.AuxiliaryTree


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalDataLog.lean =====
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

/-- Projection of the actual retained record, including dummy rows. No true
factorization is used in constructing this projection. -/
def dataLog (x : Basis c) : (t : ℕ)→Trace n t→List (ℕ×List ℕ)
  | 0,_=>[]
  | t+1,h=>
    let q:=M.query.eval (M.config x t h.1)
    ((bitsValue q).toNat,SortedWords.numbers
      (PhysicalTree.nodeWords n (NodeKernel.encoding q h.2)))::dataLog x t h.1
lemma dataLog_length (x : Basis c) (t : ℕ) (h : Trace n t) : (M.dataLog x t h).length=t := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [dataLog,List.length_cons,ih]
lemma dataLog_correct (x : Basis c) (t : ℕ) (h : Trace n t) (hv : M.verified x t h) :
    ∀ a∈M.dataLog x t h, a.1=0 ∨ CorrectEncoding a.1 n a.2 := by
  induction t with
  | zero=>simp only [dataLog,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ t ih=>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hv.2
    · exact ih h.1 hv.1 a ha
end NodeMachine
namespace PhysicalTree

lemma verified_query_value {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t h) :
    (bitsValue ((query n).eval ((machine n).config (initialQueue n N) t h))).toNat=
      (AuxiliaryTree.run t [N]).headD 0 := by
  rw [verified_queue_invariant hn hN hb t h hv]
  have hbounds:=AuxiliaryTree.run_bounds (xs:=[N]) (B:=2^n) (by
    intro a ha
    have he : a=N := by simpa using ha
    subst a
    exact ⟨hN,hb⟩) t
  cases he : AuxiliaryTree.run t [N] with
  | nil=>
    change (bitsValue ((query n).eval (stackEncoding (capacity n) n []))).toNat=0
    rw [query,blockNet_eval,block_stackEncoding]
    simp only [List.getElem?_nil,Option.getD_none,zeroBasis_value]
    rfl
  | cons a as=>
    have ha:=hbounds a (by rw [he];simp)
    change (bitsValue ((query n).eval (stackEncoding (capacity n) n
      (natBasis n a::canonicalWords n as)))).toNat=a
    rw [query_encoding,natBasis_value,Nat.mod_eq_of_lt ha.2]

/-- The labels on the actual verified physical history are exactly the
occurrence-preserving canonical traversal, including its zero padding. -/
lemma verified_dataLog_labels {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t h) :
    ((machine n).dataLog (initialQueue n N) t h).map Prod.fst=AuxiliaryTree.seen [N] t := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    change (bitsValue ((query n).eval ((machine n).config (initialQueue n N) t h.1))).toNat::
      List.map Prod.fst ((machine n).dataLog (initialQueue n N) t h.1)=_
    rw [verified_query_value hn hN hb t h.1 hv.1,ih h.1 hv.1]
    rfl

/-- Concrete flat complete-data condition sufficient for retrospective lookup:
root present, every required child present, and every non-dummy row a complete
prime factorization. Equal labels from different parents are NOT collapsed. -/
def CompleteLog (n N : ℕ) (rows : List (ℕ×List ℕ)) : Prop :=
  N∈rows.map Prod.fst ∧
  (∀ a∈rows, a.1=0 ∨ CorrectEncoding a.1 n a.2) ∧
  (∀ a∈rows, ∀ d∈AuxiliaryTree.children a.1, d∈rows.map Prod.fst)

theorem verified_complete_log {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (h : NodeMachine.Trace n (2*n^2))
    (hv : (machine n).verified (initialQueue n N) (2*n^2) h) :
    CompleteLog n N ((machine n).dataLog (initialQueue n N) (2*n^2) h) := by
  have he:=verified_dataLog_labels hn hN hb (2*n^2) h hv
  refine ⟨?_,(machine n).dataLog_correct _ _ _ hv,?_⟩
  · rw [he]
    exact AuxiliaryTree.completed_root hN hb
  · intro a ha d hd
    rw [he]
    apply AuxiliaryTree.completed_children hN hb (a:=a.1) _ hd
    rw [←he]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FlatVerifiedData.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree
namespace PhysicalTree

/-- Data lookup runs on the retained flat rows, not on a factorization oracle. -/
def lookupFields (rows : List (ℕ×List ℕ)) (m : ℕ) : List ℕ :=
  match rows.find? (fun r=>decide (r.1=m)) with
  | none=>[]
  | some r=>r.2

def lookupPrimes (rows : List (ℕ×List ℕ)) (m : ℕ) : List ℕ :=
  (lookupFields rows m).filter (fun p=>decide (p≠0))

lemma lookupFields_correct {rows : List (ℕ×List ℕ)} {n N m : ℕ}
    (h : CompleteLog n N rows) (hm : m∈rows.map Prod.fst) (hpos : m≠0) :
    CorrectEncoding m n (lookupFields rows m) := by
  cases hf : rows.find? (fun r=>decide (r.1=m)) with
  | none=>
    obtain ⟨r,hr,he⟩:=List.mem_map.mp hm
    have hh:=List.find?_eq_none.mp hf r hr
    simp only [he,decide_true] at hh
    contradiction
  | some r=>
    have hr:=List.mem_of_find?_eq_some hf
    have he : r.1=m := by simpa only [decide_eq_true_eq] using List.find?_some hf
    have hv:=h.2.1 r hr
    rcases hv with hz | hv
    · exact (hpos (he.symm.trans hz)).elim
    · simpa only [lookupFields,hf,he] using hv

lemma encoding_filter {n m : ℕ} {xs : List ℕ} (h : CorrectEncoding m n xs) :
    (∀ p∈xs.filter (fun p=>decide (p≠0)),p.Prime) ∧
      (xs.filter (fun p=>decide (p≠0))).prod=m := by
  obtain ⟨ps,hp,_hs,hprod,_hlen,rfl⟩:=h
  have he : (ps++List.replicate (n-ps.length) 0).filter (fun p=>decide (p≠0))=ps := by
    rw [List.filter_append]
    have hx : ps.filter (fun p=>decide (p≠0))=ps :=
      List.filter_eq_self.mpr (by intro p h; simpa only [decide_eq_true_eq] using (hp p h).ne_zero)
    rw [hx]
    simp
  rw [he]
  exact ⟨hp,hprod⟩

lemma lookupPrimes_correct {rows : List (ℕ×List ℕ)} {n N m : ℕ}
    (h : CompleteLog n N rows) (hm : m∈rows.map Prod.fst) (hpos : m≠0) :
    (∀ p∈lookupPrimes rows m,p.Prime) ∧ (lookupPrimes rows m).prod=m :=
  encoding_filter (lookupFields_correct h hm hpos)

def logDivisorPrimes (rows : List (ℕ×List ℕ)) (M m : ℕ) : List ℕ :=
  divisorPrimes m (lookupPrimes rows M)

lemma logDivisorPrimes_correct {rows : List (ℕ×List ℕ)} {n N M m : ℕ}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hpos : M≠0) (hd : m∣M) :
    (∀ p∈logDivisorPrimes rows M m,p.Prime) ∧ (logDivisorPrimes rows M m).prod=m := by
  obtain ⟨hp,hprod⟩:=lookupPrimes_correct h hM hpos
  exact ⟨divisorPrimes_prime m _ hp,divisorPrimes_prod _ hp (by rwa [hprod])⟩

lemma log_child_present {rows : List (ℕ×List ℕ)} {n N M d : ℕ}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hd : d∈children M) :
    d∈rows.map Prod.fst := by
  obtain ⟨r,hr,he⟩:=List.mem_map.mp hM
  exact h.2.2 r hr d (by rwa [he])

/-- The only factor data used are supplied parent factors and already verified
p−1 rows. This representation is a mathematical list interface; its Boolean
implementation is a separate obligation, not hidden in this definition. -/
noncomputable def logTotientPrimes (rows : List (ℕ×List ℕ)) (M m : ℕ) : List ℕ :=
  let f:=primeRecord (logDivisorPrimes rows M m)
  (f.support.sort (·≤·)).flatMap (fun p=>
    List.replicate (f p-1) p ++ if p=2 then [] else lookupPrimes rows (p-1))

lemma logTotientPrimes_correct {rows : List (ℕ×List ℕ)} {n N M m : ℕ}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hpos : M≠0)
    (hm : 0 < m) (hd : m∣M) :
    (∀ p∈logTotientPrimes rows M m,p.Prime) ∧ (logTotientPrimes rows M m).prod=m.totient := by
  obtain ⟨hp,hprod⟩:=logDivisorPrimes_correct h hM hpos hd
  have hf : primeRecord (logDivisorPrimes rows M m)=m.factorization := by
    rw [primeRecord_eq_factorization _ hp,hprod]
  have hc (p : ℕ) (hp : p∈m.factorization.support) (h2 : p≠2) :
      (∀ q∈lookupPrimes rows (p-1),q.Prime) ∧ (lookupPrimes rows (p-1)).prod=p-1 := by
    have hpm:=Nat.mem_primeFactors.mp hp
    have hb : 2<p := by have := hpm.1.two_le; omega
    have hchild : p-1∈children M :=
      mem_children.mpr ⟨p,hpm.1,hpm.2.1.trans hd,hpos,hb,rfl⟩
    exact lookupPrimes_correct h (log_child_present h hM hchild) (by omega)
  rw [logTotientPrimes,hf]
  refine ⟨?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,hp⟩:=List.mem_flatMap.mp hp
    have hq':=(Finset.mem_sort (·≤·)).mp hq
    rcases List.mem_append.mp hp with hp | hp
    · have he:=(List.mem_replicate.mp hp).2
      subst p
      exact Nat.prime_of_mem_primeFactors hq'
    · split_ifs at hp with h2
      · simp at hp
      · exact (hc q hq' h2).1 p hp
  · rw [prod_flatMap]
    calc
      _ = ((m.factorization.support.sort (·≤·)).map
          (fun p=>p^(m.factorization p-1)*(p-1))).prod := by
        congr 1
        apply List.map_congr_left
        intro p hp
        rw [List.prod_append,List.prod_replicate]
        split_ifs with h2
        · subst p; simp
        · rw [(hc p ((Finset.mem_sort (·≤·)).mp hp) h2).2]
      _ = m.factorization.prod (fun p e=>p^(e-1)*(p-1)) := by
        rw [←List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
        rfl
      _ = m.totient := (Nat.totient_eq_prod_factorization hm.ne').symm

theorem verified_log_strip_order {n N m : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N)
    (hb : N < 2^n) (hm : 2 ≤ m) (hd : m∣N)
    (h : NodeMachine.Trace n (2*n^2))
    (hv : (machine n).verified (initialQueue n N) (2*n^2) h) (a : (ZMod m)ˣ) :
    stripOrderFactors a
      (logTotientPrimes ((machine n).dataLog (initialQueue n N) (2*n^2) h) N m)
      m.totient=orderOf a := by
  have hc:=verified_complete_log hn hN hb h hv
  obtain ⟨hp,hprod⟩:=logTotientPrimes_correct hc hc.1 (by omega) (by omega) hd
  exact strip_totient_factors hm a _ hp hprod
end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FlatDataView.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

/-- Precisely the supplied local record and p−1 lookup facts consumed by the
retrospective arithmetic. This is established below from actual verified rows. -/
def DataView (d : FactorData) (M : ℕ) : Prop :=
  d.factors=M.factorization ∧
    ∀ l∈children M,dataChildPrimes d l=recordPrimes l.factorization

lemma trueData_view (M : ℕ) : DataView (trueData M) M := by
  refine ⟨trueData_factors M,?_⟩
  intro l hl
  cases hf : ((children M).map trueData).find? (fun d=>decide (d.label=l)) with
  | none=>
    have hh:=List.find?_eq_none.mp hf (trueData l) (List.mem_map.mpr ⟨l,hl,rfl⟩)
    simp only [trueData_label,decide_true] at hh
    contradiction
  | some d=>
    obtain ⟨a,_ha,he⟩:=List.mem_map.mp (List.mem_of_find?_eq_some hf)
    subst d
    have he : a=l := by simpa only [trueData_label,decide_eq_true_eq] using List.find?_some hf
    subst a
    simp only [dataChildPrimes,trueData_descendants,hf,trueData_factors]

namespace PhysicalTree
noncomputable def rowData (r : ℕ×List ℕ) : FactorData :=
  .node r.1 (primeRecord (r.2.filter (fun p=>decide (p≠0)))) []
noncomputable def flatData (rows : List (ℕ×List ℕ)) (M : ℕ) : FactorData :=
  .node M (primeRecord (lookupPrimes rows M)) (rows.map rowData)
@[simp] lemma rowData_label (r : ℕ×List ℕ) : (rowData r).label=r.1 := rfl
lemma rowData_factors {r : ℕ×List ℕ} {n : ℕ} (h : CorrectEncoding r.1 n r.2) :
    (rowData r).factors=r.1.factorization := by
  have hh:=encoding_filter h
  change primeRecord _=_
  rw [primeRecord_eq_factorization _ hh.1,hh.2]

/-- The read-only view is constructed solely by projection of retained fields.
No trueData or factorization operation occurs in its definition. -/
theorem completeLog_view {n N M : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hpos : M≠0) :
    DataView (flatData rows M) M := by
  refine ⟨?_,?_⟩
  · have hh:=lookupPrimes_correct h hM hpos
    change primeRecord _=_
    rw [primeRecord_eq_factorization _ hh.1,hh.2]
  · intro l hl
    have hlpos : l≠0 := by have hh:=(child_bounds hl).1;omega
    have hlmem:=log_child_present h hM hl
    cases hf : (rows.map rowData).find? (fun d=>decide (d.label=l)) with
    | none=>
      obtain ⟨r,hr,he⟩:=List.mem_map.mp hlmem
      have hh:=List.find?_eq_none.mp hf (rowData r) (List.mem_map.mpr ⟨r,hr,rfl⟩)
      simp only [rowData_label,he,decide_true] at hh
      contradiction
    | some d=>
      obtain ⟨r,hr,he⟩:=List.mem_map.mp (List.mem_of_find?_eq_some hf)
      subst d
      have hh : decide ((rowData r).label=l)=true := List.find?_some (p := fun d : FactorData => decide (d.label=l)) (a := rowData r) hf
      have he : r.1=l := (decide_eq_true_eq).mp hh
      have hv : CorrectEncoding r.1 n r.2 := (h.2.1 r hr).resolve_left (by rwa [he])
      change (match (rows.map rowData).find? (fun d=>decide (d.label=l)) with
        | none=>[] | some d=>recordPrimes d.factors)=_
      simp only [hf,rowData_factors hv,he]
end PhysicalTree

namespace DataView
variable {d : FactorData} {M : ℕ} (h : DataView d M)
include h

lemma divisorPrimes (m : ℕ) : dataDivisorPrimes d m=dataDivisorPrimes (trueData M) m := by
  simp only [dataDivisorPrimes,h.1,trueData_factors]
lemma record (m : ℕ) : dataRecord d m=dataRecord (trueData M) m := by
  rw [dataRecord,dataRecord,h.divisorPrimes]
lemma phi (m : ℕ) : dataPhi d m=dataPhi (trueData M) m := by
  rw [dataPhi,dataPhi,h.record]
lemma favorable (m n : ℕ) : dataFavorable d m n=dataFavorable (trueData M) m n := by
  rw [dataFavorable,dataFavorable,h.record]
lemma childPrimes {l : ℕ} (hl : l∈children M) :
    dataChildPrimes d l=dataChildPrimes (trueData M) l := by
  rw [h.2 l hl,(trueData_view M).2 l hl]
lemma totientPrimes {m : ℕ} (hM : 0 < M) (hd : m ∣ M) :
    dataTotientPrimes d m=dataTotientPrimes (trueData M) m := by
  have hf : primeRecord (dataDivisorPrimes (trueData M) m)=m.factorization := dataRecord_correct hM hd
  simp only [dataTotientPrimes,h.divisorPrimes,hf]
  apply List.flatMap_congr
  intro p hp
  by_cases h2 : p=2
  · simp only [ite_eq_left h2]
  · have hpm:=Nat.mem_primeFactors.mp ((Finset.mem_sort (· ≤ ·)).mp hp)
    have hc : p-1∈children M := mem_children.mpr
      ⟨p,hpm.1,hpm.2.1.trans hd,hM.ne',by have hh:=hpm.1.two_le;omega,rfl⟩
    rw [ite_eq_right h2,ite_eq_right h2,h.childPrimes hc]
lemma order (a m : ℕ) (hM : 0 < M) (hd : m ∣ M) : dataOrder d a m=dataOrder (trueData M) a m := by
  rw [dataOrder,dataOrder,h.totientPrimes hM hd,h.phi]
lemma listSuccess (m n K : ℕ) : dataListSuccess d m n K=dataListSuccess (trueData M) m n K := by
  rw [dataListSuccess,dataListSuccess,h.favorable]
lemma orderSuccess (a m K : ℕ) (hM : 0 < M) (hd : m ∣ M) :
    dataOrderSuccess d a m K=dataOrderSuccess (trueData M) a m K := by
  rw [dataOrderSuccess,dataOrderSuccess,h.order a m hM hd]
end DataView
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FlatDataPredicates.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree OrderTrial
namespace DataView
variable {d : FactorData} {M : ℕ} (h : DataView d M)
include h

lemma residueGood {m : ℕ} (hM : 0 < M) (hd : m ∣ M) (a : ℕ) :
    dataResidueGood d a m ↔ dataResidueGood (trueData M) a m := by
  have ho (p : ℕ) : dataOrder d a (p^m.factorization p)=
      dataOrder (trueData M) a (p^m.factorization p) :=
    h.order _ _ hM ((Nat.ordProj_dvd m p).trans hd)
  simp only [dataResidueGood,h.record,dataRecord_correct hM hd,ho]

lemma canonicalResidue (a m : ℕ) :
    dataCanonicalResidue d a m ↔ dataCanonicalResidue (trueData M) a m := by
  simp only [dataCanonicalResidue,h.record]

lemma goodList {m : ℕ} (hM : 0 < M) (hd : m ∣ M) (n : ℕ)
    (y : Basis (Completion.transitionWidth n)) :
    dataGoodList d m n y ↔ dataGoodList (trueData M) m n y := by
  simp only [dataGoodList,h.residueGood hM hd]

lemma canonicalList (m n : ℕ) (hn : 0 < n) (y : Basis (Completion.transitionWidth n)) :
    dataCanonicalList d m n hn y ↔ dataCanonicalList (trueData M) m n hn y := by
  simp only [dataCanonicalList,h.canonicalResidue]

lemma listPassed {n : ℕ} (hM : 0 < M) (m : Basis n) (hd : (bitsValue m).toNat ∣ M)
    (hn : 0 < n) (r : PhysicalListSlots.Result n) :
    dataListPassed d m hn r ↔ dataListPassed (trueData M) m hn r := by
  have hg : (fun x=>dataGoodList d (bitsValue m).toNat n (PhysicalListSlots.ordinary x))=
      (fun x=>dataGoodList (trueData M) (bitsValue m).toNat n (PhysicalListSlots.ordinary x)) := by
    funext x
    exact propext (h.goodList hM hd n _)
  have hc : dataCanonicalList d (bitsValue m).toNat n hn=
      dataCanonicalList (trueData M) (bitsValue m).toNat n hn := by
    funext y
    exact propext (h.canonicalList _ n hn y)
  rw [dataListPassed,dataListPassed,hg,hc,h.listSuccess]

lemma orderPassed {n : ℕ} (hM : 0 < M) (a m : Basis n) (hd : (bitsValue m).toNat ∣ M)
    (r : OrderSlots.Result n) : dataOrderPassed d a m r ↔ dataOrderPassed (trueData M) a m r := by
  classical
  simp only [dataOrderPassed,h.order _ _ hM hd,h.orderSuccess _ _ _ hM hd]

lemma splitPassed {n : ℕ} (hM : 0 < M) (m : Basis n) (hd : (bitsValue m).toNat ∣ M)
    (hn : 0 < n) (r : UniversalSplit.Raw n) :
    dataSplitPassed d m hn r ↔ dataSplitPassed (trueData M) m hn r := by
  classical
  simp only [dataSplitPassed,h.listPassed hM m hd hn,h.orderPassed hM _ m hd]

/-- Actual verified data give the ideal local event on exactly the same retained
outcome. The statement covers all nonzero divisors of a verified node. -/
theorem splitPassed_correct {n : ℕ} (hM : 0 < M) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat ∣ M)
    (hn : 0 < n) (r : UniversalSplit.Raw n) :
    dataSplitPassed d m hn r ↔ UniversalSplit.passed m r := by
  rw [h.splitPassed hM m hd hn]
  exact dataSplitPassed_correct hM m hm hd hn r
end DataView
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeStateFailure.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController
namespace NodeStateCircuit

/-- Failed candidates leave genuine pending factors unchanged and only set the
sticky verifier bit. They cannot introduce an unrelated query into the log. -/
lemma step_failure {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w)
    (xs ys : List (Basis w)) (b : Bool) (hx : xs.length ≤ s)
    (ha : 2 ≤ (bitsValue a).toNat) (hp : ¬(bitsValue a).toNat.Prime)
    (hd : ¬ProperDivisor (bitsValue a).toNat (bitsValue d).toNat) :
    (step s w).eval (Fin.append (pack (a::xs) ys b) d)=pack (a::xs) ys true := by
  have he : (emission s w).eval (Fin.append (pack (a::xs) ys b) d)=(fun _=>false) := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_pack_cons hw,ite_eq_right hp]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack (a::xs) ys b) d) 0=true := by
    rw [zeroWord_value,he,zeroBasis_value]
    rfl
  have hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack (a::xs) d) 0=true :=
    (NodeCircuit.failed_pack_cons hw a d xs ha).mpr ⟨hp,hd⟩
  have hb : (nextBad s w).eval (Fin.append (pack (a::xs) ys b) d)=(fun _=>true) := by
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rw [nextBad,eval_bor,eval_comp,old_append,bad_pack,eval_comp,nodeInput_pack,hf,Bool.or_true]
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_pack_cons hw _ _ _ hx ha,ite_eq_right hp,ite_eq_right hd,nextOutput,wordMux_eval,
    ite_eq_left hz,eval_comp,old_append,output_pack,hb]
  rfl
end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalNodeSafety.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic FactorController AuxiliaryTree OrderTrial
namespace PhysicalNode

lemma next_safe {n N s : ℕ} (hn : 128  ≤  n) (xs ys : List (Basis (n+1)))
    (b : Bool) (h : Good n N s xs ys) (r : FixedSplit.Raw n) :
    ∃ xs' ys' b', (machine n s).next (NodeStateCircuit.pack xs ys b) r=
      NodeStateCircuit.pack xs' ys' b' ∧ Good n N s xs' ys' := by
  cases xs with
  | nil=>exact ⟨[],ys,b,next_nil hn ys b r,h⟩
  | cons a xs=>
    have ha:=h.bounded a (by simp)
    have ht : ∀ x∈xs,2 ≤ (bitsValue x).toNat ∧ (bitsValue x).toNat < 2^n :=
      fun x hx=>h.bounded x (List.mem_cons_of_mem _ hx)
    have hcap : xs.length ≤ s := by have hh:=h.length_le; simp only [List.length_cons] at hh;omega
    by_cases hp : (bitsValue a).toNat.Prime
    · refine ⟨xs,a::ys,b,next_prime hn a xs ys b hcap hp r,⟨ht,?_,?_,?_⟩⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hp
        · exact h.primes z hz
      · have hh:=h.product
        simp only [values_cons,List.prod_cons] at hh ⊢
        calc
          (values xs).prod*((bitsValue a).toNat*(values ys).prod)=
            ((bitsValue a).toNat*(values xs).prod)*(values ys).prod := by ac_rfl
          _=N := hh
      · have hw:=h.clock
        rw [values_cons,weight_prime _ _ hp] at hw
        omega
    · let q:=(query n s).eval (NodeStateCircuit.pack (a::xs) ys b)
      let d:=decoded q r
      by_cases hd : ProperDivisor (bitsValue a).toNat (bitsValue d).toNat
      · let z:=(NodeCircuit.quotient s (n+1)).eval (NodeCircuit.pack (a::xs) d)
        have hz : (bitsValue z).toNat=(bitsValue a).toNat/(bitsValue d).toNat :=
          NodeCircuit.quotient_pack a d xs
        have hquot:=hd.quotient
        refine ⟨d::z::xs,ys,b,?_,⟨?_,h.primes,?_,?_⟩⟩
        · rw [next_eq]
          exact NodeStateCircuit.step_split (by omega) _ _ _ _ _ hcap ha.1 hp hd
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact ⟨by have hh:=hd.1;omega,hd.2.1.trans ha.2⟩
          · rcases List.mem_cons.mp hv with rfl | hv
            · rw [hz]
              exact ⟨hquot.1,hquot.2.1.trans ha.2⟩
            · exact ht v hv
        · have hh:=h.product
          simp only [values_cons,List.prod_cons] at hh ⊢
          rw [hz,←Nat.mul_assoc,hd.quotient.2.2]
          exact hh
        · have hw:=h.clock
          rw [values_cons,weight_split hd] at hw
          simpa only [values_cons,hz] using
            (show weight ((bitsValue d).toNat::(bitsValue a).toNat/(bitsValue d).toNat::values xs) ≤ s by omega)
      · refine ⟨a::xs,ys,true,?_,h⟩
        rw [next_eq]
        exact NodeStateCircuit.step_failure (by omega) a d xs ys b hcap ha.1 hp hd

/-- Safety is unconditional on every raw quantum outcome. In particular even a
failed retained candidate only stalls; all subsequent nonzero queries divide
this node's original modulus. -/
theorem config_safe {n N : ℕ} (hn : 128  ≤  n) (hN : 2  ≤  N) (hb : N < 2^n)
    (t : ℕ) (h : SplitMachine.Trace n t) :
    ∃ xs ys b, (machine n (2*n)).config
        (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h=NodeStateCircuit.pack xs ys b ∧
      Good n N (2*n) xs ys := by
  induction t with
  | zero=>
    have hbw : N < 2^(n+1) := hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have ha : (bitsValue (natBasis (n+1) N)).toNat=N := by
      rw [natBasis_value,Nat.mod_eq_of_lt hbw]
    refine ⟨[natBasis (n+1) N],[],false,rfl,⟨?_,?_,?_,?_⟩⟩
    · intro a ha'
      have he : a=natBasis (n+1) N := List.mem_singleton.mp ha'
      subst a
      rw [ha]
      exact ⟨hN,hb⟩
    · simp
    · simp only [values_cons,values_nil,List.prod_cons,List.prod_nil,ha,mul_one]
    · have hs:=splitWeight_bound (by omega : 0 < N) hb
      simp only [values_cons,values_nil,ha,weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega
  | succ t ih=>
    obtain ⟨xs,ys,b,he,hg⟩:=ih h.1
    obtain ⟨xs',ys',b',he',hg'⟩:=next_safe hn xs ys b hg h.2
    refine ⟨xs',ys',b',?_,hg'⟩
    change (machine n (2*n)).next ((machine n (2*n)).config _ t h.1) h.2=_
    rw [he,he']

lemma Good.pending_dvd {n N s : ℕ} {xs ys : List (Basis (n+1))}
    (h : Good n N s xs ys) (a : Basis (n+1)) (ha : a∈xs) : (bitsValue a).toNat ∣ N := by
  rw [←h.product]
  exact (List.dvd_prod (List.mem_map.mpr ⟨a,ha,rfl⟩)).trans (dvd_mul_right _ _)

theorem query_safe {n N : ℕ} (hn : 128  ≤  n) (hN : 2  ≤  N) (hb : N < 2^n)
    (t : ℕ) (h : SplitMachine.Trace n t) :
    let m:=(bitsValue ((query n (2*n)).eval ((machine n (2*n)).config
      (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h))).toNat
    m=0 ∨ (2 ≤ m ∧ m < 2^n ∧ m ∣ N) := by
  obtain ⟨xs,ys,b,he,hg⟩:=config_safe hn hN hb t h
  dsimp only
  rw [he]
  cases xs with
  | nil=>
    left
    rw [query,eval_comp,NodeStateCircuit.top_pack]
    change (bitsValue ((resizeWord (n+1) n).eval (fun _=>false))).toNat=0
    rw [resizeWord_value,zeroBasis_value]
    simp
  | cons a xs=>
    have ha:=hg.bounded a (by simp)
    rw [query_value a xs ys b ha.2]
    exact Or.inr ⟨ha.1,ha.2,hg.pending_dvd a (by simp)⟩
end PhysicalNode
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetrospectiveNode.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree
namespace PhysicalNode

lemma natBasis_zero (w : ℕ) : natBasis w 0=(fun _=>false) := by
  apply (bitsEquiv w).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue (natBasis w 0)).toNat=(bitsValue (fun _=>false)).toNat
  rw [natBasis_value,zeroBasis_value]
  simp

lemma start_zero {n : ℕ} (q : Basis n) (hq : (bitsValue q).toNat=0) :
    NodeKernel.start q=NodeStateCircuit.pack (s:=2*n) [] [] false := by
  rw [NodeKernel.start,startNet_eval,hq,natBasis_zero,NodeStateCircuit.pack,NodeStateCircuit.pack]
  apply congrArg (fun x=>Fin.append (Fin.append x (stackEncoding (2*n+1) (n+1) [])) (fun _=>false))
  apply block_ext
  intro i
  rw [block_stackEncoding,block_stackEncoding]
  cases he : i.val with
  | zero=>rfl
  | succ j=>rfl

lemma config_zero {n : ℕ} (hn : 128 ≤ n) (q : Basis n) (hq : (bitsValue q).toNat=0)
    (t : ℕ) (r : SplitMachine.Trace n t) :
    (machine n (2*n)).config (NodeKernel.start q) t r=NodeStateCircuit.pack [] [] false := by
  induction t with
  | zero=>exact start_zero q hq
  | succ t ih=>
    change (machine n (2*n)).next ((machine n (2*n)).config (NodeKernel.start q) t r.1) r.2=_
    rw [ih,next_nil hn]

lemma query_zero {n : ℕ} (hn : 128 ≤ n) (q : Basis n) (hq : (bitsValue q).toNat=0)
    (t : ℕ) (r : SplitMachine.Trace n t) :
    (bitsValue ((query n (2*n)).eval
      ((machine n (2*n)).config (NodeKernel.start q) t r))).toNat=0 := by
  rw [config_zero hn q hq,query,eval_comp,NodeStateCircuit.top_pack]
  change (bitsValue ((resizeWord (n+1) n).eval (fun _=>false))).toNat=0
  rw [resizeWord_value,zeroBasis_value]
  simp
end PhysicalNode

lemma dataSplitPassed_zero {n : ℕ} (d : FactorData) (q : Basis n) (hn : 0<n)
    (hq : (bitsValue q).toNat=0) (r : UniversalSplit.Raw n) :
    dataSplitPassed d q hn r ↔ UniversalSplit.passed q r := by
  classical
  have hh : ¬UniversalSplit.Hard (bitsValue q).toNat := by
    rintro ⟨h,_⟩
    omega
  rw [dataSplitPassed,ite_eq_right hh,UniversalSplit.passed,dite_eq_right hh]

namespace NodeKernel
/-- Retrospective evaluation on the actual split trace, with one verified
read-only factor-data view for this physical node. The controller and all query
words are the same ones used by the physical run. -/
noncomputable def dataTests {n : ℕ} (q : Basis n) (d : FactorData) (hn : 0<n) :
    (t : ℕ)→SplitMachine.Trace n t→Prop
  | 0,_=>True
  | t+1,r=>dataTests q d hn t r.1 ∧ dataSplitPassed d
      ((PhysicalNode.query n (2*n)).eval
        ((PhysicalNode.machine n (2*n)).config (start q) t r.1)) hn r.2

lemma dataTests_correct {n : ℕ} (hn : 128 ≤ n) (q : Basis n) (d : FactorData)
    (hq : (bitsValue q).toNat=0 ∨ 2 ≤ (bitsValue q).toNat)
    (hd : (bitsValue q).toNat≠0 → DataView d (bitsValue q).toNat)
    (t : ℕ) (r : SplitMachine.Trace n t) :
    dataTests q d (by omega) t r ↔ (PhysicalNode.machine n (2*n)).passed (start q) t r := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    apply and_congr (ih r.1)
    rcases hq with hz | hm
    · exact dataSplitPassed_zero d _ _ (PhysicalNode.query_zero hn q hz t r.1) r.2
    · have hb : (bitsValue q).toNat<2^n := (bitsValue q).isLt
      have hs:=PhysicalNode.query_safe hn hm hb t r.1
      rw [←PhysicalNode.startNet_eval n q] at hs
      change _ ∨ _ at hs
      rcases hs with hz | hs
      · exact dataSplitPassed_zero d _ _ hz r.2
      · exact (hd (by omega)).splitPassed_correct (by omega) _ hs.1 hs.2.2 (by omega) r.2

noncomputable def dataPassed {n : ℕ} (q : Basis n) (d : FactorData) (hn : 0<n)
    (r : Raw n) : Prop := dataTests q d hn (2*n) r

lemma dataPassed_correct {n : ℕ} (hn : 128 ≤ n) (q : Basis n) (d : FactorData)
    (hq : (bitsValue q).toNat=0 ∨ 2 ≤ (bitsValue q).toNat)
    (hd : (bitsValue q).toNat≠0 → DataView d (bitsValue q).toNat) (r : Raw n) :
    dataPassed q d (by omega) r ↔ passed q r := dataTests_correct hn q d hq hd (2*n) r
end NodeKernel
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SplitHistoryAccess.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

def previousNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (M.width t) :=
  (select (firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork)).comp
    (select (firstRegister (M.width t) (FixedSplit.width n) M.initWork))
def lastSplitNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (FixedSplit.width n) :=
  (select (firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork)).comp
    (select (targetRegister (M.width t) (FixedSplit.width n) M.initWork))

lemma previousNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : FixedSplit.Raw n) :
    (M.previousNet t).eval (M.encoded x (t+1) (h,r))=M.encoded x t h := by
  rw [previousNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (FixedSplit.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork) ∘
      firstRegister (M.width t) (FixedSplit.width n) M.initWork=_
  rw [packed_first,packed_first]
lemma lastSplitNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : FixedSplit.Raw n) :
    (M.lastSplitNet t).eval (M.encoded x (t+1) (h,r))=
      FixedSplit.encoding (M.query.eval (M.config x t h)) r := by
  rw [lastSplitNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (FixedSplit.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork) ∘
      targetRegister (M.width t) (FixedSplit.width n) M.initWork=_
  rw [packed_first,packed_targetRegister]
end SplitMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/HardFilterCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace UniversalSplit

def hardOn {k n : ℕ} (m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  ((wordLe (wordConstant (BitVec.ofNat n 2)) m).band (m.comp (primeWord n)).bnot).band
    ((evenOn m).bnot.band ((m.comp (resizeWord n (rootWidth n))).comp (perfectPowerNet n)).bnot)

lemma hardOn_value {k n : ℕ} (hn : 128≤n) (m : BooleanNetwork k n) (x : Basis k) :
    (hardOn m).eval x 0=true ↔ Hard (bitsValue (m.eval x)).toNat := by
  have hf : 2<2^n := (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) (by omega : 2≤n))
  have hp : (((m.comp (resizeWord n (rootWidth n))).comp (perfectPowerNet n)).eval x 0=true) ↔
      Primality.PerfectPower (bitsValue (m.eval x)).toNat := by
    rw [eval_comp,perfectPowerNet_correct (by omega)]
    · rw [eval_comp,resizeWord_toNat (rootWidth_ge n)]
    · rw [eval_comp,resizeWord_toNat (rootWidth_ge n)]
      exact (bitsValue (m.eval x)).isLt
  rw [hardOn,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    wordLe_eval,decide_eq_true_eq,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hf,
    bnot_value,eval_comp,primeWord_value hn,eval_band,Bool.and_eq_true,bnot_value,
    evenOn_value (by omega),bnot_value,hp]
  rw [←even_iff_two_dvd,Nat.not_even_iff_odd]
  exact and_assoc
end UniversalSplit
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RationalPowerCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
namespace NatExpr
variable {v : Type*}

lemma pow_size (a : NatExpr v) (k : ℕ) : (a.pow k).size=k*(a.size+1)+1 := by
  induction k with
  | zero=>simp [pow,size]
  | succ k ih=>simp only [pow,size,ih]; ring
lemma pow_sharedCost (a : NatExpr v) (k : ℕ) :
    (a.pow k).sharedCost=k*(a.sharedCost+1)+1 := by
  induction k with
  | zero=>simp [pow,sharedCost]
  | succ k ih=>simp only [pow,sharedCost,ih]; ring
lemma pow_maxConst (a : NatExpr v) (k : ℕ) : (a.pow k).maxConst ≤ Nat.max a.maxConst 1 := by
  induction k with
  | zero=>exact le_max_right _ _
  | succ k ih=>exact max_le ih (le_max_left _ _)

end NatExpr
namespace IntExpr
variable {v : Type*}

/-- Power of a balanced signed integer without the exponentially expanding
positive/negative multiplication tree. The sign test is static in parity and
uses only absolute value and linear-length natural-power expressions. -/
def signedPower (a : IntExpr v) (k : ℕ) : IntExpr v :=
  let M:=ofNat (a.natAbs.pow k)
  if Even k then M else iteLe a.neg a.pos M M.negation

@[simp] lemma eval_signedPower (x : v→ℕ) (a : IntExpr v) (k : ℕ) :
    (signedPower a k).eval x=(a.eval x)^k := by
  have hm : (ofNat (a.natAbs.pow k)).eval x=|a.eval x|^k := by
    simp only [eval_ofNat,NatExpr.eval_pow,eval_natAbs,Nat.cast_pow,Int.natCast_natAbs]
  unfold signedPower
  split_ifs with hk
  · rw [hm]
    exact hk.pow_abs _
  · rw [eval_iteLe,eval_negation,hm]
    have ho : Odd k := Nat.not_even_iff_odd.mp hk
    by_cases hp : a.neg.eval x≤a.pos.eval x
    · rw [ite_eq_left hp,abs_of_nonneg]
      dsimp only [eval]
      omega
    · rw [ite_eq_right hp,abs_of_neg,ho.neg_pow,neg_neg]
      dsimp only [eval]
      omega

lemma signedPower_size (a : IntExpr v) (k : ℕ) :
    (a.signedPower k).pos.size ≤ 4*(k+1)*(a.pos.size+a.neg.size+2) ∧
    (a.signedPower k).neg.size ≤ 4*(k+1)*(a.pos.size+a.neg.size+2) := by
  unfold signedPower
  split_ifs <;>
    simp only [ofNat,iteLe,negation,natAbs,NatExpr.size,NatExpr.pow_size] <;>
    constructor <;> nlinarith

lemma signedPower_sharedCost (a : IntExpr v) (k : ℕ) :
    (a.signedPower k).pos.sharedCost ≤ 6*(k+1)*(a.pos.sharedCost+a.neg.sharedCost+2) ∧
    (a.signedPower k).neg.sharedCost ≤ 6*(k+1)*(a.pos.sharedCost+a.neg.sharedCost+2) := by
  unfold signedPower
  split_ifs <;>
    simp only [ofNat,iteLe,negation,natAbs,NatExpr.sharedCost,NatExpr.pow_sharedCost] <;>
    constructor <;> nlinarith

lemma signedPower_maxConst (a : IntExpr v) (k : ℕ) :
    (a.signedPower k).pos.maxConst ≤ max (max a.pos.maxConst a.neg.maxConst) 1 ∧
    (a.signedPower k).neg.maxConst ≤ max (max a.pos.maxConst a.neg.maxConst) 1 := by
  have hp := NatExpr.pow_maxConst a.natAbs k
  have he : a.natAbs.maxConst=max a.pos.maxConst a.neg.maxConst := by
    simp only [natAbs,NatExpr.maxConst]
    omega
  rw [he] at hp
  have h₁ : a.pos.maxConst ≤ max (max a.pos.maxConst a.neg.maxConst) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have h₂ : a.neg.maxConst ≤ max (max a.pos.maxConst a.neg.maxConst) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  unfold signedPower
  split_ifs <;> simp only [ofNat,iteLe,negation,NatExpr.maxConst]
  · exact ⟨hp,Nat.zero_le _⟩
  · simp only [max_le_iff]
    exact ⟨⟨⟨h₂,h₁⟩,hp,Nat.zero_le _⟩,⟨⟨h₂,h₁⟩,Nat.zero_le _,hp⟩⟩
end IntExpr
namespace RatExpr
variable {v : Type*}

/-- Exact rational power, with polynomial syntax in k, including zero
unreduced denominators. Existing `pow` and its semantics are not changed. -/
def signedPower (a : RatExpr v) (k : ℕ) : RatExpr v :=
  ⟨a.num.signedPower k,a.den.pow k⟩

@[simp] lemma eval_signedPower (x : v→ℕ) (a : RatExpr v) (k : ℕ) :
    (a.signedPower k).eval x=(a.eval x)^k := by
  simp only [signedPower,eval,IntExpr.eval_signedPower,NatExpr.eval_pow,
    Int.cast_pow,Nat.cast_pow,div_pow]

/-- The repeated-success expression used by both real transitions, without
an exponentially expanded balanced-integer numerator syntax. -/
def repeatedSuccess (a : RatExpr v) (K : ℕ) : RatExpr v :=
  (const 1).sub (((const 1).sub a).signedPower K)
lemma repeatedSuccess_value (x : v→ℕ) (a : RatExpr v) (K : ℕ) :
    (a.repeatedSuccess K).eval x=1-(1-a.eval x)^K := by
  simp only [repeatedSuccess,eval_sub,eval_const,eval_signedPower]

end RatExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CompletionFilterCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion
namespace Expressions
variable {v : Type*}

def ordinaryMass (t : ℕ) (s : RatExpr v) : RatExpr v :=
  (RatExpr.const (1-1/(2:ℚ)^t)).mul s

def coefficient (W t : ℕ) (s z : RatExpr v) : RatExpr v :=
  (RatExpr.ofInt (((RatExpr.const ((2:ℚ)^(W+t+2))).mul
    (z.div (ordinaryMass t s))).floor)).div (RatExpr.const ((2:ℚ)^(W+t+2)))

def guess (W t : ℕ) (s z : RatExpr v) : RatExpr v :=
  ((z.sub ((coefficient W t s z).mul (ordinaryMass t s))).mul
    (RatExpr.const ((2:ℚ)^W))).div (RatExpr.const (1/(2:ℚ)^t))

lemma ordinaryMass_value (x : v→ℕ) (t : ℕ) (s : RatExpr v) :
    (ordinaryMass t s).eval x=(1-1/(2:ℚ)^t)*s.eval x := by
  simp only [ordinaryMass,RatExpr.eval_mul,RatExpr.eval_const]
lemma coefficient_value (x : v→ℕ) (W t : ℕ) (s z : RatExpr v) :
    (coefficient W t s z).eval x=coeff W t (s.eval x) (z.eval x) := by
  simp only [coefficient,RatExpr.eval_div,RatExpr.eval_ofInt,RatExpr.eval_floor,
    RatExpr.eval_mul,RatExpr.eval_const,ordinaryMass_value,coeff,Exactness.completionCoeff]
lemma guess_value (x : v→ℕ) (W t : ℕ) (s z : RatExpr v) :
    (guess W t s z).eval x=guessRetention W t (s.eval x) (z.eval x) := by
  simp only [guess,RatExpr.eval_div,RatExpr.eval_mul,RatExpr.eval_sub,
    RatExpr.eval_const,coefficient_value,ordinaryMass_value,
    guessRetention,Exactness.completionRemainder,coeff]

end Expressions

/-- Literal deferred completion filter on retained registers. The input s and
canonical-output circuits are to be computed from the verified full log; this
compiler does not smuggle those quantities into the preparation. -/
def filterNet {v : Type*} {k b W t : ℕ} (d : ℕ)
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (guess canonical : BooleanNetwork k W)
    (coin : NatExpr v) (good : BooleanNetwork k 1) : BooleanNetwork k 1 :=
  let rare:=zeroWord branch
  let ordinaryKeep:=retentionNet (coinBits W t d) (Expressions.coefficient W t s z) coin vars
  let guessKeep:=retentionNet (coinBits W t d) (Expressions.guess W t s z) coin vars
  ((rare.bnot).band (good.band ordinaryKeep)).bor
    (rare.band ((equalOn guess canonical).band guessKeep))

lemma filterNet_value {v : Type*} {k b W t : ℕ} (d : ℕ)
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (guess canonical : BooleanNetwork k W)
    (coin : NatExpr v) (good : BooleanNetwork k 1) (x : Basis k) :
    (filterNet d s z vars branch guess canonical coin good).eval x 0=true ↔
      ((bitsValue (branch.eval x)).toNat≠0 ∧ (good.eval x 0=true ∧
        coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)<
          (Int.floor (coeff W t (s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))
            (z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))*(2:ℚ)^(coinBits W t d))).toNat)) ∨
      ((bitsValue (branch.eval x)).toNat=0 ∧ (guess.eval x=canonical.eval x ∧
        coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)<
          (Int.floor (guessRetention W t (s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))
            (z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))*(2:ℚ)^(coinBits W t d))).toNat)) := by
  have he : (bitsValue (guess.eval x)).toNat=(bitsValue (canonical.eval x)).toNat ↔
      guess.eval x=canonical.eval x := by
    constructor
    · intro h
      exact (bitsEquiv W).injective (BitVec.eq_of_toNat_eq h)
    · intro h; rw [h]
  simp only [filterNet,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    bnot_value,zeroWord_value,retentionNet_value,Expressions.coefficient_value,
    equalOn_value,Expressions.guess_value,he]


/-- On the very same retained record, the gate flag is exactly the §6 event. -/
theorem filterNet_passed {α v : Type*} {k b W t d : ℕ}
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (guess canonical : BooleanNetwork k W)
    (coin : NatExpr v) (good : BooleanNetwork k 1) (P : α→Prop)
    (x : Basis k) (r : Raw α W t d) (y₀ : Basis W) (S Z : ℚ)
    (hbranch : branch.eval x=r.1) (hguess : guess.eval x=r.2.2.1)
    (hcanonical : canonical.eval x=y₀)
    (hcoin : coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=(bitsValue r.2.2.2).toNat)
    (hgood : good.eval x 0=true ↔ P r.2.1)
    (hs : s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=S)
    (hz : z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=Z) :
    (filterNet d s z vars branch guess canonical coin good).eval x 0=true ↔ passed P y₀ S Z r := by
  rw [filterNet_value,hbranch,hguess,hcanonical,hcoin,hgood,hs,hz]
  rfl
end Completion
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CompletionPredicateCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion

/-- A deferred guess predicate, rather than a circuit that constructs the
canonical CRT string.  Both branches use the same retained completion coin. -/
def predicateFilter {v : Type*} {k b W t : ℕ} (d : ℕ)
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (coin : NatExpr v)
    (good guessGood : BooleanNetwork k 1) : BooleanNetwork k 1 :=
  let rare:=zeroWord branch
  let ordinaryKeep:=retentionNet (coinBits W t d) (Expressions.coefficient W t s z) coin vars
  let guessKeep:=retentionNet (coinBits W t d) (Expressions.guess W t s z) coin vars
  ((rare.bnot).band (good.band ordinaryKeep)).bor
    (rare.band (guessGood.band guessKeep))

lemma predicateFilter_value {v : Type*} {k b W t : ℕ} (d : ℕ)
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (coin : NatExpr v)
    (good guessGood : BooleanNetwork k 1) (x : Basis k) :
    (predicateFilter (W:=W) d s z vars branch coin good guessGood).eval x 0=true ↔
      ((bitsValue (branch.eval x)).toNat≠0 ∧ (good.eval x 0=true ∧
        coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)<
          (Int.floor (coeff W t (s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))
            (z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))*(2:ℚ)^(coinBits W t d))).toNat)) ∨
      ((bitsValue (branch.eval x)).toNat=0 ∧ (guessGood.eval x 0=true ∧
        coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)<
          (Int.floor (guessRetention W t (s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))
            (z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))*(2:ℚ)^(coinBits W t d))).toNat)) := by
  simp only [predicateFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    bnot_value,zeroWord_value,retentionNet_value,Expressions.coefficient_value,
    Expressions.guess_value]

/-- Exact same-history predicate semantics: this theorem does not supply or
assume an algorithm for either of the two input Boolean tests. -/
theorem predicateFilter_test {α v : Type*} {k b W t d : ℕ}
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (coin : NatExpr v)
    (good guessGood : BooleanNetwork k 1) (x : Basis k)
    (P : α→Prop) (Q : Basis W→Prop) (r : Raw α W t d) (S Z : ℚ)
    (hbranch : branch.eval x=r.1)
    (hcoin : coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=(bitsValue r.2.2.2).toNat)
    (hgood : good.eval x 0=true ↔ P r.2.1)
    (hguess : guessGood.eval x 0=true ↔ Q r.2.2.1)
    (hs : s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=S)
    (hz : z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=Z) :
    (predicateFilter (W:=W) d s z vars branch coin good guessGood).eval x 0=true ↔
      test P Q S Z r := by
  rw [predicateFilter_value,hbranch,hcoin,hgood,hguess,hs,hz]
  rfl
end Completion
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TwoAdicCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

lemma twoadic_lt_width {d n : ℕ} (hd : d≠0) (hb : d<2^n) : padicValNat 2 d<n := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hd)
    ((padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) hd).mpr le_rfl)).trans_lt hb

lemma twoadic_eq_iff {a b n : ℕ} (ha : a≠0) (hb : b≠0) (haB : a<2^n) (hbB : b<2^n) :
    padicValNat 2 a=padicValNat 2 b ↔ ∀ i : Fin n,2^i.val∣a ↔ 2^i.val∣b := by
  simp only [padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) ha,
    padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) hb]
  constructor
  · intro he i; rw [he]
  · intro h
    exact le_antisymm ((h ⟨_,twoadic_lt_width ha haB⟩).mp le_rfl)
      ((h ⟨_,twoadic_lt_width hb hbB⟩).mpr le_rfl)

namespace BitArithmetic

def bequiv {k : ℕ} (a b : BooleanNetwork k 1) : BooleanNetwork k 1 := (a.bxor b).bnot
lemma bequiv_value {k : ℕ} (a b : BooleanNetwork k 1) (x : Basis k) :
    (bequiv a b).eval x 0=true ↔ (a.eval x 0=true ↔ b.eval x 0=true) := by
  rw [bequiv,bnot_value,eval_bxor]
  cases a.eval x 0 <;> cases b.eval x 0 <;> decide
lemma bequiv_count {k : ℕ} (a b : BooleanNetwork k 1) :
    (bequiv a b).net.count=2*a.net.count+2*b.net.count+9 := by
  simp only [bequiv,count_bnot,count_bxor]

/-- Equality of exact dyadic valuations by bounded divisibility tests.  The
parameter is the word width, not an input-dependent search cap. -/
def sameTwoVal {k n : ℕ} (a b : BooleanNetwork k n) : BooleanNetwork k 1 :=
  all (List.ofFn (fun i : Fin n=>bequiv (a.comp (dividesNet n (2^i.val)))
    (b.comp (dividesNet n (2^i.val)))))

lemma sameTwoVal_value {k n : ℕ} (a b : BooleanNetwork k n) (x : Basis k)
    (ha : (bitsValue (a.eval x)).toNat≠0) (hb : (bitsValue (b.eval x)).toNat≠0) :
    (sameTwoVal a b).eval x 0=true ↔
      padicValNat 2 (bitsValue (a.eval x)).toNat=padicValNat 2 (bitsValue (b.eval x)).toNat := by
  rw [twoadic_eq_iff ha hb (bitsValue (a.eval x)).isLt (bitsValue (b.eval x)).isLt]
  simp only [sameTwoVal,all_eval,List.forall_mem_ofFn_iff,bequiv_value,eval_comp,
    dividesNet_value _ _ _ (Nat.pow_lt_pow_right (by decide : 1<2) (Fin.isLt _))]

lemma sameTwoVal_count {k n : ℕ} (a b : BooleanNetwork k n) :
    (sameTwoVal a b).net.count≤n*(2*a.net.count+2*b.net.count+864*n*n+616*n+118)+1 := by
  have hh:=all_count (List.ofFn (fun i : Fin n=>bequiv (a.comp (dividesNet n (2^i.val)))
    (b.comp (dividesNet n (2^i.val)))) )
    (c:=2*a.net.count+2*b.net.count+864*n*n+616*n+117) (by
      intro c hc
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc
      have hd:=dividesNet_count n (2^i.val)
      simp only [bequiv_count,count_comp]
      nlinarith)
  change (all _).net.count≤_
  simp only [List.length_ofFn] at hh
  have hr : 2*a.net.count+2*b.net.count+864*n*n+616*n+117+1=
      2*a.net.count+2*b.net.count+864*n*n+616*n+118 := by omega
  rwa [hr] at hh
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableOrder.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

lemma divisorPrimes_subset (m : ℕ) (ps : List ℕ) : divisorPrimes m ps ⊆ ps := by
  induction ps generalizing m with
  | nil=>simp [divisorPrimes]
  | cons p ps ih=>
    intro q hq
    rw [divisorPrimes] at hq
    split_ifs at hq
    · rcases List.mem_cons.mp hq with rfl|hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ hq)
    · exact List.mem_cons_of_mem _ (ih _ hq)

lemma primeRecord_support_subset (ps : List ℕ) : ∀ p∈(primeRecord ps).support,p∈ps := by
  induction ps with
  | nil=>simp [primeRecord]
  | cons q qs ih=>
    intro p hp
    have hp':=(Finsupp.mem_support_iff).mp hp
    by_cases he : p=q
    · subst p; exact List.mem_cons_self
    · have htail : (primeRecord qs) p≠0 := by
        simpa only [primeRecord,Finsupp.add_apply,Finsupp.single_eq_of_ne he,zero_add] using hp'
      exact List.mem_cons_of_mem _ (ih p (Finsupp.mem_support_iff.mpr htail))

namespace PhysicalTree
/-- A fixed rectangular table of prime candidates. Unused rows and zero
padding become 2. This requires no support enumeration or factor search. -/
def tableFactors (rows : List (ℕ×List ℕ)) : List ℕ :=
  rows.flatMap (fun r=>r.2.map (fun p=>if r.1=0 ∨ p=0 then 2 else p))

lemma tableFactors_prime {n N : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) : ∀ p∈tableFactors rows,p.Prime := by
  intro p hp
  obtain ⟨r,hr,hp⟩:=List.mem_flatMap.mp hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  split_ifs with hz
  · exact Nat.prime_two
  · have hr0 : r.1≠0 := fun he=>hz (Or.inl he)
    have hq0 : q≠0 := fun he=>hz (Or.inr he)
    have hv:=(h.2.1 r hr).resolve_left hr0
    exact (encoding_filter hv).1 q (List.mem_filter.mpr ⟨hq,by simpa using hq0⟩)

lemma lookupPrimes_subset_table {rows : List (ℕ×List ℕ)} {M : ℕ} (hM : M≠0) :
    lookupPrimes rows M ⊆ tableFactors rows := by
  intro p hp
  obtain ⟨hp,hp0⟩:=List.mem_filter.mp hp
  have hp0 : p≠0 := by simpa only [decide_eq_true_eq] using hp0
  cases hf : rows.find? (fun r=>decide (r.1=M)) with
  | none=>simp only [lookupFields,hf,List.not_mem_nil] at hp
  | some r=>
    have hr:=List.mem_of_find?_eq_some hf
    have he : r.1=M := by simpa only [decide_eq_true_eq] using List.find?_some hf
    have hpr : p∈r.2 := by simpa only [lookupFields,hf] using hp
    apply List.mem_flatMap.mpr
    refine ⟨r,hr,List.mem_map.mpr ⟨p,hpr,?_⟩⟩
    rw [ite_eq_right (by simp only [he,hM,hp0,or_self,not_false_eq_true])]

lemma logTotientPrimes_subset_table {n N M m : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0) (_hd : m∣M) :
    logTotientPrimes rows M m ⊆ tableFactors rows := by
  intro p hp
  obtain ⟨q,hq,hp⟩:=List.mem_flatMap.mp hp
  have hq' := primeRecord_support_subset (logDivisorPrimes rows M m) q
    ((Finset.mem_sort (·≤·)).mp hq)
  have hqparent : q∈lookupPrimes rows M := divisorPrimes_subset m _ hq'
  have hqprime := (lookupPrimes_correct h hM hM0).1 q hqparent
  rcases List.mem_append.mp hp with hp|hp
  · have he:=(List.mem_replicate.mp hp).2
    subst p
    exact lookupPrimes_subset_table hM0 hqparent
  · split_ifs at hp with h2
    · simp at hp
    · exact lookupPrimes_subset_table (by have:=hqprime.two_le; omega) hp

/-- A support-covering list gives a known multiple after n repetitions,
because every prime exponent of an n-bit positive integer is at most n. -/
lemma dvd_cover_power {v n : ℕ} (ps : List ℕ) (hv : v≠0) (hb : v≤2^n)
    (hp : ∀ p∈ps,p.Prime) (hcover : ∀ p : ℕ,p.Prime→p∣v→p∈ps) : v∣ps.prod^n := by
  have hprod : ps.prod≠0 := List.prod_ne_zero (by intro h;exact (hp 0 h).ne_zero rfl)
  apply (Nat.factorization_prime_le_iff_dvd hv (pow_ne_zero _ hprod)).mp
  intro p hprime
  by_cases hd : p∣v
  · have hm:=hcover p hprime hd
    have hpd : p∣ps.prod := List.dvd_prod hm
    have hpos : 1≤ps.prod.factorization p := (hprime.factorization_pos_of_dvd hprod hpd)
    have he : v.factorization p≤n := Nat.factorization_le_of_le_pow
      (hb.trans (Nat.pow_le_pow_left hprime.two_le n))
    rw [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
    exact he.trans (by nlinarith)
  · rw [Nat.factorization_eq_zero_of_not_dvd hd]
    exact Nat.zero_le _

/-- A rectangular verified data table is sufficient to recover the same
literal multiplicative order. No unbounded support extraction is required. -/
theorem table_strip_order {n N M m : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hb : m<2^n) (hd : m∣M) (a : (ZMod m)ˣ) :
    stripOrderFactors a (List.flatten (List.replicate n (tableFactors rows)))
      ((tableFactors rows).prod^n)=orderOf a := by
  let : NeZero m := ⟨by omega⟩
  have hc:=logTotientPrimes_correct h hM hM0 (by omega : 0 < m) hd
  have hcover : ∀ p : ℕ,p.Prime→p∣m.totient→p∈tableFactors rows := by
    intro p hp hpd
    have mem : p∈logTotientPrimes rows M m := by
      have hpd' : p∣(logTotientPrimes rows M m).prod := by rwa [hc.2]
      obtain ⟨q,hq,hpq⟩:=(Nat.prime_iff.mp hp).dvd_prod_iff.mp hpd'
      have he:=((hc.1 q hq).eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one
      simpa only [he] using hq
    exact logTotientPrimes_subset_table h hM hM0 hd mem
  have hphi : m.totient∣(tableFactors rows).prod^n := dvd_cover_power _
    (Nat.totient_pos.mpr (by omega : 0 < m)).ne'
    ((Nat.totient_le m).trans hb.le) (tableFactors_prime h) hcover
  have horder : orderOf a∣m.totient := by
    simpa [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] using orderOf_dvd_natCard a
  have hmul := Nat.mul_div_cancel' (horder.trans hphi)
  rw [←hmul]
  apply stripOrderFactors_exact a (orderOf_pos a)
  · intro p hp
    obtain ⟨xs,hxs,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hxs).2
    subst xs
    exact tableFactors_prime h p hp
  · have he : (List.flatten (List.replicate n (tableFactors rows))).prod=
        (tableFactors rows).prod^n := by
      rw [List.prod_flatten,List.map_replicate,List.prod_replicate]
    rw [he]
    exact Nat.div_dvd_of_dvd (horder.trans hphi)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
