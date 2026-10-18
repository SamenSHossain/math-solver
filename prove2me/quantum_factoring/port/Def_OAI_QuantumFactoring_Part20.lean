/-
Exact quantum factoring development (port of OpenAI's formalization), part 20 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: TableOrderCircuit.lean, VerifiedTreeBounds.lean, PrimeComponentCircuit.lean, TablePrimeSupport.lean, CanonicalResidueCircuit.lean, FlatLookupCircuit.lean, VerifiedTableOrder.lean, RetainedTable.lean, RetainedCanonical.lean, RetainedComponentOrder.lean, TableFavorable.lean, RetainedFavorable.lean, ClosedLevelCircuit.lean, ComponentPhiCircuit.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted; compatibility edits for the platform Lean/Mathlib versions: in TableOrderCircuit.lean, `List.prod_le_pow_length` → `List.prod_le_pow_card` (older name).
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part19

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableOrderCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

/-- A zero/unused-row word is replaced by the harmless prime 2. -/
def tableFactor {k n : ℕ} (label p : BooleanNetwork k n) : BooleanNetwork k n :=
  wordMux ((zeroWord label).bor (zeroWord p)) (wordConstant 2) p

lemma tableFactor_value {k n : ℕ} (hn : 2≤n) (label p : BooleanNetwork k n) (x : Basis k) :
    (bitsValue ((tableFactor label p).eval x)).toNat=
      if (bitsValue (label.eval x)).toNat=0 ∨ (bitsValue (p.eval x)).toNat=0 then 2
      else (bitsValue (p.eval x)).toNat := by
  have hb : 2<2^n := lt_of_lt_of_le (by norm_num : 2<2^2) (Nat.pow_le_pow_right (by norm_num) hn)
  have hh : ((zeroWord label).bor (zeroWord p)).eval x 0=true ↔
      (bitsValue (label.eval x)).toNat=0 ∨ (bitsValue (p.eval x)).toNat=0 := by
    rw [eval_bor,Bool.or_eq_true,zeroWord_value,zeroWord_value]
  rw [tableFactor,wordMux_eval]
  by_cases h : ((zeroWord label).bor (zeroWord p)).eval x 0=true
  · rw [ite_eq_left h,ite_eq_left (hh.mp h),wordConstant_eval]
    exact Nat.mod_eq_of_lt hb
  · rw [ite_eq_right h,ite_eq_right (fun h' => h (hh.mpr h'))]

lemma tableFactor_count {k n : ℕ} (label p : BooleanNetwork k n) :
    (tableFactor label p).net.count≤label.net.count+2*p.net.count+220*n+50 := by
  have hl:=zeroWord_count label
  have hp:=zeroWord_count p
  simp only [tableFactor,wordMux_count,count_bor,wordConstant_count]
  omega

def tableNets {k n : ℕ} (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) :
    List (BooleanNetwork k n) := rows.flatMap (fun r=>r.2.map (tableFactor r.1))

def tableValues {k n : ℕ} (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    List (ℕ×List ℕ) := rows.map (fun r=>((bitsValue (r.1.eval x)).toNat,
      r.2.map (fun p=>(bitsValue (p.eval x)).toNat)))

lemma tableNets_values {k n : ℕ} (hn : 2≤n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    (tableNets rows).map (fun p=>(bitsValue (p.eval x)).toNat)=
      PhysicalTree.tableFactors (tableValues rows x) := by
  simp only [tableNets,tableValues,PhysicalTree.tableFactors,List.map_flatMap,List.flatMap_map,
    List.map_map,Function.comp_def,tableFactor_value hn]

lemma tableNets_counts {k n c : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n)))
    (hc : ∀ r∈rows,r.1.net.count≤c ∧ ∀ p∈r.2,p.net.count≤c) :
    ∀ p∈tableNets rows,p.net.count≤3*c+220*n+50 := by
  intro p hp
  obtain ⟨r,hr,hp⟩:=List.mem_flatMap.mp hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  have H:=hc r hr
  have Hq:=H.2 q hq
  exact (tableFactor_count r.1 q).trans (by omega)

/-- Start at the complete product of a known prime list and scan it once.
This is sufficient whenever the group order divides that product. -/
def orderFromList {k w : ℕ} (a m : BooleanNetwork k w) (qs : List (BooleanNetwork k w)) :
    BooleanNetwork k w :=
  (((select id).pair (productNet qs)).comp (stripScan a m qs)).comp (select (Fin.natAdd k))

lemma orderFromList_unit {k w m : ℕ} (hm : 2 ≤ m) (aN mN : BooleanNetwork k w)
    (u : (ZMod m)ˣ) (qs : List (BooleanNetwork k w)) (x : Basis k)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m)
    (hb : (qs.map (fun q=>(bitsValue (q.eval x)).toNat)).prod<2^w) :
    (bitsValue ((orderFromList aN mN qs).eval x)).toNat=
      stripOrderFactors u (qs.map (fun q=>(bitsValue (q.eval x)).toNat))
        ((qs.map (fun q=>(bitsValue (q.eval x)).toNat)).prod) := by
  obtain ⟨z,he,hv⟩:=stripScan_unit hm aN mN u qs x ((productNet qs).eval x) ha hmN
  have hz : Fin.append x z ∘ Fin.natAdd k=z := by funext i;exact Fin.append_right _ _ i
  rw [orderFromList,eval_comp,eval_comp,eval_pair,eval_select]
  change (bitsValue ((select (Fin.natAdd k)).eval ((stripScan aN mN qs).eval
    (Fin.append x ((productNet qs).eval x))))).toNat=_
  rw [he,eval_select,hz,hv,productNet_nat,Nat.mod_eq_of_lt hb]

lemma orderFromList_count {k w c : ℕ} (a m : BooleanNetwork k w)
    (qs : List (BooleanNetwork k w)) (ha : a.net.count≤c) (hm : m.net.count≤c)
    (hq : ∀ q∈qs,q.net.count≤c) :
    (orderFromList a m qs).net.count≤
      qs.length*(c+90*w*w+14*w+6+stripStepBound w c)+w := by
  have hp:=productNet_count qs hq
  have hs:=stripScan_count a m qs ha hm hq
  simp only [orderFromList,count_comp,count_pair,count_select,zero_add,Nat.add_zero]
  nlinarith

/-- A uniform polynomial-width exact product bound. -/
lemma word_list_product_bound {k w n : ℕ} (qs : List (BooleanNetwork k w)) (x : Basis k)
    (h : ∀ q∈qs,(bitsValue (q.eval x)).toNat≤2^n) :
    (qs.map (fun q=>(bitsValue (q.eval x)).toNat)).prod<2^(n*qs.length+1) := by
  have hb:=List.prod_le_pow_card (qs.map (fun q=>(bitsValue (q.eval x)).toNat)) (2^n)
    (by intro p hp;obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp;exact h q hq)
  rw [List.length_map,←pow_mul] at hb
  exact hb.trans_lt (Nat.pow_lt_pow_right (by omega : 1<2) (by omega))

end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/VerifiedTreeBounds.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PhysicalNode
abbrev resultBound (n : ℕ) := n*n+n*n*(498*n+114)
lemma resultField_count (n : ℕ) (i : Fin n) : (resultField n i).net.count≤n := by
  have h:=resizeWord_count (n+1) n
  simpa only [resultField,count_comp,NodeStateCircuit.output,count_select,blockNet,count_vector,
    Nat.zero_add] using h
lemma sortedOutput_count (n : ℕ) : (sortedOutput n).net.count≤resultBound n := by
  have h₁:=tensorNetwork_count_le (resultField n) (resultField_count n)
  have h₂:=SortedWords.sortNet_count n n
  simp only [sortedOutput,count_comp]
  unfold resultBound
  omega
end PhysicalNode
namespace PhysicalTree
lemma nodeResult_count (n : ℕ) : (nodeResult n).net.count≤PhysicalNode.resultBound n := by
  have h:=PhysicalNode.sortedOutput_count n
  simpa only [nodeResult,count_comp,SplitMachine.currentNet,count_select,Nat.zero_add] using h
lemma resultFields_count (n : ℕ) (i : Fin n) : (resultFields n i).net.count≤PhysicalNode.resultBound n := by
  simpa only [resultFields,count_comp,tensorSelect,count_select,Nat.add_zero] using nodeResult_count n
end PhysicalTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)
lemma previousNet_count (t : ℕ) : (M.previousNet t).net.count=0 := by
  simp only [previousNet,count_comp,count_select,Nat.add_zero]
lemma lastNodeNet_count (t : ℕ) : (M.lastNodeNet t).net.count=0 := by
  simp only [lastNodeNet,count_comp,count_select,Nat.add_zero]
lemma rowQuery_count (t : ℕ) : (M.rowQuery t).net.count=M.query.net.count := by
  simp only [rowQuery,count_comp,M.previousNet_count,currentNet,count_select,Nat.zero_add]
lemma rowFields_count (t : ℕ) (i : Fin n) :
    (M.rowFields t i).net.count≤PhysicalNode.resultBound n := by
  simpa only [rowFields,count_comp,M.lastNodeNet_count,Nat.zero_add] using
    PhysicalTree.resultFields_count n i
abbrev rowBound := M.query.net.count+97*n+25+
  factorVerifierBound n (M.query.net.count+PhysicalNode.resultBound n)
lemma rowVerifiedNet_count (t : ℕ) : (M.rowVerifiedNet t).net.count≤M.rowBound := by
  have h₁:=zeroWord_count (M.rowQuery t)
  have h₂:=factorVerifierOn_count (M.rowQuery t) (M.rowFields t)
    (c:=M.query.net.count+PhysicalNode.resultBound n) (by rw [M.rowQuery_count];omega)
    (by intro i;exact (M.rowFields_count t i).trans (Nat.le_add_left _ _))
  rw [M.rowQuery_count] at h₁
  simp only [rowVerifiedNet,count_bor]
  unfold rowBound
  omega
lemma verifiedNet_count (t : ℕ) : (M.verifiedNet t).net.count≤t*(M.rowBound+1)+1 := by
  induction t with
  | zero=>simp only [verifiedNet,count_constant,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ t ih=>
    have h:=M.rowVerifiedNet_count t
    simp only [verifiedNet,count_band,count_comp,M.previousNet_count,Nat.zero_add]
    nlinarith
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PrimeComponentCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

lemma prime_component_gcd {m p n : ℕ} (hm : m≠0) (hp : p.Prime) (hb : m≤2^n) :
    Nat.gcd m (p^n)=p^(m.factorization p) := by
  have he : m.factorization p≤n :=
    Nat.factorization_le_of_le_pow (hb.trans (Nat.pow_le_pow_left hp.two_le n))
  apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left hm) (pow_ne_zero _ hp.ne_zero)
  intro q
  rw [Nat.factorization_gcd hm (pow_ne_zero _ hp.ne_zero),hp.factorization_pow,
    hp.factorization_pow,Finsupp.inf_apply]
  by_cases h : q=p
  · subst q
    simp only [Finsupp.single_eq_same]
    exact min_eq_left he
  · simp only [Finsupp.single_eq_of_ne h,Nat.min_zero]

namespace BitArithmetic
/-- A polynomial-width, polynomial-size component modulus circuit. It uses
p as an input prime, not an oracle or enumeration of prime factors of m. -/
def componentWidth (n : ℕ) : ℕ := n*n+1

def primeComponent {k n : ℕ} (m p : BooleanNetwork k n) : BooleanNetwork k n :=
  let w:=componentWidth n
  let mw:=m.comp (resizeWord n w)
  let pw:=p.comp (resizeWord n w)
  ((mw.pair (productNet (List.replicate n pw))).comp (gcdNet w)).comp (resizeWord w n)

lemma primeComponent_value {k n : ℕ} (m p : BooleanNetwork k n) (x : Basis k)
    (hm : (bitsValue (m.eval x)).toNat≠0) (hp : ((bitsValue (p.eval x)).toNat).Prime) :
    (bitsValue ((primeComponent m p).eval x)).toNat=
      (bitsValue (p.eval x)).toNat^((bitsValue (m.eval x)).toNat.factorization
        (bitsValue (p.eval x)).toNat) := by
  have hn : n≤componentWidth n := by dsimp only [componentWidth];nlinarith
  have hpB : (bitsValue (p.eval x)).toNat^n<2^(componentWidth n) := by
    have h₁ := Nat.pow_le_pow_left (bitsValue (p.eval x)).isLt.le n
    rw [←pow_mul] at h₁
    exact h₁.trans_lt (by rw [componentWidth,pow_succ];have := Nat.two_pow_pos (n*n);omega)
  have hh : (bitsValue ((productNet (List.replicate n
      (p.comp (resizeWord n (componentWidth n))))).eval x)).toNat=(bitsValue (p.eval x)).toNat^n := by
    rw [productNet_nat,List.map_replicate,List.prod_replicate,eval_comp,resizeWord_toNat hn,
      Nat.mod_eq_of_lt hpB]
  rw [primeComponent,eval_comp,resizeWord_value,BitVec.toNat_setWidth,eval_comp,
    eval_pair,gcdNet_value,eval_comp,resizeWord_toNat hn,hh]
  rw [prime_component_gcd hm hp (bitsValue (m.eval x)).isLt.le]
  exact Nat.mod_eq_of_lt ((Nat.le_of_dvd (Nat.pos_of_ne_zero hm)
    (Nat.ordProj_dvd _ _)).trans_lt (bitsValue (m.eval x)).isLt)

def primeComponentBound (n c : ℕ) : ℕ :=
  let w:=componentWidth n
  c+w+(w+n*(c+w+90*w*w+14*w+6))+2*w*(216*w*w+300*w+100)+n

lemma primeComponent_count {k n c : ℕ} (m p : BooleanNetwork k n)
    (hm : m.net.count≤c) (hp : p.net.count≤c) :
    (primeComponent m p).net.count≤primeComponentBound n c := by
  have hr:=resizeWord_count n (componentWidth n)
  have hr':=resizeWord_count (componentWidth n) n
  have hprod:=productNet_count (List.replicate n (p.comp (resizeWord n (componentWidth n))))
    (c:=c+componentWidth n) (by
      intro q hq
      have he:=(List.mem_replicate.mp hq).2
      subst q
      rw [count_comp]
      omega)
  have hg:=gcdNet_count (componentWidth n)
  simp only [List.length_replicate] at hprod
  simp only [primeComponent,count_comp,count_pair]
  dsimp only [primeComponentBound]
  omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TablePrimeSupport.lean =====
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

lemma tableFactors_cover {n N M m : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0)
    (_hm : m≠0) (hd : m∣M) : ∀ p : ℕ,p.Prime→p∣m→p∈tableFactors rows := by
  intro p hp hpm
  have hh:=lookupPrimes_correct h hM hM0
  have hpM : p∣(lookupPrimes rows M).prod := by rw [hh.2];exact hpm.trans hd
  obtain ⟨q,hq,hpq⟩:=(Nat.prime_iff.mp hp).dvd_prod_iff.mp hpM
  have he:=((hh.1 q hq).eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one
  have hpq' : p∈lookupPrimes rows M := by simpa only [he] using hq
  exact lookupPrimes_subset_table hM0 hpq'

end PhysicalTree

/-- A distinguished component can be tested by polynomially many pairwise
comparisons, without constructing the least prime factor of an unknown N. -/
def leastDivisorIn (ps : List ℕ) (m p : ℕ) : Prop := ∀ q∈ps,q∣m→p≤q

lemma leastDivisorIn_iff {ps : List ℕ} {m p : ℕ} (hm : 2 ≤ m)
    (hps : ∀ q∈ps,q.Prime) (hcover : ∀ q : ℕ,q.Prime→q∣m→q∈ps)
    (hp : p∈ps) (hpd : p∣m) : leastDivisorIn ps m p ↔ p=m.minFac := by
  have hmin : m.minFac∈ps := hcover _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd m)
  constructor
  · intro h
    exact le_antisymm (h _ hmin (Nat.minFac_dvd m)) (Nat.minFac_le_of_dvd (hps p hp).two_le hpd)
  · rintro rfl q hq hqd
    exact Nat.minFac_le_of_dvd (hps q hq).two_le hqd

/-- Redundant rectangular-table entries and harmless dummy primes are ignored
unless they divide m; duplicates impose exactly the same congruence. -/
noncomputable def tableCanonical (ps : List ℕ) (a m n : ℕ) : Prop := by
  classical
  exact a < m ∧ ∀ p∈ps,p∣m→a%(Nat.gcd m (p^n))=
    if leastDivisorIn ps m p then 1 else Nat.gcd m (p^n)-1

lemma tableCanonical_correct {ps : List ℕ} {M m n : ℕ} (hM : 0 < M) (hm : 2 ≤ m)
    (hb : m ≤ 2^n) (hd : m∣M) (hps : ∀ q∈ps,q.Prime)
    (hcover : ∀ q : ℕ,q.Prime→q∣m→q∈ps) (a : ℕ) :
    tableCanonical ps a m n ↔ dataCanonicalResidue (trueData M) a m := by
  rw [tableCanonical,dataCanonicalResidue,dataRecord_correct hM hd,recordFirst_factorization hm]
  apply and_congr_right
  intro _
  constructor
  · intro h p hp
    obtain ⟨hprime,hpd,_⟩:=Nat.mem_primeFactors.mp hp
    have hmem:=hcover p hprime hpd
    have hh:=h p hmem hpd
    simpa only [prime_component_gcd (by omega) hprime hb,
      leastDivisorIn_iff hm hps hcover hmem hpd] using hh
  · intro h p hp hpd
    have hh:=h p (Nat.mem_primeFactors.mpr ⟨hps p hp,hpd,by omega⟩)
    simpa only [prime_component_gcd (by omega) (hps p hp) hb,
      leastDivisorIn_iff hm hps hcover hp hpd] using hh
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CanonicalResidueCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic
attribute [local instance] Classical.propDecidable

def dividesOn {k n : ℕ} (p m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  zeroWord ((m.pair p).comp (mod n))
lemma dividesOn_value {k n : ℕ} (p m : BooleanNetwork k n) (x : Basis k) :
    (dividesOn p m).eval x 0=true ↔ (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat := by
  rw [dividesOn,zeroWord_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,Nat.dvd_iff_mod_eq_zero]
lemma dividesOn_count {k n : ℕ} (p m : BooleanNetwork k n) :
    (dividesOn p m).net.count ≤ p.net.count+m.net.count+216*n*n+154*n+27 := by
  have hh:=zeroWord_count ((m.pair p).comp (mod n))
  have hd:=mod_count n
  simp only [count_comp,count_pair] at hh
  exact hh.trans (by omega)

def leastDivisorTest {k n : ℕ} (ps : List (BooleanNetwork k n)) (m p : BooleanNetwork k n) :
    BooleanNetwork k 1 := all (ps.map (fun q=>(dividesOn q m).bnot.bor (wordLe p q)))

lemma leastDivisorTest_value {k n : ℕ} (ps : List (BooleanNetwork k n))
    (m p : BooleanNetwork k n) (x : Basis k) :
    (leastDivisorTest ps m p).eval x 0=true ↔
      leastDivisorIn (ps.map (fun q=>(bitsValue (q.eval x)).toNat))
        (bitsValue (m.eval x)).toNat (bitsValue (p.eval x)).toNat := by
  simp only [leastDivisorTest,all_eval,List.forall_mem_map,eval_bor,Bool.or_eq_true,
    bnot_value,dividesOn_value,wordLe_eval,decide_eq_true_eq,leastDivisorIn,
    List.forall_mem_map,or_iff_not_imp_left,not_not]

lemma leastDivisorTest_count {k n c : ℕ} (ps : List (BooleanNetwork k n))
    (m p : BooleanNetwork k n) (hps : ∀ q∈ps,q.net.count≤c)
    (hm : m.net.count≤c) (hp : p.net.count≤c) :
    (leastDivisorTest ps m p).net.count≤ps.length*(4*c+216*n*n+202*n+42)+1 := by
  have hh:=all_count (ps.map (fun q=>(dividesOn q m).bnot.bor (wordLe p q)))
    (c:=4*c+216*n*n+202*n+41) (by
      intro b hb
      obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hb
      have hd:=dividesOn_count q m
      have hl:=wordLe_count p q
      have hqc:=hps q hq
      simp only [count_bor,count_bnot]
      omega)
  change (all (ps.map (fun q=>(dividesOn q m).bnot.bor (wordLe p q)))).net.count ≤ _
  simp only [List.length_map] at hh
  omega

def componentCongruence {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m p : BooleanNetwork k n) : BooleanNetwork k 1 :=
  let q:=primeComponent m p
  equalOn ((a.pair q).comp (mod n)) (wordMux (leastDivisorTest ps m p)
    (wordConstant (BitVec.ofNat n 1)) (natSubOn q (wordConstant (BitVec.ofNat n 1))))

lemma componentCongruence_value {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m p : BooleanNetwork k n) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hp : ((bitsValue (p.eval x)).toNat).Prime) :
    (componentCongruence ps a m p).eval x 0=true ↔
      (bitsValue (a.eval x)).toNat % Nat.gcd (bitsValue (m.eval x)).toNat
        ((bitsValue (p.eval x)).toNat^n)=
      if leastDivisorIn (ps.map (fun q=>(bitsValue (q.eval x)).toNat))
        (bitsValue (m.eval x)).toNat (bitsValue (p.eval x)).toNat
      then 1 else Nat.gcd (bitsValue (m.eval x)).toNat ((bitsValue (p.eval x)).toNat^n)-1 := by
  have h1 : 1<2^n := by have hh:=(bitsValue (m.eval x)).isLt;omega
  have hq : (bitsValue ((primeComponent m p).eval x)).toNat=
      Nat.gcd (bitsValue (m.eval x)).toNat ((bitsValue (p.eval x)).toNat^n) := by
    rw [primeComponent_value m p x (by omega) hp,
      prime_component_gcd (by omega) hp (bitsValue (m.eval x)).isLt.le]
  rw [componentCongruence,equalOn_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,hq,wordMux_eval]
  by_cases ht : (leastDivisorTest ps m p).eval x 0=true
  · rw [ite_eq_left ht,ite_eq_left ((leastDivisorTest_value ps m p x).mp ht),wordConstant_eval,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  · rw [ite_eq_right ht,ite_eq_right (fun h=>ht ((leastDivisorTest_value ps m p x).mpr h)),natSubOn_value,
      hq,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]

def tableCanonicalNet {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (wordLt a m).band (all (ps.map (fun p=>(dividesOn p m).bnot.bor (componentCongruence ps a m p))))

lemma tableCanonicalNet_value {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m : BooleanNetwork k n) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat)
    (hps : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime) :
    (tableCanonicalNet ps a m).eval x 0=true ↔
      tableCanonical (ps.map (fun p=>(bitsValue (p.eval x)).toNat))
        (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat n := by
  rw [tableCanonicalNet,eval_band,Bool.and_eq_true,wordLt_eval,decide_eq_true_eq,tableCanonical]
  apply and_congr_right
  intro _
  simp only [all_eval,List.forall_mem_map,eval_bor,Bool.or_eq_true,bnot_value,dividesOn_value]
  constructor
  · intro h p hp hpd
    exact (componentCongruence_value ps a m p x hm (hps p hp)).mp ((h p hp).resolve_left (not_not.mpr hpd))
  · intro h p hp
    by_cases hpd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat
    · exact Or.inr ((componentCongruence_value ps a m p x hm (hps p hp)).mpr
        (h p hp hpd))
    · exact Or.inl hpd
def componentCongruenceBound (n l c : ℕ) : ℕ :=
  c+3*primeComponentBound n c+216*n*n+500*n+100+
    l*(4*c+216*n*n+202*n+42)

lemma componentCongruence_count {k n c : ℕ} (ps : List (BooleanNetwork k n))
    (a m p : BooleanNetwork k n) (hps : ∀ q∈ps,q.net.count≤c)
    (ha : a.net.count≤c) (hm : m.net.count≤c) (hp : p.net.count≤c) :
    (componentCongruence ps a m p).net.count≤componentCongruenceBound n ps.length c := by
  have hq:=primeComponent_count m p hm hp
  have hl:=leastDivisorTest_count ps m p hps hm hp
  have he:=equalOn_count ((a.pair (primeComponent m p)).comp (mod n))
    (wordMux (leastDivisorTest ps m p) (wordConstant (BitVec.ofNat n 1))
      (natSubOn (primeComponent m p) (wordConstant (BitVec.ofNat n 1))))
  have hs:=natSubOn_count (primeComponent m p) (wordConstant (BitVec.ofNat n 1))
  have hd:=mod_count n
  simp only [count_comp,count_pair,wordMux_count,wordConstant_count] at he hs
  change (equalOn _ _).net.count≤_
  dsimp only [componentCongruenceBound]
  omega

def tableCanonicalBound (n l c : ℕ) : ℕ :=
  2*c+48*n+10+l*(2*c+216*n*n+154*n+33+componentCongruenceBound n l c)+2

lemma tableCanonicalNet_count {k n c : ℕ} (ps : List (BooleanNetwork k n))
    (a m : BooleanNetwork k n) (hps : ∀ q∈ps,q.net.count≤c)
    (ha : a.net.count≤c) (hm : m.net.count≤c) :
    (tableCanonicalNet ps a m).net.count≤tableCanonicalBound n ps.length c := by
  have hl:=wordLt_count a m
  have hall:=all_count (ps.map (fun p=>(dividesOn p m).bnot.bor (componentCongruence ps a m p)))
    (c:=2*c+216*n*n+154*n+32+componentCongruenceBound n ps.length c) (by
      intro b hb
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hb
      have hc:=componentCongruence_count ps a m p hps ha hm (hps p hp)
      have hd:=dividesOn_count p m
      have hp':=hps p hp
      simp only [count_bor,count_bnot]
      omega)
  simp only [List.length_map] at hall
  have hr : 2*c+216*n*n+154*n+32+componentCongruenceBound n ps.length c+1 =
      2*c+216*n*n+154*n+33+componentCongruenceBound n ps.length c := by omega
  rw [hr] at hall
  simp only [tableCanonicalNet,count_band,tableCanonicalBound]
  omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FlatLookupCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

/-- Fixed-capacity, first-match read-only lookup. Every iteration is an explicit
Boolean network; malformed/missing labels use the zero word. -/
def lookupWordNet {k q w : ℕ} (query : BooleanNetwork k q) :
    List (BooleanNetwork k q × BooleanNetwork k w)→BooleanNetwork k w
  | []=>wordConstant 0
  | a::as=>wordMux (equalOn query a.1) a.2 (lookupWordNet query as)

def lookupWord {q w : ℕ} (query : Basis q) : List (Basis q × Basis w)→Basis w
  | []=>fun _=>false
  | a::as=>if query=a.1 then a.2 else lookupWord query as

lemma lookupWordNet_value {k q w : ℕ} (query : BooleanNetwork k q)
    (rows : List (BooleanNetwork k q × BooleanNetwork k w)) (x : Basis k) :
    (lookupWordNet query rows).eval x=lookupWord (query.eval x)
      (rows.map (fun a=>(a.1.eval x,a.2.eval x))) := by
  induction rows with
  | nil=>
    funext i
    simp [lookupWordNet,lookupWord,wordConstant]
  | cons a as ih=>
    have he : (bitsValue (query.eval x)).toNat=(bitsValue (a.1.eval x)).toNat ↔
        query.eval x=a.1.eval x := by
      exact ⟨fun h=>(bitsEquiv q).injective (BitVec.eq_of_toNat_eq h),fun h=>by rw [h]⟩
    rw [lookupWordNet,wordMux_eval,ih]
    simp only [List.map_cons,lookupWord,equalOn_value,he]

lemma lookupWordNet_count {k q w a b : ℕ} (query : BooleanNetwork k q)
    (rows : List (BooleanNetwork k q × BooleanNetwork k w))
    (hr : ∀ r∈rows,r.1.net.count≤a ∧ r.2.net.count≤b) :
    (lookupWordNet query rows).net.count≤
      w+rows.length*(query.net.count+a+b+96*q+21+7*w) := by
  induction rows with
  | nil=>simp only [lookupWordNet,wordConstant_count,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons r rs ih=>
    have h:=hr r (by simp)
    have ht:=ih (fun r hh=>hr r (List.mem_cons_of_mem _ hh))
    have he:=equalOn_count query r.1
    have hc:=wordMux_count (equalOn query r.1) r.2 (lookupWordNet query rs)
    simp only [lookupWordNet,List.length_cons]
    nlinarith

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- The rows are at their true retained locations. This construction has no
quantum conditioning and does not evaluate a factorization operation. -/
def logNets : (t : ℕ)→List (BooleanNetwork (M.width t) n ×
    BooleanNetwork (M.width t) (tensorWidth n n))
  | 0=>[]
  | t+1=>(M.rowQuery t,(M.lastNodeNet t).comp (PhysicalTree.nodeResult n))::
      ((logNets t).map (fun r=>((M.previousNet t).comp r.1,(M.previousNet t).comp r.2)))

lemma logNets_length (t : ℕ) : (M.logNets t).length=t := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [logNets,List.length_cons,List.length_map,ih]

lemma logNets_counts (t : ℕ) : ∀ r∈M.logNets t,
    r.1.net.count≤M.query.net.count ∧ r.2.net.count≤PhysicalNode.resultBound n := by
  induction t with
  | zero=>simp only [logNets,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ t ih=>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨(M.rowQuery_count t).le,?_⟩
      simpa only [count_comp,M.lastNodeNet_count,Nat.zero_add] using PhysicalTree.nodeResult_count n
    · change r ∈ (M.logNets t).map (fun a=>((M.previousNet t).comp a.1,
        (M.previousNet t).comp a.2)) at hr
      obtain ⟨a,ha,he⟩:=List.mem_map.mp hr
      subst r
      simpa only [count_comp,M.previousNet_count,Nat.zero_add] using ih a ha

lemma logNets_values (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.logNets t).map (fun r=>((bitsValue (r.1.eval (M.encoded x t h))).toNat,
      SortedWords.numbers (List.ofFn (fun i=>(tensorLayout n n).symm
        (r.2.eval (M.encoded x t h)) i))))=M.dataLog x t h := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    change (_::List.map _ (List.map _ (M.logNets t)))=_
    simp only [List.map_map,Function.comp_def,eval_comp,M.previousNet_encoded,
      M.lastNodeNet_encoded,M.rowQuery_encoded]
    rw [ih]
    simp only [dataLog,PhysicalTree.nodeWords,PhysicalTree.resultFields,eval_comp,
      tensorSelect_inverse]
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/VerifiedTableOrder.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

/-- The extra n bits make zero-extension unconditional, including empty
malformed tables. On verified input this holds the entire repeated product. -/
def tableOrderWidth (n f : ℕ) : ℕ := n*(n*f)+n+1

def tableOrderPrimes {k n : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) :
    List (BooleanNetwork k (tableOrderWidth n (tableNets rows).length)) :=
  List.flatten (List.replicate n ((tableNets rows).map (fun p=>
    p.comp (resizeWord n (tableOrderWidth n (tableNets rows).length)))))

lemma tableOrderPrimes_values {k n : ℕ} (hn : 2 ≤ n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    (tableOrderPrimes rows).map (fun p=>(bitsValue (p.eval x)).toNat)=
      List.flatten (List.replicate n (PhysicalTree.tableFactors (tableValues rows x))) := by
  have hw : n ≤ tableOrderWidth n (tableNets rows).length := by
    dsimp only [tableOrderWidth]
    omega
  simp only [tableOrderPrimes,List.map_flatten,List.map_replicate,List.map_map,
    Function.comp_def,eval_comp,resizeWord_toNat hw]
  rw [tableNets_values hn]

lemma tableOrderPrimes_length {k n : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) :
    (tableOrderPrimes rows).length=n*(tableNets rows).length := by
  simp only [tableOrderPrimes,List.length_flatten,List.map_replicate,List.length_map,
    List.sum_replicate,smul_eq_mul]

lemma tableOrderPrimes_product_bound {k n : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    ((tableOrderPrimes rows).map (fun p=>(bitsValue (p.eval x)).toNat)).prod < 2^(tableOrderWidth n (tableNets rows).length) := by
  have h : ∀ p∈tableOrderPrimes rows,(bitsValue (p.eval x)).toNat ≤ 2^n := by
    intro p hp
    obtain ⟨ps,hps,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hps).2
    subst ps
    obtain ⟨r,_hr,rfl⟩:=List.mem_map.mp hp
    rw [eval_comp,resizeWord_toNat (by dsimp [tableOrderWidth];omega)]
    exact (bitsValue (r.eval x)).isLt.le
  have hb:=word_list_product_bound (tableOrderPrimes rows) x h
  rw [tableOrderPrimes_length] at hb
  exact hb.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by dsimp [tableOrderWidth];omega))

/-- A literal order circuit using only retained verified table entries and
modular powering. No mathematical factorization/support enumeration appears in
its definition, even on malformed inputs. -/
def tableOrder {k n : ℕ} (a m : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) : BooleanNetwork k n :=
  let w:=tableOrderWidth n (tableNets rows).length
  (orderFromList (a.comp (resizeWord n w)) (m.comp (resizeWord n w))
    (tableOrderPrimes rows)).comp (resizeWord w n)

theorem tableOrder_exact {k n N M m : ℕ} (hn : 2 ≤ n)
    (aN mN : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k)
    (h : PhysicalTree.CompleteLog n N (tableValues rows x))
    (hM : M∈(tableValues rows x).map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hd : m∣M) (u : (ZMod m)ˣ)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m) :
    (bitsValue ((tableOrder aN mN rows).eval x)).toNat=orderOf u := by
  let w:=tableOrderWidth n (tableNets rows).length
  have hwide : n ≤ w := by dsimp [w,tableOrderWidth];omega
  have hv:=orderFromList_unit hm (aN.comp (resizeWord n w)) (mN.comp (resizeWord n w))
    u (tableOrderPrimes rows) x
    (by simpa only [eval_comp,resizeWord_toNat hwide] using ha)
    (by simpa only [eval_comp,resizeWord_toNat hwide] using hmN)
    (tableOrderPrimes_product_bound rows x)
  rw [tableOrderPrimes_values hn] at hv
  have hb : m < 2^n := by rw [←hmN];exact (bitsValue (mN.eval x)).isLt
  have hs:=PhysicalTree.table_strip_order h hM hM0 hm hb hd u
  rw [List.prod_flatten,List.map_replicate,List.prod_replicate,hs] at hv
  have hord : orderOf u < 2^n := by
    let : NeZero m:=⟨by omega⟩
    have hh : orderOf u ≤ m.totient := by
      simpa only [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] using (orderOf_le_card (x := u))
    exact (hh.trans (Nat.totient_le m)).trans_lt hb
  rw [tableOrder,eval_comp,resizeWord_value,BitVec.toNat_setWidth,hv,Nat.mod_eq_of_lt hord]

/-- This bound is polynomial in n, table length and the individual stored-word
circuit cost. Resizing is itself a bounded circuit, not a word-RAM primitive. -/
def tableOrderBound (n f c : ℕ) : ℕ :=
  let w:=tableOrderWidth n f
  let C:=3*c+220*n+50+w
  (n*f)*(C+90*w*w+14*w+6+stripStepBound w C)+w+n

lemma tableOrder_count {k n c : ℕ} (a m : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n)))
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c)
    (hr : ∀ r∈rows,r.1.net.count ≤ c ∧ ∀ p∈r.2,p.net.count ≤ c) :
    (tableOrder a m rows).net.count ≤ tableOrderBound n (tableNets rows).length c := by
  let w:=tableOrderWidth n (tableNets rows).length
  let C:=3*c+220*n+50+w
  have hres:=resizeWord_count n w
  have hp : ∀ p∈tableOrderPrimes rows,p.net.count ≤ C := by
    intro p hp
    obtain ⟨ps,hps,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hps).2
    subst ps
    obtain ⟨r,hr',rfl⟩:=List.mem_map.mp hp
    have H:=tableNets_counts rows hr r hr'
    rw [count_comp]
    exact Nat.add_le_add H hres
  have hs:=orderFromList_count (a.comp (resizeWord n w)) (m.comp (resizeWord n w))
    (tableOrderPrimes rows) (c:=C)
    (by rw [count_comp];dsimp [C];omega)
    (by rw [count_comp];dsimp [C];omega) hp
  rw [tableOrderPrimes_length] at hs
  have hsmall:=resizeWord_count w n
  change _ ≤ _+n
  simp only [tableOrder,count_comp]
  exact Nat.add_le_add hs hsmall

end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedTable.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Every field is selected from its actual retained location. Dummy rows
are kept: the rectangular shape is a compile-time function only of n and t. -/
def fieldRows (t : ℕ) : List (BooleanNetwork (M.width t) n ×
    List (BooleanNetwork (M.width t) n)) :=
  (M.logNets t).map (fun r=>(r.1,List.ofFn (fun i : Fin n=>r.2.comp (tensorSelect n n i))))

lemma fieldRows_length (t : ℕ) : (M.fieldRows t).length=t := by
  simp only [fieldRows,List.length_map,M.logNets_length]

lemma fieldRows_values (x : Basis c) (t : ℕ) (h : Trace n t) :
    tableValues (M.fieldRows t) (M.encoded x t h)=M.dataLog x t h := by
  rw [←M.logNets_values x t h]
  simp only [fieldRows,tableValues,List.map_map,Function.comp_def,List.map_ofFn,
    eval_comp,tensorSelect_inverse,SortedWords.numbers,List.map_ofFn]

lemma fieldRows_counts (t : ℕ) : ∀ r∈M.fieldRows t,
    r.1.net.count ≤ M.query.net.count ∧ ∀ p∈r.2,p.net.count ≤ PhysicalNode.resultBound n := by
  intro r hr
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr
  have hh:=M.logNets_counts t a ha
  refine ⟨hh.1,?_⟩
  intro p hp
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp
  simpa only [count_comp,tensorSelect,count_select,Nat.add_zero] using hh.2

lemma fieldRows_table_length (t : ℕ) : (tableNets (M.fieldRows t)).length=t*n := by
  have h : ∀ a : BooleanNetwork (M.width t) n×BooleanNetwork (M.width t) (tensorWidth n n),
      (List.ofFn (fun i : Fin n => tableFactor a.1 (a.2.comp (tensorSelect n n i)))).length=n :=
    fun _=>List.length_ofFn
  simp only [tableNets,fieldRows,List.flatMap_map,Function.comp_def,List.map_ofFn,
    List.length_flatMap]
  simp only [h,List.map_const',List.sum_replicate,smul_eq_mul,M.logNets_length]

/-- The literal order network already available at any retained stage, before
adding its reversible phase-flag wrapper. -/
def retainedOrder (t : ℕ) (a m : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) n :=
  tableOrder a m (M.fieldRows t)

lemma retainedOrder_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedOrder t a m).eval (M.encoded x t r))).toNat=orderOf u := by
  apply tableOrder_exact hn a m (M.fieldRows t) (M.encoded x t r)
  · rwa [M.fieldRows_values]
  · rwa [M.fieldRows_values]
  · exact hP0
  · exact hd
  · exact hdiv
  · exact ha
  · exact hm

lemma retainedOrder_count {b : ℕ} (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (ha : a.net.count ≤ b) (hm : m.net.count ≤ b)
    (hq : M.query.net.count ≤ b) (hr : PhysicalNode.resultBound n ≤ b) :
    (M.retainedOrder t a m).net.count ≤ tableOrderBound n (t*n) b := by
  have hh:=tableOrder_count a m (M.fieldRows t) ha hm (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  rwa [M.fieldRows_table_length] at hh

end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedCanonical.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def retainedCanonical (t : ℕ) (a m : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) 1 :=
  tableCanonicalNet (tableNets (M.fieldRows t)) a m

lemma retainedCanonical_exact {N P d : ℕ} (hn : 2≤n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedCanonical t a m).eval (M.encoded x t r) 0=true ↔
      dataCanonicalResidue (trueData P)
        (bitsValue (a.eval (M.encoded x t r))).toNat d := by
  have he:=tableNets_values hn (M.fieldRows t) (M.encoded x t r)
  rw [M.fieldRows_values] at he
  have hp : ∀ p∈tableNets (M.fieldRows t),
      ((bitsValue (p.eval (M.encoded x t r))).toNat).Prime := by
    intro p hp
    apply PhysicalTree.tableFactors_prime hc
    rw [←he]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  rw [retainedCanonical,tableCanonicalNet_value _ a m _ (by omega) hp,he,hm]
  exact tableCanonical_correct (by omega) hd (hm ▸ (bitsValue (m.eval (M.encoded x t r))).isLt.le)
    hdiv (PhysicalTree.tableFactors_prime hc)
    (PhysicalTree.tableFactors_cover hc hP hP0 (by omega) hdiv) _

lemma retainedCanonical_count {b : ℕ} (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (ha : a.net.count≤b) (hm : m.net.count≤b)
    (hq : M.query.net.count≤b) (hr : PhysicalNode.resultBound n≤b) :
    (M.retainedCanonical t a m).net.count≤tableCanonicalBound n (t*n) (3*b+220*n+50) := by
  have hf:=tableNets_counts (M.fieldRows t) (c:=b) (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  have h:=tableCanonicalNet_count (tableNets (M.fieldRows t)) a m hf
    (ha.trans (by omega)) (hm.trans (by omega))
  rwa [M.fieldRows_table_length] at h
end NodeMachine

namespace TransitionWords

def readNet {k n K : ℕ} (y : BooleanNetwork k (n*(K+1))) (i : Fin K) : BooleanNetwork k n :=
  y.rewire (fun j=>Fin.cast (Nat.mul_comm _ _) (finProdFinEquiv (i.castSucc,j)))
lemma readNet_eval {k n K : ℕ} (y : BooleanNetwork k (n*(K+1))) (i : Fin K) (x : Basis k) :
    (readNet y i).eval x=read (y.eval x) i := rfl

/-- A polynomial-size literal shape check, including the otherwise-unused last
word. It does not construct the unknown canonical CRT residue. -/
def firstOnly {k n K : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k (n*(K+1)) :=
  encodeNet (fun i : Fin K=>if i.val=0 then a else wordConstant (BitVec.ofNat n 0))
lemma firstOnly_eval {k n K : ℕ} (a : BooleanNetwork k n) (x : Basis k) :
    (firstOnly (K:=K) a).eval x=encode (fun i : Fin K=>if i.val=0 then a.eval x else OrderTrial.natBasis n 0) := by
  rw [firstOnly,encodeNet_eval]
  congr 1
  funext i
  split_ifs
  · rfl
  · funext j
    simp only [wordConstant,eval_vector,eval_constant,OrderTrial.natBasis]
end TransitionWords

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def retainedCanonicalList (hn : 0<n) (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (y : BooleanNetwork (M.width t) (n*(n^5+1))) : BooleanNetwork (M.width t) 1 :=
  let a:=TransitionWords.readNet y ⟨0,pow_pos hn 5⟩
  (M.retainedCanonical t a m).band (equalOn y (TransitionWords.firstOnly a))

lemma retainedCanonicalList_exact {N P d : ℕ} (hn : 2≤n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (y : BooleanNetwork (M.width t) (n*(n^5+1)))
    (x : Basis c) (r : Trace n t) (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedCanonicalList (by omega) t m y).eval (M.encoded x t r) 0=true ↔
      dataCanonicalList (trueData P) d n (by omega) (y.eval (M.encoded x t r)) := by
  change (M.retainedCanonicalList _ t m y).eval (M.encoded x t r) 0=true ↔
    dataCanonicalResidue (trueData P) (bitsValue (TransitionWords.read (y.eval (M.encoded x t r))
      ⟨0,pow_pos (by omega : 0<n) 5⟩)).toNat d ∧
    y.eval (M.encoded x t r)=TransitionWords.encode (fun i : Fin (n^5)=>if i.val=0 then
      TransitionWords.read (y.eval (M.encoded x t r)) ⟨0,pow_pos (by omega : 0<n) 5⟩ else OrderTrial.natBasis n 0)
  let aa : BooleanNetwork (M.width t) n := TransitionWords.readNet y ⟨0,pow_pos (by omega : 0<n) 5⟩
  have hcan := M.retainedCanonical_exact hn t aa m x r hc hP hP0 hd hdiv hm
  have hshape : (equalOn y (TransitionWords.firstOnly (K:=n^5) aa)).eval (M.encoded x t r) 0=true ↔
      y.eval (M.encoded x t r)=TransitionWords.encode (fun i : Fin (n^5)=>
        if i.val=0 then aa.eval (M.encoded x t r) else OrderTrial.natBasis n 0) := by
    rw [equalOn_value y (TransitionWords.firstOnly (K:=n^5) aa),TransitionWords.firstOnly_eval]
    exact ⟨fun h=>(bitsEquiv _).injective (BitVec.eq_of_toNat_eq h),congrArg (fun z=>(bitsValue z).toNat)⟩
  simpa only [retainedCanonicalList,eval_band,Bool.and_eq_true,aa,
    TransitionWords.readNet_eval] using and_congr hcan hshape
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedComponentOrder.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def retainedComponentOrder (t : ℕ) (a m p : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) n :=
  M.retainedOrder t a (primeComponent m p)

lemma retainedComponentOrder_exact {N P d : ℕ} (hn : 2≤n) (t : ℕ)
    (a m p : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d)
    (hp : ((bitsValue (p.eval (M.encoded x t r))).toNat).Prime)
    (hpd : (bitsValue (p.eval (M.encoded x t r))).toNat∣d)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat).Coprime d) :
    (bitsValue ((M.retainedComponentOrder t a m p).eval (M.encoded x t r))).toNat=
      dataOrder (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat
        (Nat.gcd d ((bitsValue (p.eval (M.encoded x t r))).toNat^n)) := by
  let z:=M.encoded x t r
  let pN:=(bitsValue (p.eval z)).toNat
  let q:=pN^(d.factorization pN)
  have hq : 2≤q := hp.two_le.trans (Nat.le_pow (hp.factorization_pos_of_dvd (by omega) hpd))
  have hqd : q∣d := Nat.ordProj_dvd d pN
  have hqa : ((bitsValue (a.eval z)).toNat).Coprime q := ha.of_dvd_right hqd
  have hu : IsUnit ((bitsValue (a.eval z)).toNat : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hqa
  have he : (bitsValue ((primeComponent m p).eval z)).toNat=q := by
    rw [primeComponent_value m p z (by change (bitsValue (m.eval (M.encoded x t r))).toNat≠0;omega) hp,hm]
  have ho:=M.retainedOrder_exact hn t a (primeComponent m p) x r hc hP hP0 hq
    (hqd.trans hdiv) hu.unit hu.unit_spec.symm he
  have ht:=dataOrder_correct (by omega : 0<P) hq (hqd.trans hdiv) hu.unit hu.unit_spec.symm
  dsimp only [retainedComponentOrder]
  rw [ho,prime_component_gcd (by omega) hp (hm ▸ (bitsValue (m.eval z)).isLt.le)]
  exact ht.symm

lemma data_component_order_ne_zero {P d a p n : ℕ} (hP : 0<P) (hd : 2≤d)
    (hdiv : d∣P) (hb : d≤2^n) (hp : p.Prime) (hpd : p∣d) (ha : a.Coprime d) :
    dataOrder (trueData P) a (Nat.gcd d (p^n))≠0 := by
  rw [prime_component_gcd (by omega) hp hb]
  let q:=p^(d.factorization p)
  have hq : 2≤q:=hp.two_le.trans (Nat.le_pow (hp.factorization_pos_of_dvd (by omega) hpd))
  have hqd : q∣d:=Nat.ordProj_dvd d p
  have hqa : a.Coprime q:=ha.of_dvd_right hqd
  let : NeZero q:=⟨by omega⟩
  have hu : IsUnit (a : ZMod q):=(ZMod.isUnit_iff_coprime _ _).mpr hqa
  rw [dataOrder_correct hP hq (hqd.trans hdiv) hu.unit hu.unit_spec.symm]
  exact Nat.ne_of_gt (orderOf_pos _)
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableFavorable.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma table_pairwise_iff {ps : List ℕ} {m : ℕ} (hm : 2 ≤ m)
    (hps : ∀ p∈ps,p.Prime) (hcover : ∀ p : ℕ,p.Prime→p ∣ m→p∈ps) (v : ℕ→ℕ) :
    (∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→v p=v q) ↔
      ∀ p∈m.primeFactors,v p=v m.minFac := by
  have hmin:=hcover m.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd m)
  constructor
  · intro h p hp
    have H:=Nat.mem_primeFactors.mp hp
    exact h p (hcover p H.1 H.2.1) H.2.1 _ hmin (Nat.minFac_dvd m)
  · intro h p hp hpd q hq hqd
    have hp':=Nat.mem_primeFactors.mpr ⟨hps p hp,hpd,by omega⟩
    have hq':=Nat.mem_primeFactors.mpr ⟨hps q hq,hqd,by omega⟩
    exact (h p hp').trans (h q hq').symm

/-- Pairwise comparison avoids searching for a least component. The supplied
rectangular table may contain duplicates and harmless primes not dividing m. -/
noncomputable def tableFavorable (ps : List ℕ) (data : FactorData) (a m n : ℕ) : Prop :=
  a < m  ∧  a.Coprime m  ∧   ¬ ∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→
    padicValNat 2 (dataOrder data a (Nat.gcd m (p^n)))=
      padicValNat 2 (dataOrder data a (Nat.gcd m (q^n)))

lemma tableFavorable_correct {ps : List ℕ} {P m n : ℕ} (hP : 0 < P) (hm : 2 ≤ m)
    (hb : m ≤ 2^n) (hd : m ∣ P) (hps : ∀ p∈ps,p.Prime)
    (hcover : ∀ p : ℕ,p.Prime→p ∣ m→p∈ps) (a : ℕ) :
    tableFavorable ps (trueData P) a m n ↔ dataResidueGood (trueData P) a m := by
  rw [tableFavorable,dataResidueGood,dataRecord_correct hP hd,recordFirst_factorization hm]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply not_congr
  have he : (∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→
      padicValNat 2 (dataOrder (trueData P) a (Nat.gcd m (p^n)))=
        padicValNat 2 (dataOrder (trueData P) a (Nat.gcd m (q^n)))) ↔
      ∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→
        padicValNat 2 (dataOrder (trueData P) a (p^m.factorization p))=
          padicValNat 2 (dataOrder (trueData P) a (q^m.factorization q)) := by
    apply forall_congr';intro p
    apply forall_congr';intro hp
    apply forall_congr';intro _
    apply forall_congr';intro q
    apply forall_congr';intro hq
    rw [prime_component_gcd (by omega) (hps p hp) hb,prime_component_gcd (by omega) (hps q hq) hb]
  exact he.trans (table_pairwise_iff hm hps hcover _)
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedFavorable.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- All component computations read the same retained, verified occurrence log.
Only primes dividing the requested cofactor contribute to the comparison. -/
def retainedFavorable (t : ℕ) (a m : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) 1 :=
  let ps:=tableNets (M.fieldRows t)
  (OrderSlots.usableOn a m).band ((all (ps.map (fun p=>all (ps.map (fun q=>
    (dividesOn p m).bnot.bor ((dividesOn q m).bnot.bor
      (sameTwoVal (M.retainedComponentOrder t a m p) (M.retainedComponentOrder t a m q)))))))).bnot)

lemma retainedFavorable_table {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedFavorable t a m).eval (M.encoded x t r) 0=true ↔
      tableFavorable (PhysicalTree.tableFactors (M.dataLog x t r)) (trueData P)
        (bitsValue (a.eval (M.encoded x t r))).toNat d n := by
  have hval:=tableNets_values hn (M.fieldRows t) (M.encoded x t r)
  rw [M.fieldRows_values] at hval
  have hp : ∀ p∈tableNets (M.fieldRows t),
      ((bitsValue (p.eval (M.encoded x t r))).toNat).Prime := by
    intro p hp
    apply PhysicalTree.tableFactors_prime hc
    rw [←hval]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  rw [retainedFavorable,eval_band,Bool.and_eq_true,OrderSlots.usableOn_value a m _ (by omega),
    OrderSlots.Usable,ZMod.isUnit_iff_coprime,hm,tableFavorable,←hval,and_assoc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro ha
  rw [bnot_value]
  apply not_congr
  simp only [all_eval,List.forall_mem_map,eval_bor,Bool.or_eq_true,bnot_value,
    dividesOn_value,hm,or_iff_not_imp_left,not_not]
  have hcmp (p q : BooleanNetwork (M.width t) n)
      (hp' : p∈tableNets (M.fieldRows t)) (hq' : q∈tableNets (M.fieldRows t))
      (hpd : (bitsValue (p.eval (M.encoded x t r))).toNat∣d)
      (hqd : (bitsValue (q.eval (M.encoded x t r))).toNat∣d) :
      (sameTwoVal (M.retainedComponentOrder t a m p) (M.retainedComponentOrder t a m q)).eval
        (M.encoded x t r) 0=true ↔
      padicValNat 2 (dataOrder (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat
        (d.gcd ((bitsValue (p.eval (M.encoded x t r))).toNat^n)))=
      padicValNat 2 (dataOrder (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat
        (d.gcd ((bitsValue (q.eval (M.encoded x t r))).toNat^n))) := by
    have hep:=M.retainedComponentOrder_exact hn t a m p x r hc hP hP0 hd hdiv hm (hp p hp') hpd ha
    have heq:=M.retainedComponentOrder_exact hn t a m q x r hc hP hP0 hd hdiv hm (hp q hq') hqd ha
    have hb : d ≤ 2^n:=hm ▸ (bitsValue (m.eval (M.encoded x t r))).isLt.le
    have hnp : (bitsValue ((M.retainedComponentOrder t a m p).eval (M.encoded x t r))).toNat≠0 := by
      rw [hep]
      exact data_component_order_ne_zero (by omega) hd hdiv hb (hp p hp') hpd ha
    have hnq : (bitsValue ((M.retainedComponentOrder t a m q).eval (M.encoded x t r))).toNat≠0 := by
      rw [heq]
      exact data_component_order_ne_zero (by omega) hd hdiv hb (hp q hq') hqd ha
    rw [sameTwoVal_value _ _ _ hnp hnq,hep,heq]
  constructor
  · intro h p hp' hpd q hq' hqd
    exact (hcmp p q hp' hq' hpd hqd).mp (h p hp' q hq' hpd hqd)
  · intro h p hp' q hq' hpd hqd
    exact (hcmp p q hp' hq' hpd hqd).mpr (h p hp' hpd q hq' hqd)

lemma retainedFavorable_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedFavorable t a m).eval (M.encoded x t r) 0=true ↔
      dataResidueGood (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat d := by
  rw [M.retainedFavorable_table hn t a m x r hc hP hP0 hd hdiv hm]
  exact tableFavorable_correct (by omega) hd (hm ▸ (bitsValue (m.eval (M.encoded x t r))).isLt.le)
    hdiv (PhysicalTree.tableFactors_prime hc)
    (PhysicalTree.tableFactors_cover hc hP hP0 (by omega) hdiv) _

def retainedGoodList (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (y : BooleanNetwork (M.width t) (n*(n^5+1))) : BooleanNetwork (M.width t) 1 :=
  any (List.ofFn (fun i : Fin (n^5)=>M.retainedFavorable t (TransitionWords.readNet y i) m))

lemma retainedGoodList_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (y : BooleanNetwork (M.width t) (n*(n^5+1)))
    (x : Basis c) (r : Trace n t) (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedGoodList t m y).eval (M.encoded x t r) 0=true ↔
      dataGoodList (trueData P) d n (y.eval (M.encoded x t r)) := by
  change (M.retainedGoodList t m y).eval (M.encoded x t r) 0=true ↔
    ∃ i : Fin (n^5),dataResidueGood (trueData P)
      (bitsValue (TransitionWords.read (y.eval (M.encoded x t r)) i)).toNat d
  rw [retainedGoodList,any_eval]
  constructor
  · rintro ⟨v,hv,he⟩
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hv
    refine ⟨i,?_⟩
    rw [M.retainedFavorable_exact hn t _ m x r hc hP hP0 hd hdiv hm,
      TransitionWords.readNet_eval] at he
    exact he
  · rintro ⟨i,hi⟩
    refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    rw [M.retainedFavorable_exact hn t _ m x r hc hP hP0 hd hdiv hm,
      TransitionWords.readNet_eval]
    exact hi
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ClosedLevelCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

/-- Compute the odd part by a bounded gcd and exact integer division. -/
def oddPartNet {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k n :=
  (a.pair (primeComponent a (wordConstant (BitVec.ofNat n 2)))).comp (div n)

lemma oddPartNet_value {k n : ℕ} (hn : 2 ≤ n) (a : BooleanNetwork k n)
    (x : Basis k) (ha : (bitsValue (a.eval x)).toNat≠0) :
    (bitsValue ((oddPartNet a).eval x)).toNat=
      (bitsValue (a.eval x)).toNat/2^padicValNat 2 (bitsValue (a.eval x)).toNat := by
  have h2 : 2<2^n := lt_of_lt_of_le (by decide : 2<2^2)
    (Nat.pow_le_pow_right (by decide : 0<2) hn)
  have hc : (bitsValue ((wordConstant (n:=k) (BitVec.ofNat n 2)).eval x)).toNat=2 := by
    rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2]
  have hh:=primeComponent_value a (wordConstant (BitVec.ofNat n 2)) x ha
    (by rw [hc];exact Nat.prime_two)
  rw [hc,Nat.factorization_def _ Nat.prime_two] at hh
  rw [oddPartNet,eval_comp,eval_pair,div_word,BitVec.toNat_udiv,hh]

/-- An exact level count, selected by the bounded divisibility predicate.
The branch at t≥n is zero since a is a nonzero n-bit word. -/
def closedLevelNet {k n : ℕ} (a : BooleanNetwork k n) (t : ℕ) : BooleanNetwork k n :=
  if t=0 then oddPartNet a
  else if t<n then wordMux (a.comp (dividesNet n (2^t)))
    (((oddPartNet a).pair (wordConstant (BitVec.ofNat n (2^(t-1))))).comp (mul n))
    (wordConstant (BitVec.ofNat n 0))
  else wordConstant (BitVec.ofNat n 0)

lemma closedLevelNet_value {k n : ℕ} (hn : 2≤n) (a : BooleanNetwork k n)
    (x : Basis k) (ha : (bitsValue (a.eval x)).toNat≠0) (t : ℕ) :
    (bitsValue ((closedLevelNet a t).eval x)).toNat=
      closedLevelCount (bitsValue (a.eval x)).toNat t := by
  have hodd:=oddPartNet_value hn a x ha
  have hv:=twoadic_lt_width ha (bitsValue (a.eval x)).isLt
  rw [closedLevelNet,closedLevelCount]
  by_cases ht : t=0
  · rw [ite_eq_left ht,ite_eq_left ht,hodd]
  · rw [ite_eq_right ht,ite_eq_right ht]
    by_cases htn : t<n
    · rw [ite_eq_left htn,wordMux_eval]
      have hd : (a.comp (dividesNet n (2^t))).eval x 0=true ↔
          t≤padicValNat 2 (bitsValue (a.eval x)).toNat := by
        rw [eval_comp,dividesNet_value _ _ _ (Nat.pow_lt_pow_right (by decide : 1<2) htn),
          padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) ha]
      by_cases he : t≤padicValNat 2 (bitsValue (a.eval x)).toNat
      · rw [ite_eq_left (hd.mpr he),ite_eq_left he,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,hodd,
          wordConstant_eval,BitVec.toNat_ofNat]
        have hc : 2^(t-1)<2^n:=Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
        rw [Nat.mod_eq_of_lt hc]
        have hdvd : 2^padicValNat 2 (bitsValue (a.eval x)).toNat∣(bitsValue (a.eval x)).toNat :=
          (padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) ha).mpr le_rfl
        have hp : 2^(t-1)≤2^padicValNat 2 (bitsValue (a.eval x)).toNat :=
          Nat.pow_le_pow_right (by decide : 0<2) (by omega)
        have hb := Nat.mul_le_mul_left ((bitsValue (a.eval x)).toNat/
          2^padicValNat 2 (bitsValue (a.eval x)).toNat) hp
        rw [Nat.div_mul_cancel hdvd] at hb
        rw [Nat.mod_eq_of_lt (hb.trans_lt (bitsValue (a.eval x)).isLt),Nat.mul_comm]
      · rw [ite_eq_right (fun h=>he (hd.mp h)),ite_eq_right he,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod]
    · rw [ite_eq_right htn,ite_eq_right (by omega),wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod]

def oddPartBound (n c : ℕ) : ℕ := c+primeComponentBound n (c+n)+216*n*n+56*n+6
lemma oddPartNet_count {k n c : ℕ} (a : BooleanNetwork k n) (ha : a.net.count≤c) :
    (oddPartNet a).net.count≤oddPartBound n c := by
  have hp:=primeComponent_count a (wordConstant (BitVec.ofNat n 2))
    (c:=c+n) (by omega) (by rw [wordConstant_count];omega)
  have hd:=div_count n
  simp only [oddPartNet,count_comp,count_pair]
  dsimp only [oddPartBound]
  omega

def closedLevelBound (n c : ℕ) : ℕ := oddPartBound n c+c+1000*n*n+1000*n+100
lemma closedLevelNet_count {k n c : ℕ} (a : BooleanNetwork k n) (ha : a.net.count≤c) (t : ℕ) :
    (closedLevelNet a t).net.count≤closedLevelBound n c := by
  have ho:=oddPartNet_count a ha
  have hd:=dividesNet_count n (2^t)
  have hm:=mul_count n
  rw [closedLevelNet]
  by_cases ht : t=0
  · rw [ite_eq_left ht]
    dsimp only [closedLevelBound];omega
  · rw [ite_eq_right ht]
    by_cases htn : t<n
    · rw [ite_eq_left htn,wordMux_count,count_comp,count_comp,count_pair,
        wordConstant_count,wordConstant_count]
      dsimp only [closedLevelBound]
      nlinarith
    · rw [ite_eq_right htn,wordConstant_count]
      dsimp only [closedLevelBound]
      omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ComponentPhiCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

/-- Euler's prime-power formula, implemented by n-bit arithmetic on the
computed gcd component. Divisibility by p is a verified-call precondition. -/
def componentPhiNet {k n : ℕ} (m p : BooleanNetwork k n) : BooleanNetwork k n :=
  let q:=primeComponent m p
  natSubOn q ((q.pair p).comp (div n))

lemma componentPhiNet_value {k n : ℕ} (m p : BooleanNetwork k n) (x : Basis k)
    (hm : (bitsValue (m.eval x)).toNat≠0) (hp : ((bitsValue (p.eval x)).toNat).Prime)
    (hd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat) :
    (bitsValue ((componentPhiNet m p).eval x)).toNat=
      primePowerUnitCount (bitsValue (p.eval x)).toNat
        ((bitsValue (m.eval x)).toNat.factorization (bitsValue (p.eval x)).toNat) := by
  have hq:=primeComponent_value m p x hm hp
  have he:=hp.factorization_pos_of_dvd hm hd
  rw [componentPhiNet,natSubOn_value,eval_comp,eval_pair,div_word,BitVec.toNat_udiv,hq]
  obtain ⟨e,he'⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  rw [he',primePowerUnitCount,Nat.succ_sub_one,pow_succ,Nat.mul_div_cancel _ hp.pos]
  simpa only [Nat.mul_one,Nat.one_mul,Nat.mul_comm] using
    (Nat.mul_sub_left_distrib ((bitsValue (p.eval x)).toNat^e) (bitsValue (p.eval x)).toNat 1).symm

lemma componentPhiNet_ne_zero {k n : ℕ} (m p : BooleanNetwork k n) (x : Basis k)
    (hm : (bitsValue (m.eval x)).toNat≠0) (hp : ((bitsValue (p.eval x)).toNat).Prime)
    (hd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat) :
    (bitsValue ((componentPhiNet m p).eval x)).toNat≠0 := by
  rw [componentPhiNet_value m p x hm hp hd,primePowerUnitCount]
  exact Nat.ne_of_gt (Nat.mul_pos (by have := hp.two_le;omega) (Nat.pow_pos hp.pos))

def componentPhiBound (n c : ℕ) : ℕ := 4*primeComponentBound n c+2*c+1000*n*n+1000*n+100
lemma componentPhiNet_count {k n c : ℕ} (m p : BooleanNetwork k n)
    (hm : m.net.count≤c) (hp : p.net.count≤c) :
    (componentPhiNet m p).net.count≤componentPhiBound n c := by
  have hq:=primeComponent_count m p hm hp
  have hd:=div_count n
  have hs:=natSubOn_count (primeComponent m p) (((primeComponent m p).pair p).comp (div n))
  simp only [count_comp,count_pair] at hs
  change (natSubOn _ _).net.count≤_
  dsimp only [componentPhiBound]
  nlinarith

def componentLevelNet {k n : ℕ} (m p : BooleanNetwork k n) (t : ℕ) : BooleanNetwork k n :=
  wordMux (dividesOn p m) (closedLevelNet (componentPhiNet m p) t)
    (wordConstant (BitVec.ofNat n 1))

lemma componentLevelNet_value {k n : ℕ} (hn : 2≤n) (m p : BooleanNetwork k n)
    (x : Basis k) (hm : (bitsValue (m.eval x)).toNat≠0)
    (hp : ((bitsValue (p.eval x)).toNat).Prime) (t : ℕ) :
    (bitsValue ((componentLevelNet m p t).eval x)).toNat=
      if (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat then
        closedLevelCount (primePowerUnitCount (bitsValue (p.eval x)).toNat
          ((bitsValue (m.eval x)).toNat.factorization (bitsValue (p.eval x)).toNat)) t
      else 1 := by
  rw [componentLevelNet,wordMux_eval]
  by_cases hd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat
  · rw [ite_eq_left ((dividesOn_value p m x).mpr hd),ite_eq_left hd,
      closedLevelNet_value hn _ x (componentPhiNet_ne_zero m p x hm hp hd),
      componentPhiNet_value m p x hm hp hd]
  · rw [ite_eq_right (fun h=>hd ((dividesOn_value p m x).mp h)),ite_eq_right hd,
      wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.one_lt_pow (by omega) (by decide))]

def componentLevelBound (n c : ℕ) : ℕ :=
  2*c+216*n*n+308*n+50+closedLevelBound n (componentPhiBound n c)+8*n
lemma componentLevelNet_count {k n c : ℕ} (m p : BooleanNetwork k n)
    (hm : m.net.count≤c) (hp : p.net.count≤c) (t : ℕ) :
    (componentLevelNet m p t).net.count≤componentLevelBound n c := by
  have hc:=closedLevelNet_count (componentPhiNet m p) (componentPhiNet_count m p hm hp) t
  have hd:=dividesOn_count p m
  rw [componentLevelNet,wordMux_count,wordConstant_count]
  dsimp only [componentLevelBound]
  nlinarith
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
