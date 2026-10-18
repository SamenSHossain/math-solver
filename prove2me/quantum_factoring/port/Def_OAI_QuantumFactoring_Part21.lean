/-
Exact quantum factoring development (port of OpenAI's formalization), part 21 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: DistinctProductCircuit.lean, TableLevelCircuit.lean, TableTotient.lean, TotientAccumulator.lean, TotientCircuit.lean, TableTotientCircuit.lean, TableDirectPhi.lean, WordSumCircuit.lean, TableFavorableCount.lean, RetainedFavorableCount.lean, RetainedListFilter.lean, RetainedListDummy.lean, RetainedTotient.lean, RetainedOrderFilter.lean, RetainedOrderTest.lean, RetainedSplitFilter.lean, RetainedSplitPass.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part20

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/DistinctProductCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
open scoped BigOperators
namespace BitArithmetic

/-- Equality is tested on runtime word values, not on network syntax. -/
def occursLater {k n : ℕ} (p : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k 1 := any (ps.map (fun q=>(p.pair q).comp (wordEq n)))

lemma occursLater_value {k n : ℕ} (p : BooleanNetwork k n) (ps : List (BooleanNetwork k n))
    (x : Basis k) : (occursLater p ps).eval x 0=true ↔
      (bitsValue (p.eval x)).toNat∈ps.map (fun q=>(bitsValue (q.eval x)).toNat) := by
  simp only [occursLater,any_eval,List.mem_map,exists_exists_and_eq_and,
    eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq]
  constructor
  · rintro ⟨q,hq,he⟩
    exact ⟨q,hq,(congrArg BitVec.toNat he).symm⟩
  · rintro ⟨q,hq,he⟩
    exact ⟨q,hq,BitVec.eq_of_toNat_eq he.symm⟩

/-- A quadratic comparison scan counts every runtime prime only once.
No sorting primitive or mathematical finset operation is used by the circuit. -/
def distinctProductNet {k n : ℕ} (value : BooleanNetwork k n→BooleanNetwork k n) :
    List (BooleanNetwork k n)→BooleanNetwork k n
  | []=>wordConstant 1
  | p::ps=>(wordMux (occursLater p ps) (wordConstant 1) (value p)).pair
      (distinctProductNet value ps) |>.comp (mul n)

lemma distinctProductNet_value {k n : ℕ} (value : BooleanNetwork k n→BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (f : ℕ→ℕ)
    (hv : ∀ p∈ps,(bitsValue ((value p).eval x)).toNat=f (bitsValue (p.eval x)).toNat%2^n) :
    (bitsValue ((distinctProductNet value ps).eval x)).toNat=
      (∏ p∈(ps.map (fun q=>(bitsValue (q.eval x)).toNat)).toFinset,f p)%2^n := by
  induction ps with
  | nil=>simp [distinctProductNet,wordConstant_eval]
  | cons p ps ih=>
    have hp:=hv p (by simp)
    have hi:=ih (fun q hq=>hv q (by simp [hq]))
    rw [distinctProductNet,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,
      wordMux_eval,hi,List.map_cons,List.toFinset_cons]
    by_cases he : (bitsValue (p.eval x)).toNat∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)
    · rw [ite_eq_left ((occursLater_value p ps x).mpr he),wordConstant_eval,
        Finset.insert_eq_of_mem (List.mem_toFinset.mpr he),show (1 : BitVec n).toNat=1%2^n from rfl,Nat.mod_mul_mod,Nat.mul_mod_mod,one_mul]
    · rw [ite_eq_right (fun h=>he ((occursLater_value p ps x).mp h)),hp,
        Finset.prod_insert (by simpa only [List.mem_toFinset] using he),Nat.mod_mul_mod,Nat.mul_mod_mod]

lemma occursLater_count {k n c : ℕ} (p : BooleanNetwork k n) (ps : List (BooleanNetwork k n))
    (hp : p.net.count≤c) (hps : ∀ q∈ps,q.net.count≤c) :
    (occursLater p ps).net.count≤ps.length*(2*c+96*n+25)+1 := by
  have hh:=any_count (ps.map (fun q=>(p.pair q).comp (wordEq n)))
    (c:=2*c+96*n+21) (by
      intro q hq
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hq
      have h:=hps b hb
      have hw:=wordEq_count n
      rw [count_comp,count_pair]
      omega)
  simpa only [occursLater,List.length_map,Nat.add_assoc] using hh

lemma distinctProductNet_count {k n c d : ℕ} (value : BooleanNetwork k n→BooleanNetwork k n)
    (ps : List (BooleanNetwork k n))
    (hp : ∀ p∈ps,p.net.count≤c) (hv : ∀ p∈ps,(value p).net.count≤d) :
    (distinctProductNet value ps).net.count≤
      ps.length*(d+90*n*n+22*n+7+ps.length*(2*c+96*n+25))+n := by
  induction ps with
  | nil=>simp [distinctProductNet,wordConstant_count]
  | cons p ps ih=>
    have hps:=fun q hq=>hp q (List.mem_cons_of_mem p hq)
    have hvs:=fun q hq=>hv q (List.mem_cons_of_mem p hq)
    have hi:=ih hps hvs
    have ho:=occursLater_count p ps (hp p (by simp)) hps
    have hd:=hv p (by simp)
    have hm:=mul_count n
    simp only [distinctProductNet,count_comp,count_pair,wordMux_count,wordConstant_count,
      List.length_cons]
    nlinarith
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableLevelCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
open scoped BigOperators

lemma equalLevelSum_le_totient {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (ho : Odd m) :
    (∑ t : Fin (n+1),∏ p : Component m,
      closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val)≤ m.totient := by
  classical
  let p₀ : Component m := ⟨m.minFac,Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd m,by omega⟩⟩
  have h0 : m≠0:=by omega
  let : NeZero m:=⟨h0⟩
  rw [←equal_component_card h0 hb ho p₀]
  calc
    _≤Fintype.card (∀ p : Component m,ComponentUnits m p):=Fintype.card_subtype_le _
    _=Fintype.card (ZMod m)ˣ:=(Fintype.card_congr (unitCRT m h0).toEquiv).symm
    _=m.totient:=ZMod.card_units_eq_totient m

lemma componentLevelProduct_lt {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (ho : Odd m)
    (t : Fin (n+1)) :
    (∏ p : Component m,closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val)<2^n := by
  have hs:=Finset.single_le_sum (f:=fun t : Fin (n+1)=>∏ p : Component m,
    closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ t)
  exact (hs.trans (equalLevelSum_le_totient hm hb ho)).trans_lt ((Nat.totient_le m).trans_lt hb)

lemma table_level_product {ps : List ℕ} {m : ℕ} (hm : m≠0)
    (hp : ∀ p∈ps,p.Prime) (hcover : ∀ p : ℕ,p.Prime→p∣m→p∈ps) (t : ℕ) :
    (∏ p∈ps.toFinset,if p∣m then closedLevelCount (primePowerUnitCount p (m.factorization p)) t else 1)=
      ∏ p : Component m,closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t := by
  classical
  have he : ps.toFinset.filter (fun p=>p∣m)=m.primeFactors := by
    ext p
    simp only [Finset.mem_filter,List.mem_toFinset]
    constructor
    · rintro ⟨hps,hpd⟩
      exact Nat.mem_primeFactors.mpr ⟨hp p hps,hpd,hm⟩
    · intro h
      obtain ⟨hpp,hpd,_⟩:=Nat.mem_primeFactors.mp h
      exact ⟨hcover p hpp hpd,hpd⟩
  rw [←Finset.prod_filter,he]
  exact (Finset.prod_coe_sort _ _).symm

namespace BitArithmetic

def tableLevelNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) (t : ℕ) :
    BooleanNetwork k n := distinctProductNet (fun p=>componentLevelNet m p t) ps

lemma tableLevelNet_value {k n : ℕ} (hn : 2 ≤ n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (ho : Odd (bitsValue (m.eval x)).toNat)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) (t : Fin (n+1)) :
    (bitsValue ((tableLevelNet m ps t.val).eval x)).toNat=
      ∏ p : Component (bitsValue (m.eval x)).toNat,
        closedLevelCount (primePowerUnitCount p.val ((bitsValue (m.eval x)).toNat.factorization p.val)) t.val := by
  let f : ℕ→ℕ:=fun p=>if p∣(bitsValue (m.eval x)).toNat then
    closedLevelCount (primePowerUnitCount p ((bitsValue (m.eval x)).toNat.factorization p)) t.val else 1
  have hh:=distinctProductNet_value (fun p=>componentLevelNet m p t.val) ps x f (by
    intro p hp'
    have he:=componentLevelNet_value hn m p x (by omega) (hp p hp') t.val
    change (bitsValue ((componentLevelNet m p t.val).eval x)).toNat=f (bitsValue (p.eval x)).toNat at he
    rw [←he,Nat.mod_eq_of_lt (bitsValue ((componentLevelNet m p t.val).eval x)).isLt])
  rw [tableLevelNet,hh]
  dsimp only [f]
  rw [table_level_product (by omega) (by
    intro p hp'
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp'
    exact hp q hq) hcover t.val]
  exact Nat.mod_eq_of_lt (componentLevelProduct_lt hm (bitsValue (m.eval x)).isLt ho t)

lemma tableLevelNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count≤c)
    (hp : ∀ p∈ps,p.net.count≤c) (t : ℕ) :
    (tableLevelNet m ps t).net.count≤
      ps.length*(componentLevelBound n c+90*n*n+22*n+7+ps.length*(2*c+96*n+25))+n := by
  exact distinctProductNet_count _ _ hp (fun p hh=>componentLevelNet_count m p hm (hp p hh) t)
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableTotient.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Strip a given prime multiset, updating Euler's totient one prime factor
at a time. The supplied list may contain redundant factors. -/
def totientScan : List ℕ → ℕ → ℕ
  | [], _ => 1
  | p::ps, v => if p ∣ v then
      (if p ∣ v/p then p else p-1)*totientScan ps (v/p)
    else totientScan ps v

lemma totientScan_exact (ps : List ℕ) (v : ℕ) (hv : 0 < v)
    (hp : ∀ p∈ps,p.Prime) (hd : v ∣ ps.prod) : totientScan ps v=v.totient := by
  induction ps generalizing v with
  | nil=>
    have he : v=1 := Nat.eq_one_of_dvd_one hd
    subst v
    simp [totientScan]
  | cons p ps ih=>
    have hprime:=hp p (List.mem_cons_self)
    have hps : ∀ q∈ps,q.Prime := fun q hq=>hp q (List.mem_cons_of_mem _ hq)
    rw [List.prod_cons] at hd
    rw [totientScan]
    by_cases hdv : p ∣ v
    · rw [ite_eq_left hdv]
      have he : p*(v/p)=v := Nat.mul_div_cancel' hdv
      have hd' : v/p ∣ ps.prod := by
        apply (Nat.mul_dvd_mul_iff_left hprime.pos).mp
        rwa [he]
      have hv' : 0 < v/p := by
        exact Nat.div_pos (Nat.le_of_dvd hv hdv) hprime.pos
      rw [ih (v/p) hv' hps hd']
      conv_rhs => rw [←he]
      by_cases hpp : p ∣ v/p
      · rw [ite_eq_left hpp,Nat.totient_mul_of_prime_of_dvd hprime hpp]
      · rw [ite_eq_right hpp,Nat.totient_mul_of_prime_of_not_dvd hprime hpp]
    · rw [ite_eq_right hdv]
      apply ih v hv hps
      exact (hprime.coprime_iff_not_dvd.mpr hdv).symm.dvd_of_dvd_mul_left hd

namespace PhysicalTree
/-- The same rectangular table which suffices for order stripping supplies
Euler's totient of every positive divisor of the group exponent. -/
theorem table_totient_exact {n N M m d : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hb : m < 2^n) (hd : m∣M) (hd0 : 0 < d) (hdt : d∣m.totient) :
    totientScan (List.flatten (List.replicate n (tableFactors rows))) d=d.totient := by
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
  apply totientScan_exact _ d hd0
  · intro p hp
    obtain ⟨xs,hxs,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hxs).2
    subst xs
    exact tableFactors_prime h p hp
  · rw [List.prod_flatten,List.map_replicate,List.prod_replicate]
    exact hdt.trans hphi
end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TotientAccumulator.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The finite-word accumulator semantics. Only the multiplicative
accumulator is reduced; division of the residual never overflows. -/
def totientStepNat (B p : ℕ) (s : ℕ×ℕ) : ℕ×ℕ :=
  if p ∣ s.1 then (s.1/p,(s.2*(if p ∣ s.1/p then p else p-1))%B) else s

def totientFoldNat (B : ℕ) : List ℕ → (ℕ×ℕ) → (ℕ×ℕ)
  | [], s => s
  | p::ps, s => totientFoldNat B ps (totientStepNat B p s)

lemma totientStepNat_bound {B p : ℕ} (hB : 0 < B) (s : ℕ×ℕ)
    (hs : s.1 < B ∧ s.2 < B) :
    (totientStepNat B p s).1 < B ∧ (totientStepNat B p s).2 < B := by
  unfold totientStepNat
  split
  · exact ⟨(Nat.div_le_self _ _).trans_lt hs.1,Nat.mod_lt _ hB⟩
  · exact hs

lemma totientFoldNat_score (B : ℕ) (ps : List ℕ) (s : ℕ×ℕ) (hs : s.2 < B) :
    (totientFoldNat B ps s).2=(s.2*totientScan ps s.1)%B := by
  induction ps generalizing s with
  | nil=>simp only [totientFoldNat,totientScan,mul_one,Nat.mod_eq_of_lt hs]
  | cons p ps ih=>
    rw [totientFoldNat,ih (totientStepNat B p s) (by
      unfold totientStepNat
      split
      · exact Nat.mod_lt _ (Nat.zero_lt_of_lt hs)
      · exact hs)]
    rw [totientScan]
    unfold totientStepNat
    split_ifs with hd hp
    · simp only [Nat.mod_mul_mod,mul_assoc]
    · simp only [Nat.mod_mul_mod,mul_assoc]
    · rfl

lemma totientFoldNat_exact (B : ℕ) (ps : List ℕ) (v : ℕ)
    (hB : 1 < B) (hv : 0 < v) (hb : v < B)
    (hp : ∀ p∈ps,p.Prime) (hd : v∣ps.prod) :
    (totientFoldNat B ps (v,1)).2=v.totient := by
  rw [totientFoldNat_score B ps (v,1) hB,totientScan_exact ps v hv hp hd,one_mul,
    Nat.mod_eq_of_lt ((Nat.totient_le v).trans_lt hb)]
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TotientCircuit.lean =====
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

/-- A division-based totient step. Redundant prime entries do nothing. -/
def totientPair {k w : ℕ} (q v a : BooleanNetwork k w) : BooleanNetwork k (w+w) :=
  let d := (v.pair q).comp (div w)
  let cond := zeroWord ((v.pair q).comp (mod w))
  let weight := wordMux (zeroWord ((d.pair q).comp (mod w))) q
    (natSubOn q (wordConstant (BitVec.ofNat w 1)))
  (wordMux cond d v).pair (wordMux cond ((a.pair weight).comp (mul w)) a)

lemma totientPair_value {k w : ℕ} (hw : 0 < w) (q v a : BooleanNetwork k w) (x : Basis k) :
    let y := (totientPair q v a).eval x
    ((bitsValue (y ∘ Fin.castAdd w)).toNat,(bitsValue (y ∘ Fin.natAdd w)).toNat)=
      totientStepNat (2^w) (bitsValue (q.eval x)).toNat
        ((bitsValue (v.eval x)).toNat,(bitsValue (a.eval x)).toNat) := by
  have h1 : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  let d := (v.pair q).comp (div w)
  let cond := zeroWord ((v.pair q).comp (mod w))
  let weight := wordMux (zeroWord ((d.pair q).comp (mod w))) q
    (natSubOn q (wordConstant (BitVec.ofNat w 1)))
  have hd : (bitsValue (d.eval x)).toNat=(bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat := by
    rw [show d=(v.pair q).comp (div w) from rfl,eval_comp,eval_pair,div_word,BitVec.toNat_udiv]
  have hc : cond.eval x 0=true ↔ (bitsValue (q.eval x)).toNat ∣ (bitsValue (v.eval x)).toNat := by
    rw [show cond=zeroWord ((v.pair q).comp (mod w)) from rfl,zeroWord_value,
      eval_comp,eval_pair,mod_word,BitVec.toNat_umod,Nat.dvd_iff_mod_eq_zero]
  have hweight : (bitsValue (weight.eval x)).toNat=
      if (bitsValue (q.eval x)).toNat ∣ (bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat
      then (bitsValue (q.eval x)).toNat else (bitsValue (q.eval x)).toNat-1 := by
    have hh : (zeroWord ((d.pair q).comp (mod w))).eval x 0=true ↔
        (bitsValue (q.eval x)).toNat ∣ (bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat := by
      rw [zeroWord_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,hd,Nat.dvd_iff_mod_eq_zero]
    rw [show weight=wordMux (zeroWord ((d.pair q).comp (mod w))) q
      (natSubOn q (wordConstant (BitVec.ofNat w 1))) from rfl,wordMux_eval]
    by_cases he : (zeroWord ((d.pair q).comp (mod w))).eval x 0=true
    · rw [ite_eq_left he,ite_eq_left (hh.mp he)]
    · rw [ite_eq_right he,ite_eq_right (fun h=>he (hh.mpr h)),natSubOn_value,wordConstant_eval,
        BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  dsimp only
  rw [totientPair,eval_pair]
  change ((bitsValue ((Fin.append ((wordMux cond d v).eval x)
      ((wordMux cond ((a.pair weight).comp (mul w)) a).eval x)) ∘ Fin.castAdd w)).toNat,
    (bitsValue ((Fin.append ((wordMux cond d v).eval x)
      ((wordMux cond ((a.pair weight).comp (mul w)) a).eval x)) ∘ Fin.natAdd w)).toNat)=_
  have hl (l r : Basis w) : Fin.append l r ∘ Fin.castAdd w=l := by
    funext i; exact Fin.append_left _ _ i
  have hr (l r : Basis w) : Fin.append l r ∘ Fin.natAdd w=r := by
    funext i; exact Fin.append_right _ _ i
  rw [hl,hr,wordMux_eval,wordMux_eval,totientStepNat]
  by_cases he : cond.eval x 0=true
  · rw [ite_eq_left he,ite_eq_left he,ite_eq_left (hc.mp he),hd,eval_comp,eval_pair,mul_word,
      BitVec.toNat_mul,hweight]
  · rw [ite_eq_right he,ite_eq_right he,ite_eq_right (fun h=>he (hc.mpr h))]

/-- A loose but explicit uniform polynomial bound; the residual, prime and
accumulator subcircuits are evaluated a constant number of times per step. -/
def totientStepBound (w c : ℕ) : ℕ := 30*c+3000*w*w+3000*w+300

lemma totientPair_count {k w c : ℕ} (q v a : BooleanNetwork k w)
    (hq : q.net.count ≤ c) (hv : v.net.count ≤ c) (ha : a.net.count ≤ c) :
    (totientPair q v a).net.count ≤ totientStepBound w c := by
  have hd := div_count w
  have hm := mod_count w
  have hmul := mul_count w
  have hzero := zeroWord_count ((v.pair q).comp (mod w))
  have hz := zeroWord_count ((((v.pair q).comp (div w)).pair q).comp (mod w))
  have hs := natSubOn_count q (wordConstant (n:=k) (BitVec.ofNat w 1))
  simp only [count_comp,count_pair,wordConstant_count] at hzero hz hs
  simp only [totientPair,count_pair,wordMux_count,count_comp]
  dsimp only [totientStepBound]
  nlinarith

/-- Carry the input unchanged and update two finite-word accumulators. -/
def totientUpdate {k w : ℕ} (q : BooleanNetwork k w) :
    BooleanNetwork (k+(w+w)) (k+(w+w)) :=
  (select (Fin.castAdd (w+w))).pair (totientPair (liftInput q (Fin.castAdd (w+w)))
    (select (fun i=>Fin.natAdd k (Fin.castAdd w i)))
    (select (fun i=>Fin.natAdd k (Fin.natAdd w i))))

lemma totientUpdate_value {k w : ℕ} (hw : 0 < w) (q : BooleanNetwork k w)
    (x : Basis k) (s : Basis (w+w)) :
    ∃ s', (totientUpdate q).eval (Fin.append x s)=Fin.append x s' ∧
      ((bitsValue (s' ∘ Fin.castAdd w)).toNat,(bitsValue (s' ∘ Fin.natAdd w)).toNat)=
        totientStepNat (2^w) (bitsValue (q.eval x)).toNat
          ((bitsValue (s ∘ Fin.castAdd w)).toNat,(bitsValue (s ∘ Fin.natAdd w)).toNat) := by
  have hx : Fin.append x s ∘ Fin.castAdd (w+w)=x := by funext i;exact Fin.append_left _ _ i
  let Q:=liftInput q (Fin.castAdd (w+w))
  let V : BooleanNetwork (k+(w+w)) w:=select (fun i=>Fin.natAdd k (Fin.castAdd w i))
  let A : BooleanNetwork (k+(w+w)) w:=select (fun i=>Fin.natAdd k (Fin.natAdd w i))
  have hq : Q.eval (Fin.append x s)=q.eval x := by simp only [Q,liftInput_eval,hx]
  have hv : V.eval (Fin.append x s)=s ∘ Fin.castAdd w := by
    funext i; exact Fin.append_right _ _ _
  have ha : A.eval (Fin.append x s)=s ∘ Fin.natAdd w := by
    funext i; exact Fin.append_right _ _ _
  refine ⟨(totientPair Q V A).eval (Fin.append x s),?_,?_⟩
  · simp only [totientUpdate,eval_pair,eval_select,hx]
    rfl
  · simpa only [hq,hv,ha] using totientPair_value hw Q V A (Fin.append x s)

lemma totientUpdate_count {k w c : ℕ} (q : BooleanNetwork k w) (hq : q.net.count ≤ c) :
    (totientUpdate q).net.count ≤ totientStepBound w c := by
  simp only [totientUpdate,count_pair,count_select,zero_add]
  exact totientPair_count _ _ _ (by simpa using hq) (by simp) (by simp)

def totientScanNet {k w : ℕ} : List (BooleanNetwork k w)→BooleanNetwork (k+(w+w)) (k+(w+w))
  | []=>select id
  | q::qs=>(totientUpdate q).comp (totientScanNet qs)

lemma totientScanNet_count {k w c : ℕ} (qs : List (BooleanNetwork k w))
    (hq : ∀ q∈qs,q.net.count ≤ c) :
    (totientScanNet qs).net.count ≤ qs.length*totientStepBound w c := by
  induction qs with
  | nil=>simp [totientScanNet]
  | cons q qs ih=>
    have hh:=totientUpdate_count q (hq q (List.mem_cons_self))
    have ht:=ih (fun q h=>hq q (List.mem_cons_of_mem _ h))
    simp only [totientScanNet,count_comp,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

lemma totientScanNet_value {k w : ℕ} (hw : 0 < w) (qs : List (BooleanNetwork k w))
    (x : Basis k) (s : Basis (w+w)) :
    ∃ s', (totientScanNet qs).eval (Fin.append x s)=Fin.append x s' ∧
      ((bitsValue (s' ∘ Fin.castAdd w)).toNat,(bitsValue (s' ∘ Fin.natAdd w)).toNat)=
        totientFoldNat (2^w) (qs.map (fun q=>(bitsValue (q.eval x)).toNat))
          ((bitsValue (s ∘ Fin.castAdd w)).toNat,(bitsValue (s ∘ Fin.natAdd w)).toNat) := by
  induction qs generalizing s with
  | nil=>exact ⟨s,rfl,rfl⟩
  | cons q qs ih=>
    obtain ⟨s₁,he₁,hv₁⟩:=totientUpdate_value hw q x s
    obtain ⟨s₂,he₂,hv₂⟩:=ih s₁
    refine ⟨s₂,?_,?_⟩
    · rw [totientScanNet,eval_comp,he₁,he₂]
    · rw [List.map_cons,totientFoldNat,←hv₁]
      exact hv₂

end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableTotientCircuit.lean =====
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

/-- Run the polynomial accumulator scan from the queried word and one. -/
def totientFromList {k w : ℕ} (v : BooleanNetwork k w) (qs : List (BooleanNetwork k w)) :
    BooleanNetwork k w :=
  (((select id).pair (v.pair (wordConstant (BitVec.ofNat w 1)))).comp
    (totientScanNet qs)).comp (select (fun i=>Fin.natAdd k (Fin.natAdd w i)))

lemma totientFromList_value {k w : ℕ} (hw : 0 < w) (v : BooleanNetwork k w)
    (qs : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((totientFromList v qs).eval x)).toNat=
      totientScan (qs.map (fun q=>(bitsValue (q.eval x)).toNat))
        (bitsValue (v.eval x)).toNat % 2^w := by
  let one : Basis w:=(wordConstant (n:=k) (BitVec.ofNat w 1)).eval x
  let s:=Fin.append (v.eval x) one
  have h1 : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  have hs : ((bitsValue (s ∘ Fin.castAdd w)).toNat,(bitsValue (s ∘ Fin.natAdd w)).toNat)=
      ((bitsValue (v.eval x)).toNat,1) := by
    have hl : s ∘ Fin.castAdd w=v.eval x := by funext i; exact Fin.append_left _ _ i
    have hr : s ∘ Fin.natAdd w=one := by funext i; exact Fin.append_right _ _ i
    rw [hl,hr]
    simp only [one,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  obtain ⟨s',he,hv⟩:=totientScanNet_value hw qs x s
  rw [hs] at hv
  have hv':=congrArg Prod.snd hv
  rw [totientFoldNat_score _ _ (_,1) h1,one_mul] at hv'
  have houtput : Fin.append x s' ∘ (fun i=>Fin.natAdd k (Fin.natAdd w i))=s' ∘ Fin.natAdd w := by
    funext i; exact Fin.append_right _ _ _
  rw [totientFromList,eval_comp,eval_comp,eval_pair,eval_pair,eval_select]
  change (bitsValue ((select (fun i=>Fin.natAdd k (Fin.natAdd w i))).eval
    ((totientScanNet qs).eval (Fin.append x s)))).toNat=_
  rw [he,eval_select,houtput]
  exact hv'

lemma totientFromList_count {k w c : ℕ} (v : BooleanNetwork k w)
    (qs : List (BooleanNetwork k w)) (hq : ∀ q∈qs,q.net.count ≤ c) :
    (totientFromList v qs).net.count ≤ v.net.count+w+qs.length*totientStepBound w c := by
  have hh:=totientScanNet_count qs hq
  simp only [totientFromList,count_comp,count_pair,count_select,zero_add,Nat.add_zero,
    wordConstant_count]
  omega

/-- At most n repetitions of each rectangular prime entry suffice. Unlike
order stripping, the totient accumulator does not need a wide product. -/
def tableTotient {k n : ℕ} (v : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) : BooleanNetwork k n :=
  totientFromList v (List.flatten (List.replicate n (tableNets rows)))

theorem tableTotient_exact {k n N M m d : ℕ} (hn : 2 ≤ n) (v : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k)
    (hc : PhysicalTree.CompleteLog n N (tableValues rows x))
    (hM : M∈(tableValues rows x).map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hb : m < 2^n) (hd : m∣M) (hd0 : 0 < d) (hdt : d∣m.totient)
    (hv : (bitsValue (v.eval x)).toNat=d) :
    (bitsValue ((tableTotient v rows).eval x)).toNat=d.totient := by
  rw [tableTotient,totientFromList_value (by omega),List.map_flatten,List.map_replicate,
    tableNets_values hn,hv,PhysicalTree.table_totient_exact hc hM hM0 hm hb hd hd0 hdt]
  have hdB : d < 2^n := by rw [←hv]; exact (bitsValue (v.eval x)).isLt
  exact Nat.mod_eq_of_lt ((Nat.totient_le d).trans_lt hdB)

def tableTotientBound (n f c : ℕ) : ℕ := c+n+(n*f)*totientStepBound n (3*c+220*n+50)

lemma tableTotient_count {k n c : ℕ} (v : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n)))
    (hv : v.net.count ≤ c)
    (hr : ∀ r∈rows,r.1.net.count ≤ c ∧ ∀ p∈r.2,p.net.count ≤ c) :
    (tableTotient v rows).net.count ≤ tableTotientBound n (tableNets rows).length c := by
  have hp : ∀ p∈List.flatten (List.replicate n (tableNets rows)),p.net.count ≤ 3*c+220*n+50 := by
    intro p hp
    obtain ⟨qs,hqs,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hqs).2
    subst qs
    exact tableNets_counts rows hr p hp
  have hh:=totientFromList_count v _ hp
  simp only [List.length_flatten,List.map_replicate,List.sum_replicate,smul_eq_mul] at hh
  exact hh.trans (by dsimp only [tableTotientBound];omega)
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableDirectPhi.lean =====
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

def primesPhiNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k n := totientFromList m (List.flatten (List.replicate n ps))

lemma primesPhiNet_value {k n : ℕ} (hn : 0<n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : (bitsValue (m.eval x)).toNat≠0)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) :
    (bitsValue ((primesPhiNet m ps).eval x)).toNat=(bitsValue (m.eval x)).toNat.totient := by
  let vals:=ps.map (fun q=>(bitsValue (q.eval x)).toNat)
  have hps : ∀ p∈vals,p.Prime := by
    intro p hp'
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp'
    exact hp q hq
  have hd:=PhysicalTree.dvd_cover_power vals hm (bitsValue (m.eval x)).isLt.le hps hcover
  rw [primesPhiNet,totientFromList_value hn,List.map_flatten,List.map_replicate,
    totientScan_exact _ _ (Nat.pos_of_ne_zero hm) (by
      intro p hp'
      obtain ⟨qs,hqs,hp'⟩:=List.mem_flatten.mp hp'
      have he:=(List.mem_replicate.mp hqs).2
      subst qs
      exact hps p hp') (by
      rw [List.prod_flatten,List.map_replicate,List.prod_replicate]
      exact hd)]
  exact Nat.mod_eq_of_lt ((Nat.totient_le _).trans_lt (bitsValue (m.eval x)).isLt)

lemma primesPhiNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count≤c) (hp : ∀ p∈ps,p.net.count≤c) :
    (primesPhiNet m ps).net.count≤c+n+(n*ps.length)*totientStepBound n c := by
  have hh:=totientFromList_count m (List.flatten (List.replicate n ps)) (c:=c) (by
    intro p hp'
    obtain ⟨qs,hqs,hp'⟩:=List.mem_flatten.mp hp'
    have he:=(List.mem_replicate.mp hqs).2
    subst qs
    exact hp p hp')
  simp only [List.length_flatten,List.map_replicate,List.sum_replicate,smul_eq_mul] at hh
  exact hh.trans (by omega)
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/WordSumCircuit.lean =====
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

def sumNet {k w : ℕ} : List (BooleanNetwork k w)→BooleanNetwork k w
  | []=>wordConstant 0
  | a::as=>(a.pair (sumNet as)).comp (add w)

lemma sumNet_nat {k w : ℕ} (as : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((sumNet as).eval x)).toNat=
      (as.map (fun a=>(bitsValue (a.eval x)).toNat)).sum%2^w := by
  induction as with
  | nil=>simp [sumNet,wordConstant_eval]
  | cons a as ih=>
    simp only [sumNet,eval_comp,eval_pair,add_word,BitVec.toNat_add,ih,
      List.map_cons,List.sum_cons,Nat.add_mod_mod]

lemma sumNet_count {k w c : ℕ} (as : List (BooleanNetwork k w))
    (h : ∀ a∈as,a.net.count≤c) :
    (sumNet as).net.count≤as.length*(c+86*w+6)+w := by
  induction as with
  | nil=>simp [sumNet,wordConstant_count]
  | cons a as ih=>
    have ha:=h a (by simp)
    have hi:=ih (fun b hb=>h b (by simp [hb]))
    have hh:=add_count w
    simp only [sumNet,count_comp,count_pair,List.length_cons]
    nlinarith
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableFavorableCount.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
open scoped BigOperators
namespace BitArithmetic

def tableBadCountNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k n := sumNet (List.ofFn (fun t : Fin (n+1)=>tableLevelNet m ps t.val))

lemma tableBadCountNet_value {k n : ℕ} (hn : 2 ≤ n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (ho : Odd (bitsValue (m.eval x)).toNat)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) :
    (bitsValue ((tableBadCountNet m ps).eval x)).toNat=
      ∑ t : Fin (n+1),∏ p : Component (bitsValue (m.eval x)).toNat,
        closedLevelCount (primePowerUnitCount p.val ((bitsValue (m.eval x)).toNat.factorization p.val)) t.val := by
  have hs:=equalLevelSum_le_totient hm (bitsValue (m.eval x)).isLt ho
  rw [tableBadCountNet,sumNet_nat,List.map_ofFn,List.sum_ofFn]
  have he : (fun t : Fin (n+1)=>(bitsValue ((tableLevelNet m ps t.val).eval x)).toNat)=
      (fun t : Fin (n+1)=>∏ p : Component (bitsValue (m.eval x)).toNat,
        closedLevelCount (primePowerUnitCount p.val ((bitsValue (m.eval x)).toNat.factorization p.val)) t.val) := by
    funext t
    exact tableLevelNet_value hn m ps x hm ho hp hcover t
  change (∑ t : Fin (n+1),(bitsValue ((tableLevelNet m ps t.val).eval x)).toNat)%2^n=_
  rw [he,Nat.mod_eq_of_lt (hs.trans_lt ((Nat.totient_le _).trans_lt (bitsValue (m.eval x)).isLt))]

/-- The exact source F, computed from supplied prime rows using polynomial
integer circuits. Distinctness tests remove repeated table entries. -/
def tableFavorableCountNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k n := natSubOn (primesPhiNet m ps) (tableBadCountNet m ps)

lemma tableFavorableCountNet_value {k n : ℕ} (hn : 2 ≤ n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (ho : Odd (bitsValue (m.eval x)).toNat)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) :
    (bitsValue ((tableFavorableCountNet m ps).eval x)).toNat=
      favorableCount (bitsValue (m.eval x)).toNat n := by
  rw [tableFavorableCountNet,natSubOn_value,primesPhiNet_value (by omega) m ps x (by omega) hp hcover,
    tableBadCountNet_value hn m ps x hm ho hp hcover]
  rfl

def tableBadCountBound (n f c : ℕ) : ℕ :=
  (n+1)*(f*(componentLevelBound n c+90*n*n+22*n+7+f*(2*c+96*n+25))+n+86*n+6)+n

lemma tableBadCountNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count≤c) (hp : ∀ p∈ps,p.net.count≤c) :
    (tableBadCountNet m ps).net.count≤tableBadCountBound n ps.length c := by
  have hh:=sumNet_count (List.ofFn (fun t : Fin (n+1)=>tableLevelNet m ps t.val)) (by
    intro q hq
    obtain ⟨t,rfl⟩:=List.mem_ofFn.mp hq
    exact tableLevelNet_count m ps hm hp t.val)
  simpa only [tableBadCountNet,tableBadCountBound,List.length_ofFn] using hh

def tableFavorableCountBound (n f c : ℕ) : ℕ :=
  2*(c+n+(n*f)*totientStepBound n c)+2*tableBadCountBound n f c+214*n+15

lemma tableFavorableCountNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count≤c) (hp : ∀ p∈ps,p.net.count≤c) :
    (tableFavorableCountNet m ps).net.count≤tableFavorableCountBound n ps.length c := by
  have hphi:=primesPhiNet_count m ps hm hp
  have hbad:=tableBadCountNet_count m ps hm hp
  have hs:=natSubOn_count (primesPhiNet m ps) (tableBadCountNet m ps)
  change (natSubOn _ _).net.count≤_
  dsimp only [tableFavorableCountBound]
  omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedFavorableCount.lean =====
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

def retainedFavorableCount (t : ℕ) (m : BooleanNetwork (M.width t) n) :
    BooleanNetwork (M.width t) n := tableFavorableCountNet m (tableNets (M.fieldRows t))

lemma retainedFavorableCount_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (ho : Odd d)
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedFavorableCount t m).eval (M.encoded x t r))).toNat=
      dataFavorable (trueData P) d n := by
  rw [dataFavorable_correct (by omega) (by omega) hdiv]
  have hval:=tableNets_values hn (M.fieldRows t) (M.encoded x t r)
  rw [M.fieldRows_values] at hval
  have hh:=tableFavorableCountNet_value hn m (tableNets (M.fieldRows t)) (M.encoded x t r)
    (hm ▸ hd) (hm ▸ ho) (by
      intro p hp
      apply PhysicalTree.tableFactors_prime hc
      rw [←hval]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩) (by
      rw [hm,hval]
      exact PhysicalTree.tableFactors_cover hc hP hP0 (by omega) hdiv)
  simpa only [retainedFavorableCount,hm] using hh

lemma retainedFavorableCount_count {b : ℕ} (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (hm : m.net.count ≤ b) (hq : M.query.net.count ≤ b) (hr : PhysicalNode.resultBound n ≤ b) :
    (M.retainedFavorableCount t m).net.count ≤
      tableFavorableCountBound n (t*n) (3*b+220*n+50) := by
  have hp:=tableNets_counts (M.fieldRows t) (c:=b) (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  have hh:=tableFavorableCountNet_count m (tableNets (M.fieldRows t))
    (c:=3*b+220*n+50) (by omega) hp
  rwa [M.fieldRows_table_length] at hh
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedListFilter.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion.Expressions

def listRateCoin (n K : ℕ) : RatExpr (Fin 3) :=
  ((RatExpr.ofNat (v:=Fin 3) (.var 1)).div
    (RatExpr.ofNat (OrderTrial.Expressions.coveringPow (.var 0) n))).repeatedSuccess K

lemma listRateCoin_value (n K : ℕ) (v : Fin 3→ℕ) (hm : v 0≤2^n) :
    (listRateCoin n K).eval v=1-(1-(v 1:ℚ)/(2:ℚ)^(Nat.clog 2 (v 0)))^K := by
  rw [listRateCoin,RatExpr.repeatedSuccess_value,RatExpr.eval_div,RatExpr.eval_ofNat,
    RatExpr.eval_ofNat,OrderTrial.Expressions.coveringPow_correct]
  · simp only [NatExpr.eval,Nat.cast_pow,Nat.cast_ofNat]
  · exact hm
end Completion.Expressions

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

abbrev listCoinWidth (n : ℕ) := Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5)
abbrev listVarWidth (n : ℕ) := n+listCoinWidth n

def listFilterVars (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) :
    Fin 3→BooleanNetwork (M.width t) (listVarWidth n) := fun i=>
  if i=0 then m.comp (resizeWord n (listVarWidth n)) else
  if i=1 then (M.retainedFavorableCount t m).comp (resizeWord n (listVarWidth n)) else
  (raw.comp (Completion.retentionWires (PhysicalListSlots.ordinaryWidth n)
    (Completion.transitionWidth n) (2*n) (n*n^5))).comp (resizeWord (listCoinWidth n) (listVarWidth n))

def retainedListFilter (hn : 0<n) (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) (n*n^5)
    (Completion.Expressions.listRateCoin n (n^5)) (RatExpr.const (Completion.target n))
    (M.listFilterVars t m raw)
    (raw.comp (Completion.rareWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))) (.var 2)
    (M.retainedGoodList t m ((raw.comp (Completion.ordinaryWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))).comp (PhysicalListSlots.ordinaryNet n)))
    (M.retainedCanonicalList hn t m (raw.comp (Completion.guessWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))))

lemma listFilterVars_eval (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n))
    (x : Basis (M.width t)) (r : PhysicalListSlots.Result n)
    (hraw : raw.eval x=PhysicalListSlots.layout n r) :
    (bitsValue ((M.listFilterVars t m raw 0).eval x)).toNat=(bitsValue (m.eval x)).toNat ∧
    (bitsValue ((M.listFilterVars t m raw 1).eval x)).toNat=
      (bitsValue ((M.retainedFavorableCount t m).eval x)).toNat ∧
    (bitsValue ((M.listFilterVars t m raw 2).eval x)).toNat=(bitsValue r.2.2.2).toNat := by
  simp only [listFilterVars,Fin.reduceEq,ite_true,ite_false,eval_comp]
  simp only [resizeWord_toNat (show n ≤ listVarWidth n from Nat.le_add_right _ _),
    resizeWord_toNat (show listCoinWidth n ≤ listVarWidth n from Nat.le_add_left _ _),hraw]
  change _ ∧ _ ∧ (bitsValue ((Completion.retentionWires _ _ _ _).eval (Completion.layout _ _ _ _ r))).toNat=_
  rw [Completion.retentionWires_eval]
  exact ⟨True.intro,True.intro,rfl⟩

/-- Concrete local same-history test: the only inputs are the physical retained
words and the complete verified table, not an assumed success oracle. -/
theorem retainedListFilter_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n))
    (x : Basis c) (h : Trace n t) (r : PhysicalListSlots.Result n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (ho : Odd d)
    (hm : (bitsValue (m.eval (M.encoded x t h))).toNat=d)
    (hr : raw.eval (M.encoded x t h)=PhysicalListSlots.layout n r) :
    (M.retainedListFilter (by omega) t m raw).eval (M.encoded x t h) 0=true ↔
      dataListPassed (trueData P) (m.eval (M.encoded x t h)) (by omega) r := by
  have hv:=M.listFilterVars_eval t m raw (M.encoded x t h) r hr
  have hf:=M.retainedFavorableCount_exact hn t m x h hc hP hP0 hd hdiv ho hm
  unfold retainedListFilter dataListPassed
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval r
  · exact hv.2.2
  · rw [M.retainedGoodList_exact hn t m _ x h hc hP hP0 hd hdiv hm]
    erw [eval_comp,eval_comp,hr]
    change dataGoodList (trueData P) d n
      ((PhysicalListSlots.ordinaryNet n).eval ((Completion.ordinaryWires _ _ _ _).eval
        (Completion.layout _ _ _ _ r))) ↔ _
    rw [Completion.ordinaryWires_eval,PhysicalListSlots.ordinaryNet_eval,hm]
  · rw [M.retainedCanonicalList_exact hn t m _ x h hc hP hP0 hd hdiv hm]
    erw [eval_comp,hr]
    change dataCanonicalList (trueData P) d n _
      ((Completion.guessWires _ _ _ _).eval (Completion.layout _ _ _ _ r)) ↔ _
    rw [Completion.guessWires_eval,hm]
  · rw [Completion.Expressions.listRateCoin_value]
    · rw [hv.1,hv.2.1,hf,hm]
      rfl
    · rw [hv.1]
      exact (bitsValue (m.eval (M.encoded x t h))).isLt.le
  · exact RatExpr.eval_const _ _
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedListDummy.lean =====
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

def listDummyFilter (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) (n*n^5)
    (RatExpr.const 1) (RatExpr.const (Completion.target n)) (M.listFilterVars t m raw)
    (raw.comp (Completion.rareWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))) (.var 2)
    (constant true)
    (zeroWord (raw.comp (Completion.guessWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))))

lemma listDummyFilter_exact (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) (x : Basis (M.width t))
    (r : PhysicalListSlots.Result n) (hr : raw.eval x=PhysicalListSlots.layout n r) :
    (M.listDummyFilter t m raw).eval x 0=true ↔ UniversalSplit.dummyList r := by
  have hv:=M.listFilterVars_eval t m raw x r hr
  have hh : Completion.test (fun _=>True) (fun y=>y=natBasis _ 0) 1 (Completion.target n) r ↔
    UniversalSplit.dummyList r := Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) r
  refine Iff.trans ?_ hh
  unfold listDummyFilter
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval r
  · exact hv.2.2
  · simp only [eval_constant]
  · rw [zeroWord_value,eval_comp,hr]
    change (bitsValue ((Completion.guessWires _ _ _ _).eval
      (Completion.layout _ _ _ _ r))).toNat=0 ↔ _
    rw [Completion.guessWires_eval]
    exact basis_eq_natBasis (by positivity) _
  · exact RatExpr.eval_const _ _
  · exact RatExpr.eval_const _ _
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedTotient.lean =====
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

/-- The totient network reads only the actual retained rectangular table. -/
def retainedTotient (t : ℕ) (v : BooleanNetwork (M.width t) n) :
    BooleanNetwork (M.width t) n := tableTotient v (M.fieldRows t)

lemma retainedTotient_exact {N P m d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (v : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hm : 2 ≤ m) (hb : m < 2^n) (hdiv : m∣P) (hd0 : 0 < d) (hdt : d∣m.totient)
    (hv : (bitsValue (v.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedTotient t v).eval (M.encoded x t r))).toNat=d.totient := by
  apply tableTotient_exact hn v (M.fieldRows t) (M.encoded x t r)
  · rwa [M.fieldRows_values]
  · rwa [M.fieldRows_values]
  · exact hP0
  · exact hm
  · exact hb
  · exact hdiv
  · exact hd0
  · exact hdt
  · exact hv

lemma retainedTotient_count {b : ℕ} (t : ℕ) (v : BooleanNetwork (M.width t) n)
    (hv : v.net.count ≤ b) (hq : M.query.net.count ≤ b) (hr : PhysicalNode.resultBound n ≤ b) :
    (M.retainedTotient t v).net.count ≤ tableTotientBound n (t*n) b := by
  have hh:=tableTotient_count v (M.fieldRows t) hv (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  rwa [M.fieldRows_table_length] at hh

/-- The numerator of the exact order-trial success probability, with no
recovery of an exponent record and no factorization call at runtime. -/
def retainedOrderPhi (t : ℕ) (a m : BooleanNetwork (M.width t) n) :
    BooleanNetwork (M.width t) n := M.retainedTotient t (M.retainedOrder t a m)

lemma retainedOrderPhi_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedOrderPhi t a m).eval (M.encoded x t r))).toNat=(orderOf u).totient := by
  let : NeZero d := ⟨by omega⟩
  apply M.retainedTotient_exact hn t (M.retainedOrder t a m) x r hc hP hP0 hd
  · rw [←hm]; exact (bitsValue (m.eval (M.encoded x t r))).isLt
  · exact hdiv
  · exact orderOf_pos u
  · simpa only [ZMod.card_units_eq_totient] using (orderOf_dvd_card (x:=u))
  · exact M.retainedOrder_exact hn t a m x r hc hP hP0 hd hdiv u ha hm
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedOrderFilter.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace Completion.Expressions

def orderRateCoin (n K : ℕ) : RatExpr (Fin 3) :=
  ((RatExpr.ofNat (v:=Fin 3) (.var 1)).mul (OrderTrial.Expressions.lambdaE n (.var 0))).repeatedSuccess K
lemma orderRateCoin_value (n K : ℕ) (v : Fin 3→ℕ) (hd : v 0≤2^n) :
    (orderRateCoin n K).eval v=1-(1-(v 1:ℚ)*prescribedMass (v 0))^K := by
  rw [orderRateCoin,RatExpr.repeatedSuccess_value,RatExpr.eval_mul,RatExpr.eval_ofNat,
    OrderTrial.Expressions.lambdaE_correct]
  · rfl
  · exact hd
end Completion.Expressions
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)
abbrev orderVarWidth (n : ℕ) := n+OrderSlots.coinWidth n

def orderFilterVars (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) :
    Fin 3→BooleanNetwork (M.width t) (orderVarWidth n) := fun i=>
  if i=0 then (M.retainedOrder t a m).comp (resizeWord n (orderVarWidth n)) else
  if i=1 then (M.retainedOrderPhi t a m).comp (resizeWord n (orderVarWidth n)) else
  (raw.comp (Completion.retentionWires (OrderSlots.ordinaryWidth n)
    (Completion.transitionWidth n) (2*n) ((n+10)*n^5))).comp
      (resizeWord (OrderSlots.coinWidth n) (orderVarWidth n))

def orderActualFilter (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) ((n+10)*n^5)
    (Completion.Expressions.orderRateCoin n (n^5)) (RatExpr.const (Completion.target n))
    (M.orderFilterVars t a m raw)
    (raw.comp (Completion.rareWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5))) (.var 2)
    (equalOn (OrderSlots.orderResultNet a m (raw.comp (Completion.ordinaryWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))) (M.retainedOrder t a m))
    (equalOn (raw.comp (Completion.guessWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))
      ((M.retainedOrder t a m).comp (resizeWord n (Completion.transitionWidth n))))

def orderDummyFilter (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) ((n+10)*n^5)
    (RatExpr.const 1) (RatExpr.const (Completion.target n)) (M.orderFilterVars t a m raw)
    (raw.comp (Completion.rareWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5))) (.var 2)
    (constant true)
    (zeroWord (raw.comp (Completion.guessWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5))))

def retainedOrderFilter (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  ((OrderSlots.usableOn a m).band (M.orderActualFilter t a m raw)).bor
    ((OrderSlots.usableOn a m).bnot.band (M.orderDummyFilter t a m raw))

lemma orderFilterVars_eval (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
    (x : Basis (M.width t)) (r : OrderSlots.Result n)
    (hraw : raw.eval x=OrderSlots.layout n r) :
    (bitsValue ((M.orderFilterVars t a m raw 0).eval x)).toNat=
      (bitsValue ((M.retainedOrder t a m).eval x)).toNat ∧
    (bitsValue ((M.orderFilterVars t a m raw 1).eval x)).toNat=
      (bitsValue ((M.retainedOrderPhi t a m).eval x)).toNat ∧
    (bitsValue ((M.orderFilterVars t a m raw 2).eval x)).toNat=(bitsValue r.2.2.2).toNat := by
  simp only [orderFilterVars,Fin.reduceEq,ite_true,ite_false,eval_comp]
  rw [resizeWord_toNat (by dsimp only [orderVarWidth,OrderSlots.coinWidth]; omega),
    resizeWord_toNat (by dsimp only [orderVarWidth,OrderSlots.coinWidth]; omega),
    resizeWord_toNat (by dsimp only [orderVarWidth,OrderSlots.coinWidth]; omega),hraw]
  change _ ∧ _ ∧ (bitsValue ((Completion.retentionWires _ _ _ _).eval
    (Completion.layout _ _ _ _ (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)))).toNat=_
  rw [Completion.retentionWires_eval]
  exact ⟨rfl,rfl,rfl⟩

lemma orderActualFilter_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
    (x : Basis c) (h : Trace n t) (r : OrderSlots.Result n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t h))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t h))).toNat=d)
    (hr : raw.eval (M.encoded x t h)=OrderSlots.layout n r) :
    (M.orderActualFilter t a m raw).eval (M.encoded x t h) 0=true ↔
      Completion.test (fun y=>orderResult (OrderSlots.sampleExponent n) n
        (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h)) (n^5) y=orderOf u)
        (fun y=>y=natBasis _ (orderOf u)) (Completion.orderSuccess (orderOf u) (n^5)) (Completion.target n) r := by
  have hv:=M.orderFilterVars_eval t a m raw (M.encoded x t h) r hr
  have he:=M.retainedOrder_exact hn t a m x h hc hP hP0 hd hdiv u ha hm
  have hf:=M.retainedOrderPhi_exact hn t a m x h hc hP hP0 hd hdiv u ha hm
  unfold orderActualFilter
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
  · exact hv.2.2
  · rw [equalOn_value,he,OrderSlots.orderResultNet_value _ _ _ _ r.2.1]
    · rw [eval_comp,hr]
      exact Completion.ordinaryWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
    · rwa [hm]
  · have heq : ((M.retainedOrder t a m).comp (resizeWord n (Completion.transitionWidth n))).eval (M.encoded x t h)=
        natBasis (Completion.transitionWidth n) (orderOf u) := by
      rw [eval_comp,resizeWord_eq_natBasis,he]
    have hvv : (raw.comp (Completion.guessWires (OrderSlots.ordinaryWidth n)
        (Completion.transitionWidth n) (2*n) ((n+10)*n^5))).eval (M.encoded x t h)=r.2.2.1 := by
      rw [eval_comp,hr]
      exact Completion.guessWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
    rw [equalOn_value,hvv,heq]
    exact ⟨fun hh=>(bitsEquiv _).injective (BitVec.eq_of_toNat_eq hh),congrArg (fun z=>(bitsValue z).toNat)⟩
  · rw [Completion.Expressions.orderRateCoin_value]
    · rw [hv.1,hv.2.1,he,hf]
      rfl
    · rw [hv.1]
      exact (bitsValue ((M.retainedOrder t a m).eval (M.encoded x t h))).isLt.le
  · exact RatExpr.eval_const _ _

lemma orderDummyFilter_exact (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) (x : Basis (M.width t))
    (r : OrderSlots.Result n) (hr : raw.eval x=OrderSlots.layout n r) :
    (M.orderDummyFilter t a m raw).eval x 0=true ↔
      Completion.test (fun _=>True) (fun y=>y=natBasis _ 0) 1 (Completion.target n) r := by
  have hv:=M.orderFilterVars_eval t a m raw x r hr
  unfold orderDummyFilter
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
  · exact hv.2.2
  · simp only [eval_constant]
  · rw [zeroWord_value,eval_comp,hr]
    change (bitsValue ((Completion.guessWires _ _ _ _).eval
      (Completion.layout _ _ _ _ (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)))).toNat=0 ↔ _
    rw [Completion.guessWires_eval]
    exact basis_eq_natBasis (by positivity) _
  · exact RatExpr.eval_const _ _
  · exact RatExpr.eval_const _ _
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedOrderTest.lean =====
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

/-- Both actual usable slots and actual dummy slots, with the identical physical
coin and retained guessed string in their respective branches. -/
theorem retainedOrderFilter_exact {N P : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
    (x : Basis c) (h : Trace n t) (r : OrderSlots.Result n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ (bitsValue (m.eval (M.encoded x t h))).toNat)
    (hdiv : (bitsValue (m.eval (M.encoded x t h))).toNat∣P)
    (hr : raw.eval (M.encoded x t h)=OrderSlots.layout n r) :
    (M.retainedOrderFilter t a m raw).eval (M.encoded x t h) 0=true ↔
      dataOrderPassed (trueData P) (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h)) r := by
  classical
  rw [retainedOrderFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,OrderSlots.usableOn_value a m _ (by omega),
    dataOrderPassed,residueUsable_iff]
  by_cases hu : OrderSlots.Usable (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h))
  · simp only [hu,ite_eq_left,true_and,not_true_eq_false,false_and,or_false]
    rw [dataOrder_correct (by omega) hd hdiv hu.2.unit hu.2.unit_spec.symm,
      dataOrderSuccess_correct (by omega) hd hdiv hu.2.unit hu.2.unit_spec.symm]
    exact M.orderActualFilter_exact hn t a m raw x h r hc hP hP0 hd hdiv
      hu.2.unit hu.2.unit_spec.symm rfl hr
  · simp only [hu,ite_eq_right,false_and,not_false_eq_true,true_and,false_or]
    exact M.orderDummyFilter_exact t a m raw (M.encoded x t h) r hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedSplitFilter.lean =====
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

def splitModulus (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :=
  raw.comp (FixedSplit.modulusNet n)
def splitList (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :=
  (raw.comp (FixedSplit.launchWires n)).comp (FixedSplit.listWires n)
def splitBase (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) (i : Fin (n^5)) :=
  raw.comp (FixedSplit.actualBaseNet i)
def splitOrder (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) (i : Fin (n^5)) :=
  raw.comp (FixedSplit.actualOrderRawNet i)

def splitActualFilter (hn : 0<n) (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :
    BooleanNetwork (M.width t) 1 :=
  (M.retainedListFilter hn t (M.splitModulus t raw) (M.splitList t raw)).band
    (all (List.ofFn (fun i : Fin (n^5)=>M.retainedOrderFilter t (M.splitBase t raw i)
      (M.splitModulus t raw) (M.splitOrder t raw i))))

def splitDummyFilter (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :
    BooleanNetwork (M.width t) 1 :=
  (M.listDummyFilter t (M.splitModulus t raw) (M.splitList t raw)).band
    (all (List.ofFn (fun i : Fin (n^5)=>M.orderDummyFilter t (M.splitBase t raw i)
      (M.splitModulus t raw) (M.splitOrder t raw i))))

def retainedSplitFilter (hn : 0<n) (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :
    BooleanNetwork (M.width t) 1 :=
  ((UniversalSplit.hardOn (M.splitModulus t raw)).band (M.splitActualFilter hn t raw)).bor
    ((UniversalSplit.hardOn (M.splitModulus t raw)).bnot.band (M.splitDummyFilter t raw))

lemma splitModulus_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.splitModulus t raw).eval x=q := by
  rw [splitModulus,eval_comp,hr,FixedSplit.modulusNet_eval]
lemma splitList_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.splitList t raw).eval x=PhysicalListSlots.layout n r.1 := by
  rw [splitList,eval_comp,eval_comp,hr,FixedSplit.launchWires_eval,FixedSplit.listWires_eval]
lemma splitBase_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) (i : Fin (n^5)) :
    (M.splitBase t raw i).eval x=FixedSplit.bases r.1 i := by
  rw [splitBase,eval_comp,hr,FixedSplit.actualBaseNet_eval]
lemma splitOrder_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) (i : Fin (n^5)) :
    (M.splitOrder t raw i).eval x=OrderSlots.layout n (r.2 i) := by
  rw [splitOrder,eval_comp,hr,FixedSplit.actualOrderRawNet_eval]

lemma splitDummyFilter_exact (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.splitDummyFilter t raw).eval x 0=true ↔ UniversalSplit.dummy r := by
  rw [splitDummyFilter,eval_band,Bool.and_eq_true,
    M.listDummyFilter_exact t _ _ x r.1 (M.splitList_eval t raw x q r hr),all_eval]
  simp only [List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  rw [M.orderDummyFilter_exact t _ _ _ x (r.2 i) (M.splitOrder_eval t raw x q r hr i)]
  exact Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) (r.2 i)

/-- The hard/ordinary/rare/dummy selection is on the actual retained split's
modulus and coin strings. The table is the same final retained complete log. -/
theorem retainedSplitFilter_exact {N P : ℕ} (hn : 128≤n) (t : ℕ)
    (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis c) (h : Trace n t) (q : Basis n) (r : UniversalSplit.Raw n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hdiv : UniversalSplit.Hard (bitsValue q).toNat → (bitsValue q).toNat∣P)
    (hr : raw.eval (M.encoded x t h)=FixedSplit.encoding q r) :
    (M.retainedSplitFilter (by omega) t raw).eval (M.encoded x t h) 0=true ↔
      dataSplitPassed (trueData P) q (by omega) r := by
  classical
  rw [retainedSplitFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,UniversalSplit.hardOn_value hn,
    M.splitModulus_eval t raw _ q r hr,dataSplitPassed]
  by_cases hh : UniversalSplit.Hard (bitsValue q).toNat
  · simp only [hh,ite_eq_left,true_and,not_true_eq_false,false_and,or_false]
    rw [splitActualFilter,eval_band,Bool.and_eq_true,
      M.retainedListFilter_exact (by omega) t _ _ x h r.1 hc hP hP0 hh.1 (hdiv hh) hh.2.2.1
        (by rw [M.splitModulus_eval t raw _ q r hr]) (M.splitList_eval t raw _ q r hr),
      M.splitModulus_eval t raw _ q r hr,all_eval]
    simp only [List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    rw [M.retainedOrderFilter_exact (by omega) t _ _ _ x h (r.2 i) hc hP hP0
      (by rw [M.splitModulus_eval t raw _ q r hr];exact hh.1)
      (by rw [M.splitModulus_eval t raw _ q r hr];exact hdiv hh)
      (M.splitOrder_eval t raw _ q r hr i),M.splitBase_eval t raw _ q r hr,
      M.splitModulus_eval t raw _ q r hr]
  · simp only [hh,ite_eq_right,false_and,not_false_eq_true,true_and,false_or]
    exact M.splitDummyFilter_exact t raw _ q r hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedSplitPass.lean =====
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

lemma retainedSplitFilter_nonhard (hn : 128≤n) (t : ℕ)
    (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hh : ¬UniversalSplit.Hard (bitsValue q).toNat)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.retainedSplitFilter (by omega) t raw).eval x 0=true ↔ UniversalSplit.passed q r := by
  classical
  rw [retainedSplitFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,UniversalSplit.hardOn_value hn,
    M.splitModulus_eval t raw x q r hr]
  simp only [hh,false_and,not_false_eq_true,true_and,false_or]
  rw [UniversalSplit.passed,dite_eq_right hh]
  exact M.splitDummyFilter_exact t raw x q r hr

lemma retainedSplitFilter_passed {N P : ℕ} (hn : 128≤n) (t : ℕ)
    (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis c) (h : Trace n t) (q : Basis n) (r : UniversalSplit.Raw n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hdiv : UniversalSplit.Hard (bitsValue q).toNat → (bitsValue q).toNat∣P)
    (hr : raw.eval (M.encoded x t h)=FixedSplit.encoding q r) :
    (M.retainedSplitFilter (by omega) t raw).eval (M.encoded x t h) 0=true ↔
      UniversalSplit.passed q r := by
  classical
  by_cases hh : UniversalSplit.Hard (bitsValue q).toNat
  · rw [M.retainedSplitFilter_exact hn t raw x h q r hc hP hP0 hdiv hr]
    exact dataSplitPassed_correct (by omega) q hh.1 (hdiv hh) (by omega) r
  · exact M.retainedSplitFilter_nonhard hn t raw _ q r hh hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI
