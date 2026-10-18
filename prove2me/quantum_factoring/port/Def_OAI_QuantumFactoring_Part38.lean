/-
Exact quantum factoring development (port of OpenAI's formalization), part 38 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: RationalEmission.lean, CompletionPredicateEmission.lean, RetainedListFilterEmission.lean, RetainedOrderFilterEmission.lean, RetainedSplitFilterEmission.lean, RetainedNodeEmission.lean, RetainedTreeEmission.lean, QuarterRetentionEmission.lean, FinalUniformity.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part37

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RationalEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool}
lemma ratAdd {f g : α→ℚ} (hf : Emits ea ratCode f) (hg : Emits ea ratCode g) :
    Emits ea ratCode (fun x=>f x+g x):=(ofProcedure Procedure.ratAdd).comp (hf.pair hg)
lemma ratMul {f g : α→ℚ} (hf : Emits ea ratCode f) (hg : Emits ea ratCode g) :
    Emits ea ratCode (fun x=>f x*g x):=(ofProcedure Procedure.ratMul).comp (hf.pair hg)
lemma ratDiv {f g : α→ℚ} (hf : Emits ea ratCode f) (hg : Emits ea ratCode g) :
    Emits ea ratCode (fun x=>f x/g x):=(ofProcedure Procedure.ratDiv).comp (hf.pair hg)
lemma ratSub {f g : α→ℚ} (hf : Emits ea ratCode f) (hg : Emits ea ratCode g) :
    Emits ea ratCode (fun x=>f x-g x):=(ofProcedure Procedure.ratSub).comp (hf.pair hg)
lemma ratPow {f : α→ℚ} {k : α→ℕ} (hf : Emits ea ratCode f) (hk : Emits ea unaryCode k) :
    Emits ea ratCode (fun x=>(f x)^(k x)):=(ofProcedure Procedure.ratPow).comp (hk.pair hf)
lemma ratFloor {f : α→ℚ} (hf : Emits ea ratCode f) :
    Emits ea intCode (fun x=>⌊f x⌋):=(ofProcedure Procedure.ratFloor).comp hf
lemma intRat {f : α→ℤ} (hf : Emits ea intCode f) :
    Emits ea ratCode (fun x=>(f x:ℚ)):=(ofProcedure Procedure.intToRat).comp hf
lemma completionCoeff {E : α→ℕ} {z A : α→ℚ} (hE : Emits ea unaryCode E)
    (hz : Emits ea ratCode z) (hA : Emits ea ratCode A) :
    Emits ea ratCode (fun x=>Exactness.completionCoeff (E x) (z x) (A x)):=by
  have htwo:=(const ea ratCode 2).ratPow hE
  exact ((htwo.ratMul (hz.ratDiv hA)).ratFloor.intRat).ratDiv htwo
lemma knownProbability {n : α→ℕ} (hn : Emits ea unaryCode n) :
    Emits ea ratCode (fun x=>Exactness.knownProbability (n x)):=by
  exact ((const ea ratCode 1).ratSub ((const ea ratCode 1).ratDiv
    ((const ea ratCode 2).ratPow hn))).ratPow (hn.unaryPow 10)
lemma quarterRetention {n : α→ℕ} (hn : Emits ea unaryCode n) :
    Emits ea ratCode (fun x=>Quarter.retention (n x)):=by
  exact completionCoeff ((hn.unaryMul hn).unaryAdd (const ea unaryCode 2))
    (const ea ratCode (1/2)) (knownProbability hn)
lemma quarterGuessRetention {n : α→ℕ} (hn : Emits ea unaryCode n) :
    Emits ea ratCode (fun x=>Quarter.guessRetention (n x)):=by
  have ht:=(const ea ratCode 2).ratPow ((hn.unaryMul hn).unaryAdd (const ea unaryCode 1))
  exact ht.ratMul ((const ea ratCode (1/4)).ratSub
    (((knownProbability hn).ratMul (quarterRetention hn)).ratDiv (const ea ratCode 2)))
end ExactQuantumFactoring.BitStackProgram.Emits

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CompletionPredicateEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool} {W t : α→ℕ}
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
lemma ordinaryMass {s : α→RatExpr v} (ht : BitStackProgram.Emits ea unaryCode t) (hs : REm s) :
    REm (fun x=>Completion.Expressions.ordinaryMass (t x) (s x)):=
  rMul (rConst ((const _ _ 1).ratSub ((const _ _ 1).ratDiv ((const _ _ 2).ratPow ht)))) hs
lemma completionCoefficient {s z : α→RatExpr v} (hW : BitStackProgram.Emits ea unaryCode W)
    (ht : BitStackProgram.Emits ea unaryCode t) (hs : REm s) (hz : REm z) :
    REm (fun x=>Completion.Expressions.coefficient (W x) (t x) (s x) (z x)):=by
  have h2:=rConst ((const _ _ 2).ratPow ((hW.unaryAdd ht).unaryAdd (const _ _ 2))) (ev:=ev)
  exact rDiv (rOfInt (rFloor (rMul h2 (rDiv hz (ordinaryMass ht hs))))) h2
lemma completionGuess {s z : α→RatExpr v} (hW : BitStackProgram.Emits ea unaryCode W)
    (ht : BitStackProgram.Emits ea unaryCode t) (hs : REm s) (hz : REm z) :
    REm (fun x=>Completion.Expressions.guess (W x) (t x) (s x) (z x)):=
  rDiv (rMul (rSub hz (rMul (completionCoefficient hW ht hs hz) (ordinaryMass ht hs)))
    (rConst ((const _ _ 2).ratPow hW))) (rConst ((const _ _ 1).ratDiv ((const _ _ 2).ratPow ht)))
end ExactQuantumFactoring.NetworkEmission.Emits
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α v : Type} {ea : α→List Bool} {k b W t d : α→ℕ}
lemma predicateFilter {K : ℕ} (en : Fin K ≃ v) {s z : α→RatExpr v} {coin : α→NatExpr v}
    {vars : ∀x,v→BooleanNetwork (k x) (b x)} {branch : ∀x,BooleanNetwork (k x) (t x)}
    {good guess : ∀x,BooleanNetwork (k x) 1}
    (hk : Emits ea unaryCode k) (hb : Emits ea unaryCode b) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d)
    (hs : Emits ea (ratExprCode (fun i:v=>(en.symm i).val.bits)) s)
    (hz : Emits ea (ratExprCode (fun i:v=>(en.symm i).val.bits)) z)
    (hc : Emits ea (exprCode (fun i:v=>(en.symm i).val.bits)) coin)
    (hv : ∀i,NetEmits ea (fun x=>vars x i)) (hr : NetEmits ea branch)
    (hg : NetEmits ea good) (hgg : NetEmits ea guess) :
    NetEmits ea (fun x=>Completion.predicateFilter (W:=W x) (d x) (s x) (z x) (vars x) (branch x) (coin x) (good x) (guess x)):=by
  have hrare:=zeroWord hk ht hr
  have ho:=retention en hk hb (coinBits hW ht hd) (Emits.completionCoefficient hW ht hs hz) hc hv
  have hguess:=retention en hk hb (coinBits hW ht hd) (Emits.completionGuess hW ht hs hz) hc hv
  exact (hrare.bnot.band (hg.band ho)).bor (hrare.band (hgg.band hguess))
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedListFilterEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma localTarget (hn : Emits ea unaryCode n) : Emits ea ratCode (fun x=>Completion.target (n x)):=
  (const _ _ 1).ratSub ((const _ _ 1).ratDiv ((const _ _ 2).ratPow hn))
lemma listRate (hn : Emits ea unaryCode n) : Emits ea (ratExprCode (fun i:Fin 3=>i.val.bits))
    (fun x=>Completion.Expressions.listRateCoin (n x) (n x^5)):=by
  exact NetworkEmission.Emits.repeatedSuccess
    (NetworkEmission.Emits.rDiv (NetworkEmission.Emits.rOfNat (const _ _ (NatExpr.var (1:Fin 3))))
      (NetworkEmission.Emits.rOfNat (NetworkEmission.Emits.coveringPow (const _ _ (NatExpr.var (0:Fin 3))) hn))) (hn.unaryPow 5)
lemma listVarWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>NodeMachine.listVarWidth (n x)):=
  hn.unaryAdd (coinBits (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5)))
lemma listFilterVars {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (PhysicalListSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hm : NetEmits ea m) (hr : NetEmits ea raw) (i : Fin 3) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).listFilterVars (t x) (m x) (raw x) i):=by
  have hq:=PhysicalListEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=hn.unaryMul (hn.unaryPow 5)
  fin_cases i
  · exact hm.comp (resize hn (listVarWidth hn))
  · exact (retainedFavorableCount hn ht hm).comp (resize hn (listVarWidth hn))
  · exact (hr.comp (retentionWires hq hW h2 hd)).comp (resize (coinBits hW h2 hd) (listVarWidth hn))
lemma retainedListFilter {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (PhysicalListSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x)
    (hm : NetEmits ea m) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedListFilter (hn0 x) (t x) (m x) (raw x)):=by
  have hq:=PhysicalListEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=hn.unaryMul (hn.unaryPow 5)
  exact predicateFilter (Equiv.refl (Fin 3)) (machineWidth hn ht) (listVarWidth hn) hW h2 hd
    (listRate hn) (NetworkEmission.Emits.rConst (localTarget hn)) (const _ _ (NatExpr.var (2:Fin 3)))
    (listFilterVars hn ht hm hr) (hr.comp (rareWires hq hW h2 hd))
    (retainedGoodList hn ht hm ((hr.comp (ordinaryWires hq hW h2 hd)).comp (PhysicalListEmission.ordinary hn)))
    (retainedCanonicalList hn ht hn0 hm (hr.comp (guessWires hq hW h2 hd)))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedOrderFilterEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma orderRate (hn : Emits ea unaryCode n) : Emits ea (ratExprCode (fun i:Fin 3=>i.val.bits))
    (fun x=>Completion.Expressions.orderRateCoin (n x) (n x^5)):=
  NetworkEmission.Emits.repeatedSuccess
    (NetworkEmission.Emits.rMul (NetworkEmission.Emits.rOfNat (const _ _ (NatExpr.var (1:Fin 3))))
      (NetworkEmission.Emits.lambdaExpr hn (const _ _ (NatExpr.var (0:Fin 3))))) (hn.unaryPow 5)
lemma orderVarWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>NodeMachine.orderVarWidth (n x)):=
  hn.unaryAdd (coinBits (transitionWidth hn) ((const _ _ 2).unaryMul hn) ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5)))
lemma orderFilterVars {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (OrderSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea raw) (i : Fin 3) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).orderFilterVars (t x) (a x) (m x) (raw x) i):=by
  have hq:=PhysicalOrderEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=(hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5)
  fin_cases i
  · exact (retainedOrder hn ht ha hm).comp (resize hn (orderVarWidth hn))
  · exact (retainedOrderPhi hn ht ha hm).comp (resize hn (orderVarWidth hn))
  · exact (hr.comp (retentionWires hq hW h2 hd)).comp (resize (coinBits hW h2 hd) (orderVarWidth hn))
lemma orderActualFilter {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (OrderSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).orderActualFilter (t x) (a x) (m x) (raw x)):=by
  have hq:=PhysicalOrderEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=(hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5)
  have ho:=retainedOrder hn ht ha hm
  exact predicateFilter (Equiv.refl (Fin 3)) (machineWidth hn ht) (orderVarWidth hn) hW h2 hd
    (orderRate hn) (NetworkEmission.Emits.rConst (localTarget hn)) (const _ _ (NatExpr.var (2:Fin 3)))
    (orderFilterVars hn ht ha hm hr) (hr.comp (rareWires hq hW h2 hd))
    ((PhysicalOrderEmission.result (machineWidth hn ht) hn ha hm (hr.comp (ordinaryWires hq hW h2 hd))).equalOn ho hn)
    ((hr.comp (guessWires hq hW h2 hd)).equalOn (ho.comp (resize hn hW)) hW)
lemma orderDummyFilter {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (OrderSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).orderDummyFilter (t x) (a x) (m x) (raw x)):=by
  have hq:=PhysicalOrderEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=(hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5)
  exact predicateFilter (Equiv.refl (Fin 3)) (machineWidth hn ht) (orderVarWidth hn) hW h2 hd
    (const _ _ (RatExpr.const (v:=Fin 3) 1)) (NetworkEmission.Emits.rConst (localTarget hn)) (const _ _ (NatExpr.var (2:Fin 3)))
    (orderFilterVars hn ht ha hm hr) (hr.comp (rareWires hq hW h2 hd)) (constant (machineWidth hn ht) (const _ _ true))
    (zeroWord (machineWidth hn ht) hW (hr.comp (guessWires hq hW h2 hd)))
lemma retainedOrderFilter {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (OrderSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedOrderFilter (t x) (a x) (m x) (raw x)):=by
  have hu:=PhysicalOrderEmission.usable (machineWidth hn ht) hn ha hm
  exact (hu.band (orderActualFilter hn ht ha hm hr)).bor (hu.bnot.band (orderDummyFilter hn ht ha hm hr))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedSplitFilterEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma hardOn {k w : α→ℕ} {a : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>UniversalSplit.hardOn (a x)):=
  (((wordConst hk hw (const _ _ 2)).wordLe ha hw).band (ha.comp (primeWord hw)).bnot).band
    ((evenOn hk hw ha).bnot.band (((ha.comp (resize hw (hw.unaryMul hw).unarySucc)).comp (perfectPower hw)).bnot))
lemma listDummyFilter {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (PhysicalListSlots.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hm : NetEmits ea m) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).listDummyFilter (t x) (m x) (raw x)):=by
  have hq:=PhysicalListEmission.ordinaryWidth hn
  have hW:=transitionWidth hn
  have h2:=(const _ _ 2).unaryMul hn
  have hd:=hn.unaryMul (hn.unaryPow 5)
  exact predicateFilter (Equiv.refl (Fin 3)) (machineWidth hn ht) (listVarWidth hn) hW h2 hd
    (const _ _ (RatExpr.const (v:=Fin 3) 1)) (NetworkEmission.Emits.rConst (localTarget hn)) (const _ _ (NatExpr.var (2:Fin 3)))
    (listFilterVars hn ht hm hr) (hr.comp (rareWires hq hW h2 hd)) (constant (machineWidth hn ht) (const _ _ true))
    (zeroWord (machineWidth hn ht) hW (hr.comp (guessWires hq hW h2 hd)))
lemma splitActualFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (FixedSplit.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).splitActualFilter (hn0 x) (t x) (raw x)):=by
  have hh:=retainedListFilter hn ht hn0 (hr.comp (PhysicalSplitEmission.modulus hn))
    ((hr.comp (PhysicalSplitEmission.launchWires hn)).comp (PhysicalSplitEmission.listWires hn))
  apply hh.band
  apply allOfFn (machineWidth hn ht) (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a^5)=>(x.2.val,x.1))
  have hn':=hn.comp hx.snd
  have hr':=hr.compInput hx.snd
  exact retainedOrderFilter hn' (ht.comp hx.snd)
    (hr'.comp (PhysicalSplitEmission.actualBase hn' (fun x=>x.2) hx.fst.unaryNat))
    (hr'.comp (PhysicalSplitEmission.modulus hn'))
    (hr'.comp (PhysicalSplitEmission.actualOrderRaw hn' (fun x=>x.2) hx.fst.unaryNat))
lemma splitDummyFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (FixedSplit.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).splitDummyFilter (t x) (raw x)):=by
  have hh:=listDummyFilter hn ht (hr.comp (PhysicalSplitEmission.modulus hn))
    ((hr.comp (PhysicalSplitEmission.launchWires hn)).comp (PhysicalSplitEmission.listWires hn))
  apply hh.band
  apply allOfFn (machineWidth hn ht) (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a^5)=>(x.2.val,x.1))
  have hn':=hn.comp hx.snd
  have hr':=hr.compInput hx.snd
  exact orderDummyFilter hn' (ht.comp hx.snd)
    (hr'.comp (PhysicalSplitEmission.actualBase hn' (fun x=>x.2) hx.fst.unaryNat))
    (hr'.comp (PhysicalSplitEmission.modulus hn'))
    (hr'.comp (PhysicalSplitEmission.actualOrderRaw hn' (fun x=>x.2) hx.fst.unaryNat))
lemma retainedSplitFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (FixedSplit.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedSplitFilter (hn0 x) (t x) (raw x)):=by
  have hh:=hardOn (machineWidth hn ht) hn (hr.comp (PhysicalSplitEmission.modulus hn))
  exact (hh.band (splitActualFilter hn ht hn0 hr)).bor (hh.bnot.band (splitDummyFilter hn ht hr))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedNodeEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalNodeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n s t : α→ℕ}
lemma previous (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) :
    NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).previousNet (t x)):=
  (firstSelect (((width hn hs ht).unaryAdd (PhysicalSplitEmission.width hn)).unaryAdd (initWork hn hs))
    (configWidth hn hs) (updateWork hn hs)).comp (firstSelect (width hn hs ht) (PhysicalSplitEmission.width hn) (initWork hn hs))
lemma lastSplit (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) :
    NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).lastSplitNet (t x)):=
  (firstSelect (((width hn hs ht).unaryAdd (PhysicalSplitEmission.width hn)).unaryAdd (initWork hn hs))
    (configWidth hn hs) (updateWork hn hs)).comp (targetSelect (width hn hs ht) (PhysicalSplitEmission.width hn) (initWork hn hs))
end ExactQuantumFactoring.PhysicalNodeEmission
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t s : α→ℕ}
lemma nodePrefix_eq {n t : ℕ} (hn : 0<n) (s : ℕ) (v : BooleanNetwork ((PhysicalTree.machine n).width t) ((PhysicalNode.machine n (2*n)).width s)) :
    filterPrefix (fun s=>(PhysicalNode.machine n (2*n)).previousNet s)
      (fun s v=>(PhysicalTree.machine n).retainedSplitFilter hn t (v.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s))) s v=
      (PhysicalTree.machine n).nodePrefixFilter hn t s v:=by
  induction s with
  | zero=>rfl
  | succ s ih=>dsimp only [filterPrefix,NodeMachine.nodePrefixFilter];rw [ih]
lemma nodePrefixFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) ((PhysicalNode.machine (n x) (2*n x)).width (s x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hs : Emits ea unaryCode s) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).nodePrefixFilter (hn0 x) (t x) (s x) (raw x)):=by
  have h2:=(const _ _ 2).unaryMul hn
  have hW:=PhysicalNodeEmission.width hn h2 hs
  have hep : NetEmits (prodCode ea unaryCode) (fun x=>(PhysicalNode.machine (n x.1) (2*n x.1)).previousNet x.2):=by
    have hx:=BitStackProgram.Emits.id (prodCode ea unaryCode)
    exact PhysicalNodeEmission.previous (hn.comp hx.fst) (h2.comp hx.fst) hx.snd
  have hec : NetEmits (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalNode.machine (n a) (2*n a)).width (j+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2)))
      (fun x=>(PhysicalTree.machine (n x.1)).retainedSplitFilter (hn0 x.1) (t x.1)
        (x.2.2.comp ((PhysicalNode.machine (n x.1) (2*n x.1)).lastSplitNet x.2.1))):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalNode.machine (n a) (2*n a)).width (j+1))=>(x.1,(x.2.1,erasePack x.2.2)))
    exact retainedSplitFilter (hn.comp hx.fst) (ht.comp hx.fst) (fun x=>hn0 x.1)
      ((ofCanonical hx.snd.snd).comp (PhysicalNodeEmission.lastSplit (hn.comp hx.fst) (h2.comp hx.fst) hx.snd.fst))
  have h:=filterPrefixEmits (fun x j=>(PhysicalNode.machine (n x) (2*n x)).previousNet j)
    (fun x j v=>(PhysicalTree.machine (n x)).retainedSplitFilter (hn0 x) (t x) (v.comp ((PhysicalNode.machine (n x) (2*n x)).lastSplitNet j)))
    (fun x j=>SplitMachine.previousNet_count _ j)
    (W:=fun x=>(PhysicalNode.machine (n x) (2*n x)).width (s x)) (fun x j hj=>by
      rw [SplitMachine.width_eq,SplitMachine.width_eq];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _)
    raw hs (machineWidth hn ht) hr hW.unaryPoly hep hec
  exact h.congr (fun x=>nodePrefix_eq (hn0 x) (s x) (raw x))
lemma retainedNodeFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (NodeKernel.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedNodeFilter (hn0 x) (t x) (raw x)):=
  nodePrefixFilter hn ht ((const _ _ 2).unaryMul hn) hn0 hr
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedTreeEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t s : α→ℕ}
lemma treePrefix_eq {n t : ℕ} (hn : 0<n) (s : ℕ) (v : BooleanNetwork ((PhysicalTree.machine n).width t) ((PhysicalTree.machine n).width s)) :
    filterPrefix (fun s=>(PhysicalTree.machine n).previousNet s)
      (fun s v=>(PhysicalTree.machine n).retainedNodeFilter hn t (v.comp ((PhysicalTree.machine n).lastNodeNet s))) s v=
      (PhysicalTree.machine n).treePrefixFilter hn t s v:=by
  induction s with
  | zero=>rfl
  | succ s ih=>dsimp only [filterPrefix,NodeMachine.treePrefixFilter];rw [ih]
lemma treePrefixFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) ((PhysicalTree.machine (n x)).width (s x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hs : Emits ea unaryCode s) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).treePrefixFilter (hn0 x) (t x) (s x) (raw x)):=by
  have hep : NetEmits (prodCode ea unaryCode) (fun x=>(PhysicalTree.machine (n x.1)).previousNet x.2):=by
    have hx:=BitStackProgram.Emits.id (prodCode ea unaryCode)
    exact previous (hn.comp hx.fst) hx.snd
  have hec : NetEmits (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalTree.machine (n a)).width (j+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2)))
      (fun x=>(PhysicalTree.machine (n x.1)).retainedNodeFilter (hn0 x.1) (t x.1)
        (x.2.2.comp ((PhysicalTree.machine (n x.1)).lastNodeNet x.2.1))):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalTree.machine (n a)).width (j+1))=>(x.1,(x.2.1,erasePack x.2.2)))
    exact retainedNodeFilter (hn.comp hx.fst) (ht.comp hx.fst) (fun x=>hn0 x.1)
      ((ofCanonical hx.snd.snd).comp (lastNode (hn.comp hx.fst) hx.snd.fst))
  have h:=filterPrefixEmits (fun x j=>(PhysicalTree.machine (n x)).previousNet j)
    (fun x j v=>(PhysicalTree.machine (n x)).retainedNodeFilter (hn0 x) (t x) (v.comp ((PhysicalTree.machine (n x)).lastNodeNet j)))
    (fun x j=>NodeMachine.previousNet_count _ j)
    (W:=fun x=>(PhysicalTree.machine (n x)).width (s x)) (fun x j hj=>by
      rw [NodeMachine.width_eq,NodeMachine.width_eq];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _)
    raw hs (machineWidth hn ht) hr (machineWidth hn hs).unaryPoly hep hec
  exact h.congr (fun x=>treePrefix_eq (hn0 x) (s x) (raw x))
lemma accepted (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).acceptedNet (hn0 x) (t x)):=
  (verified hn ht).band (treePrefixFilter hn ht ht hn0 (identity (machineWidth hn ht)))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/QuarterRetentionEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
def unitEquiv : Fin 1 ≃ Unit where
  toFun := fun _=>()
  invFun := fun _=>0
  left_inv i:=by exact Subsingleton.elim ..
  right_inv i:=by exact Subsingleton.elim ..
lemma quarterD (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>Quarter.D (n x)):=
  coinBits (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma keepGeneric {k d : α→ℕ} {coin : ∀x,BooleanNetwork (k x) (d x)} {p : α→ℚ}
    (hk : Emits ea unaryCode k) (hd : Emits ea unaryCode d) (hp : Emits ea ratCode p)
    (hc : NetEmits ea coin) :
    NetEmits ea (fun x=>retentionNet (d x) (.const (p x)) (.var ()) (fun _:Unit=>coin x)):=
by
  apply retention (v:=Unit) unitEquiv (fs:=fun x (_:Unit)=>coin x)
    (p:=fun x=>RatExpr.const (p x)) (coin:=fun _=>NatExpr.var ()) hk hd hd
  · exact NetworkEmission.Emits.rConst hp
  · exact const _ _ (NatExpr.var ())
  · intro i;exact hc
lemma quarterKeep {p : α→ℚ} (hn : Emits ea unaryCode n) (hp : Emits ea ratCode p) :
    NetEmits ea (fun x=>PhysicalTree.quarterKeep (n x) (p x)):=by
  exact keepGeneric (quarterWidth hn) (quarterD hn) hp (quarterCoin hn)
lemma quarterOrdKeep (hn : Emits ea unaryCode n) :
    NetEmits ea (fun x=>PhysicalTree.quarterKeep (n x) (Quarter.retention (n x))):=
  quarterKeep hn (quarterRetention hn)
lemma quarterGuessKeep (hn : Emits ea unaryCode n) :
    NetEmits ea (fun x=>PhysicalTree.quarterKeep (n x) (Quarter.guessRetention (n x))):=
  quarterKeep hn (quarterGuessRetention hn)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FinalUniformity.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma paddedFlag (hn : Emits ea unaryCode n) (hn0 : ∀x,0<n x) :
    NetEmits ea (fun x=>PhysicalTree.paddedFlag (n x) (hn0 x)):=
  ((paddedHistory hn).comp (accepted hn (steps hn) hn0)).band ((paddedPad hn).comp (padFlag hn))
lemma quarterFlag (hn : Emits ea unaryCode n) (hn0 : ∀x,0<n x) :
    NetEmits ea (fun x=>PhysicalTree.quarterFlag (n x) (hn0 x)):=
  ((quarterRare hn).bnot.band (((quarterOrd hn).comp (paddedFlag hn hn0)).band (quarterOrdKeep hn))).bor
    ((quarterRare hn).band ((quarterGuessFlag hn).band (quarterGuessKeep hn)))
end ExactQuantumFactoring.PhysicalTreeEmission
namespace ExactQuantumFactoring.PhysicalTree
open BitStackProgram BitStackProgram.Emits
/-- A single finite Boolean-stack TM2 generates the literal family in polynomial
unary-input time, including all compile-time expression and primality decisions. -/
theorem finalCircuit_uniform : Uniform finalCircuit:=by
  have hn : Emits unaryCode unaryCode paddedLength:=
    (const unaryCode unaryCode 128).unaryMax (BitStackProgram.Emits.id unaryCode)
  exact UniformResources.PhysicalTree.uniform_of_quarter_emitters_clean
    (PhysicalTreeEmission.quarterWidth hn) (PhysicalTreeEmission.quarterProgram hn)
    (PhysicalTreeEmission.quarterFlag hn paddedLength_pos) (PhysicalTreeEmission.quarterOutput hn)
end ExactQuantumFactoring.PhysicalTree

end



end OAI
