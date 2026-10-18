/-
Exact quantum factoring development (port of OpenAI's formalization), part 25 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: SplitDecoderPolynomial.lean, ActualDivisorPolynomial.lean, NodeStateBounds.lean, PrimalityPolynomial.lean, NodePreparationPolynomial.lean, TreePreparationPolynomial.lean, RetainedNetworkPolynomial.lean, RetainedNetworkAt.lean, RetainedFavorablePolynomial.lean, CompletionFilterPolynomial.lean, RetainedFilterPolynomial.lean, RetainedSplitPolynomial.lean, RetainedPrefixPolynomial.lean, RetainedQuarterPolynomial.lean, FinalPolynomialResources.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part24

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SplitDecoderPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace BitArithmetic
lemma firstProperNet_count {k w c : ℕ} (m : BooleanNetwork k w)
    (ds : List (BooleanNetwork k w)) (h : ∀d∈ds,d.net.count≤c) :
    (firstProperNet m ds).net.count≤w+ds.length*(2*m.net.count+4*c+216*w*w+257*w+45) := by
  induction ds with
  | nil=>simp only [firstProperNet,wordConstant_count,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons d ds ih=>
    have hd:=h d (by simp)
    have ht:=ih (fun e he=>h e (by simp [he]))
    have hp:=properOn_count m d
    simp only [firstProperNet,wordMux_count,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
end BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a w e : α→ℕ}
lemma addNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.add (w x)) :=
  of_le (((PolyAt.const len 86).mul hw).add (PolyAt.const len 6)) fun x=>add_count (w x)
lemma subNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.sub (w x)) :=
  of_le (((PolyAt.const len 158).mul hw).add (PolyAt.const len 6)) fun x=>sub_count (w x)
lemma divNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.div (w x)) :=
  of_le (((((PolyAt.const len 216).mul hw).mul hw).add ((PolyAt.const len 56).mul hw)).add
    (PolyAt.const len 6)) fun x=>div_count (w x)
lemma modNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.mod (w x)) :=
  of_le (((((PolyAt.const len 216).mul hw).mul hw).add ((PolyAt.const len 56).mul hw)).add
    (PolyAt.const len 6)) fun x=>mod_count (w x)
lemma properOn {m d : ∀x,BooleanNetwork (a x) (w x)}
    (hm : NetworkAt len m) (hd : NetworkAt len d) (hw : PolyAt len w) :
    NetworkAt len (fun x=>BitArithmetic.properOn (m x) (d x)) :=
  of_le ((((((PolyAt.const len 2).mul hm).add ((PolyAt.const len 3).mul hd)).add
    (((PolyAt.const len 216).mul hw).mul hw)).add ((PolyAt.const len 250).mul hw)).add
    (PolyAt.const len 45)) fun x=>properOn_count (m x) (d x)
lemma evenOn {m : ∀x,BooleanNetwork (a x) (w x)} (hm : NetworkAt len m) (hw : PolyAt len w) :
    NetworkAt len (fun x=>BitArithmetic.evenOn (m x)) :=
  ((hm.pair (wordConstant _ hw)).comp (modNet hw)).zeroWord hw
lemma halfWord {m : ∀x,BooleanNetwork (a x) (w x)} (hm : NetworkAt len m) (hw : PolyAt len w) :
    NetworkAt len (fun x=>BitArithmetic.halfWord (m x)) :=
  (hm.pair (wordConstant _ hw)).comp (divNet hw)
lemma halfPowerBits {b m : ∀x,BooleanNetwork (a x) (w x)} {d : ∀x,BooleanNetwork (a x) (e x)}
    (hb : NetworkAt len b) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hw : PolyAt len w) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.halfPowerBits (b x) (m x) (d x)) :=
  ((hb.pair hm).pair ((hd.halfWord he).rewire _)).comp (modularPower hw he)
lemma shiftedHalfBits {b m : ∀x,BooleanNetwork (a x) (w x)} {d : ∀x,BooleanNetwork (a x) (e x)}
    (hb : NetworkAt len b) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hw : PolyAt len w) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.shiftedHalfBits (b x) (m x) (d x)) :=
  ((((hb.halfPowerBits hm hd hw he).pair hm).comp (addNet hw)).pair
    (wordConstant _ hw)).comp (subNet hw)
lemma candidateBits {b m : ∀x,BooleanNetwork (a x) (w x)} {d : ∀x,BooleanNetwork (a x) (e x)}
    (hb : NetworkAt len b) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hw : PolyAt len w) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.candidateBits (b x) (m x) (d x)) :=
  (((hd.zeroWord he).bnot).band (hd.evenOn he)).wordMux
    (((hb.shiftedHalfBits hm hd hw he).pair hm).comp (gcdNet hw)) (wordConstant _ hw) hw
lemma firstProperNet {m : ∀x,BooleanNetwork (a x) (w x)} {ds : ∀x,List (BooleanNetwork (a x) (w x))}
    (hm : NetworkAt len m) (hw : PolyAt len w) (hL : PolyAt len (fun x=>(ds x).length))
    (h : ∃p : Polynomial ℕ,∀x d,d∈ds x → d.net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>BitArithmetic.firstProperNet (m x) (ds x)) := by
  obtain ⟨p,hp⟩:=h
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply of_le (hw.add (hL.mul ((((((PolyAt.const len 2).mul hm).add ((PolyAt.const len 4).mul hc)).add
    (((PolyAt.const len 216).mul hw).mul hw)).add ((PolyAt.const len 257).mul hw)).add
    (PolyAt.const len 45))))
  exact fun x=>firstProperNet_count (m x) (ds x) (hp x)
lemma rootOn {n : α→ℕ} {m : ∀x,BooleanNetwork (a x) (n x+1)} (hm : NetworkAt len m)
    (hn : PolyAt len n) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.rootOn (n x) (e x) (m x)) := by
  have hr : PolyAt len (fun x=>rootWidth (n x)) := by unfold rootWidth;poly_at
  have hw:=hn.add (PolyAt.const len 1)
  exact ((hm.comp (resizeWord hw hr)).comp (boundedRootNet hn he)).comp (resizeWord hr hw)
lemma rootsOn {n : α→ℕ} {m : ∀x,BooleanNetwork (a x) (n x+1)} (hm : NetworkAt len m)
    (hn : PolyAt len n) : NetworkAt len (fun x=>BitArithmetic.rootsOn (n x) (m x)) := by
  let ix:=Σx:α,Fin (n x+1)
  have he : PolyAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val) :=
    (hn.add (PolyAt.const len 1) |>.pull Sigma.fst).of_le fun xi=>Nat.le_of_lt xi.2.isLt
  obtain ⟨p,hp⟩:=(hm.pull (Sigma.fst (β:=fun x=>Fin (n x+1)))).rootOn (hn.pull Sigma.fst) he
  apply firstProperNet hm (hn.add (PolyAt.const len 1))
    (by simpa only [List.length_map,List.length_range] using hn.add (PolyAt.const len 1))
  refine ⟨p,?_⟩
  intro x d hd
  obtain ⟨e,he,rfl⟩:=List.mem_map.mp hd
  exact hp ⟨x,⟨e,List.mem_range.mp he⟩⟩
end NetworkAt
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ActualDivisorPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace FixedSplit
lemma actualBaseNet_poly : NetworkAt (fun xi:Σn,Fin (n^5)=>xi.1) (fun xi=>actualBaseNet xi.2) := by
  simpa only [NetworkAt,actualBaseNet,count_comp,launchWires,count_select,Nat.zero_add,
    baseNet_count] using PolyAt.ofPoly PreparationPolynomial.listOutput (fun xi:Σn,Fin (n^5)=>xi.1)
lemma modulusNet_poly : NetworkAt id modulusNet :=
  (NetworkAt.select _).comp (NetworkAt.select _)
lemma actualOrderRawNet_poly : NetworkAt (fun xi:Σn,Fin (n^5)=>xi.1) (fun xi=>actualOrderRawNet xi.2) :=
  (NetworkAt.select _).comp (NetworkAt.select _)
lemma actualOrderNet_poly : NetworkAt (fun xi:Σn,Fin (n^5)=>xi.1) (fun xi=>actualOrderNet xi.2) :=
  OrderSlots.outputOn_poly actualBaseNet_poly (modulusNet_poly.pull Sigma.fst) actualOrderRawNet_poly
lemma liftedModulus_poly : NetworkAt id liftedModulus :=
  modulusNet_poly.comp (NetworkAt.resizeWord (PolyAt.self id) ((PolyAt.self id).add (PolyAt.const id 1)))
lemma roots_poly : NetworkAt id (fun n=>rootsOn n (liftedModulus n)) :=
  liftedModulus_poly.rootsOn (PolyAt.self id)
lemma ordersBits_poly : NetworkAt id (fun n=>ordersBits (liftedModulus n) (actualPairs n)) := by
  let len : (Σn,Fin (n^5))→ℕ:=Sigma.fst
  have hn:=PolyAt.self len
  have hw:=hn.add (PolyAt.const len 1)
  have hm:=liftedModulus_poly.pull (Sigma.fst (β:=fun n=>Fin (n^5)))
  have he:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  obtain ⟨p,hp⟩:=((actualBaseNet_poly.comp (NetworkAt.resizeWord hn hw)).candidateBits hm
    actualOrderNet_poly hw he)
  apply NetworkAt.firstProperNet liftedModulus_poly
    ((PolyAt.self id).add (PolyAt.const id 1))
    (by simpa only [actualPairs,List.length_map,List.length_ofFn,id_eq] using (PolyAt.self (id : ℕ→ℕ)).pow 5)
  refine ⟨p,?_⟩
  intro n d hd
  obtain ⟨ar,har,rfl⟩:=List.mem_map.mp hd
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp har
  exact hp ⟨n,i⟩
lemma divisorNet_poly : NetworkPoly divisorNet := by
  have hn:=PolyAt.self (id : ℕ→ℕ)
  have hw:=hn.add (PolyAt.const id 1)
  exact (liftedModulus_poly.evenOn hw).wordMux (NetworkAt.wordConstant _ hw)
    ((liftedModulus_poly.properOn roots_poly hw).wordMux roots_poly ordersBits_poly hw) hw
end FixedSplit
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeStateBounds.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.NodeStateCircuit
open BooleanNetwork

lemma pending_count (s w : ℕ) : (pending s w).net.count=0 := rfl
lemma output_count (s w : ℕ) : (output s w).net.count=0 := rfl
lemma bad_count (s w : ℕ) : (bad s w).net.count=0 := rfl
lemma old_count (s w : ℕ) : (old s w).net.count=0 := rfl
lemma supplied_count (s w : ℕ) : (supplied s w).net.count=0 := rfl
lemma nodeInput_count (s w : ℕ) : (nodeInput s w).net.count=0 := by
  simp only [nodeInput,count_pair,count_comp,old_count,pending_count,supplied_count,zero_add]
lemma top_count (s w : ℕ) : (top s w).net.count=0 := by
  simp only [top,count_comp,pending_count,blockNet_count,zero_add]
lemma nextPending_count (s w : ℕ) : (nextPending s w).net.count ≤ NodeCircuit.nextBound s w := by
  simpa only [nextPending,count_comp,nodeInput_count,zero_add] using NodeCircuit.next_count s w
lemma emission_count (s w : ℕ) : (emission s w).net.count ≤ NodeCircuit.primeBound w+8*w := by
  simpa only [emission,count_comp,nodeInput_count,zero_add] using NodeCircuit.emitted_count s w

def outputBound (s w : ℕ) :=
  NodeCircuit.primeBound w+8*w+97*w+21+(s+1)*w*(NodeCircuit.primeBound w+8*w)+7*((s+1)*w)
def stepBound (s w : ℕ) := NodeCircuit.nextBound s w+outputBound s w+
  (97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+9)

lemma nextOutput_count (s w : ℕ) : (nextOutput s w).net.count ≤ outputBound s w := by
  have hz := zeroWord_count (emission s w)
  have he := emission_count s w
  have hs := stackPush_count (emission s w) ((old s w).comp (output s w))
  simp only [count_comp,old_count,output_count,add_zero] at hs
  have hs' : (stackPush (emission s w) ((old s w).comp (output s w))).net.count ≤
      (s+1)*w*(NodeCircuit.primeBound w+8*w) := hs.trans (Nat.mul_le_mul_left _ he)
  simp only [nextOutput,wordMux_count,count_comp,old_count,output_count,add_zero]
  dsimp only [outputBound]
  omega
lemma nextBad_count (s w : ℕ) : (nextBad s w).net.count ≤
    97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+9 := by
  calc
    (nextBad s w).net.count = (NodeCircuit.failed s w).net.count+4 := by
      simp only [nextBad,count_bor,count_comp,old_count,bad_count,nodeInput_count,zero_add]
    _ ≤ (97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+5)+4 :=
      Nat.add_le_add_right (NodeCircuit.failed_count s w) 4
    _ = 97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+9 := by omega

theorem step_count (s w : ℕ) : (step s w).net.count ≤ stepBound s w := by
  have h1 := nextPending_count s w
  have h2 := nextOutput_count s w
  have h3 := nextBad_count s w
  simp only [step,count_pair]
  exact Nat.add_le_add (Nat.add_le_add h1 h2) h3

end ExactQuantumFactoring.BitArithmetic.NodeStateCircuit


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PrimalityPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BitArithmetic
namespace PreparationPolynomial
variable {α : Sort*} {len s w a b c : α→ℕ}
lemma cyclicMulBound_poly (hs : PolyAt len s) (hw : PolyAt len w)
    (ha : PolyAt len a) (hb : PolyAt len b) (hc : PolyAt len c) :
    PolyAt len (fun x=>cyclicMulBound (s x) (w x) (a x) (b x) (c x)) := by
  unfold cyclicMulBound
  have hwp:=hw.add (PolyAt.const len 1)
  exact (hs.mul hw).mul (hw.add (hs.mul ((((((ha.add hb).add ((PolyAt.const len 2).mul hc)).add
    (((((PolyAt.const len 1224).mul hw).mul hw).add ((PolyAt.const len 143).mul hw)).add (PolyAt.const len 12))).add
    ((PolyAt.const len 216).mul (hwp.pow 2))).add ((PolyAt.const len 142).mul hwp)).add (PolyAt.const len 15))))
lemma cyclicAddBound_poly (hs : PolyAt len s) (hw : PolyAt len w)
    (ha : PolyAt len a) (hb : PolyAt len b) (hc : PolyAt len c) :
    PolyAt len (fun x=>cyclicAddBound (s x) (w x) (a x) (b x) (c x)) := by
  unfold cyclicAddBound
  have hwp:=hw.add (PolyAt.const len 1)
  exact (hs.mul hw).mul ((((((ha.add hb).add hc).add ((PolyAt.const len 216).mul (hwp.pow 2))).add
    ((PolyAt.const len 142).mul hwp)).add (PolyAt.const len 15)))
lemma cyclicStepBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>cyclicStepBound (s x) (w x)) := by
  have h0:=PolyAt.const len 0
  have hm:=cyclicMulBound_poly hs hw h0 h0 h0
  exact ((cyclicMulBound_poly hs hw hm h0 h0).add hm).add ((PolyAt.const len 7).mul (hs.mul hw))
lemma cyclicTestBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>cyclicTestBound (s x) (w x)) := by
  have h0:=PolyAt.const len 0
  have hsw:=(hs.mul hw).mul hw
  have hstep:=hw.mul (cyclicStepBound_poly hs hw)
  exact (((((cyclicAddBound_poly hs hw hsw hsw h0).add hsw).add hstep).add
    (cyclicAddBound_poly hs hw (((PolyAt.const len 2).mul hsw).add hstep) hsw h0)).add
      ((PolyAt.const len 96).mul (hs.mul hw))).add (PolyAt.const len 21)
lemma rootWidth_poly : PolyBound rootWidth := by unfold rootWidth;poly_fast
lemma perfectCheckBound_poly : PolyBound perfectCheckBound := by
  have hn:=PolyBound.id
  have hr:=rootWidth_poly
  have hb:=((((PolyBound.const 90).mul hr).mul hr).add ((PolyBound.const 14).mul hr)).add (PolyBound.const 6)
  exact ((((PolyBound.const 147).mul hr).add (PolyBound.const 31)).add
    (hn.mul ((((PolyBound.const 230).mul hr).add (PolyBound.const 21)).add (hn.mul hb)))).add (hn.mul hb)
lemma aksBranchBound_poly : PolyBound (fun n=>aksBranchBound n (n^8) (rootWidth n)) := by
  have hn:=PolyBound.id
  have hr:=rootWidth_poly
  have hc : PolyBound (fun n=>cyclicTestBound (n^8) (rootWidth n)) :=
    cyclicTestBound_poly ((PolyAt.self (id : ℕ→ℕ)).pow 8) hr
  have hbase:=(((((PolyBound.const 216).mul hr).mul hr).add ((PolyBound.const 154).mul hr)).add
    (PolyBound.const 27)).add (PolyBound.const 1)
  have hstep:=(((((PolyBound.const 3672).mul hr).mul hr).add ((PolyBound.const 436).mul hr)).add (PolyBound.const 36))
  have hord:=((hn.pow 2).mul ((((PolyBound.const 100).mul hr).add (PolyBound.const 23)).add (hr.mul hstep))).add (PolyBound.const 1)
  have hdiv:=(((PolyBound.const 8).mul (hn.pow 8)).mul
    (((((PolyBound.const 216).mul hr).mul hr).add ((PolyBound.const 203).mul hr)).add (PolyBound.const 38))).add (PolyBound.const 1)
  have hcon:=(((PolyBound.const 8).mul (hn.pow 8)).mul (hc.add (PolyBound.const 1))).add (PolyBound.const 1)
  exact (((hbase.add hord).add hdiv).add hcon).add (PolyBound.const 3)
lemma primalityBound_poly : PolyBound primalityBound := by
  have hn:=PolyBound.id
  exact (((hn.add (PolyBound.const 1)).mul (perfectCheckBound_poly.add (PolyBound.const 4))).add
    (PolyBound.const 1)).add (PolyBound.const 1) |>.add
      ((((hn.pow 8).add (PolyBound.const 1)).mul (aksBranchBound_poly.add (PolyBound.const 4))).add (PolyBound.const 1)) |>.add (PolyBound.const 1)
lemma primeBound_poly : PolyBound NodeCircuit.primeBound :=
  ((((PolyBound.const 49).mul PolyBound.id).add (PolyBound.const 10)).add rootWidth_poly).add primalityBound_poly
lemma guardBound_poly : PolyBound NodeCircuit.guardBound :=
  (((((PolyBound.const 216).mul PolyBound.id).mul PolyBound.id).add
    ((PolyBound.const 250).mul PolyBound.id)).add (PolyBound.const 45))
lemma quotientBound_poly : PolyBound NodeCircuit.quotientBound :=
  (((((PolyBound.const 216).mul PolyBound.id).mul PolyBound.id).add
    ((PolyBound.const 56).mul PolyBound.id)).add (PolyBound.const 6))
lemma nodeStepBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>NodeStateCircuit.stepBound (s x) (w x)) := by
  have hp:=PolyAt.comp primeBound_poly hw
  have hg:=PolyAt.comp guardBound_poly hw
  have hq:=PolyAt.comp quotientBound_poly hw
  have hn : PolyAt len (fun x=>NodeCircuit.nextBound (s x) (w x)) := by
    unfold NodeCircuit.nextBound NodeCircuit.splitBound
    poly_at
  have ho : PolyAt len (fun x=>NodeStateCircuit.outputBound (s x) (w x)) := by
    unfold NodeStateCircuit.outputBound
    poly_at
  unfold NodeStateCircuit.stepBound
  poly_at
end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodePreparationPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PreparationPolynomial
lemma nodeConfig : PolyBound (fun n=>PhysicalNode.configWidth n (2*n)) := by
  unfold PhysicalNode.configWidth NodeStateCircuit.width
  poly_fast
lemma nodeQuery : NetworkPoly (fun n=>PhysicalNode.query n (2*n)) := by
  apply PolyBound.id.of_le
  intro n
  simpa only [PhysicalNode.query,count_comp,NodeStateCircuit.top_count,zero_add]
    using resizeWord_count (n+1) n
lemma nodeStep : NetworkPoly (fun n=>NodeStateCircuit.step (2*n) (n+1)) := by
  apply PolyBound.of_le (g:=fun n=>NodeStateCircuit.stepBound (2*n) (n+1))
  · exact nodeStepBound_poly ((PolyAt.const id 2).mul (PolyAt.self id))
      ((PolyAt.self id).add (PolyAt.const id 1))
  · intro n;exact NodeStateCircuit.step_count _ _
lemma nodeUpdate : NetworkPoly (fun n=>PhysicalNode.update n (2*n)) :=
  ((NetworkPoly.select _).pair ((NetworkPoly.select _).comp FixedSplit.divisorNet_poly)).comp nodeStep
lemma nodeInitWork : PolyBound (fun n=>(PhysicalNode.machine n (2*n)).initWork) :=
  nodeQuery.add splitInitial
lemma nodeUpdateWork : PolyBound (fun n=>(PhysicalNode.machine n (2*n)).updateWork) := nodeUpdate
lemma nodeWidth : PolyBound NodeKernel.width := by
  change PolyBound (fun n=>(PhysicalNode.machine n (2*n)).width (2*n))
  simp only [SplitMachine.width_eq]
  have :=nodeConfig;have:=splitWidth;have:=nodeInitWork;have:=nodeUpdateWork
  poly_fast
lemma machineNodeInitial : PolyBound (fun n=>((PhysicalNode.machine n (2*n)).initialNet (2*n)).net.count) := by
  simp only [SplitMachine.initialNet_count]
  have :=nodeConfig;have:=splitWidth;have:=nodeInitWork;have:=nodeUpdateWork
  poly_fast
lemma nodeStart : NetworkPoly PhysicalNode.startNet := by
  apply PolyBound.of_le (g:=fun n=>(2*n+1)*(n+1)*((n+1)+(2*n+1)*(n+1))+(2*n+1)*(n+1)+1)
  · poly_fast
  · intro n
    have hh:=stackPush_count (resizeWord n (n+1)) (Completion.zeros n ((2*n+1)*(n+1)))
    simp only [Completion.zeros_count] at hh
    have hr:=resizeWord_count n (n+1)
    have hh' :=hh.trans (Nat.mul_le_mul_left ((2*n+1)*(n+1)) (Nat.add_le_add_right hr _))
    simp only [PhysicalNode.startNet,count_pair,Completion.zeros_count,count_constant]
    omega
lemma nodeInitial : NetworkPoly NodeKernel.initialNet := nodeStart.comp machineNodeInitial
lemma nodeSteps : PolyBound (fun n=>(NodeKernel.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>2*n*(4*(PhysicalNode.machine n (2*n)).initWork+
    2*FixedSplit.width n+(FixedSplit.program n).length+
    4*(PhysicalNode.machine n (2*n)).updateWork+2*PhysicalNode.configWidth n (2*n)))
  · have :=nodeInitWork;have:=splitWidth;have:=splitSteps;have:=nodeUpdateWork;have:=nodeConfig
    poly_fast
  · intro n;exact SplitMachine.program_length _ _
end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreePreparationPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PreparationPolynomial
lemma treeConfig : PolyBound PhysicalTree.configWidth := by
  unfold PhysicalTree.configWidth PhysicalTree.capacity;poly_fast
lemma treeQuery_count (n : ℕ) : (PhysicalTree.query n).net.count=0 := by
  simp only [PhysicalTree.query,blockNet,count_select]
lemma treeQuery : NetworkPoly PhysicalTree.query := by
  simp only [NetworkPoly,treeQuery_count];exact PolyBound.const 0
lemma treePushed : NetworkPoly PhysicalTree.pushed := by
  apply PolyBound.of_le (g:=fun n=>PhysicalTree.capacity n*n*n+n*ChildQueue.oneBound
    (PhysicalTree.capacity n) n (PhysicalNode.resultBound n) n)
  · have cap : PolyBound PhysicalTree.capacity :=by unfold PhysicalTree.capacity;poly_fast
    have res : PolyBound PhysicalNode.resultBound :=
      (PolyBound.id.mul PolyBound.id).add ((PolyBound.id.mul PolyBound.id).mul
        (((PolyBound.const 498).mul PolyBound.id).add (PolyBound.const 114)))
    have lin : PolyBound (fun n=>2*PhysicalNode.resultBound n+96*n+25) :=
      (((PolyBound.const 2).mul res).add ((PolyBound.const 96).mul PolyBound.id)).add (PolyBound.const 25)
    have lin' : PolyBound (fun n=>PhysicalNode.resultBound n+159*n+6) :=
      (res.add ((PolyBound.const 159).mul PolyBound.id)).add (PolyBound.const 6)
    have one : PolyBound (fun n=>ChildQueue.oneBound (PhysicalTree.capacity n) n (PhysicalNode.resultBound n) n) :=
      (((((res.add ((PolyBound.const 49).mul PolyBound.id)).add (PolyBound.const 11)).add
        (PolyBound.id.mul lin)).add ((cap.mul PolyBound.id).mul lin')).add
          ((PolyBound.const 7).mul (cap.mul PolyBound.id)))
    exact ((cap.mul PolyBound.id).mul PolyBound.id).add (PolyBound.id.mul one)
  · intro n
    have h:=ChildQueue.pushAll_count (PhysicalTree.capacity n) (PhysicalTree.fields n)
      (c:=PhysicalNode.resultBound n) (by
        intro b hb
        obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hb
        simpa only [count_comp,tensorSelect,count_select,add_zero]
          using PhysicalTree.nodeResult_count n)
    have hs:=stackPop_count (PhysicalTree.capacity n) n
    have hh:=Nat.add_le_add hs h
    simpa only [PhysicalTree.pushed,PhysicalTree.localNode,PhysicalTree.old,
      count_comp,count_pair,count_select,ChildQueue.queue,
      zero_add,add_zero,PhysicalTree.fields,List.length_ofFn] using hh
lemma treeUpdate : NetworkPoly PhysicalTree.update := by
  apply PolyBound.of_le (g:=fun n=>97*n+21+7*PhysicalTree.configWidth n+(PhysicalTree.pushed n).net.count)
  · exact ((((PolyBound.const 97).mul PolyBound.id).add (PolyBound.const 21)).add
      ((PolyBound.const 7).mul treeConfig)).add treePushed
  · intro n
    have h:=zeroWord_count ((PhysicalTree.old n).comp (PhysicalTree.query n))
    simp only [count_comp,PhysicalTree.old,count_select,treeQuery_count,zero_add] at h
    simp only [PhysicalTree.update,wordMux_count,PhysicalTree.old,count_select]
    omega
lemma treeInitWork : PolyBound (fun n=>(PhysicalTree.machine n).initWork) :=
  treeQuery.add nodeInitial
lemma treeUpdateWork : PolyBound (fun n=>(PhysicalTree.machine n).updateWork) :=treeUpdate
lemma treeWidth : PolyBound PhysicalTree.width := by
  change PolyBound (fun n=>(PhysicalTree.machine n).width (PhysicalTree.steps n))
  simp only [NodeMachine.width_eq]
  have :=treeConfig;have :=nodeWidth;have :=treeInitWork;have :=treeUpdateWork
  unfold PhysicalTree.steps;poly_fast
lemma treeMachineInitial : PolyBound (fun n=>((PhysicalTree.machine n).initialNet
    (PhysicalTree.steps n)).net.count) := by
  simp only [NodeMachine.initialNet_count]
  have :=treeConfig;have :=nodeWidth;have :=treeInitWork;have :=treeUpdateWork
  unfold PhysicalTree.steps;poly_fast
lemma treeStart : NetworkPoly PhysicalTree.startNet := by
  apply PolyBound.of_le (g:=fun n=>PhysicalTree.capacity n*n*(PhysicalTree.capacity n*n))
  · unfold PhysicalTree.capacity;poly_fast
  · intro n
    simpa only [PhysicalTree.startNet,count_select,Completion.zeros_count,zero_add]
      using stackPush_count (select (n:=n) id) (Completion.zeros n (PhysicalTree.configWidth n))
lemma treeLaunchWork : PolyBound PhysicalTree.launchWork :=treeStart.comp treeMachineInitial
lemma treeSteps : PolyBound (fun n=>((PhysicalTree.machine n).program (PhysicalTree.steps n)).length) := by
  apply PolyBound.of_le (g:=fun n=>PhysicalTree.steps n*(4*(PhysicalTree.machine n).initWork+
    2*NodeKernel.width n+(NodeKernel.program n).length+
    4*(PhysicalTree.machine n).updateWork+2*PhysicalTree.configWidth n))
  · have :=treeInitWork;have :=nodeWidth;have :=nodeSteps;have :=treeUpdateWork;have :=treeConfig
    unfold PhysicalTree.steps;poly_fast
  · intro n;exact NodeMachine.program_length _ _
lemma treeLaunchWidth : PolyBound PhysicalTree.launchWidth :=by
  unfold PhysicalTree.launchWidth
  have :=treeWidth;have :=treeLaunchWork;poly_fast
lemma treeLaunchSteps : PolyBound (fun n=>(PhysicalTree.launchProgram n).length) := by
  apply PolyBound.of_le (g:=fun n=>4*PhysicalTree.launchWork n+2*PhysicalTree.width n+
    ((PhysicalTree.machine n).program (PhysicalTree.steps n)).length)
  · have :=treeLaunchWork;have :=treeWidth;have :=treeSteps;poly_fast
  · exact PhysicalTree.launchProgram_length
lemma treePadding : PolyBound PhysicalTree.padding := by
  apply (PolyBound.id.pow 10).of_le
  intro n;exact Nat.sub_le _ _
lemma treePaddedWidth : PolyBound PhysicalTree.paddedWidth :=by
  unfold PhysicalTree.paddedWidth
  simp only [tensorWidth_eq]
  exact treeLaunchWidth.add (treePadding.mul PolyBound.id)
lemma treePaddedSteps : PolyBound (fun n=>(PhysicalTree.paddedProgram n).length) :=by
  apply PolyBound.of_le (g:=fun n=>4*PhysicalTree.launchWork n+2*PhysicalTree.width n+
    ((PhysicalTree.machine n).program (PhysicalTree.steps n)).length+PhysicalTree.padding n*n)
  · have :=treeLaunchWork;have :=treeWidth;have :=treeSteps;have :=treePadding;poly_fast
  · exact PhysicalTree.paddedProgram_length
lemma quarterWidth : PolyBound PhysicalTree.quarterWidth :=by
  unfold PhysicalTree.quarterWidth
  exact (PolyBound.const 1).add (treePaddedWidth.add ((PolyBound.id.mul PolyBound.id).add Quarter.D_poly))
lemma quarterSteps : PolyBound (fun n=>(PhysicalTree.quarterProgram n).length) :=by
  simp only [PhysicalTree.quarterProgram_length]
  exact ((treePaddedSteps.add (PolyBound.const 1)).add (PolyBound.id.mul PolyBound.id)).add Quarter.D_poly
end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedNetworkPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace RetainedPolynomial
variable {α : Type*} {len n f c : α→ℕ}
lemma primeComponentBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>primeComponentBound (n x) (c x)) := by
  have hw : PolyAt len (fun x=>componentWidth (n x)) := by unfold componentWidth;poly_at
  unfold primeComponentBound
  exact (((hc.add hw).add (hw.add (hn.mul (((hc.add hw).add
    (((PolyAt.const len 90).mul hw).mul hw)).add ((PolyAt.const len 14).mul hw) |>.add
      (PolyAt.const len 6))))).add (((PolyAt.const len 2).mul hw).mul
        (((PolyAt.const len 216).mul hw |>.mul hw).add ((PolyAt.const len 300).mul hw) |>.add
          (PolyAt.const len 100)))).add hn
lemma tableOrderBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableOrderBound (n x) (f x) (c x)) := by
  have hw : PolyAt len (fun x=>tableOrderWidth (n x) (f x)) := by unfold tableOrderWidth;poly_at
  have hC : PolyAt len (fun x=>3*c x+220*n x+50+tableOrderWidth (n x) (f x)) := by poly_at
  have hs : PolyAt len (fun x=>stripStepBound (tableOrderWidth (n x) (f x))
      (3*c x+220*n x+50+tableOrderWidth (n x) (f x))) := by unfold stripStepBound;poly_at
  unfold tableOrderBound
  exact ((hn.mul hf).mul ((((hC.add (((PolyAt.const len 90).mul hw).mul hw)).add
    ((PolyAt.const len 14).mul hw)).add (PolyAt.const len 6)).add hs) |>.add hw).add hn
lemma totientStepBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>totientStepBound (n x) (c x)) := by unfold totientStepBound;poly_at
lemma tableTotientBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableTotientBound (n x) (f x) (c x)) :=
  (hc.add hn).add ((hn.mul hf).mul (totientStepBound_at hn
    (((PolyAt.const len 3).mul hc).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50))))
lemma oddPartBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>oddPartBound (n x) (c x)) := by
  have hp:=primeComponentBound_at hn (hc.add hn)
  unfold oddPartBound;poly_at
lemma closedLevelBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>closedLevelBound (n x) (c x)) := by
  have ho:=oddPartBound_at hn hc
  unfold closedLevelBound;poly_at
lemma componentLevelBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>componentLevelBound (n x) (c x)) := by
  have hp:=primeComponentBound_at hn hc
  have hphi : PolyAt len (fun x=>componentPhiBound (n x) (c x)) := by unfold componentPhiBound;poly_at
  have hclosed:=closedLevelBound_at hn hphi
  unfold componentLevelBound;poly_at
lemma tableFavorableCountBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableFavorableCountBound (n x) (f x) (c x)) := by
  have hstep:=totientStepBound_at hn hc
  have hlev:=componentLevelBound_at hn hc
  have hinner : PolyAt len (fun x=>2*c x+96*n x+25) := by poly_at
  have hmiddle : PolyAt len (fun x=>componentLevelBound (n x) (c x)+90*n x*n x+22*n x+7+f x*(2*c x+96*n x+25)) :=
    ((((hlev.add (((PolyAt.const len 90).mul hn).mul hn)).add ((PolyAt.const len 22).mul hn)).add
      (PolyAt.const len 7)).add (hf.mul hinner))
  have hbad : PolyAt len (fun x=>tableBadCountBound (n x) (f x) (c x)) :=
    ((hn.add (PolyAt.const len 1)).mul ((((hf.mul hmiddle).add hn).add
      ((PolyAt.const len 86).mul hn)).add (PolyAt.const len 6))).add hn
  unfold tableFavorableCountBound;poly_at
lemma tableCanonicalBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableCanonicalBound (n x) (f x) (c x)) := by
  have hp:=primeComponentBound_at hn hc
  have hi : PolyAt len (fun x=>4*c x+216*n x*n x+202*n x+42) := by poly_at
  have hh : PolyAt len (fun x=>componentCongruenceBound (n x) (f x) (c x)) :=
    (((((hc.add ((PolyAt.const len 3).mul hp)).add (((PolyAt.const len 216).mul hn).mul hn)).add
      ((PolyAt.const len 500).mul hn)).add (PolyAt.const len 100)).add (hf.mul hi))
  have hi' : PolyAt len (fun x=>2*c x+216*n x*n x+154*n x+33+componentCongruenceBound (n x) (f x) (c x)) :=
    (((((PolyAt.const len 2).mul hc).add (((PolyAt.const len 216).mul hn).mul hn)).add
      ((PolyAt.const len 154).mul hn)).add (PolyAt.const len 33)).add hh
  exact (((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 48).mul hn)).add
    (PolyAt.const len 10)).add (hf.mul hi')).add (PolyAt.const len 2)
lemma resultBound_at (hn : PolyAt len n) : PolyAt len (fun x=>PhysicalNode.resultBound (n x)) :=
  (hn.mul hn).add ((hn.mul hn).mul (((PolyAt.const len 498).mul hn).add (PolyAt.const len 114)))
end RetainedPolynomial
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedNetworkAt.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a b : α→ℕ}
lemma all_map {δ : α→Type*} (ls : ∀x,List (δ x)) (f : ∀x,δ x→BooleanNetwork (a x) 1)
    (hl : PolyAt len (fun x=>(ls x).length))
    (hf : NetworkAt (fun xi : Σx,{i // i∈ls x}=>len xi.1) (fun xi=>f xi.1 xi.2.val)) :
    NetworkAt len (fun x=>BooleanNetwork.all ((ls x).map (f x))) := by
  obtain ⟨p,hp⟩:=hf
  apply all (by simpa only [List.length_map] using hl)
  refine ⟨p,?_⟩
  intro x g hg
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hg
  exact hp ⟨x,⟨i,hi⟩⟩
lemma any_ofFn {k : α→ℕ} {f : ∀x,Fin (k x)→BooleanNetwork (a x) 1} (hk : PolyAt len k)
    (hf : NetworkAt (fun xi : Σx,Fin (k x)=>len xi.1) (fun xi=>f xi.1 xi.2)) :
    NetworkAt len (fun x=>BooleanNetwork.any (List.ofFn (f x))) := by
  obtain ⟨p,hp⟩:=hf
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply of_le ((hk.mul (hc.add (PolyAt.const len 4))).add (PolyAt.const len 1))
  intro x
  have h:=any_count (List.ofFn (f x)) (c:=p.eval (len x)) (by
    intro g hg;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hg;exact hp ⟨x,i⟩)
  simpa only [List.length_ofFn] using h
lemma primeComponent {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hb : PolyAt len b) (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>BitArithmetic.primeComponent (f x) (g x)) :=
  of_le (RetainedPolynomial.primeComponentBound_at hb (PolyAt.add hf hg))
    (fun x=>primeComponent_count _ _ (by omega) (by omega))
lemma dividesOn {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hb : PolyAt len b) (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>BitArithmetic.dividesOn (f x) (g x)) := by
  have hh : PolyAt len (fun x=>(f x).net.count+(g x).net.count+216*b x*b x+154*b x+27) :=
    ((((PolyAt.add hf hg).add (((PolyAt.const len 216).mul hb).mul hb)).add
      ((PolyAt.const len 154).mul hb)).add (PolyAt.const len 27))
  exact of_le hh fun x=>dividesOn_count _ _
lemma sameTwoVal {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hb : PolyAt len b) (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>BitArithmetic.sameTwoVal (f x) (g x)) := by
  have hi : PolyAt len (fun x=>2*(f x).net.count+2*(g x).net.count+864*b x*b x+616*b x+118) :=
    (((((PolyAt.const len 2).mul hf).add ((PolyAt.const len 2).mul hg)).add
      (((PolyAt.const len 864).mul hb).mul hb)).add ((PolyAt.const len 616).mul hb)).add (PolyAt.const len 118)
  exact of_le ((hb.mul hi).add (PolyAt.const len 1)) fun x=>sameTwoVal_count _ _
end NetworkAt
namespace NodeMachine
variable {α : Type*} {len n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
variable (hn : PolyAt len n) (ht : PolyAt len t)
  (hq : NetworkAt len (fun x=>(M x).query))
include hn ht hq
lemma retainedOrder_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedOrder (t x) (a x) (m x)) := by
  have hB:=((PolyAt.add ha hm).add hq).add (RetainedPolynomial.resultBound_at hn)
  apply NetworkAt.of_le (RetainedPolynomial.tableOrderBound_at hn (ht.mul hn) hB)
  intro x
  exact (M x).retainedOrder_count _ _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedTotient_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedTotient (t x) (m x)) := by
  have hB:=(PolyAt.add hm hq).add (RetainedPolynomial.resultBound_at hn)
  apply NetworkAt.of_le (RetainedPolynomial.tableTotientBound_at hn (ht.mul hn) hB)
  intro x
  exact (M x).retainedTotient_count _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedFavorableCount_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedFavorableCount (t x) (m x)) := by
  have hB:=(PolyAt.add hm hq).add (RetainedPolynomial.resultBound_at hn)
  have hC:=((PolyAt.const len 3).mul hB).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50)
  apply NetworkAt.of_le (RetainedPolynomial.tableFavorableCountBound_at hn (ht.mul hn) hC)
  intro x
  exact (M x).retainedFavorableCount_count _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedCanonical_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedCanonical (t x) (a x) (m x)) := by
  have hB:=((PolyAt.add ha hm).add hq).add (RetainedPolynomial.resultBound_at hn)
  have hC:=((PolyAt.const len 3).mul hB).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50)
  apply NetworkAt.of_le (RetainedPolynomial.tableCanonicalBound_at hn (ht.mul hn) hC)
  intro x
  exact (M x).retainedCanonical_count _ _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedComponentOrder_at {a m p : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hp : NetworkAt len p) :
    NetworkAt len (fun x=>(M x).retainedComponentOrder (t x) (a x) (m x) (p x)) :=
  retainedOrder_at hn ht hq ha (NetworkAt.primeComponent hn hm hp)
omit hq in
lemma tableNets_length_at : PolyAt len (fun x=>(tableNets ((M x).fieldRows (t x))).length) := by
  simpa only [fieldRows_table_length] using ht.mul hn
omit ht in
lemma tableNets_at : NetworkAt (fun xi : Σx,{p // p∈tableNets ((M x).fieldRows (t x))}=>len xi.1)
    (fun xi=>xi.2.val) := by
  let pull:=fun xi : Σx,{p // p∈tableNets ((M x).fieldRows (t x))}=>xi.1
  have hB:=PolyAt.add hq (RetainedPolynomial.resultBound_at hn)
  have hC:=((PolyAt.const len 3).mul hB).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50)
  apply NetworkAt.of_le (hC.pull pull)
  rintro ⟨x,p,hp⟩
  apply tableNets_counts _ (c:=(M x).query.net.count+PhysicalNode.resultBound (n x)) _ _ hp
  intro r hr
  have hh:=(M x).fieldRows_counts (t x) r hr
  exact ⟨hh.1.trans (by omega),fun p hp=>(hh.2 p hp).trans (by omega)⟩
end NodeMachine
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedFavorablePolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len k n K : α→ℕ}
lemma usableOn {a m : ∀x,BooleanNetwork (k x) (n x)}
    (hn : PolyAt len n) (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>OrderSlots.usableOn (a x) (m x)) :=
  (ha.wordLt hm hn).band
    (((ha.pair hm).comp (NetworkAt.gcdNet hn)).equalOn (NetworkAt.wordConstant _ hn) hn)
lemma firstOnly {a : ∀x,BooleanNetwork (k x) (n x)}
    (hn : PolyAt len n) (hK : PolyAt len K) (ha : NetworkAt len a) :
    NetworkAt len (fun x=>TransitionWords.firstOnly (K:=K x) (a x)) := by
  apply of_le ((hn.mul (hK.add (PolyAt.const len 1))).mul
    ((PolyAt.add ha hn).add (PolyAt.const len 1)))
  intro x
  apply TransitionWords.encodeNet_count
  intro i
  by_cases hi:i.val=0
  · rw [ite_eq_left hi];omega
  · rw [ite_eq_right hi,wordConstant_count];omega
end NetworkAt
namespace NodeMachine
variable {α : Type*} {len n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
variable (hn : PolyAt len n) (ht : PolyAt len t)
  (hq : NetworkAt len (fun x=>(M x).query))
include hn ht hq
lemma retainedFavorable_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedFavorable (t x) (a x) (m x)) := by
  let ps:=fun x=>tableNets ((M x).fieldRows (t x))
  let ix:=Σx,{p // p∈ps x}
  let fst:ix→α:=Sigma.fst
  let jx:=Σxi:ix,{q // q∈ps xi.1}
  let both:jx→α:=fun xi=>xi.1.1
  have hps : NetworkAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val):=tableNets_at hn hq
  have hl : PolyAt len (fun x=>(ps x).length):=tableNets_length_at hn ht
  apply (NetworkAt.usableOn hn ha hm).band
  apply NetworkAt.bnot
  apply NetworkAt.all_map ps _ hl
  apply NetworkAt.all_map (fun xi:ix=>ps xi.1) _ (hl.pull fst)
  have hp:=hps.pull (fun xi:jx=>xi.1)
  have hq':=hps.pull (fun xi:jx=>⟨xi.1.1,xi.2⟩)
  have hn':=hn.pull both
  have ht':=ht.pull both
  have hquery:=hq.pull both
  have ha':=ha.pull both
  have hm':=hm.pull both
  exact (NetworkAt.dividesOn hn' hp hm').bnot.bor
    ((NetworkAt.dividesOn hn' hq' hm').bnot.bor
      (NetworkAt.sameTwoVal hn'
        (retainedComponentOrder_at hn' ht' hquery ha' hm' hp)
        (retainedComponentOrder_at hn' ht' hquery ha' hm' hq')))
lemma retainedGoodList_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    {y : ∀x,BooleanNetwork ((M x).width (t x)) (n x*((n x)^5+1))}
    (hm : NetworkAt len m) (hy : NetworkAt len y) :
    NetworkAt len (fun x=>(M x).retainedGoodList (t x) (m x) (y x)) := by
  let param:=fun xi : Σx,Fin ((n x)^5)=>xi.1
  apply NetworkAt.any_ofFn (hn.pow 5)
  exact retainedFavorable_at (hn.pull param) (ht.pull param) (hq.pull param)
    ((hy.pull param).rewire _) (hm.pull param)
lemma retainedCanonicalList_at (hpos : ∀x,0<n x)
    {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    {y : ∀x,BooleanNetwork ((M x).width (t x)) (n x*((n x)^5+1))}
    (hm : NetworkAt len m) (hy : NetworkAt len y) :
    NetworkAt len (fun x=>(M x).retainedCanonicalList (hpos x) (t x) (m x) (y x)) := by
  have ha : NetworkAt len (fun x=>TransitionWords.readNet (y x) ⟨0,pow_pos (hpos x) 5⟩):=
    hy.rewire _
  exact (retainedCanonical_at hn ht hq ha hm).band
    (hy.equalOn (NetworkAt.firstOnly hn (hn.pow 5) ha) (hn.mul ((hn.pow 5).add (PolyAt.const len 1))))
end NodeMachine
end ExactQuantumFactoring

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CompletionFilterPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
namespace RatExprPoly
lemma ofHeight {v : ℕ→Type*} {q : ℕ→ℚ} (h : RatHeightPoly q) :
    RatExprPoly (fun n=>RatExpr.const (q n) : ∀n,RatExpr (v n)) := const h.1 h.2
end RatExprPoly
namespace Completion.Expressions
variable {v : ℕ→Type*} {W t : ℕ→ℕ} {s z : ∀n,RatExpr (v n)}
lemma ordinaryMass_poly (ht : PolyBound t) (hs : RatExprPoly s) :
    RatExprPoly (fun n=>ordinaryMass (t n) (s n)) :=
  (RatExprPoly.ofHeight ((RatHeightPoly.constant 1).sub
    ((RatHeightPoly.constant 1).div ((RatHeightPoly.constant 2).pow ht)))).mul hs
lemma coefficient_poly (hW : PolyBound W) (ht : PolyBound t)
    (hs : RatExprPoly s) (hz : RatExprPoly z) :
    RatExprPoly (fun n=>coefficient (W n) (t n) (s n) (z n)) := by
  have hp : RatExprPoly (fun n=>RatExpr.const ((2:ℚ)^(W n+t n+2)) : ∀n,RatExpr (v n)) :=
    RatExprPoly.ofHeight ((RatHeightPoly.constant 2).pow ((hW.add ht).add (PolyBound.const 2)))
  exact (RatExprPoly.ofInt (hp.mul (hz.div (ordinaryMass_poly ht hs))).floor).div hp
lemma guess_poly (hW : PolyBound W) (ht : PolyBound t)
    (hs : RatExprPoly s) (hz : RatExprPoly z) :
    RatExprPoly (fun n=>guess (W n) (t n) (s n) (z n)) :=
  ((hz.sub ((coefficient_poly hW ht hs hz).mul (ordinaryMass_poly ht hs))).mul
    (RatExprPoly.ofHeight ((RatHeightPoly.constant 2).pow hW))).div
    (RatExprPoly.ofHeight ((RatHeightPoly.constant 1).div ((RatHeightPoly.constant 2).pow ht)))
lemma listRateCoin_poly : RatExprPoly (fun n=>listRateCoin n (n^5)) :=
  ((RatExprPoly.ofNat (NatExprPoly.var (fun _=>1))).div
    (RatExprPoly.ofNat (OrderTrial.Expressions.coveringPow_poly
      (NatExprPoly.var (fun _=>0)) PolyBound.id))).repeatedSuccess (PolyBound.id.pow 5)
lemma orderRateCoin_poly : RatExprPoly (fun n=>orderRateCoin n (n^5)) :=
  ((RatExprPoly.ofNat (NatExprPoly.var (fun _=>1))).mul
    (OrderTrial.Expressions.lambdaE_poly PolyBound.id
      (NatExprPoly.var (fun _=>0)))).repeatedSuccess (PolyBound.id.pow 5)
end Completion.Expressions
lemma retentionNet_at {α : Type*} {len a b : α→ℕ} {v : ℕ→Type*} {T : ℕ→ℕ}
    {p : ∀n,RatExpr (v n)} {c : ∀n,NatExpr (v n)}
    {vars : ∀x,v (len x)→BooleanNetwork (a x) (b x)}
    (hT : PolyBound T) (hp : RatExprPoly p) (hc : NatExprPoly c)
    (hb : PolyAt len b) (hv : ∃q : Polynomial ℕ,∀x i,(vars x i).net.count≤q.eval (len x)) :
    NetworkAt len (fun x=>retentionNet (T (len x)) (p (len x)) (c (len x)) (vars x)) :=
  (NatExprAt.ofPoly (thresholdExpr_poly hT hp hc) len).isOne hb hv
namespace Completion
lemma predicateFilter_at {α : Type*} {len a b : α→ℕ} {v : ℕ→Type*} {W t d : ℕ→ℕ}
    {s z : ∀n,RatExpr (v n)} {coin : ∀n,NatExpr (v n)}
    {vars : ∀x,v (len x)→BooleanNetwork (a x) (b x)}
    {branch : ∀x,BooleanNetwork (a x) (t (len x))}
    {good guessGood : ∀x,BooleanNetwork (a x) 1}
    (hW : PolyBound W) (ht : PolyBound t) (hd : PolyBound d)
    (hs : RatExprPoly s) (hz : RatExprPoly z) (hc : NatExprPoly coin)
    (hb : PolyAt len b) (hv : ∃q : Polynomial ℕ,∀x i,(vars x i).net.count≤q.eval (len x))
    (hbranch : NetworkAt len branch) (hgood : NetworkAt len good) (hguess : NetworkAt len guessGood) :
    NetworkAt len (fun x=>predicateFilter (W:=W (len x)) (d (len x))
      (s (len x)) (z (len x)) (vars x) (branch x) (coin (len x)) (good x) (guessGood x)) := by
  have hT : PolyBound (fun n=>coinBits (W n) (t n) (d n)) := by
    unfold coinBits;poly_bound
  have ho:=retentionNet_at hT (Expressions.coefficient_poly hW ht hs hz) hc hb hv
  have hg:=retentionNet_at hT (Expressions.guess_poly hW ht hs hz) hc hb hv
  have hr:=hbranch.zeroWord (PolyAt.ofPoly ht len)
  exact (hr.bnot.band (hgood.band ho)).bor (hr.band (hguess.band hg))
end Completion
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedFilterPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
lemma ite {α : Type*} {len a b : α→ℕ} (p : α→Prop) [∀x,Decidable (p x)]
    {f g : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>if p x then f x else g x) := by
  apply of_le (PolyAt.add hf hg)
  intro x
  by_cases h : p x
  · rw [ite_eq_left h];omega
  · rw [ite_eq_right h];omega
end NetworkAt
namespace Completion.Expressions
lemma target_poly : RatExprPoly (fun n=>RatExpr.const (Completion.target n) : ℕ→RatExpr (Fin 3)) :=
  RatExprPoly.ofHeight ((RatHeightPoly.constant 1).sub
    ((RatHeightPoly.constant 1).div ((RatHeightPoly.constant 2).pow PolyBound.id)))
end Completion.Expressions
namespace Completion
lemma rareWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>rareWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
lemma ordinaryWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>ordinaryWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
lemma guessWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>guessWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
lemma retentionWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>retentionWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
end Completion
namespace NodeMachine
variable {α : Type*} {len c t : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
variable (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query))
include ht hq
lemma listFilterVars_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (PhysicalListSlots.width (len x))}
    (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt (fun xi : α×Fin 3=>len xi.1) (fun xi=>(M xi.1).listFilterVars (t xi.1) (m xi.1) (raw xi.1) xi.2) := by
  unfold listFilterVars
  let fst : α×Fin 3→α:=Prod.fst
  have hn:=PolyAt.self len
  have hc:=PolyAt.ofPoly PreparationPolynomial.listCoin len
  have hw:=hn.add hc
  have hresize:=NetworkAt.resizeWord hn hw
  apply NetworkAt.ite (fun xi=>xi.2=0) ((hm.comp hresize).pull fst)
  apply NetworkAt.ite (fun xi=>xi.2=1)
    (((retainedFavorableCount_at hn ht hq hm).comp hresize).pull fst)
  exact ((hr.comp (Completion.retentionWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
      (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))).comp (NetworkAt.resizeWord hc hw)).pull fst
lemma orderFilterVars_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt (fun xi : α×Fin 3=>len xi.1) (fun xi=>(M xi.1).orderFilterVars (t xi.1) (a xi.1) (m xi.1) (raw xi.1) xi.2) := by
  unfold orderFilterVars
  let fst : α×Fin 3→α:=Prod.fst
  have hn:=PolyAt.self len
  have hc:=PolyAt.ofPoly PreparationPolynomial.orderCoin len
  have hw:=hn.add hc
  have ho:=retainedOrder_at hn ht hq ha hm
  have hphi:=retainedTotient_at hn ht hq ho
  have hresize:=NetworkAt.resizeWord hn hw
  apply NetworkAt.ite (fun xi=>xi.2=0) ((ho.comp hresize).pull fst)
  apply NetworkAt.ite (fun xi=>xi.2=1) ((hphi.comp hresize).pull fst)
  exact ((hr.comp (Completion.retentionWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
      (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))).comp (NetworkAt.resizeWord hc hw)).pull fst
lemma retainedListFilter_at (hpos : ∀x,0<len x)
    {m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (PhysicalListSlots.width (len x))}
    (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).retainedListFilter (hpos x) (t x) (m x) (raw x)) := by
  unfold retainedListFilter
  have hn:=PolyAt.self len
  obtain ⟨p,hp⟩:=listFilterVars_at ht hq hm hr
  have hord : NetworkAt len (fun x=>PhysicalListSlots.ordinaryNet (len x)) :=
    NetworkAt.of_le (PolyAt.ofPoly PreparationPolynomial.transitionWidth len)
      (fun x=>PhysicalListSlots.ordinaryNet_count (len x))
  have hgood := retainedGoodList_at hn ht hq hm ((hr.comp (Completion.ordinaryWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))).comp hord)
  have hcanonical := retainedCanonicalList_at hn ht hq hpos hm (hr.comp (Completion.guessWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5))))
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>listVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) (PolyBound.id.mul (PolyBound.id.pow 5))
      Completion.Expressions.listRateCoin_poly Completion.Expressions.target_poly (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.listCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5))))
      hgood hcanonical
lemma listDummyFilter_at
    {m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (PhysicalListSlots.width (len x))}
    (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).listDummyFilter (t x) (m x) (raw x)) := by
  unfold listDummyFilter
  have hn:=PolyAt.self len
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  obtain ⟨p,hp⟩:=listFilterVars_at ht hq hm hr
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>listVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) (PolyBound.id.mul (PolyBound.id.pow 5))
      (RatExprPoly.ofHeight (RatHeightPoly.constant 1)) Completion.Expressions.target_poly
      (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.listCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))) (NetworkAt.constant (fun _=>true))
      ((hr.comp (Completion.guessWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))).zeroWord hw)
lemma orderActualFilter_at
    {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).orderActualFilter (t x) (a x) (m x) (raw x)) := by
  unfold orderActualFilter
  have hn:=PolyAt.self len
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  have ho:=retainedOrder_at hn ht hq ha hm
  obtain ⟨p,hp⟩:=orderFilterVars_at ht hq ha hm hr
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>orderVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) ((PolyBound.id.add (PolyBound.const 10)).mul (PolyBound.id.pow 5))
      Completion.Expressions.orderRateCoin_poly Completion.Expressions.target_poly
      (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.orderCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5))))
      ((OrderSlots.orderResultNet_poly ha hm (hr.comp (Completion.ordinaryWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5))))).equalOn ho hn)
      ((hr.comp (Completion.guessWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))).equalOn (ho.comp (NetworkAt.resizeWord hn hw)) hw)
lemma orderDummyFilter_at
    {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).orderDummyFilter (t x) (a x) (m x) (raw x)) := by
  unfold orderDummyFilter
  have hn:=PolyAt.self len
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  obtain ⟨p,hp⟩:=orderFilterVars_at ht hq ha hm hr
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>orderVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) ((PolyBound.id.add (PolyBound.const 10)).mul (PolyBound.id.pow 5))
      (RatExprPoly.ofHeight (RatHeightPoly.constant 1)) Completion.Expressions.target_poly
      (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.orderCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))) (NetworkAt.constant (fun _=>true))
      ((hr.comp (Completion.guessWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))).zeroWord hw)
lemma retainedOrderFilter_at
    {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).retainedOrderFilter (t x) (a x) (m x) (raw x)) :=
  ((NetworkAt.usableOn (PolyAt.self len) ha hm).band (orderActualFilter_at ht hq ha hm hr)).bor
    ((NetworkAt.usableOn (PolyAt.self len) ha hm).bnot.band (orderDummyFilter_at ht hq ha hm hr))
end NodeMachine
end ExactQuantumFactoring

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedSplitPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
lemma primeWord {α : Type*} {len n : α→ℕ} (hn : PolyAt len n) :
    NetworkAt len (fun x=>BitArithmetic.primeWord (n x)) :=
  of_le (PolyAt.comp PreparationPolynomial.primeBound_poly hn) (fun x=>primeWord_count (n x))
lemma perfectPowerNet {α : Type*} {len n : α→ℕ} (hn : PolyAt len n) :
    NetworkAt len (fun x=>BitArithmetic.perfectPowerNet (n x)) :=
  of_le (((hn.add (PolyAt.const len 1)).mul
    ((PolyAt.comp PreparationPolynomial.perfectCheckBound_poly hn).add (PolyAt.const len 4))).add
    (PolyAt.const len 1)) (fun x=>perfectPowerNet_count (n x))
lemma hardOn {α : Type*} {len a n : α→ℕ} {m : ∀x,BooleanNetwork (a x) (n x)}
    (hn : PolyAt len n) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>UniversalSplit.hardOn (m x)) := by
  have hr:=PolyAt.comp PreparationPolynomial.rootWidth_poly hn
  exact (((NetworkAt.wordConstant _ hn).wordLe hm hn).band (hm.comp (primeWord hn)).bnot).band
    ((hm.evenOn hn).bnot.band ((hm.comp (NetworkAt.resizeWord hn hr)).comp (perfectPowerNet hn)).bnot)
end NetworkAt
namespace NodeMachine
variable {α : Type*} {len c t : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
variable (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query))
variable {raw : ∀x,BooleanNetwork ((M x).width (t x)) (FixedSplit.width (len x))}
variable (hr : NetworkAt len raw)
include hr
omit ht hq in
lemma splitModulus_at : NetworkAt len (fun x=>(M x).splitModulus (t x) (raw x)) :=
  hr.comp (FixedSplit.modulusNet_poly.pull len)
omit ht hq in
lemma splitList_at : NetworkAt len (fun x=>(M x).splitList (t x) (raw x)) :=
  (hr.comp (NetworkAt.select _)).comp (NetworkAt.select _)
omit ht hq in
lemma splitBase_at : NetworkAt (fun xi : Σx,Fin ((len x)^5)=>len xi.1)
    (fun xi=>(M xi.1).splitBase (t xi.1) (raw xi.1) xi.2) := by
  unfold splitBase
  with_reducible
    exact (hr.pull (fun xi : Σx,Fin ((len x)^5)=>xi.1)).comp
      (FixedSplit.actualBaseNet_poly.pull (fun xi : Σx,Fin ((len x)^5)=>⟨len xi.1,xi.2⟩))
omit ht hq in
lemma splitOrder_at : NetworkAt (fun xi : Σx,Fin ((len x)^5)=>len xi.1)
    (fun xi=>(M xi.1).splitOrder (t xi.1) (raw xi.1) xi.2) := by
  unfold splitOrder
  with_reducible
    exact (hr.pull (fun xi : Σx,Fin ((len x)^5)=>xi.1)).comp
      (FixedSplit.actualOrderRawNet_poly.pull (fun xi : Σx,Fin ((len x)^5)=>⟨len xi.1,xi.2⟩))
include ht hq in
lemma splitActualFilter_at (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>(M x).splitActualFilter (hpos x) (t x) (raw x)) := by
  let pull : (Σx,Fin ((len x)^5))→α:=Sigma.fst
  exact (retainedListFilter_at ht hq hpos (splitModulus_at hr) (splitList_at hr)).band
    (NetworkAt.all_ofFn ((PolyAt.self len).pow 5)
      (retainedOrderFilter_at (ht.pull pull) (hq.pull pull) (splitBase_at hr)
        ((splitModulus_at hr).pull pull) (splitOrder_at hr)))
include ht hq in
lemma splitDummyFilter_at :
    NetworkAt len (fun x=>(M x).splitDummyFilter (t x) (raw x)) := by
  let pull : (Σx,Fin ((len x)^5))→α:=Sigma.fst
  exact (listDummyFilter_at ht hq (splitModulus_at hr) (splitList_at hr)).band
    (NetworkAt.all_ofFn ((PolyAt.self len).pow 5)
      (orderDummyFilter_at (ht.pull pull) (hq.pull pull) (splitBase_at hr)
        ((splitModulus_at hr).pull pull) (splitOrder_at hr)))
include ht hq in
lemma retainedSplitFilter_at (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>(M x).retainedSplitFilter (hpos x) (t x) (raw x)) := by
  have hh:=NetworkAt.hardOn (PolyAt.self len) (splitModulus_at hr)
  exact (hh.band (splitActualFilter_at ht hq hr hpos)).bor
    (hh.bnot.band (splitDummyFilter_at ht hq hr))
end NodeMachine
end ExactQuantumFactoring

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedPrefixPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace SplitMachine
lemma previousNet_count {n c : ℕ} (M : SplitMachine n c) (s : ℕ) :
    (M.previousNet s).net.count=0 := by
  simp only [previousNet,count_comp,count_select,Nat.add_zero]
lemma lastSplitNet_count {n c : ℕ} (M : SplitMachine n c) (s : ℕ) :
    (M.lastSplitNet s).net.count=0 := by
  simp only [lastSplitNet,count_comp,count_select,Nat.add_zero]
end SplitMachine
namespace NodeMachine
lemma nodePrefixFilter_count {n c : ℕ} (M : NodeMachine n c) (hn : 0<n) (T B C : ℕ)
    (h : ∀v : BooleanNetwork (M.width T) (FixedSplit.width n),v.net.count≤B→
      (M.retainedSplitFilter hn T v).net.count≤C)
    (s : ℕ) (v : BooleanNetwork (M.width T) ((PhysicalNode.machine n (2*n)).width s))
    (hv : v.net.count≤B) : (M.nodePrefixFilter hn T s v).net.count≤ s*(C+1)+1 := by
  induction s with
  | zero=>simp only [nodePrefixFilter,count_constant,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ s ih=>
    have hi:=ih (v.comp ((PhysicalNode.machine n (2*n)).previousNet s)) (by
      simpa only [count_comp,SplitMachine.previousNet_count,Nat.add_zero] using hv)
    have hh:=h (v.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s)) (by
      simpa only [count_comp,SplitMachine.lastSplitNet_count,Nat.add_zero] using hv)
    simp only [nodePrefixFilter,count_band]
    nlinarith
lemma nodePrefixFilter_at {α : Type*} {len c T s : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len T) (hs : PolyAt len s)
    (hq : NetworkAt len (fun x=>(M x).query))
    {raw : ∀x,BooleanNetwork ((M x).width (T x)) ((PhysicalNode.machine (len x) (2*len x)).width (s x))}
    (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).nodePrefixFilter (hpos x) (T x) (s x) (raw x)) := by
  let ix:=Σx,{v : BooleanNetwork ((M x).width (T x)) (FixedSplit.width (len x)) // v.net.count≤(raw x).net.count}
  let fst : ix→α:=Sigma.fst
  have hv : NetworkAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val):=
    NetworkAt.of_le (hr.pull fst) (fun xi=>xi.2.property)
  obtain ⟨p,hp⟩:=retainedSplitFilter_at (ht.pull fst) (hq.pull fst) hv (fun xi:ix=>hpos xi.1)
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply NetworkAt.of_le ((hs.mul (hc.add (PolyAt.const len 1))).add (PolyAt.const len 1))
  intro x
  exact nodePrefixFilter_count (M x) (hpos x) (T x) (raw x).net.count (p.eval (len x))
    (fun v hh=>hp ⟨x,v,hh⟩) (s x) (raw x) le_rfl
lemma retainedNodeFilter_at {α : Type*} {len c T : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len T)
    (hq : NetworkAt len (fun x=>(M x).query))
    {raw : ∀x,BooleanNetwork ((M x).width (T x)) (NodeKernel.width (len x))}
    (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).retainedNodeFilter (hpos x) (T x) (raw x)) :=
  nodePrefixFilter_at hpos ht ((PolyAt.const len 2).mul (PolyAt.self len)) hq hr
lemma treePrefixFilter_count {n c : ℕ} (M : NodeMachine n c) (hn : 0<n) (T B C : ℕ)
    (h : ∀v : BooleanNetwork (M.width T) (NodeKernel.width n),v.net.count≤B→
      (M.retainedNodeFilter hn T v).net.count≤C)
    (s : ℕ) (v : BooleanNetwork (M.width T) (M.width s))
    (hv : v.net.count≤B) : (M.treePrefixFilter hn T s v).net.count≤ s*(C+1)+1 := by
  induction s with
  | zero=>simp only [treePrefixFilter,count_constant,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ s ih=>
    have hi:=ih (v.comp (M.previousNet s)) (by
      simpa only [count_comp,previousNet_count,Nat.add_zero] using hv)
    have hh:=h (v.comp (M.lastNodeNet s)) (by
      simpa only [count_comp,lastNodeNet_count,Nat.add_zero] using hv)
    simp only [treePrefixFilter,count_band]
    nlinarith
lemma treePrefixFilter_at {α : Type*} {len c T s : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len T) (hs : PolyAt len s)
    (hq : NetworkAt len (fun x=>(M x).query))
    {raw : ∀x,BooleanNetwork ((M x).width (T x)) ((M x).width (s x))}
    (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).treePrefixFilter (hpos x) (T x) (s x) (raw x)) := by
  let ix:=Σx,{v : BooleanNetwork ((M x).width (T x)) (NodeKernel.width (len x)) // v.net.count≤(raw x).net.count}
  let fst : ix→α:=Sigma.fst
  have hv : NetworkAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val):=
    NetworkAt.of_le (hr.pull fst) (fun xi=>xi.2.property)
  obtain ⟨p,hp⟩:=retainedNodeFilter_at (fun xi:ix=>hpos xi.1) (ht.pull fst) (hq.pull fst) hv
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply NetworkAt.of_le ((hs.mul (hc.add (PolyAt.const len 1))).add (PolyAt.const len 1))
  intro x
  exact treePrefixFilter_count (M x) (hpos x) (T x) (raw x).net.count (p.eval (len x))
    (fun v hh=>hp ⟨x,v,hh⟩) (s x) (raw x) le_rfl
end NodeMachine
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedQuarterPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PreparationPolynomial
lemma factorVerifierBound_at {α : Type*} {len n c : α→ℕ}
    (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>factorVerifierBound (n x) (c x)) := by
  have hr:=PolyAt.comp rootWidth_poly hn
  have hp:=PolyAt.comp primalityBound_poly hn
  have hprod:= (hn.mul ((((((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 105).mul hn)).add
    (PolyAt.const len 21)).add hr).add (((PolyAt.const len 90).mul hr).mul hr)).add
    ((PolyAt.const len 14).mul hr)).add (PolyAt.const len 6))).add hr
  have hfirst:= (hn.mul (((((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 146).mul hn)).add
    (PolyAt.const len 35)).add hr).add hp).add (PolyAt.const len 1))).add (PolyAt.const len 1)
  have hsecond:= ((hn.mul hn).mul ((((PolyAt.const len 4).mul hc).add
    ((PolyAt.const len 242).mul hn)).add (PolyAt.const len 58))).add (PolyAt.const len 1)
  exact ((((hfirst.add hsecond).add (PolyAt.const len 1)).add
    ((((hprod.add hc).add hr).add ((PolyAt.const len 96).mul hr)).add (PolyAt.const len 21))).add
      (PolyAt.const len 1))
lemma physicalResultBound : PolyBound PhysicalNode.resultBound := by
  exact (PolyBound.id.mul PolyBound.id).add ((PolyBound.id.mul PolyBound.id).mul
    (((PolyBound.const 498).mul PolyBound.id).add (PolyBound.const 114)))
end PreparationPolynomial
namespace NodeMachine
lemma rowBound_at {α : Type*} {len n c : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
    (hn : PolyAt len n) (hq : NetworkAt len (fun x=>(M x).query)) :
    PolyAt len (fun x=>(M x).rowBound) := by
  have hr:=PolyAt.comp PreparationPolynomial.physicalResultBound hn
  exact (((PolyAt.add hq ((PolyAt.const len 97).mul hn)).add (PolyAt.const len 25)).add
    (PreparationPolynomial.factorVerifierBound_at hn (PolyAt.add hq hr)))
lemma verifiedNet_at {α : Type*} {len n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
    (hn : PolyAt len n) (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query)) :
    NetworkAt len (fun x=>(M x).verifiedNet (t x)) :=
  NetworkAt.of_le ((ht.mul ((rowBound_at hn hq).add (PolyAt.const len 1))).add (PolyAt.const len 1))
    (fun x=>(M x).verifiedNet_count (t x))
lemma acceptedNet_at {α : Type*} {len c t : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query)) :
    NetworkAt len (fun x=>(M x).acceptedNet (hpos x) (t x)) :=
  (verifiedNet_at (PolyAt.self len) ht hq).band
    (treePrefixFilter_at hpos ht ht hq (NetworkAt.select (fun _=>id)))
end NodeMachine
namespace PhysicalTree
lemma padFlag_poly : NetworkPoly padFlag := by
  unfold padFlag
  exact NetworkAt.all_ofFn PreparationPolynomial.treePadding
    (((NetworkAt.select _).zeroWord (PolyAt.self (fun xi:Σn,Fin (padding n)=>xi.1))).bnot)
lemma paddedFlag_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>paddedFlag (len x) (hpos x)) := by
  have ht : PolyAt len (fun x=>2*(len x)^2):=(PolyAt.const len 2).mul ((PolyAt.self len).pow 2)
  have hq : NetworkAt len (fun x=>(machine (len x)).query):=NetworkAt.ofPoly PreparationPolynomial.treeQuery len
  have ha:=NodeMachine.acceptedNet_at hpos ht hq
  exact (((NetworkAt.select _).comp (NetworkAt.select _)).comp ha).band
    ((NetworkAt.select _).comp (NetworkAt.ofPoly padFlag_poly len))
lemma guessVerifier_poly : NetworkPoly guessVerifier := by
  apply NetworkAt.of_le (PreparationPolynomial.factorVerifierBound_at (PolyAt.self id) (PolyAt.const id 0))
  intro n
  exact factorVerifierOn_count _ _ (by simp only [count_select,le_refl]) (by intro i;simp only [count_select,le_refl])
lemma quarterGuessFlag_poly : NetworkPoly quarterGuessFlag :=
  ((((NetworkAt.select _).comp ((NetworkAt.select _).comp (NetworkAt.select _))).pair
    (NetworkAt.select _)).comp guessVerifier_poly)
lemma quarterRare_poly : NetworkPoly quarterRare :=
  ((NetworkAt.select _).zeroWord (PolyAt.const id 1))
lemma quarterKeep_poly {p : ℕ→ℚ} (hp : RatHeightPoly p) :
    NetworkPoly (fun n=>quarterKeep n (p n)) := by
  unfold quarterKeep
  exact retentionNet_at Quarter.D_poly (RatExprPoly.ofHeight hp) (NatExprPoly.var (fun _=>()))
    Quarter.D_poly ⟨0,fun n i=>by simp only [quarterCoin,Completion.retentionWires,count_select,Polynomial.eval_zero,le_refl]⟩
lemma quarterFlag_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>quarterFlag (len x) (hpos x)) := by
  have hr:=NetworkAt.ofPoly quarterRare_poly len
  have hp:=paddedFlag_at len hpos
  have hk:=NetworkAt.ofPoly (quarterKeep_poly Quarter.retention_height) len
  have hg:=NetworkAt.ofPoly (quarterKeep_poly Quarter.guessRetention_height) len
  have hv:=NetworkAt.ofPoly quarterGuessFlag_poly len
  exact (hr.bnot.band (((NetworkAt.select _).comp hp).band hk)).bor (hr.band (hv.band hg))
end PhysicalTree
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FinalPolynomialResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
namespace PhysicalTree
lemma factoringProgram_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    PolyAt len (fun x=>(factoringProgram (len x) (hpos x)).length) := by
  have hprep:=PolyAt.ofPoly PreparationPolynomial.quarterSteps len
  have hflag : PolyAt len (fun x=>(quarterFlag (len x) (hpos x)).net.count):=quarterFlag_at len hpos
  have hwidth:=PolyAt.ofPoly PreparationPolynomial.quarterWidth len
  have hresult:=PolyAt.ofPoly PreparationPolynomial.physicalResultBound len
  exact (((((((PolyAt.const len 3).mul hprep).add ((PolyAt.const len 8).mul hflag)).add
    ((PolyAt.const len 16).mul hwidth)).add ((PolyAt.const len 4).mul hresult)).add
      ((PolyAt.const len 34).mul ((PolyAt.self len).mul (PolyAt.self len)))).add
        (PolyAt.const len 492)).of_le (fun x=>(factoringProgram_resources_reduced (len x) (hpos x)).1)
lemma readoutWidth_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    PolyAt len (fun x=>readoutWidth (len x) (hpos x)) := by
  have hflag : PolyAt len (fun x=>(quarterFlag (len x) (hpos x)).net.count):=quarterFlag_at len hpos
  have hwidth:=PolyAt.ofPoly PreparationPolynomial.quarterWidth len
  have hresult:=PolyAt.ofPoly PreparationPolynomial.physicalResultBound len
  exact ((((((PolyAt.const len 3).mul hwidth).add hflag).add hresult).add
    ((PolyAt.const len 9).mul ((PolyAt.self len).mul (PolyAt.self len)))).add
      (PolyAt.const len 120)).of_le (fun x=>(factoringProgram_resources_reduced (len x) (hpos x)).2)
lemma paddedLength_poly : PolyBound paddedLength :=
  (PolyBound.const 128).max PolyBound.id
lemma finalCircuit_qubits_poly : PolyBound (fun ℓ=>(finalCircuit ℓ).qubits) := by
  obtain ⟨p,hp⟩:=readoutWidth_at paddedLength paddedLength_pos
  exact (PolyBound.comp (⟨p,fun _=>le_rfl⟩ : PolyBound (fun n=>p.eval n)) paddedLength_poly).of_le hp
lemma finalCircuit_gates_poly : PolyBound (fun ℓ=>(finalCircuit ℓ).instructions.length) := by
  obtain ⟨p,hp⟩:=factoringProgram_at paddedLength paddedLength_pos
  apply (PolyBound.comp (⟨p,fun _=>le_rfl⟩ : PolyBound (fun n=>p.eval n)) paddedLength_poly).of_le
  intro ℓ
  rw [finalCircuit_length]
  exact hp ℓ
theorem finalCircuit_resources : PolynomialResources finalCircuit := by
  obtain ⟨p,hp⟩:=finalCircuit_qubits_poly
  obtain ⟨q,hq⟩:=finalCircuit_gates_poly
  refine ⟨p+q,fun ℓ=>?_⟩
  rw [Polynomial.eval_add]
  exact ⟨(hp ℓ).trans (Nat.le_add_right _ _),(hq ℓ).trans (Nat.le_add_left _ _)⟩
end PhysicalTree
end ExactQuantumFactoring

end


end OAI
