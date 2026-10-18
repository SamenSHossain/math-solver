/-
Exact quantum factoring development (port of OpenAI's formalization), part 37 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: SplitMachineEmission.lean, PhysicalNodeEmission.lean, ChildQueueEmission.lean, NodeMachineEmission.lean, PhysicalTreeEmission.lean, TreePreparationEmission.lean, TreeHistoryEmission.lean, TreeVerificationEmission.lean, TreeTableEmission.lean, TableNetsEmission.lean, TableScanEmission.lean, TableArithmeticEmission.lean, CanonicalTableEmission.lean, ComponentLevelEmission.lean, DistinctProductEmission.lean, TableFavorableEmission.lean, RetainedArithmeticEmission.lean, RetainedFavorableEmission.lean, BitStackRationalDivision.lean, BitStackRationalFloor.lean, BitStackRationalPower.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part36

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SplitMachineEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.SplitMachineEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n c t : α→ℕ} {M : ∀x,SplitMachine (n x) (c x)}
lemma width (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>FixedSplit.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(M x).width (t x)):=
  (hc.unaryAdd (ht.unaryMul (((hk.unaryAdd hi).unaryAdd hc).unaryAdd hu))).congr
    (fun x=>((M x).width_eq (t x)).symm)
lemma current (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>FixedSplit.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).currentNet (t x)):=by
  have ht':=(ht.unaryNat.natSub (const _ _ 1)).boundedUnary ht (by intro x;exact Nat.sub_le _ _)
  have hs:=((ht.unaryNat.natEq (const _ _ 0)).ite (const _ Nat.bits 0)
    (((width hc hk hi hu ht').unaryNat.natAdd hk.unaryNat).natAdd hi.unaryNat))
  apply selectSlice (width hc hk hi hu ht) hc hs (fun x=>(M x).current (t x))
  intro x i
  cases h : t x with
  | zero=>simp only [SplitMachine.current,decide_true,ite_true,Nat.zero_add];rfl
  | succ j=>simp only [Nat.succ_ne_zero,decide_false,Nat.add_sub_cancel,SplitMachine.current];rfl
lemma init (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>FixedSplit.width (n x)))
    (hK : NetEmits ea (fun x=>FixedSplit.initialNet (n x)))
    (hQ : NetEmits ea (fun x=>(M x).query)) (hU : NetEmits ea (fun x=>(M x).update))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).initNet (t x)):=
  ((current hc hk (hQ.count.unaryAdd hK.count) hU.count ht).comp hQ).comp hK
lemma update (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>FixedSplit.width (n x)))
    (hK : NetEmits ea (fun x=>FixedSplit.initialNet (n x)))
    (hQ : NetEmits ea (fun x=>(M x).query)) (hU : NetEmits ea (fun x=>(M x).update))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).updateNet (t x)):=by
  have hi:=hQ.count.unaryAdd hK.count
  have hw:=width hc hk hi hU.count ht
  exact (((firstSelect hw hk hi).comp (current hc hk hi hU.count ht)).pair
    (targetSelect hw hk hi)).comp hU
lemma program (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>FixedSplit.width (n x)))
    (hK : NetEmits ea (fun x=>FixedSplit.initialNet (n x)))
    (hP : OpsEmits ea (fun x=>FixedSplit.program (n x)))
    (hQ : NetEmits ea (fun x=>(M x).query)) (hU : NetEmits ea (fun x=>(M x).update))
    (ht : Emits ea unaryCode t) : OpsEmits ea (fun x=>(M x).program (t x)):=by
  have hi:=hQ.count.unaryAdd hK.count
  have hu:=hU.count
  apply OpsEmits.boundedStages ht (f:=fun x j=>(M x).program j)
  · exact const _ _ []
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode opCode)))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,((M x.1).program x.2.val).map eraseOp)))
    have hC:=hc.comp hx.fst
    have hKW:=hk.comp hx.fst
    have hKI:=hK.compInput hx.fst
    have hQuery:=hQ.compInput hx.fst
    have hUpdate:=hU.compInput hx.fst
    have hTime:=hx.snd.fst
    have hWidth:=width hC hKW (hi.comp hx.fst) (hu.comp hx.fst) hTime
    exact ((OpsEmits.appendPrepared hx.snd.snd (init hC hKW hKI hQuery hUpdate hTime)
      hWidth (fun x=>((M x.1).initNet_count x.2.val).le) (hP.comp hx.fst)).first
        (fun x=>c x.1) (fun x=>(M x.1).updateWork)).append
      (OpsEmits.oracleOn (update hC hKW hKI hQuery hUpdate hTime)
        (fun x=>((M x.1).updateNet_count x.2.val).le))
  · have hb:=(width hc hk hi hu ht).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    exact hb.of_le (by
      intro x
      rw [(M _).width_eq,(M _).width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · have htime:=ht.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hlen:=(hP.lengthPoly).pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hinit:=hi.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hupdate:=hu.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hkernel:=hk.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hconfig:=hc.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    exact (htime.mul (((((PolyAt.const _ 4).mul hinit).add ((PolyAt.const _ 2).mul hkernel)).add hlen).add
      ((PolyAt.const _ 4).mul hupdate) |>.add ((PolyAt.const _ 2).mul hconfig))).of_le (by
        intro x
        exact ((M x.1).program_length x.2.val).trans (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)))
lemma initial (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>FixedSplit.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).initialNet (t x)):=by
  apply NetEmits.boundedStages ht (f:=fun x j=>(M x).initialNet j)
  · exact identity hc
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,erasePack ((M x.1).initialNet x.2.val))))
    have hprev:=ofCanonical hx.snd.snd
    have hC:=hc.comp hx.fst
    have hKW:=hk.comp hx.fst
    exact ((hprev.packNet (zeros hC hKW) hC (hi.comp hx.fst)).packNet (zeros hC hC) hC (hu.comp hx.fst))
  · exact hc.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
  · exact ((width hc hk hi hu ht).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by
      intro x;rw [(M _).width_eq,(M _).width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · have hb:=(ht.unaryPoly.mul (((hk.unaryPoly.add hi.unaryPoly).add hc.unaryPoly).add hu.unaryPoly)).pull
      (fun x:Σa,Fin (t a+1)=>x.1)
    exact hb.of_le (by
      intro x
      rw [(M _).initialNet_count]
      exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
end ExactQuantumFactoring.SplitMachineEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalNodeEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalNodeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n s t : α→ℕ}
lemma configWidth (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>PhysicalNode.configWidth (n x) (s x)):=
  NodeStateEmission.width hs hn.unarySucc
lemma query (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : NetEmits ea (fun x=>PhysicalNode.query (n x) (s x)):=
  (NodeStateEmission.top hs hn.unarySucc).comp (resize hn.unarySucc hn)
lemma update (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : NetEmits ea (fun x=>PhysicalNode.update (n x) (s x)):=
  ((left (configWidth hn hs) (PhysicalSplitEmission.width hn)).pair
    ((right (configWidth hn hs) (PhysicalSplitEmission.width hn)).comp (PhysicalSplitEmission.divisor hn))).comp (NodeStateEmission.step hs hn.unarySucc)
lemma initWork (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>(PhysicalNode.machine (n x) (s x)).initWork):=
  (query hn hs).count.unaryAdd (PhysicalSplitEmission.initial hn).count
lemma updateWork (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>(PhysicalNode.machine (n x) (s x)).updateWork):=(update hn hs).count
lemma width (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(PhysicalNode.machine (n x) (s x)).width (t x)):=
  SplitMachineEmission.width (configWidth hn hs) (PhysicalSplitEmission.width hn) (initWork hn hs) (updateWork hn hs) ht
lemma current (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).currentNet (t x)):=
  SplitMachineEmission.current (configWidth hn hs) (PhysicalSplitEmission.width hn) (initWork hn hs) (updateWork hn hs) ht
lemma initial (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).initialNet (t x)):=
  SplitMachineEmission.initial (configWidth hn hs) (PhysicalSplitEmission.width hn) (initWork hn hs) (updateWork hn hs) ht
lemma program (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) : OpsEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).program (t x)):=
  SplitMachineEmission.program (configWidth hn hs) (PhysicalSplitEmission.width hn) (PhysicalSplitEmission.initial hn) (PhysicalSplitEmission.program hn) (query hn hs) (update hn hs) ht
lemma start (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalNode.startNet (n x)):=by
  have hS:=((const _ _ 2).unaryMul hn).unarySucc
  have hz:=zeros hn (hS.unaryMul hn.unarySucc)
  exact ((stackPush hn hS hn.unarySucc (resize hn hn.unarySucc) hz).pair hz).pair (constant hn (const _ _ false))
lemma resultField (hn : Emits ea unaryCode n) (i : ∀x,Fin (n x))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>PhysicalNode.resultField (n x) (i x)):=
  ((NodeStateEmission.output ((const _ _ 2).unaryMul hn) hn.unarySucc).comp
    (blockNet ((const _ _ 2).unaryMul hn).unarySucc hn.unarySucc (fun x=>⟨(i x).val,by have:=(i x).isLt;omega⟩) hi)).comp (resize hn.unarySucc hn)
lemma sortedOutput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalNode.sortedOutput (n x)):=by
  apply NetEmits.comp (g:=fun x=>BitArithmetic.SortedWords.sortNet (n x) (n x)) _ (SortingEmission.sort hn hn)
  apply tensor (configWidth hn ((const _ _ 2).unaryMul hn)) hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  exact resultField (hn.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
lemma kernelWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>NodeKernel.width (n x)):=
  width hn ((const _ _ 2).unaryMul hn) ((const _ _ 2).unaryMul hn)
lemma kernelInitial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>NodeKernel.initialNet (n x)):=
  (start hn).comp (initial hn ((const _ _ 2).unaryMul hn) ((const _ _ 2).unaryMul hn))
lemma kernelProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>NodeKernel.program (n x)):=
  program hn ((const _ _ 2).unaryMul hn) ((const _ _ 2).unaryMul hn)
end ExactQuantumFactoring.PhysicalNodeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ChildQueueEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma dropOfFn_eq {β : Type} {K : ℕ} (f : Fin K→β) (d : ℕ) :
    (List.ofFn f).drop d=List.ofFn (fun i:Fin (K-d)=>f ⟨d+i.val,by have:=i.isLt;omega⟩):=by
  apply List.ext_getElem
  · simp only [List.length_drop,List.length_ofFn]
  · intro i h h'
    simp only [List.getElem_drop,List.getElem_ofFn]
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {k w K s : α→ℕ}
lemma wordMemberOfFn {a : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (ha : NetEmits ea a)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.wordMember (a x) (List.ofFn (f x))):=by
  simp only [BitArithmetic.ChildQueue.wordMember,List.map_ofFn]
  apply anyOfFn hk hK
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (K a)=>(x.2.val,x.1))
  exact ((ha.compInput hx.snd).pair hf).comp (wordEq (hw.comp hx.snd))
lemma wordMemberDrop {a : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    {d : α→ℕ} (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hd : Emits ea Nat.bits d) (ha : NetEmits ea a)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.wordMember (a x) ((List.ofFn (f x)).drop (d x))):=by
  have len:=(hK.unaryNat.natSub hd).boundedUnary hK (fun _=>Nat.sub_le _ _)
  have hh : NetEmits ea (fun x=>BitArithmetic.ChildQueue.wordMember (a x)
      (List.ofFn (fun i:Fin (K x-d x)=>f x ⟨d x+i.val,by have:=i.isLt;omega⟩))):=by
    apply wordMemberOfFn hk hw len ha
    have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
      (fun x:Σa,Fin (K a-d a)=>(x.2.val,x.1))
    let inc:(Σa,Fin (K a-d a))→(Σa,Fin (K a)):=fun x=>⟨x.1,⟨d x.1+x.2.val,by have:=x.2.isLt;omega⟩⟩
    have hi:=((hd.comp hx.snd).natAdd hx.fst.unaryNat).boundedUnary (hK.comp hx.snd) (by
      intro x;dsimp only;have:=x.2.isLt;omega)
    exact hf.compInput ((hi.pair hx.snd).recode (by intros;rfl) : Emits _ _ inc)
  exact hh.congr (fun x=>by rw [dropOfFn_eq])
lemma childPushOneDrop {a : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    {d : α→ℕ} (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hs : Emits ea unaryCode s) (hd : Emits ea Nat.bits d) (ha : NetEmits ea a)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.pushOne (s x) (a x) ((List.ofFn (f x)).drop (d x))):=by
  have hsource:=left hk (hs.unaryMul hw)
  have hqueue:=right hk (hs.unaryMul hw)
  have hwidth:=hk.unaryAdd (hs.unaryMul hw)
  have active:=((wordConst hk hw (const _ _ 2)).wordLt ha hw).band (wordMemberDrop hk hw hK hd ha hf).bnot
  exact hsource.pair ((hsource.comp active).wordMux
    (stackPush hwidth hs hw (((hsource.comp ha).pair (wordConst hwidth hw (const _ _ 1))).comp (sub hw)) hqueue) hqueue (hs.unaryMul hw))
lemma childPushAll {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hs : Emits ea unaryCode s)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.pushAll (s x) (List.ofFn (f x))):=by
  let F:=fun x j=>BitArithmetic.ChildQueue.pushAll (s x) ((List.ofFn (f x)).drop (K x-j))
  have h0 : NetEmits ea (fun x=>F x 0):=by
    refine (identity (hk.unaryAdd (hs.unaryMul hw))).congr ?_
    intro x
    dsimp only [F]
    rw [Nat.sub_zero,List.drop_eq_nil_of_le (by simp only [List.length_ofFn];exact le_rfl)]
    rfl
  have step : NetEmits (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode)
      (x.1,(x.2.val,erasePack (F x.1 x.2.val)))) (fun x=>F x.1 (x.2.val+1)):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (K a)=>(x.1,(x.2.val,erasePack (F x.1 x.2.val))))
    have hLen:=hK.comp hx.fst
    let y : (Σa,Fin (K a))→(Σa,Fin (K a)):=fun x=>⟨x.1,⟨K x.1-(x.2.val+1),by have:=x.2.isLt;omega⟩⟩
    have hi:=(hLen.unaryNat.natSub (hx.snd.fst.unaryNat.natAdd (const _ _ 1))).boundedUnary hLen (fun _=>Nat.sub_le _ _)
    have hy : Emits _ (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) y:=
      (hi.pair hx.fst).recode (by intros;rfl)
    have hfields : NetEmits (fun z:Σx:Σa,Fin (K a),Fin (K x.1)=>prodCode unaryCode
        (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.val,erasePack (F x.1 x.2.val)))) (z.2.val,z.1))
        (fun z=>f z.1.1 z.2):=by
      have hz:=(BitStackProgram.Emits.id (prodCode unaryCode (prodCode ea (prodCode unaryCode packCode)))).precompose
        (fun z:Σx:Σa,Fin (K a),Fin (K x.1)=>(z.2.val,(z.1.1,(z.1.2.val,erasePack (F z.1.1 z.1.2.val)))))
      exact hf.compInput ((hz.fst.pair hz.snd.fst).recode (g:=fun z:Σx:Σa,Fin (K a),Fin (K x.1)=>(⟨z.1.1,z.2⟩ : Σa,Fin (K a))) (by intros;rfl))
    have hnew:=(ofCanonical hx.snd.snd).comp (childPushOneDrop (f:=fun x=>f x.1) (a:=fun x=>f (y x).1 (y x).2) (hk.comp hx.fst) (hw.comp hx.fst)
      hLen (hs.comp hx.fst) (hLen.unaryNat.natSub hx.snd.fst.unaryNat) (hf.compInput hy) hfields)
    convert hnew using 1
    funext x
    dsimp only [F]
    rw [dropOfFn_step _ x.2.isLt,BitArithmetic.ChildQueue.pushAll]
  have hwidth:=(hk.unaryPoly.add (hs.unaryPoly.mul hw.unaryPoly)).pull (fun x:Σa,Fin (K a+1)=>x.1)
  obtain ⟨p,hp⟩:=countPolyIndexed hK hf
  have hc : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>p.eval (ea x.1).length):=⟨p,fun _=>le_rfl⟩
  have hS:=hs.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hW:=hw.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hL:=hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hone:=(((hc.add ((PolyAt.const _ 49).mul hW)).add (PolyAt.const _ 11)).add
    (hL.mul ((((PolyAt.const _ 2).mul hc).add ((PolyAt.const _ 96).mul hW)).add (PolyAt.const _ 25)))).add
    ((hS.mul hW).mul ((hc.add ((PolyAt.const _ 159).mul hW)).add (PolyAt.const _ 6))) |>.add
      ((PolyAt.const _ 7).mul (hS.mul hW))
  have hb : NetworkAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>F x.1 x.2.val):=by
    exact (hL.mul hone).of_le (by
      intro x
      have h:=BitArithmetic.ChildQueue.pushAll_count (s x.1) ((List.ofFn (f x.1)).drop (K x.1-x.2.val))
        (c:=p.eval (ea x.1).length) (by
          intro b hb
          obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hb)
          exact hp ⟨x.1,i⟩)
      have hl:((List.ofFn (f x.1)).drop (K x.1-x.2.val)).length≤K x.1:=by
        simp only [List.length_drop,List.length_ofFn];omega
      exact h.trans (Nat.mul_le_mul hl (BitArithmetic.ChildQueue.oneBound_mono _ _ _ hl)))
  simpa only [F,Nat.sub_self,List.drop_zero] using boundedStages hK h0 step hwidth hwidth hb
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeMachineEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NodeMachineEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
lemma width (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(M x).width (t x)):=
  (hc.unaryAdd (ht.unaryMul (((hk.unaryAdd hi).unaryAdd hc).unaryAdd hu))).congr
    (fun x=>((M x).width_eq (t x)).symm)
lemma current (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).currentNet (t x)):=by
  have ht':=(ht.unaryNat.natSub (const _ _ 1)).boundedUnary ht (by intro x;exact Nat.sub_le _ _)
  have hs:=((ht.unaryNat.natEq (const _ _ 0)).ite (const _ Nat.bits 0)
    (((width hc hk hi hu ht').unaryNat.natAdd hk.unaryNat).natAdd hi.unaryNat))
  apply selectSlice (width hc hk hi hu ht) hc hs (fun x=>(M x).current (t x))
  intro x i
  cases h : t x with
  | zero=>simp only [NodeMachine.current,decide_true,ite_true,Nat.zero_add];rfl
  | succ j=>simp only [Nat.succ_ne_zero,decide_false,Nat.add_sub_cancel,NodeMachine.current];rfl
lemma init (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hK : NetEmits ea (fun x=>NodeKernel.initialNet (n x)))
    (hQ : NetEmits ea (fun x=>(M x).query)) (hU : NetEmits ea (fun x=>(M x).update))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).initNet (t x)):=
  ((current hc hk (hQ.count.unaryAdd hK.count) hU.count ht).comp hQ).comp hK
lemma update (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hK : NetEmits ea (fun x=>NodeKernel.initialNet (n x)))
    (hQ : NetEmits ea (fun x=>(M x).query)) (hU : NetEmits ea (fun x=>(M x).update))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).updateNet (t x)):=by
  have hi:=hQ.count.unaryAdd hK.count
  have hw:=width hc hk hi hU.count ht
  exact (((firstSelect hw hk hi).comp (current hc hk hi hU.count ht)).pair
    (targetSelect hw hk hi)).comp hU
lemma program (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hK : NetEmits ea (fun x=>NodeKernel.initialNet (n x)))
    (hP : OpsEmits ea (fun x=>NodeKernel.program (n x)))
    (hQ : NetEmits ea (fun x=>(M x).query)) (hU : NetEmits ea (fun x=>(M x).update))
    (ht : Emits ea unaryCode t) : OpsEmits ea (fun x=>(M x).program (t x)):=by
  have hi:=hQ.count.unaryAdd hK.count
  have hu:=hU.count
  apply OpsEmits.boundedStages ht (f:=fun x j=>(M x).program j)
  · exact const _ _ []
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode opCode)))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,((M x.1).program x.2.val).map eraseOp)))
    have hC:=hc.comp hx.fst
    have hKW:=hk.comp hx.fst
    have hKI:=hK.compInput hx.fst
    have hQuery:=hQ.compInput hx.fst
    have hUpdate:=hU.compInput hx.fst
    have hTime:=hx.snd.fst
    have hWidth:=width hC hKW (hi.comp hx.fst) (hu.comp hx.fst) hTime
    exact ((OpsEmits.appendPrepared hx.snd.snd (init hC hKW hKI hQuery hUpdate hTime)
      hWidth (fun x=>((M x.1).initNet_count x.2.val).le) (hP.comp hx.fst)).first
        (fun x=>c x.1) (fun x=>(M x.1).updateWork)).append
      (OpsEmits.oracleOn (update hC hKW hKI hQuery hUpdate hTime)
        (fun x=>((M x.1).updateNet_count x.2.val).le))
  · have hb:=(width hc hk hi hu ht).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    exact hb.of_le (by
      intro x
      rw [(M _).width_eq,(M _).width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · have htime:=ht.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hlen:=(hP.lengthPoly).pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hinit:=hi.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hupdate:=hu.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hkernel:=hk.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hconfig:=hc.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    exact (htime.mul (((((PolyAt.const _ 4).mul hinit).add ((PolyAt.const _ 2).mul hkernel)).add hlen).add
      ((PolyAt.const _ 4).mul hupdate) |>.add ((PolyAt.const _ 2).mul hconfig))).of_le (by
        intro x
        exact ((M x.1).program_length x.2.val).trans (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)))
lemma initial (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).initialNet (t x)):=by
  apply NetEmits.boundedStages ht (f:=fun x j=>(M x).initialNet j)
  · exact identity hc
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,erasePack ((M x.1).initialNet x.2.val))))
    have hprev:=ofCanonical hx.snd.snd
    have hC:=hc.comp hx.fst
    have hKW:=hk.comp hx.fst
    exact ((hprev.packNet (zeros hC hKW) hC (hi.comp hx.fst)).packNet (zeros hC hC) hC (hu.comp hx.fst))
  · exact hc.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
  · exact ((width hc hk hi hu ht).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by
      intro x;rw [(M _).width_eq,(M _).width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · have hb:=(ht.unaryPoly.mul (((hk.unaryPoly.add hi.unaryPoly).add hc.unaryPoly).add hu.unaryPoly)).pull
      (fun x:Σa,Fin (t a+1)=>x.1)
    exact hb.of_le (by
      intro x
      rw [(M _).initialNet_count]
      exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
end ExactQuantumFactoring.NodeMachineEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalTreeEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma capacity (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.capacity (n x)):=
  ((const _ _ 2).unaryMul (hn.unaryPow 2)).unarySucc
lemma configWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.configWidth (n x)):=(capacity hn).unaryMul hn
lemma query (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.query (n x)):=
  blockNet (capacity hn) hn (fun _=>0) (const _ _ 0)
lemma nodeResult (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.nodeResult (n x)):=
  (PhysicalNodeEmission.current hn ((const _ _ 2).unaryMul hn) ((const _ _ 2).unaryMul hn)).comp
    (PhysicalNodeEmission.sortedOutput hn)
lemma fields (hn : Emits ea unaryCode n) : NetEmits
    (fun x:Σa,Fin (n a)=>prodCode unaryCode ea (x.2.val,x.1))
    (fun x=>(PhysicalTree.nodeResult (n x.1)).comp (ExactQuantumFactoring.tensorSelect (n x.1) (n x.1) x.2)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact (nodeResult hN).comp (NetEmits.tensorSelect hN hN (fun x=>x.2) hx.fst.unaryNat)
lemma old (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.old (n x)):=
  left (configWidth hn) (PhysicalNodeEmission.kernelWidth hn)
lemma localNode (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.localNode (n x)):=
  right (configWidth hn) (PhysicalNodeEmission.kernelWidth hn)
lemma pushed (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.pushed (n x)):=
  (((localNode hn).pair ((old hn).comp (stackPop (capacity hn) hn))).comp
    (childPushAll (PhysicalNodeEmission.kernelWidth hn) hn hn (capacity hn) (fields hn))).comp
      (right (PhysicalNodeEmission.kernelWidth hn) (configWidth hn))
lemma update (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.update (n x)):=
  (zeroWord ((configWidth hn).unaryAdd (PhysicalNodeEmission.kernelWidth hn)) hn ((old hn).comp (query hn))).wordMux (old hn) (pushed hn) (configWidth hn)
lemma initWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>(PhysicalTree.machine (n x)).initWork):=
  (query hn).count.unaryAdd (PhysicalNodeEmission.kernelInitial hn).count
lemma updateWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>(PhysicalTree.machine (n x)).updateWork):=(update hn).count
lemma machineWidth (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(PhysicalTree.machine (n x)).width (t x)):=
  NodeMachineEmission.width (configWidth hn) (PhysicalNodeEmission.kernelWidth hn) (initWork hn) (updateWork hn) ht
lemma machineInitial (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalTree.machine (n x)).initialNet (t x)):=
  NodeMachineEmission.initial (configWidth hn) (PhysicalNodeEmission.kernelWidth hn) (initWork hn) (updateWork hn) ht
lemma machineProgram (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : OpsEmits ea (fun x=>(PhysicalTree.machine (n x)).program (t x)):=
  NodeMachineEmission.program (configWidth hn) (PhysicalNodeEmission.kernelWidth hn) (PhysicalNodeEmission.kernelInitial hn)
    (PhysicalNodeEmission.kernelProgram hn) (query hn) (update hn) ht
lemma start (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.startNet (n x)):=
  stackPush hn (capacity hn) hn (identity hn) (zeros hn (configWidth hn))
lemma steps (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.steps (n x)):=(const _ _ 2).unaryMul (hn.unaryPow 2)
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.width (n x)):=machineWidth hn (steps hn)
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.initialNet (n x)):=(start hn).comp (machineInitial hn (steps hn))
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>(PhysicalTree.machine (n x)).program (PhysicalTree.steps (n x))):=machineProgram hn (steps hn)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreePreparationEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma launchWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.launchWork (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.launchWidth (n x)):=
  (hn.unaryAdd (width hn)).unaryAdd (launchWork hn)
lemma launchProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalTree.launchProgram (n x)):=
  OpsEmits.prepared (initial hn) hn (fun _=>le_rfl) (program hn)
lemma slots (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.slots (n x)):=
  (((hn.unaryPow 5).unarySucc).unaryMul ((const _ _ 2).unaryMul hn)).unaryMul ((const _ _ 2).unaryMul (hn.unaryPow 2))
lemma padding (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.padding (n x)):=
  ((hn.unaryPow 10).unaryNat.natSub (slots hn).unaryNat).boundedUnary (hn.unaryPow 10) (fun _=>Nat.sub_le _ _)
lemma paddedWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.paddedWidth (n x)):=
  (launchWidth hn).unaryAdd (hn.tensorWidth (padding hn))
lemma padProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalTree.padProgram (n x)):=
  (OpsEmits.hadamards hn (fun _=>le_rfl)).tensor hn (padding hn)
lemma paddedProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalTree.paddedProgram (n x)):=
  OpsEmits.parallel (launchProgram hn) (padProgram hn) (launchWidth hn)
lemma quarterWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.quarterWidth (n x)):=
  completionWidth (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma quarterProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalTree.quarterProgram (n x)):=
  OpsEmits.completion (paddedProgram hn) (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma launchHistory (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.launchHistory (n x)):=
  targetSelect hn (width hn) (launchWork hn)
lemma launchInput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.launchInput (n x)):=
  firstSelect hn (width hn) (launchWork hn)
lemma paddedHistory (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.paddedHistory (n x)):=
  (left (launchWidth hn) (hn.tensorWidth (padding hn))).comp (launchHistory hn)
lemma paddedInput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.paddedInput (n x)):=
  (left (launchWidth hn) (hn.tensorWidth (padding hn))).comp (launchInput hn)
lemma paddedPad (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.paddedPad (n x)):=
  right (launchWidth hn) (hn.tensorWidth (padding hn))
lemma padFlag (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.padFlag (n x)):=by
  apply allOfFn (hn.tensorWidth (padding hn)) (padding hn)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (PhysicalTree.padding (n a))=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact (zeroWord (hN.tensorWidth (padding hN)) hN (NetEmits.tensorSelect hN (padding hN) (fun x=>x.2) hx.fst.unaryNat)).bnot
lemma quarterOrd (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterOrd (n x)):=
  ordinaryWires (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma quarterGuess (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterGuess (n x)):=
  guessWires (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma quarterCoin (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterCoin (n x)):=
  retentionWires (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma quarterRare (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterRare (n x)):=
  rareNet (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeHistoryEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma previous (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalTree.machine (n x)).previousNet (t x)):=
  (firstSelect (((machineWidth hn ht).unaryAdd (PhysicalNodeEmission.kernelWidth hn)).unaryAdd (initWork hn))
    (configWidth hn) (updateWork hn)).comp (firstSelect (machineWidth hn ht) (PhysicalNodeEmission.kernelWidth hn) (initWork hn))
lemma lastNode (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalTree.machine (n x)).lastNodeNet (t x)):=
  (firstSelect (((machineWidth hn ht).unaryAdd (PhysicalNodeEmission.kernelWidth hn)).unaryAdd (initWork hn))
    (configWidth hn) (updateWork hn)).comp (targetSelect (machineWidth hn ht) (PhysicalNodeEmission.kernelWidth hn) (initWork hn))
lemma firstNode (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalTree.machine (n x)).firstNodeNet (t x)):=by
  apply boundedStages ht (f:=fun x j=>(PhysicalTree.machine (n x)).firstNodeNet j)
  · exact lastNode hn (const _ _ 0)
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,erasePack ((PhysicalTree.machine (n x.1)).firstNodeNet x.2.val))))
    exact (previous (hn.comp hx.fst) hx.snd.fst.unarySucc).comp (ofCanonical hx.snd.snd)
  · exact ((machineWidth hn ht.unarySucc).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by
      intro x;rw [NodeMachine.width_eq,NodeMachine.width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · exact (PhysicalNodeEmission.kernelWidth hn).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
  · exact (PolyAt.const _ 0).of_le (fun x=>by rw [NodeMachine.firstNodeNet_count])
lemma flattenWords (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.flattenWords (n x)):=by
  apply wordBlocks (hn.tensorWidth hn) hn hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact NetEmits.tensorSelect hN hN (fun x=>x.2) hx.fst.unaryNat
lemma rootFlat (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>PhysicalTree.rootFlat (n x) (t x)):=by
  apply NetEmits.splitOn (fun x=>t x=0) (ht.unaryNat.natEq (const _ _ 0))
  · let inc:{x:α // t x=0}→α:=Subtype.val
    have hN:=hn.precompose inc
    have h:=(zeros (configWidth hN) (hN.unaryMul hN))
    obtain ⟨p,hp,he⟩:=h
    refine ⟨p,hp,?_⟩
    intro x
    have hx : t x.val=0:=x.property
    have hh:=he x
    dsimp only [inc] at hh
    change (p x).val.value=erase (PhysicalTree.rootFlat (n x.val) (t x.val))
    rw [hx]
    exact hh
  · let inc:{x:α // ¬t x=0}→α:=Subtype.val
    have hN:=hn.precompose inc
    have hT:=ht.precompose inc
    have hg:=(hT.unaryNat.natSub (const _ _ 1)).boundedUnary hT (fun _=>Nat.sub_le _ _)
    have h:=((firstNode hN hg).comp (nodeResult hN)).comp (flattenWords hN)
    obtain ⟨p,hp,he⟩:=h
    refine ⟨p,hp,?_⟩
    intro x
    have hx : t x.val=(t x.val-1)+1:=by have:=x.property;omega
    have hh:=he x
    dsimp only [inc] at hh
    change (p x).val.value=erase (PhysicalTree.rootFlat (n x.val) (t x.val))
    conv_rhs => rw [hx]
    exact hh
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeVerificationEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma current (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea
    (fun x=>(PhysicalTree.machine (n x)).currentNet (t x)):=
  NodeMachineEmission.current (configWidth hn) (PhysicalNodeEmission.kernelWidth hn) (initWork hn) (updateWork hn) ht
lemma rowQuery (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea
    (fun x=>(PhysicalTree.machine (n x)).rowQuery (t x)):=
  ((previous hn ht).comp (current hn ht)).comp (query hn)
lemma rowFields (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits
    (fun x:Σa,Fin (n a)=>prodCode unaryCode ea (x.2.val,x.1))
    (fun x=>(PhysicalTree.machine (n x.1)).rowFields (t x.1) x.2):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  exact (lastNode (hn.comp hx.snd) (ht.comp hx.snd)).comp (fields hn)
lemma rowVerified (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea
    (fun x=>(PhysicalTree.machine (n x)).rowVerifiedNet (t x)):=
  (zeroWord (machineWidth hn ht.unarySucc) hn (rowQuery hn ht)).bor
    (factorVerifier (machineWidth hn ht.unarySucc) hn (rowQuery hn ht) (rowFields hn ht))
lemma verified (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea
    (fun x=>(PhysicalTree.machine (n x)).verifiedNet (t x)):=by
  apply boundedStages ht (f:=fun x j=>(PhysicalTree.machine (n x)).verifiedNet j)
  · exact constant (configWidth hn) (const _ _ true)
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,erasePack ((PhysicalTree.machine (n x.1)).verifiedNet x.2.val))))
    exact ((previous (hn.comp hx.fst) hx.snd.fst).comp (ofCanonical hx.snd.snd)).band (rowVerified (hn.comp hx.fst) hx.snd.fst)
  · exact ((machineWidth hn ht).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by
      intro x;rw [NodeMachine.width_eq,NodeMachine.width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · exact PolyAt.const _ 1
  · exact NodeMachine.verifiedNet_at (hn.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1))
      ((ht.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by intro x;have:=x.2.isLt;omega))
      ((query hn).countPoly.pull (fun x:Σa,Fin (t a+1)=>x.1))
lemma guessVerifier (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>ExactQuantumFactoring.guessVerifier (n x)):=by
  apply factorVerifier (hn.unaryAdd (hn.unaryMul hn)) hn (left hn (hn.unaryMul hn))
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact selectSlice (hN.unaryAdd (hN.unaryMul hN)) hN (hN.unaryNat.natAdd (hN.unaryNat.natMul hx.fst.unaryNat)) _
    (by intro x j;change n x.1 + (j.val+n x.1*x.2.val)=n x.1+n x.1*x.2.val+j.val;omega)
lemma quarterGuessFlag (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterGuessFlag (n x)):=
  (((quarterOrd hn).comp (paddedInput hn)).pair (quarterGuess hn)).comp (guessVerifier hn)
lemma paddedOutput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.paddedOutputNet (n x)):=
  (paddedHistory hn).comp (rootFlat hn (steps hn))
lemma quarterOutput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterOutputNet (n x)):=
  completionOutput (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11) (paddedOutput hn)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeTableEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emission
open BitStackProgram BitStackProgram.Procedure
abbrev rowCode := prodCode packCode packCode
def compRow (a : Pack) (r : Pack×Pack) : Pack×Pack:=(canonicalPack (compPack a r.1),canonicalPack (compPack a r.2))
noncomputable def compRowP : Procedure (prodCode packCode rowCode) rowCode (fun x=>compRow x.1 x.2):=by
  let a:=first packCode rowCode
  let r:=second packCode rowCode
  let b:=(first packCode packCode).comp r
  let c:=(second packCode packCode).comp r
  exact (canonicalPackP.comp (compPackP.comp (a.pair b))).pair (canonicalPackP.comp (compPackP.comp (a.pair c)))
lemma compRow_erase {k m n p : ℕ} (a : BooleanNetwork k m) (r : BooleanNetwork m n×BooleanNetwork m p) :
    compRow (erasePack a) (erasePack r.1,erasePack r.2)=(erasePack (a.comp r.1),erasePack (a.comp r.2)):=by
  apply Prod.ext <;> exact canonicalPack_erase _ _ (compPack_spec _ _ _ _ rfl rfl)
end ExactQuantumFactoring.NetworkEmission.Emission
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
def packedLog (n t : ℕ) : List (Pack×Pack):=
  ((PhysicalTree.machine n).logNets t).map (fun r=>(erasePack r.1,erasePack r.2))
lemma logCode_bound (n T j : ℕ) (hj : j≤T) :
    (listCode Emission.rowCode (packedLog n j)).length≤
      T*(8*(104*((PhysicalTree.machine n).width T+PhysicalNode.resultBound n+n+tensorWidth n n+1)^2)+4)+1:=by
  let B:=104*((PhysicalTree.machine n).width T+PhysicalNode.resultBound n+n+tensorWidth n n+1)^2
  have hw:(PhysicalTree.machine n).width j≤(PhysicalTree.machine n).width T:=by
    rw [NodeMachine.width_eq,NodeMachine.width_eq]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
  have h:=NativeAIG.listCode_length_bound Emission.rowCode (packedLog n j) (4*B+1) (by
    intro r hr
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr
    have hc:=(PhysicalTree.machine n).logNets_counts j a ha
    have hq:(PhysicalTree.machine n).query.net.count=0:=PreparationPolynomial.treeQuery_count n
    rw [hq] at hc
    have h1: (packCode (erasePack a.1)).length≤B:=by
      have h:=packCode_bound (erasePack a.1)
      change _ ≤104*((PhysicalTree.machine n).width j+a.1.net.count+n+1)^2 at h
      exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    have h2: (packCode (erasePack a.2)).length≤B:=by
      have h:=packCode_bound (erasePack a.2)
      change _ ≤104*((PhysicalTree.machine n).width j+a.2.net.count+tensorWidth n n+1)^2 at h
      exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    simp only [Emission.rowCode,prodCode,pairBits_length]
    omega)
  have hl:(packedLog n j).length=j:=by simp only [packedLog,List.length_map,NodeMachine.logNets_length]
  rw [hl] at h
  calc
    _ ≤ j*(2*(4*B+1)+2)+1:=h
    _ ≤ T*(8*B+4)+1:=by nlinarith
lemma logCode_poly {len : α→ℕ} (hn : PolyAt len n) (ht : PolyAt len t)
    (hw : PolyAt len (fun x=>(PhysicalTree.machine (n x)).width (t x))) :
    PolyAt (fun x:Σa,Fin (t a+1)=>len x.1)
      (fun x=>(listCode Emission.rowCode (packedLog (n x.1) x.2.val)).length):=by
  have hT:=ht.pull (fun x:Σa,Fin (t a+1)=>x.1)
  have hN:=hn.pull (fun x:Σa,Fin (t a+1)=>x.1)
  have hW:=hw.pull (fun x:Σa,Fin (t a+1)=>x.1)
  have hr:=PolyAt.comp PreparationPolynomial.physicalResultBound hN
  have hB:=((PolyAt.const _ 104).mul ((((hW.add hr).add hN).add (hN.mul hN) |>.add (PolyAt.const _ 1)).pow 2))
  apply ((hT.mul (((PolyAt.const _ 8).mul hB).add (PolyAt.const _ 4))).add (PolyAt.const _ 1)).of_le
  intro x
  simpa only [tensorWidth_eq] using logCode_bound (n x.1) (t x.1) x.2.val (Nat.le_of_lt_succ x.2.isLt)
lemma logNets (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) :
    Emits ea (listCode Emission.rowCode) (fun x=>packedLog (n x) (t x)):=by
  let F:=fun x j=>packedLog (n x) j
  apply stages ht (F:=F)
  · exact const _ _ []
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode Emission.rowCode)))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,F x.1 x.2.val)))
    have hN:=hn.comp hx.fst
    have hj:=hx.snd.fst
    have hp:=(previous hN hj).canonical
    have hnw:=(rowQuery hN hj).canonical.pair ((lastNode hN hj).comp (nodeResult hN)).canonical
    have hm:=(ofProcedure (Procedure.listMapWith (emptyPack,emptyPack) (emptyPack,emptyPack) Emission.compRowP)).comp (hp.pair hx.snd.snd)
    exact (hnw.listCons hm).congr (by
      intro x
      dsimp only [F,packedLog]
      simp only [NodeMachine.logNets,List.map_cons,List.map_map,Function.comp_def,Emission.compRow_erase])
  · exact logCode_poly hn.unaryPoly ht.unaryPoly (machineWidth hn ht).unaryPoly

end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableNetsEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma tableFactor {a p : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (ha : NetEmits ea a) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.tableFactor (a x) (p x)):=by
  exact wordMux ((zeroWord hk hn ha).bor (zeroWord hk hn hp)) (wordConst hk hn (const _ _ 2)) hp hn
lemma tableRow {a : ∀x,BooleanNetwork (k x) (n x)} {b : ∀x,BooleanNetwork (k x) (tensorWidth (n x) (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetsEmits ea (fun x=>List.ofFn (fun i:Fin (n x)=>BitArithmetic.tableFactor (a x) ((b x).comp (ExactQuantumFactoring.tensorSelect (n x) (n x) i)))):=by
  apply NetsEmits.ofFn hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact tableFactor (hk.comp hx.snd) hN (ha.compInput hx.snd)
    ((hb.compInput hx.snd).comp (NetEmits.tensorSelect hN hN (fun x=>x.2) hx.fst.unaryNat))
end ExactQuantumFactoring.NetworkEmission.NetEmits
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma logGet (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) :
    Emits (fun x:Σa,Fin (((PhysicalTree.machine (n a)).logNets (t a)).length)=>prodCode unaryCode ea (x.2.val,x.1))
      Emission.rowCode (fun x=>let r:=((PhysicalTree.machine (n x.1)).logNets (t x.1)).get x.2
        (erasePack r.1,erasePack r.2)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (((PhysicalTree.machine (n a)).logNets (t a)).length)=>(x.2.val,x.1))
  have h:=(ofProcedure (Procedure.listGet Emission.rowCode (emptyPack,emptyPack))).comp
    (hx.fst.unaryNat.pair ((logNets hn ht).comp hx.snd))
  exact h.congr (by
    intro x
    simp only [packedLog,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_map,
      List.getElem?_eq_getElem x.2.isLt,Option.map_some,Option.getD_some,List.get_eq_getElem])
lemma tableNets (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetsEmits ea
    (fun x=>BitArithmetic.tableNets ((PhysicalTree.machine (n x)).fieldRows (t x))):=by
  let L:=fun x=>(PhysicalTree.machine (n x)).logNets (t x)
  have hl : Emits ea unaryCode (fun x=>(L x).length):=ht.congr (fun x=>(NodeMachine.logNets_length ..).symm)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((L a).length)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  have hT:=ht.comp hx.snd
  have hq:=NetEmits.ofCanonical (logGet hn ht).fst
  have hr:=NetEmits.ofCanonical (logGet hn ht).snd
  have hrows:=NetEmits.tableRow (machineWidth hN hT) hN hq hr
  exact (NetsEmits.concat (f:=fun x i=>List.ofFn (fun j:Fin (n x)=>BitArithmetic.tableFactor ((L x).get i).1 (((L x).get i).2.comp (ExactQuantumFactoring.tensorSelect (n x) (n x) j)))) hl hrows).congrList (by
    intro x
    simp only [BitArithmetic.tableNets,NodeMachine.fieldRows,List.flatMap_map,Function.comp_def,List.map_ofFn]
    rw [List.flatMap_def]
    congr 1
    conv_rhs=>rw [←List.ofFn_get ((PhysicalTree.machine (n x)).logNets (t x)),List.map_ofFn]
    rfl)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableScanEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {k w : α→ℕ}
lemma natSubOn {a b : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k)
    (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>BitArithmetic.natSubOn (a x) (b x)):=
  (wordLe hb ha hw).wordMux ((ha.pair hb).comp (sub hw)) (wordConst hk hw (const _ _ 0)) hw
lemma stripOn {a m q v : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k)
    (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hm : NetEmits ea m)
    (hq : NetEmits ea q) (hv : NetEmits ea v) :
    NetEmits ea (fun x=>BitArithmetic.stripOn (a x) (m x) (q x) (v x)):=by
  have hd:=(hv.pair hq).comp (div hw)
  exact ((((hv.pair hq).comp (mod hw)).equalOn (wordConst hk hw (const _ _ 0)) hw).band
    ((TrialControlEmission.powOn hw ha hm hd).equalOn (wordConst hk hw (const _ _ 1)) hw)).wordMux hd hv hw
lemma stripUpdate {a m q : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k)
    (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hm : NetEmits ea m) (hq : NetEmits ea q) :
    NetEmits ea (fun x=>BitArithmetic.stripUpdate (a x) (m x) (q x)):=by
  have hl:=left hk hw
  exact hl.pair (stripOn (hk.unaryAdd hw) hw (hl.comp ha) (hl.comp hm) (hl.comp hq) (right hk hw))
lemma stripScan {a m : ∀x,BooleanNetwork (k x) (w x)} {qs : ∀x,List (BooleanNetwork (k x) (w x))}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hm : NetEmits ea m)
    (hq : NetsEmits ea qs) : NetEmits ea (fun x=>BitArithmetic.stripScan (a x) (m x) (qs x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((qs a).length)=>(x.2.val,x.1))
  have hmap:=hq.map (g:=fun x q=>BitArithmetic.stripUpdate (a x) (m x) q) (stripUpdate (hk.comp hx.snd) (hw.comp hx.snd) (ha.compInput hx.snd) (hm.compInput hx.snd) hq.get)
  exact (hmap.sequence (hk.unaryAdd hw)).congr (by
    intro x
    generalize qs x=l
    induction l with
    | nil=>rfl
    | cons q qs ih=>simp only [List.map_cons,BooleanNetwork.sequence,BitArithmetic.stripScan,ih])
lemma orderFromList {a m : ∀x,BooleanNetwork (k x) (w x)} {qs : ∀x,List (BooleanNetwork (k x) (w x))}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hm : NetEmits ea m)
    (hq : NetsEmits ea qs) : NetEmits ea (fun x=>BitArithmetic.orderFromList (a x) (m x) (qs x)):=
  (((identity hk).pair (hq.product hk hw)).comp (stripScan hk hw ha hm hq)).comp (right hk hw)
lemma totientPair {q v a : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k)
    (hw : Emits ea unaryCode w) (hq : NetEmits ea q) (hv : NetEmits ea v) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.totientPair (q x) (v x) (a x)):=by
  have hd:=(hv.pair hq).comp (div hw)
  have hc:=zeroWord hk hw ((hv.pair hq).comp (mod hw))
  have hweight:=(zeroWord hk hw ((hd.pair hq).comp (mod hw))).wordMux hq
    (natSubOn hk hw hq (wordConst hk hw (const _ _ 1))) hw
  exact (hc.wordMux hd hv hw).pair (hc.wordMux ((ha.pair hweight).comp (mul hw)) ha hw)
lemma totientUpdate {q : ∀x,BooleanNetwork (k x) (w x)} (hk : Emits ea unaryCode k)
    (hw : Emits ea unaryCode w) (hq : NetEmits ea q) :
    NetEmits ea (fun x=>BitArithmetic.totientUpdate (q x)):=by
  have hl:=left hk (hw.unaryAdd hw)
  have hv:=selectSlice (hk.unaryAdd (hw.unaryAdd hw)) hw hk.unaryNat
    (fun x i=>Fin.natAdd (k x) (Fin.castAdd (w x) i)) (by intros;rfl)
  have ha:=selectSlice (hk.unaryAdd (hw.unaryAdd hw)) hw (hk.unaryNat.natAdd hw.unaryNat)
    (fun x i=>Fin.natAdd (k x) (Fin.natAdd (w x) i)) (by intros;simp only [Fin.val_natAdd];omega)
  exact hl.pair (totientPair (hk.unaryAdd (hw.unaryAdd hw)) hw (hl.comp hq) hv ha)
lemma totientScan {qs : ∀x,List (BooleanNetwork (k x) (w x))}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hq : NetsEmits ea qs) :
    NetEmits ea (fun x=>BitArithmetic.totientScanNet (qs x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((qs a).length)=>(x.2.val,x.1))
  have hmap:=hq.map (g:=fun _ q=>BitArithmetic.totientUpdate q) (totientUpdate (hk.comp hx.snd) (hw.comp hx.snd) hq.get)
  exact (hmap.sequence (hk.unaryAdd (hw.unaryAdd hw))).congr (by
    intro x
    generalize qs x=l
    induction l with
    | nil=>rfl
    | cons q qs ih=>simp only [List.map_cons,BooleanNetwork.sequence,BitArithmetic.totientScanNet,ih])
lemma totientFromList {v : ∀x,BooleanNetwork (k x) (w x)} {qs : ∀x,List (BooleanNetwork (k x) (w x))}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hv : NetEmits ea v) (hq : NetsEmits ea qs) :
    NetEmits ea (fun x=>BitArithmetic.totientFromList (v x) (qs x)):=by
  have ha:=selectSlice (hk.unaryAdd (hw.unaryAdd hw)) hw (hk.unaryNat.natAdd hw.unaryNat)
    (fun x i=>Fin.natAdd (k x) (Fin.natAdd (w x) i)) (by intros;simp only [Fin.val_natAdd];omega)
  exact (((identity hk).pair (hv.pair (wordConst hk hw (const _ _ 1)))).comp (totientScan hk hw hq)).comp ha
lemma primesPhi {v : ∀x,BooleanNetwork (k x) (w x)} {qs : ∀x,List (BooleanNetwork (k x) (w x))}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hv : NetEmits ea v) (hq : NetsEmits ea qs) :
    NetEmits ea (fun x=>BitArithmetic.primesPhiNet (v x) (qs x)):=
  totientFromList hk hw hv (NetsEmits.repeated hw hq)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableArithmeticEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetsEmits
variable {α : Type} {ea : α→List Bool} {k n w : α→ℕ}
lemma resize {ps : ∀x,List (BooleanNetwork (k x) (n x))} (hn : Emits ea unaryCode n)
    (hw : Emits ea unaryCode w) (hp : NetsEmits ea ps) :
    NetsEmits ea (fun x=>(ps x).map (fun p=>p.comp (BitArithmetic.resizeWord (n x) (w x)))):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((ps a).length)=>(x.2.val,x.1))
  exact hp.map (g:=fun x p=>p.comp (BitArithmetic.resizeWord (n x) (w x)))
    (hp.get.comp (NetEmits.resize (hn.comp hx.snd) (hw.comp hx.snd)))
lemma all {ps : ∀x,List (BooleanNetwork (k x) 1)} (hk : Emits ea unaryCode k)
    (hp : NetsEmits ea ps) : NetEmits ea (fun x=>BooleanNetwork.all (ps x)):=by
  exact (NetEmits.allOfFn hk hp.length hp.get).congr (fun x=>by rw [List.ofFn_get])
lemma any {ps : ∀x,List (BooleanNetwork (k x) 1)} (hk : Emits ea unaryCode k)
    (hp : NetsEmits ea ps) : NetEmits ea (fun x=>BooleanNetwork.any (ps x)):=by
  exact (NetEmits.anyOfFn hk hp.length hp.get).congr (fun x=>by rw [List.ofFn_get])
end NetsEmits
namespace NetEmits
open BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma tableOrderWidth {f : α→ℕ} (hn : Emits ea unaryCode n) (hf : Emits ea unaryCode f) :
    Emits ea unaryCode (fun x=>BitArithmetic.tableOrderWidth (n x) (f x)):=
  ((hn.unaryMul (hn.unaryMul hf)).unaryAdd hn).unarySucc
lemma tableOrder {rows : ∀x,List (BooleanNetwork (k x) (n x)×List (BooleanNetwork (k x) (n x)))}
    {a m : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hp : NetsEmits ea (fun x=>BitArithmetic.tableNets (rows x))) :
    NetEmits ea (fun x=>BitArithmetic.tableOrder (a x) (m x) (rows x)):=by
  have hw:=tableOrderWidth hn hp.length
  exact (orderFromList hk hw (ha.comp (resize hn hw)) (hm.comp (resize hn hw))
    (NetsEmits.repeated hn (hp.resize hn hw))).comp (resize hw hn)
lemma tableTotient {rows : ∀x,List (BooleanNetwork (k x) (n x)×List (BooleanNetwork (k x) (n x)))}
    {v : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (hv : NetEmits ea v) (hp : NetsEmits ea (fun x=>BitArithmetic.tableNets (rows x))) :
    NetEmits ea (fun x=>BitArithmetic.tableTotient (v x) (rows x)):=
  totientFromList hk hn hv (NetsEmits.repeated hn hp)
lemma componentWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>BitArithmetic.componentWidth (n x)):=
  (hn.unaryMul hn).unarySucc
lemma primeComponent {m p : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.primeComponent (m x) (p x)):=by
  have hw:=componentWidth hn
  exact (((hm.comp (resize hn hw)).pair ((NetsEmits.replicate hn (hp.comp (resize hn hw))).product hk hw)).comp
    (gcd hw)).comp (resize hw hn)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CanonicalTableEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma dividesOn {p m : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (hp : NetEmits ea p) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>BitArithmetic.dividesOn (p x) (m x)):=zeroWord hk hn ((hm.pair hp).comp (mod hn))
lemma leastDivisorTest {ps : ∀x,List (BooleanNetwork (k x) (n x))} {m p : ∀x,BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hps : NetsEmits ea ps)
    (hm : NetEmits ea m) (hp : NetEmits ea p) : NetEmits ea (fun x=>BitArithmetic.leastDivisorTest (ps x) (m x) (p x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((ps a).length)=>(x.2.val,x.1))
  have ht:=(dividesOn (hk.comp hx.snd) (hn.comp hx.snd) hps.get (hm.compInput hx.snd)).bnot.bor
    (wordLe (hp.compInput hx.snd) hps.get (hn.comp hx.snd))
  exact (hps.map (g:=fun x q=>(BitArithmetic.dividesOn q (m x)).bnot.bor (BitArithmetic.wordLe (p x) q)) ht).all hk
lemma componentCongruence {ps : ∀x,List (BooleanNetwork (k x) (n x))} {a m p : ∀x,BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hps : NetsEmits ea ps)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.componentCongruence (ps x) (a x) (m x) (p x)):=by
  have hq:=primeComponent hk hn hm hp
  have h1:=wordConst hk hn (const _ _ 1)
  exact ((ha.pair hq).comp (mod hn)).equalOn
    ((leastDivisorTest hk hn hps hm hp).wordMux h1 (natSubOn hk hn hq h1) hn) hn
lemma tableCanonical {ps : ∀x,List (BooleanNetwork (k x) (n x))} {a m : ∀x,BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hps : NetsEmits ea ps)
    (ha : NetEmits ea a) (hm : NetEmits ea m) : NetEmits ea (fun x=>BitArithmetic.tableCanonicalNet (ps x) (a x) (m x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((ps a).length)=>(x.2.val,x.1))
  have hm':=hm.compInput hx.snd
  have ht:=(dividesOn (hk.comp hx.snd) (hn.comp hx.snd) hps.get hm').bnot.bor
    (componentCongruence (hk.comp hx.snd) (hn.comp hx.snd) (hps.comp hx.snd) (ha.compInput hx.snd) hm' hps.get)
  exact (wordLt ha hm hn).band ((hps.map (g:=fun x p=>(BitArithmetic.dividesOn p (m x)).bnot.bor
    (BitArithmetic.componentCongruence (ps x) (a x) (m x) p)) ht).all hk)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ComponentLevelEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n t : α→ℕ}
lemma oddPart {a : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (ha : NetEmits ea a) : NetEmits ea (fun x=>BitArithmetic.oddPartNet (a x)):=
  (ha.pair (primeComponent hk hn ha (wordConst hk hn (const _ _ 2)))).comp (div hn)
lemma closedLevel {a : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.closedLevelNet (a x) (t x)):=by
  have ht':=(ht.unaryNat.natSub (const _ _ 1)).boundedUnary ht (fun _=>Nat.sub_le ..)
  have hb:=((ha.comp (divides hn (Emits.powTwo ht))).wordMux
    (((oddPart hk hn ha).pair (wordConst hk hn (Emits.powTwo ht'))).comp (mul hn))
    (wordConst hk hn (const _ _ 0)) hn)
  have h:=ite (ht.unaryNat.natEq (const _ _ 0)) (oddPart hk hn ha)
    (ite (ht.unaryNat.natLt hn.unaryNat) hb (wordConst hk hn (const _ _ 0)))
  exact h.congr (by intro x;simp only [decide_eq_true_eq];rfl)
lemma componentPhi {m p : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.componentPhiNet (m x) (p x)):=by
  have hq:=primeComponent hk hn hm hp
  exact natSubOn hk hn hq ((hq.pair hp).comp (div hn))
lemma componentLevel {m p : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.componentLevelNet (m x) (p x) (t x)):=
  (dividesOn hk hn hp hm).wordMux (closedLevel hk hn ht (componentPhi hk hn hm hp))
    (wordConst hk hn (const _ _ 1)) hn
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/DistinctProductEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetsEmits
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma drop {a : α→ℕ} {ps : ∀x,List (BooleanNetwork (k x) (n x))}
    (ha : Emits ea Nat.bits a) (hp : NetsEmits ea ps) : NetsEmits ea (fun x=>(ps x).drop (a x)):=by
  exact ((ofProcedure (Procedure.listDrop packCode)).comp (ha.pair hp)).congr
    (fun x=>(List.map_drop ..).symm)
end NetsEmits
namespace NetEmits
open BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n K : α→ℕ}
lemma occursLater {p : ∀x,BooleanNetwork (k x) (n x)} {ps : ∀x,List (BooleanNetwork (k x) (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hp : NetEmits ea p) (hps : NetsEmits ea ps) :
    NetEmits ea (fun x=>BitArithmetic.occursLater (p x) (ps x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((ps a).length)=>(x.2.val,x.1))
  exact (hps.map (g:=fun x q=>((p x).pair q).comp (BitArithmetic.wordEq (n x)))
    (((hp.compInput hx.snd).pair hps.get).comp (wordEq (hn.comp hx.snd)))).any hk
lemma distinctProductOfFn {f : ∀x,Fin (K x)→BooleanNetwork (k x) (n x)}
    {value : ∀x,BooleanNetwork (k x) (n x)→BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2))
    (hv : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>value x.1 (f x.1 x.2))) :
    NetEmits ea (fun x=>BitArithmetic.distinctProductNet (value x) (List.ofFn (f x))):=by
  let F:=fun x j=>BitArithmetic.distinctProductNet (value x) ((List.ofFn (f x)).drop (K x-j))
  have h0 : NetEmits ea (fun x=>F x 0):=by
    have h:=wordConst hk hn (const _ _ 1)
    exact h.congr (by intro x;dsimp only [F];rw [Nat.sub_zero,List.drop_eq_nil_of_le (by simp)];rfl)
  have hs : NetEmits (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode)
      (x.1,(x.2.val,erasePack (F x.1 x.2.val)))) (fun x=>F x.1 (x.2.val+1)):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (K a)=>(x.1,(x.2.val,erasePack (F x.1 x.2.val))))
    let y : (Σa,Fin (K a))→(Σa,Fin (K a)):=fun x=>⟨x.1,⟨K x.1-(x.2.val+1),by have:=x.2.isLt;omega⟩⟩
    have hi:=((hK.comp hx.fst).unaryNat.natSub (hx.snd.fst.unaryNat.natAdd (const _ _ 1))).boundedUnary
      (hK.comp hx.fst) (fun _=>Nat.sub_le _ _)
    have hy : Emits (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode)
        (x.1,(x.2.val,erasePack (F x.1 x.2.val))))
        (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) y:=
      (hi.pair hx.fst).recode (by intros;rfl)
    have htail:=NetsEmits.drop ((hK.comp hx.fst).unaryNat.natSub hx.snd.fst.unaryNat)
      ((NetsEmits.ofFn hK hf).comp hx.fst)
    have hstep:=(((occursLater (hk.comp hx.fst) (hn.comp hx.fst) (hf.compInput (g:=y) hy) htail).wordMux
      (wordConst (hk.comp hx.fst) (hn.comp hx.fst) (const _ _ 1)) (hv.compInput (g:=y) hy) (hn.comp hx.fst)).pair
      (ofCanonical hx.snd.snd)).comp (mul (hn.comp hx.fst))
    convert hstep using 1
    funext x
    dsimp only [F]
    rw [dropOfFn_step _ x.2.isLt,BitArithmetic.distinctProductNet]
    rfl
  obtain ⟨pc,hpc⟩:=countPolyIndexed hK hf
  obtain ⟨pv,hpv⟩:=countPolyIndexed (f:=fun x i=>value x (f x i)) hK hv
  let len:=fun x:Σa,Fin (K a+1)=>(ea x.1).length
  have hC : PolyAt len (fun x=>pc.eval (len x)):=⟨pc,fun _=>le_rfl⟩
  have hV : PolyAt len (fun x=>pv.eval (len x)):=⟨pv,fun _=>le_rfl⟩
  have hW:=hn.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hL:=hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hc : NetworkAt len (fun x=>F x.1 x.2.val):=by
    apply (hL.mul ((((hV.add ((PolyAt.const len 90).mul (hW.pow 2))).add
      ((PolyAt.const len 22).mul hW)).add (PolyAt.const len 7)).add
      (hL.mul (((PolyAt.const len 2).mul hC).add ((PolyAt.const len 96).mul hW) |>.add (PolyAt.const len 25)))) |>.add hW).of_le
    intro x
    have hb:=BitArithmetic.distinctProductNet_count (value x.1) ((List.ofFn (f x.1)).drop (K x.1-x.2.val))
      (c:=pc.eval (len x)) (d:=pv.eval (len x))
      (by intro p hp;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hp);exact hpc ⟨x.1,i⟩)
      (by intro p hp;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hp);exact hpv ⟨x.1,i⟩)
    dsimp only [F]
    refine hb.trans ?_
    have hlen : ((List.ofFn (f x.1)).drop (K x.1-x.2.val)).length≤K x.1:=by simp only [List.length_drop,List.length_ofFn];omega
    nlinarith [Nat.mul_le_mul_left (2*pc.eval (len x)+96*n x.1+25) hlen,
      Nat.mul_le_mul hlen (Nat.add_le_add_left (Nat.mul_le_mul_right (2*pc.eval (len x)+96*n x.1+25) hlen)
        (pv.eval (len x)+90*n x.1*n x.1+22*n x.1+7))]
  simpa only [F,Nat.sub_self,List.drop_zero] using boundedStages hK h0 hs
    (hk.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)) hW hc
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TableFavorableEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n t K : α→ℕ}
lemma sumOfFn {f : ∀x,Fin (K x)→BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.sumNet (List.ofFn (f x))):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hK p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hK.pair (id ea))
  obtain ⟨c,hc,ec⟩:=add hn
  obtain ⟨b,hb,eb⟩:=wordConst hk hn (const _ _ 0)
  refine ⟨fun x=>((List.range (K x)).map (q x)).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x),
    (ofProcedure Emission.foldChoiceP).comp (hps.pair (hc.pair hb)),?_⟩
  intro x
  dsimp only
  rw [←ofFn_nat_eq_map]
  have hh:∀j (g:Fin j→BooleanNetwork (k x) (n x)) (ps:Fin j→Pack),
      (∀i,(ps i).val.value=erase (g i))→
      ((List.ofFn ps).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x)).val.value=erase (BitArithmetic.sumNet (List.ofFn g)):=by
    intro j;induction j with
    | zero=>intro g ps h;simpa only [List.ofFn_zero,List.foldr_nil,BitArithmetic.sumNet,BitVec.ofNat_eq_ofNat] using eb x
    | succ j ih=>
      intro g ps h
      rw [List.ofFn_succ,List.foldr_cons,List.ofFn_succ,BitArithmetic.sumNet]
      exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ (h 0) (ih _ _ (fun i=>h i.succ))) (ec x)
  exact hh _ _ _ (fun i=>by rw [eq];exact he ⟨x,i⟩)
lemma tableLevel {m : ∀x,BooleanNetwork (k x) (n x)} {ps : ∀x,List (BooleanNetwork (k x) (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t)
    (hm : NetEmits ea m) (hps : NetsEmits ea ps) : NetEmits ea (fun x=>BitArithmetic.tableLevelNet (m x) (ps x) (t x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((ps a).length)=>(x.2.val,x.1))
  have hv:=componentLevel (hk.comp hx.snd) (hn.comp hx.snd) (ht.comp hx.snd) (hm.compInput hx.snd) hps.get
  exact (distinctProductOfFn (f:=fun x i=>(ps x).get i) (value:=fun x p=>BitArithmetic.componentLevelNet (m x) p (t x)) hk hn hps.length hps.get hv).congr
    (by intro x;rw [List.ofFn_get];rfl)
lemma tableBadCount {m : ∀x,BooleanNetwork (k x) (n x)} {ps : ∀x,List (BooleanNetwork (k x) (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hm : NetEmits ea m) (hps : NetsEmits ea ps) :
    NetEmits ea (fun x=>BitArithmetic.tableBadCountNet (m x) (ps x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a+1)=>(x.2.val,x.1))
  exact sumOfFn hk hn hn.unarySucc (tableLevel (hk.comp hx.snd) (hn.comp hx.snd) hx.fst (hm.compInput hx.snd) (hps.comp hx.snd))
lemma tableFavorableCount {m : ∀x,BooleanNetwork (k x) (n x)} {ps : ∀x,List (BooleanNetwork (k x) (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hm : NetEmits ea m) (hps : NetsEmits ea ps) :
    NetEmits ea (fun x=>BitArithmetic.tableFavorableCountNet (m x) (ps x)):=
  natSubOn hk hn (primesPhi hk hn hm hps) (tableBadCount hk hn hm hps)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedArithmeticEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma bxor {a b : ∀x,BooleanNetwork (k x) 1} (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>(a x).bxor (b x)):=
  (ha.band hb.bnot).bor (ha.bnot.band hb)
lemma sameTwoVal {a b : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>BitArithmetic.sameTwoVal (a x) (b x)):=by
  apply allOfFn hk hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hd:=divides (hn.comp hx.snd) (Emits.powTwo hx.fst)
  exact (((ha.compInput hx.snd).comp hd).bxor ((hb.compInput hx.snd).comp hd)).bnot
lemma transitionRead {K : α→ℕ} {y : ∀x,BooleanNetwork (k x) (n x*(K x+1))}
    (hn : Emits ea unaryCode n) (hy : NetEmits ea y) (i : ∀x,Fin (K x))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    NetEmits ea (fun x=>TransitionWords.readNet (y x) (i x)):=by
  exact hy.rewireSlice hn (hi.natMul hn.unaryNat) _ (by intro x j; change j.val+n x*(i x).val=(i x).val*n x+j.val; ac_rfl)
lemma transitionFirstOnly {K : α→ℕ} {a : ∀x,BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hK : Emits ea unaryCode K) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>TransitionWords.firstOnly (K:=K x) (a x)):=by
  apply transitionEncode hk hn hK
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (K a)=>(x.2.val,x.1))
  exact (ite (hx.fst.unaryNat.natEq (const _ _ 0)) (ha.compInput hx.snd)
    (wordConst (hk.comp hx.snd) (hn.comp hx.snd) (const _ _ 0))).congr (by
      intro x;simp only [decide_eq_true_eq])
end ExactQuantumFactoring.NetworkEmission.NetEmits
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma retainedOrder {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedOrder (t x) (a x) (m x)):=
  NetEmits.tableOrder (machineWidth hn ht) hn ha hm (tableNets hn ht)
lemma retainedTotient {v : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hv : NetEmits ea v) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedTotient (t x) (v x)):=
  NetEmits.tableTotient (machineWidth hn ht) hn hv (tableNets hn ht)
lemma retainedOrderPhi {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedOrderPhi (t x) (a x) (m x)):=
  retainedTotient hn ht (retainedOrder hn ht ha hm)
lemma retainedComponentOrder {a m p : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) (p x)):=
  retainedOrder hn ht ha (primeComponent (machineWidth hn ht) hn hm hp)
lemma retainedFavorableCount {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedFavorableCount (t x) (m x)):=
  tableFavorableCount (machineWidth hn ht) hn hm (tableNets hn ht)
lemma retainedCanonical {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedCanonical (t x) (a x) (m x)):=
  NetEmits.tableCanonical (machineWidth hn ht) hn (tableNets hn ht) ha hm
lemma retainedCanonicalList {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {y : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x*(n x^5+1))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) (hm : NetEmits ea m) (hy : NetEmits ea y) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedCanonicalList (hn0 x) (t x) (m x) (y x)):=by
  have ha:=transitionRead hn hy (fun x=>⟨0,pow_pos (hn0 x) 5⟩) (const _ _ 0)
  exact (retainedCanonical hn ht ha hm).band (hy.equalOn (transitionFirstOnly (machineWidth hn ht) hn (hn.unaryPow 5) ha)
    (transitionWidth hn))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetainedFavorableEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma favorableComparison {a m p : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BooleanNetwork.all ((BitArithmetic.tableNets ((PhysicalTree.machine (n x)).fieldRows (t x))).map
      (fun q=>(BitArithmetic.dividesOn (p x) (m x)).bnot.bor ((BitArithmetic.dividesOn q (m x)).bnot.bor
        (BitArithmetic.sameTwoVal ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) (p x))
          ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) q)))))):=by
  have hps:=tableNets hn ht
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((BitArithmetic.tableNets ((PhysicalTree.machine (n a)).fieldRows (t a))).length)=>(x.2.val,x.1))
  have hn':=hn.comp hx.snd
  have ht':=ht.comp hx.snd
  have ha':=ha.compInput hx.snd
  have hm':=hm.compInput hx.snd
  have hp':=hp.compInput hx.snd
  have hk:=machineWidth hn' ht'
  have hc:=(dividesOn hk hn' hp' hm').bnot.bor ((dividesOn hk hn' hps.get hm').bnot.bor
    (sameTwoVal hk hn' (retainedComponentOrder hn' ht' ha' hm' hp') (retainedComponentOrder hn' ht' ha' hm' hps.get)))
  exact (hps.map (g:=fun x q=>(BitArithmetic.dividesOn (p x) (m x)).bnot.bor
    ((BitArithmetic.dividesOn q (m x)).bnot.bor (BitArithmetic.sameTwoVal
    ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) (p x))
    ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) q)))) hc).all (machineWidth hn ht)
lemma retainedFavorable {a m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedFavorable (t x) (a x) (m x)):=by
  have hps:=tableNets hn ht
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((BitArithmetic.tableNets ((PhysicalTree.machine (n a)).fieldRows (t a))).length)=>(x.2.val,x.1))
  have hc:=favorableComparison (hn.comp hx.snd) (ht.comp hx.snd) (ha.compInput hx.snd) (hm.compInput hx.snd) hps.get
  exact (PhysicalOrderEmission.usable (machineWidth hn ht) hn ha hm).band ((hps.map
    (g:=fun x p=>BooleanNetwork.all ((BitArithmetic.tableNets ((PhysicalTree.machine (n x)).fieldRows (t x))).map
      (fun q=>(BitArithmetic.dividesOn p (m x)).bnot.bor ((BitArithmetic.dividesOn q (m x)).bnot.bor
        (BitArithmetic.sameTwoVal ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) p)
          ((PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) q)))))) hc).all (machineWidth hn ht)).bnot
lemma retainedGoodList {m : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    {y : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x*(n x^5+1))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hm : NetEmits ea m) (hy : NetEmits ea y) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedGoodList (t x) (m x) (y x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a^5)=>(x.2.val,x.1))
  exact anyOfFn (machineWidth hn ht) (hn.unaryPow 5) (retainedFavorable (hn.comp hx.snd) (ht.comp hx.snd)
    (transitionRead (hn.comp hx.snd) (hy.compInput hx.snd) (fun x=>x.2) hx.fst.unaryNat) (hm.compInput hx.snd))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackRationalDivision.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def ratInv : Procedure ratCode ratCode (fun q=>q⁻¹):=by
  let num:=signedInt.comp ((intSign.comp ratNum).pair ratDen)
  let den:=intAbs.comp ratNum
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro q
    change mkRat (intOfSign (decide (q.num<0),q.den)) q.num.natAbs=q⁻¹
    rw [Rat.mkRat_eq_div]
    by_cases h:q.num<0
    · have hz:=Int.eq_neg_natAbs_of_nonpos h.le
      simp only [h,decide_true,intOfSign,ite_true,Int.cast_neg,Int.cast_natCast]
      conv_rhs=>rw [←Rat.num_div_den q,hz]
      simp only [Int.cast_neg,Int.cast_natCast,neg_div,inv_neg,inv_div]
    · have hz:=Int.natAbs_of_nonneg (le_of_not_gt h)
      simp only [h,decide_false,intOfSign,Bool.false_eq_true,ite_false,Int.cast_natCast]
      conv_rhs=>rw [←Rat.num_div_den q,←hz]
      simp only [inv_div,Int.cast_natCast])
noncomputable def ratDiv : Procedure (prodCode ratCode ratCode) ratCode (fun x=>x.1/x.2):=
  (ratMul.comp ((first ratCode ratCode).pair (ratInv.comp (second ratCode ratCode)))).congrFun
    (by intro x;exact (div_eq_mul_inv _ _).symm)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackRationalFloor.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
noncomputable def ratFloor : Procedure ratCode intCode (fun q=>⌊q⌋):=by
  let num:=ratNum
  let den:=ratDen
  let mag:=intAbs.comp num
  let negmag:=binaryAdd.comp ((binaryDiv.comp
    ((binarySub.comp (mag.pair (constant ratCode Nat.bits 1))).pair den)).pair
    (constant ratCode Nat.bits 1))
  let pos:=natToInt.comp (binaryDiv.comp (mag.pair den))
  let neg:=intNeg.comp (natToInt.comp negmag)
  exact (conditional (intSign.comp num) neg pos).congrFun (by
    intro q
    change (if decide (q.num<0) then -((((q.num.natAbs-1)/q.den+1):ℕ):ℤ)
      else ((q.num.natAbs/q.den):ℤ))=⌊q⌋
    rw [Rat.floor_def']
    obtain ⟨d,hd⟩:=Nat.exists_eq_succ_of_ne_zero q.den_nz
    rw [hd]
    cases q.num with
    | ofNat a=>simp
    | negSucc a=>
      simp only [Int.negSucc_lt_zero, decide_true, ite_true, Int.natAbs_negSucc,
        Int.negSucc_ediv_ofNat_succ]
      change -((((a+1-1)/(d+1)+1):ℕ):ℤ)=Int.negSucc (a/(d+1))
      simp only [Nat.add_sub_cancel]
      rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackRationalPower.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma intOfSign_pow (z : ℤ) (k : ℕ) :
    intOfSign (decide (z<0) && decide (k%2=1),z.natAbs^k)=z^k:=by
  by_cases hz:z<0
  · have he:=Int.eq_neg_natAbs_of_nonpos hz.le
    conv_rhs=>rw [he,neg_pow,neg_one_pow_eq_pow_mod_two]
    have hk:=Nat.mod_lt k (by omega : 0<2)
    have hp:k%2=0 ∨ k%2=1:=by omega
    rcases hp with h|h <;> simp [intOfSign,hz,h]
  · have he:=Int.natAbs_of_nonneg (le_of_not_gt hz)
    simp only [hz,decide_false,Bool.false_and,intOfSign,Bool.false_eq_true,ite_false,Int.natCast_pow,he]
namespace Procedure
noncomputable def intPow : Procedure (prodCode unaryCode intCode) intCode (fun x=>x.2^x.1):=by
  let k:=first unaryCode intCode
  let z:=second unaryCode intCode
  let odd:=binaryEq.comp ((binaryMod.comp ((unaryToBits.comp k).pair
    (constant _ Nat.bits 2))).pair (constant _ Nat.bits 1))
  let s:=boolAnd.comp ((intSign.comp z).pair odd)
  let a:=binaryPow.comp (k.pair (intAbs.comp z))
  exact (signedInt.comp (s.pair a)).congrFun (by intro x;exact intOfSign_pow x.2 x.1)
noncomputable def ratPow : Procedure (prodCode unaryCode ratCode) ratCode (fun x=>x.2^x.1):=by
  let k:=first unaryCode ratCode
  let q:=second unaryCode ratCode
  let num:=intPow.comp (k.pair (ratNum.comp q))
  let den:=binaryPow.comp (k.pair (ratDen.comp q))
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.2.num^x.1) (x.2.den^x.1)=x.2^x.1
    rw [Rat.mkRat_eq_div,Int.cast_pow,Nat.cast_pow,←div_pow,Rat.num_div_den])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
