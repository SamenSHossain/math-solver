/-
Exact quantum factoring development (port of OpenAI's formalization), part 36 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: OrderSamplerEmission.lean, RawTrialFieldsEmission.lean, NetworkFoldChoiceEmission.lean, FactorVerifierEmission.lean, NetworkListEmission.lean, NetworkListOperationsEmission.lean, DescendingFilter.lean, DescendingFilterEmission.lean, DescendingStepEmission.lean, DescendingPrefixAutomatic.lean, TransitionEncodingEmission.lean, PhysicalListOutputEmission.lean, PhysicalOrderEmission.lean, PhysicalSplitEmission.lean, LabelRecoveryEmission.lean, SamplerDecodeEmission.lean, RawTrialLabelEmission.lean, RawTrialDecoderEmission.lean, PhysicalOrderOutputEmission.lean, FirstProperEmission.lean, SuppliedDivisorEmission.lean, PhysicalSplitDecoderEmission.lean, NodeControlEmission.lean, NodeStateEmission.lean, SortingEmission.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part35

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OrderSamplerEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.OrderSamplerEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {w b s n : α→ℕ}
lemma inputWidth (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    Emits ea unaryCode (fun x=>OrderSample.inputWidth (w x) (b x)):=
  (hw.unaryAdd hw).unaryAdd (TriangularEmission.width hb)
lemma scratch (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    Emits ea unaryCode (fun x=>OrderSample.scratch (w x) (b x)):=
  hw.unaryAdd (hb.unaryMul (((((const _ _ 3672).unaryMul hw).unaryMul hw).unaryAdd
    ((const _ _ 436).unaryMul hw)).unaryAdd (const _ _ 36)))
lemma width (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    Emits ea unaryCode (fun x=>OrderSample.width (w x) (b x)):=
  ((inputWidth hw hb).unaryAdd hw).unaryAdd (scratch hw hb)
lemma powerInputs (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderSample.powerInputs (w x) (b x)):=by
  apply selectSlice (inputWidth hw hb) ((hw.unaryAdd hw).unaryAdd hb) (const _ _ 0) _
  intro x i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd,Nat.zero_add]
  · simp only [Fin.addCases_right,Fin.val_natAdd,Nat.zero_add];rfl
lemma powerNetwork (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderSample.powerNetwork (w x) (b x)):=
  (powerInputs hw hb).comp (modularPower hw hb)
lemma initial (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    OpsEmits ea (fun x=>OrderSample.initial (w x) (b x)):=
  ((TriangularEmission.uniform hb).right (hw.unaryAdd hw)).first w (fun x=>OrderSample.scratch (w x) (b x))
lemma program (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) :
    OpsEmits ea (fun x=>OrderSample.program (w x) (s x)):=by
  have hb:=hs.unaryAdd (const _ _ 2)
  exact (OpsEmits.oracleOn (powerNetwork hw hb) (fun x=>OrderSample.powerNetwork_count (w x) (s x+2))).append
    (((TriangularEmission.transform hs).right (hw.unaryAdd hw)).first w (fun x=>OrderSample.scratch (w x) (s x+2)))
lemma complete (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) :
    OpsEmits ea (fun x=>OrderSample.completeSampler (w x) (s x)):=
  (initial hw (hs.unaryAdd (const _ _ 2))).append (program hw hs)
lemma guessWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderTrial.guessWidth (n x)):=
  hn.unaryAdd (hn.unaryAdd (hn.unaryAdd (retentionBits hn)))
lemma guessProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>OrderTrial.guessProgram (n x)):=
  OpsEmits.parallel (OpsEmits.hadamards hn (fun _=>le_rfl))
    (OpsEmits.parallel (OpsEmits.hadamards hn (fun _=>le_rfl))
      (OpsEmits.parallel (OpsEmits.hadamards hn (fun _=>le_rfl))
        (OpsEmits.hadamards (retentionBits hn) (fun _=>le_rfl)) hn) hn) hn
lemma rawWidth (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) :
    Emits ea unaryCode (fun x=>OrderTrial.rawWidth (w x) (s x) (n x)):=
  (const _ _ 2).unaryAdd ((width hw (hs.unaryAdd (const _ _ 2))).unaryAdd (guessWidth hn))
lemma rawProgram (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) :
    OpsEmits ea (fun x=>OrderTrial.rawProgram (w x) (s x) (n x)):=
  OpsEmits.parallel (OpsEmits.hadamards (const _ _ 2) (fun _=>le_rfl))
    (OpsEmits.parallel (complete hw hs) (guessProgram hn) (width hw (hs.unaryAdd (const _ _ 2)))) (const _ _ 2)
end ExactQuantumFactoring.OrderSamplerEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RawTrialFieldsEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k u s n b : α→ℕ}
lemma left (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BooleanNetwork.leftNet (u x) (b x)):=
  selectSlice (hu.unaryAdd hb) hu (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma right (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BooleanNetwork.rightNet (u x) (b x)):=
  selectSlice (hu.unaryAdd hb) hb hu.unaryNat _ (by intros;rfl)
lemma toWidth {f : ∀x,BooleanNetwork (k x) (u x)} (hf : NetEmits ea f)
    (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderTrial.toWidth (b x) (f x)):=hf.comp (resize hu hb)
end ExactQuantumFactoring.NetworkEmission.NetEmits
namespace ExactQuantumFactoring.RawTrialEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k u s n : α→ℕ}
variable {r : ∀x,BooleanNetwork (k x) (OrderTrial.rawWidth (u x) (s x) (n x))}
lemma mode (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawMode (r x)):=
  hr.comp (left (const _ _ 2) ((OrderSamplerEmission.width hu (hs.unaryAdd (const _ _ 2))).unaryAdd (OrderSamplerEmission.guessWidth hn)))
lemma sample (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawSample (r x)):=by
  have hw:=OrderSamplerEmission.width hu (hs.unaryAdd (const _ _ 2))
  have hg:=OrderSamplerEmission.guessWidth hn
  exact (hr.comp (right (const _ _ 2) (hw.unaryAdd hg))).comp (left hw hg)
lemma guesses (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawGuesses (r x)):=by
  have hw:=OrderSamplerEmission.width hu (hs.unaryAdd (const _ _ 2))
  have hg:=OrderSamplerEmission.guessWidth hn
  exact (hr.comp (right (const _ _ 2) (hw.unaryAdd hg))).comp (right hw hg)
lemma den (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawDen (r x)):=
  (guesses hu hs hn hr).comp (left hn (hn.unaryAdd (hn.unaryAdd (retentionBits hn))))
lemma num (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawNum (r x)):=
  ((guesses hu hs hn hr).comp (right hn (hn.unaryAdd (hn.unaryAdd (retentionBits hn))))).comp (left hn (hn.unaryAdd (retentionBits hn)))
lemma residue (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawResidue (r x)):=
  (((guesses hu hs hn hr).comp (right hn (hn.unaryAdd (hn.unaryAdd (retentionBits hn))))).comp
    (right hn (hn.unaryAdd (retentionBits hn)))).comp (left hn (retentionBits hn))
lemma coin (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawCoin (r x)):=
  (((guesses hu hs hn hr).comp (right hn (hn.unaryAdd (hn.unaryAdd (retentionBits hn))))).comp
    (right hn (hn.unaryAdd (retentionBits hn)))).comp (right hn (retentionBits hn))
end ExactQuantumFactoring.RawTrialEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkFoldChoiceEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma foldChoice_budget (c : Pack) (xs : List Pack) (b : Pack) :
    (xs.foldl (fun b a=>compPack (pairPack a b) c) b).val.budget=
      b.val.budget+(xs.map (fun a=>a.val.budget)).sum+c.val.budget*xs.length:=by
  exact fold_budget_extra _ c.val.budget (by intros;rfl) _ _
lemma foldChoice_state (xs : List Pack) (c b : Pack) :
    xs.foldl (fun s a=>(s.1,compPack (pairPack a s.2) s.1)) (c,b)=
      (c,xs.foldl (fun b a=>compPack (pairPack a b) c) b):=by
  induction xs generalizing b with
  | nil=>rfl
  | cons a xs ih=>simpa only [List.foldl_cons] using ih (compPack (pairPack a b) c)
lemma quadBudget_bound (a b c d A B N : ℕ) (ha : a≤A) (hb : b≤B)
    (hd : d≤N) (hc : c≤N) :
    2*(104*(a+1)^2)+104*(b+c+a*d+1)^2+1 ≤ 1000*(N+2*A+B+1+1)^4:=by
  let T:=N+2*A+B+1
  have he : a≤T := by dsimp [T];omega
  have ht : d≤T := by dsimp [T];omega
  have hs0 : b+c≤T := by dsimp [T];omega
  have hs : b+c+a*d+1≤(T+1)^2:=by
    have hm:=Nat.mul_le_mul he ht
    nlinarith only [hs0,hm]
  have hh:=Nat.pow_le_pow_left hs 2
  have hh':=Nat.pow_le_pow_left (show a+1≤T+1 by omega) 2
  have hp4 : ((T+1)^2)^2=(T+1)^4:=by ring
  rw [hp4] at hh
  have h24 : (T+1)^2≤(T+1)^4:=Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1≤(T+1)^4:=Nat.one_le_pow _ _ (Nat.succ_pos _)
  have h2:=(hh'.trans h24)
  change _ ≤ 1000*(T+1)^4
  omega
lemma foldChoice_code_bound (xs : List Pack) (a : Pack×Pack) (i : ℕ) :
    (prodCode packCode packCode ((xs.take i).foldl (fun s a=>(s.1,compPack (pairPack a s.2) s.1)) a)).length ≤
      1000*((listCode packCode xs).length+(prodCode packCode packCode a).length+1)^4:=by
  rw [show a=(a.1,a.2) from rfl,foldChoice_state]
  simp only [prodCode,pairBits_length]
  have hc:=packCode_bound a.1
  have hb:=packCode_bound ((xs.take i).foldl (fun b t=>compPack (pairPack t b) a.1) a.2)
  rw [foldChoice_budget] at hb
  have ha:=packBudget_le_code a.1
  have ha':=packBudget_le_code a.2
  have hx:=(packBudgets_le_code (xs.take i)).trans (listCode_length_take_le packCode i xs)
  have hl:=(list_length_le_code packCode (xs.take i)).trans (listCode_length_take_le packCode i xs)
  have H:=quadBudget_bound _ _ _ _ _ _ _ ha ha' hl hx
  calc
    _ ≤ 2*(104*(a.1.val.budget+1)^2)+104*(a.2.val.budget+((xs.take i).map (fun t=>t.val.budget)).sum+a.1.val.budget*(xs.take i).length+1)^2+1 := by omega
    _ ≤ _ := by simpa only [Nat.add_assoc] using H
namespace Emission
noncomputable def foldChoiceStepP : Procedure (prodCode packCode (prodCode packCode packCode))
    (prodCode packCode packCode) (fun x=>(x.2.1,compPack (pairPack x.1 x.2.2) x.2.1)):=by
  let ex:=first packCode (prodCode packCode packCode)
  let st:=second packCode (prodCode packCode packCode)
  let sc:=(first packCode packCode).comp st
  let sb:=(second packCode packCode).comp st
  exact sc.pair (compPackP.comp ((pairPackP.comp (ex.pair sb)).pair sc))
noncomputable def foldChoiceP : Procedure
    (prodCode (listCode packCode) (prodCode packCode packCode)) packCode
    (fun x=>x.1.foldr (fun a b=>compPack (pairPack a b) x.2.1) x.2.2):=by
  let fold:=foldList emptyPack foldChoiceStepP
    (Polynomial.C 1000*(Polynomial.X+1)^4) (by
      intro xs a i
      simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        using foldChoice_code_bound xs a i)
  let inp:=((listReverse packCode emptyPack).comp (first (listCode packCode) (prodCode packCode packCode))).pair
    (second (listCode packCode) (prodCode packCode packCode))
  exact ((second packCode packCode).comp (fold.comp inp)).congrFun (by
    intro x;change (x.1.reverse.foldl (fun s a=>(s.1,compPack (pairPack a s.2) s.1)) x.2).2 = _
    rw [show x.2=(x.2.1,x.2.2) from rfl,foldChoice_state];exact List.foldl_reverse)
end Emission
namespace NetEmits
open BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n w K : α→ℕ}
lemma minimumChoice (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>OrderTrial.minimumChoice (w x)):=by
  have hl:=left hw hw
  have hr:=right hw hw
  have hz:=wordConst (hw.unaryAdd hw) hw (const _ _ 0)
  exact (hl.equalOn hz hw).wordMux hr ((hr.equalOn hz hw).wordMux hl ((hl.wordLt hr hw).wordMux hl hr hw) hw) hw
lemma minimum {f : ∀x,Fin (K x)→BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>OrderTrial.minimumNet (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hK p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hK.pair (id ea))
  obtain ⟨c,hc,ec⟩:=minimumChoice hw
  obtain ⟨b,hb,eb⟩:=wordConst hn hw (const _ _ 0)
  refine ⟨fun x=>((List.range (K x)).map (q x)).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x),
    (ofProcedure Emission.foldChoiceP).comp (hps.pair (hc.pair hb)),?_⟩
  intro x
  dsimp only
  rw [←ofFn_nat_eq_map]
  have hh:∀j (g:Fin j→BooleanNetwork (n x) (w x)) (ps:Fin j→Pack),
      (∀i,(ps i).val.value=erase (g i))→
      ((List.ofFn ps).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x)).val.value=erase (OrderTrial.minimumNet g):=by
    intro j;induction j with
    | zero=>intro g ps h;simpa only [List.ofFn_zero,List.foldr_nil,OrderTrial.minimumNet] using eb x
    | succ j ih=>
      intro g ps h
      rw [List.ofFn_succ,List.foldr_cons,OrderTrial.minimumNet]
      exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ (h 0) (ih _ _ (fun i=>h i.succ))) (ec x)
  exact hh _ _ _ (fun i=>by rw [eq];exact he ⟨x,i⟩)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FactorVerifierEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k w K : α→ℕ}
lemma productOfFn {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.productNet (List.ofFn (f x))):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hK p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hK.pair (id ea))
  obtain ⟨c,hc,ec⟩:=mul hw
  obtain ⟨b,hb,eb⟩:=wordConst hk hw (const _ _ 1)
  refine ⟨fun x=>((List.range (K x)).map (q x)).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x),
    (ofProcedure Emission.foldChoiceP).comp (hps.pair (hc.pair hb)),?_⟩
  intro x
  dsimp only
  rw [←ofFn_nat_eq_map]
  have hh:∀j (g:Fin j→BooleanNetwork (k x) (w x)) (ps:Fin j→Pack),
      (∀i,(ps i).val.value=erase (g i))→
      ((List.ofFn ps).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x)).val.value=erase (BitArithmetic.productNet (List.ofFn g)):=by
    intro j;induction j with
    | zero=>intro g ps h;simpa only [List.ofFn_zero,List.foldr_nil,BitArithmetic.productNet,BitVec.ofNat_eq_ofNat] using eb x
    | succ j ih=>
      intro g ps h
      rw [List.ofFn_succ,List.foldr_cons,List.ofFn_succ,BitArithmetic.productNet]
      exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ (h 0) (ih _ _ (fun i=>h i.succ))) (ec x)
  exact hh _ _ _ (fun i=>by rw [eq];exact he ⟨x,i⟩)
lemma primeOrZero {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.primeOrZero (a x)):=
  (zeroWord hk hw ha).bor (ha.comp (primeWord hw))
lemma paddedPair {a b : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>BitArithmetic.paddedPair (a x) (b x)):=
  (zeroWord hk hw hb).bor ((zeroWord hk hw ha).bnot.band (ha.wordLe hb hw))
lemma unpadWord {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.unpadWord (a x)):=
  (zeroWord hk hw ha).wordMux (wordConst hk hw (const _ _ 1)) ha hw
lemma candidateProduct {f : ∀x,Fin (w x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w)
    (hf : NetEmits (fun x:Σa,Fin (w a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.candidateProduct (f x)):=by
  apply productOfFn hk (hw.unaryMul hw).unarySucc hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (w a)=>(x.2.val,x.1))
  have hW:=hw.comp hx.snd
  exact (unpadWord (hk.comp hx.snd) hW hf).comp (resize hW (hW.unaryMul hW).unarySucc)
lemma factorVerifier {N : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (w x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hN : NetEmits ea N)
    (hf : NetEmits (fun x:Σa,Fin (w a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.factorVerifierOn (N x) (f x)):=by
  have hp : NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (fun i=>BitArithmetic.primeOrZero (f x i)))):=by
    apply allOfFn hk hw
    have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (w a)=>(x.2.val,x.1))
    exact primeOrZero (hk.comp hx.snd) (hw.comp hx.snd) hf
  have ho : NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (fun i:Fin (w x*w x)=>
      let p:=finProdFinEquiv.symm i
      if p.1<p.2 then BitArithmetic.paddedPair (f x p.1) (f x p.2) else BooleanNetwork.constant true))):=by
    apply allOfFn hk (hw.unaryMul hw)
    have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (w a*w a)=>(x.2.val,x.1))
    have hW:=hw.comp hx.snd
    have hi:=hx.fst.unaryNat.natDiv hW.unaryNat
    have hj:=hx.fst.unaryNat.natMod hW.unaryNat
    have h1:NetEmits (fun x:Σa,Fin (w a*w a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 (finProdFinEquiv.symm x.2).1):=by
      have hidx:=hi.boundedUnary hW (fun x=> (finProdFinEquiv.symm x.2).1.isLt.le)
      exact hf.compInput ((hidx.pair hx.snd).result (g:=fun x:Σa,Fin (w a*w a)=>(⟨x.1,(finProdFinEquiv.symm x.2).1⟩ : Σa,Fin (w a))) (by intros;rfl))
    have h2:NetEmits (fun x:Σa,Fin (w a*w a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 (finProdFinEquiv.symm x.2).2):=by
      have hidx:=hj.boundedUnary hW (fun x=> (finProdFinEquiv.symm x.2).2.isLt.le)
      exact hf.compInput ((hidx.pair hx.snd).result (g:=fun x:Σa,Fin (w a*w a)=>(⟨x.1,(finProdFinEquiv.symm x.2).2⟩ : Σa,Fin (w a))) (by intros;rfl))
    exact (NetEmits.ite (hi.natLt hj) (paddedPair (hk.comp hx.snd) hW h1 h2)
      (constant (hk.comp hx.snd) (const _ _ true))).congr (by intro x;simp only [decide_eq_true_eq];rfl)
  exact (hp.band ho).band ((candidateProduct hk hw hf).equalOn (hN.comp (resize hw (hw.unaryMul hw).unarySucc)) (hw.unaryMul hw).unarySucc)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkListEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
abbrev NetsEmits {α : Type} (ea : α→List Bool) {n m : α→ℕ}
    (f : ∀x,List (BooleanNetwork (n x) (m x))) : Prop:=
  Emits ea (listCode packCode) (fun x=>(f x).map erasePack)
namespace NetsEmits
variable {α : Type} {ea : α→List Bool} {n m K : α→ℕ} {f : ∀x,List (BooleanNetwork (n x) (m x))}
lemma ofFn {g : ∀x,Fin (K x)→BooleanNetwork (n x) (m x)} (hK : Emits ea unaryCode K)
    (hg : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>g x.1 x.2)) :
    NetsEmits ea (fun x=>List.ofFn (g x)):=by
  exact (ofFnDep emptyPack hK hg.canonical).congr (fun x=>by rw [List.map_ofFn])
lemma length (hf : NetsEmits ea f) : Emits ea unaryCode (fun x=>(f x).length):=by
  exact ((ofProcedure (NativeAIG.Emission.listUnaryLength packCode emptyPack)).comp hf).congr (by intro x;exact List.length_map ..)
lemma get (hf : NetsEmits ea f) : NetEmits
    (fun x:Σa,Fin ((f a).length)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>(f x.1).get x.2):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((f a).length)=>(x.2.val,x.1))
  have h:=(ofProcedure (Procedure.listGet packCode emptyPack)).comp (hx.fst.unaryNat.pair (hf.comp hx.snd))
  apply NetEmits.ofCanonical
  exact h.congr (by
    intro x
    simp only [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_map,List.getElem?_eq_getElem x.2.isLt,Option.map_some,Option.getD_some,List.get_eq_getElem])
lemma product (hn : Emits ea unaryCode n) (hm : Emits ea unaryCode m) (hf : NetsEmits ea f) :
    NetEmits ea (fun x=>BitArithmetic.productNet (f x)):=by
  exact (NetEmits.productOfFn hn hm hf.length hf.get).congr (by intro x;rw [List.ofFn_get])
end NetsEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkListOperationsEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetsEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma congrList {f g : ∀x,List (BooleanNetwork (n x) (m x))} (hf : NetsEmits ea f)
    (h : ∀x,f x=g x) : NetsEmits ea g:=hf.congr (fun x=>congrArg (List.map erasePack) (h x))
lemma concat {f : ∀x,Fin (k x)→List (BooleanNetwork (n x) (m x))} (hk : Emits ea unaryCode k)
    (hf : NetsEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetsEmits ea (fun x=>(List.ofFn (f x)).flatten):=by
  exact ((ofFnDep (f:=fun x i=>(f x i).map erasePack) [] hk hf).flatten emptyPack).congr (by
    intro x;simp only [List.map_flatten,List.map_ofFn];rfl)
lemma replicate {f : ∀x,BooleanNetwork (n x) (m x)} (hk : Emits ea unaryCode k) (hf : NetEmits ea f) :
    NetsEmits ea (fun x=>List.replicate (k x) (f x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (k a)=>(x.2.val,x.1))
  exact (ofFn hk (hf.compInput hx.snd)).congrList (by intro x;exact List.ofFn_const _ _)
lemma map {f : ∀x,List (BooleanNetwork (n x) (m x))} {u v : α→ℕ}
    {g : ∀x,BooleanNetwork (n x) (m x)→BooleanNetwork (u x) (v x)} (hf : NetsEmits ea f)
    (hg : NetEmits (fun x:Σa,Fin ((f a).length)=>prodCode unaryCode ea (x.2.val,x.1))
      (fun x=>g x.1 ((f x.1).get x.2))) : NetsEmits ea (fun x=>(f x).map (g x)):=by
  exact (ofFn (g:=fun x i=>g x ((f x).get i)) hf.length hg).congrList (by
    intro x;conv_rhs=>rw [←List.ofFn_get (f x),List.map_ofFn]
    rfl)
lemma repeated {f : ∀x,List (BooleanNetwork (n x) (m x))} (hk : Emits ea unaryCode k) (hf : NetsEmits ea f) :
    NetsEmits ea (fun x=>(List.replicate (k x) (f x)).flatten):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (k a)=>(x.2.val,x.1))
  exact (concat (f:=fun x _=>f x) hk (hf.comp hx.snd)).congrList (by intro x;rw [List.ofFn_const])
lemma sequence {f : ∀x,List (BooleanNetwork (n x) (n x))} (hn : Emits ea unaryCode n) (hf : NetsEmits ea f) :
    NetEmits ea (fun x=>BooleanNetwork.sequence (f x)):=by
  refine ⟨fun x=>((f x).map erasePack).foldr compPack (identityPack (n x)),
    (ofProcedure (Emission.foldRightPack 0 (by intros;rfl) Emission.compPackP)).comp
      (hf.pair ((ofProcedure Emission.identityPackP).comp hn)),?_⟩
  intro x
  dsimp only
  generalize f x=l
  induction l with
  | nil=>exact identityPack_value _
  | cons a as ih=>exact compPack_spec _ _ _ _ rfl ih
end NetsEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/DescendingFilter.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BooleanNetwork BitStackProgram BitStackProgram.Emits
structure FilterState (k : ℕ) (w : ℕ→ℕ) where
  depth : ℕ
  raw : BooleanNetwork k (w depth)
  pending : List (BooleanNetwork k 1)
def filterStep {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) : FilterState k w→FilterState k w
  | ⟨0,v,ps⟩ => ⟨0,v,ps⟩
  | ⟨s+1,v,ps⟩ => ⟨s,v.comp (prev s),keep s v::ps⟩
def FilterState.code {k : ℕ} {w : ℕ→ℕ} (s : FilterState k w) : ℕ×Pack×List Pack:=
  (s.depth,erasePack s.raw,s.pending.map erasePack)
def filterPrefix {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) : ∀s,BooleanNetwork k (w s)→BooleanNetwork k 1
  | 0,_=>BooleanNetwork.constant true
  | s+1,v=>(filterPrefix prev keep s (v.comp (prev s))).band (keep s v)
lemma filterStep_depth {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) :
    (filterStep prev keep s).depth=s.depth-1:=by cases s with | mk d v ps=>cases d <;> rfl
lemma filterRun_depth {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) (i : ℕ) :
    ((filterStep prev keep)^[i] s).depth=s.depth-i:=by
  induction i with
  | zero=>simp
  | succ i ih=>rw [Function.iterate_succ_apply',filterStep_depth,ih,Nat.sub_sub]
lemma filterStep_value {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) :
    (filterStep prev keep s).pending.foldl BooleanNetwork.band
      (filterPrefix prev keep (filterStep prev keep s).depth (filterStep prev keep s).raw)=
    s.pending.foldl BooleanNetwork.band (filterPrefix prev keep s.depth s.raw):=by
  cases s with | mk d v ps=>cases d <;> rfl
lemma filterRun_value {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) (i : ℕ) :
    ((filterStep prev keep)^[i] s).pending.foldl BooleanNetwork.band
      (filterPrefix prev keep ((filterStep prev keep)^[i] s).depth ((filterStep prev keep)^[i] s).raw)=
    s.pending.foldl BooleanNetwork.band (filterPrefix prev keep s.depth s.raw):=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',filterStep_value,ih]
lemma filterRun_result {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : ℕ) (v : BooleanNetwork k (w s)) :
    ((filterStep prev keep)^[s] ⟨s,v,[]⟩).pending.foldl BooleanNetwork.band (BooleanNetwork.constant true)=
      filterPrefix prev keep s v:=by
  have h:=filterRun_value prev keep (⟨s,v,[]⟩ : FilterState k w) s
  have hd:=filterRun_depth prev keep (⟨s,v,[]⟩ : FilterState k w) s
  dsimp only at hd
  rw [Nat.sub_self] at hd
  generalize he : ((filterStep prev keep)^[s] ⟨s,v,[]⟩)=r at *
  cases r with | mk d a ps=>
    dsimp only [FilterState.depth] at hd
    subst d
    exact h
lemma filterRun_bounds {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1)
    (hp : ∀s,(prev s).net.count=0) (S B C : ℕ)
    (hc : ∀s,S>s→∀v: BooleanNetwork k (w (s+1)),v.net.count≤B→(keep s v).net.count≤C)
    (v : BooleanNetwork k (w S)) (hv : v.net.count≤B) (i : ℕ) :
    let r := ((filterStep prev keep)^[i] ⟨S,v,[]⟩);
    r.depth ≤ S ∧ r.raw.net.count ≤ B ∧ r.pending.length ≤ i ∧ (∀ a ∈ r.pending, a.net.count ≤ C) := by
  induction i with
  | zero=>exact ⟨le_rfl,hv,le_rfl,by simp⟩
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    generalize he : ((filterStep prev keep)^[i] ⟨S,v,[]⟩)=r at *
    rcases ih with ⟨hd,hv,hl,hc'⟩
    cases r with | mk d a ps=>
      cases d with
      | zero=>exact ⟨hd,hv,hl.trans (by omega),hc'⟩
      | succ d=>
        dsimp only [FilterState.depth,FilterState.raw,FilterState.pending] at hd hv hl hc'
        refine ⟨by dsimp only [filterStep];omega,?_,?_,?_⟩
        · simpa only [filterStep,BooleanNetwork.count_comp,hp,Nat.add_zero] using hv
        · dsimp only [filterStep];simp only [List.length_cons];omega
        · intro a ha
          rcases List.mem_cons.mp ha with h|h
          · subst a;exact hc d (by omega) _ hv
          · exact hc' a h
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/DescendingFilterEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
lemma recode {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
    {f : α→β} {g : α→γ} (h : Emits ea eb f) (he : ∀x,eb (f x)=ec (g x)) : Emits ea ec g:=by
  obtain ⟨p⟩:=h;exact ⟨p.result he⟩
end ExactQuantumFactoring.BitStackProgram.Emits
namespace ExactQuantumFactoring.NetworkEmission
open BooleanNetwork BitStackProgram BitStackProgram.Emits
abbrev filterCode := prodCode unaryCode (prodCode packCode (listCode packCode))
def FilterState.positiveView {k : ℕ} {w : ℕ→ℕ} (r : FilterState k w) (h : 0<r.depth) :
    Σs,BooleanNetwork k (w (s+1)) × List (BooleanNetwork k 1):=by
  cases r with | mk d v ps=>cases d with
    | zero=>exact False.elim (Nat.not_lt_zero _ h)
    | succ s=>exact ⟨s,v,ps⟩
lemma FilterState.positiveView_eq {k : ℕ} {w : ℕ→ℕ} (r : FilterState k w) (h : 0<r.depth) :
    (⟨(r.positiveView h).1+1,(r.positiveView h).2.1,(r.positiveView h).2.2⟩ : FilterState k w)=r:=by
  cases r with | mk d v ps=>cases d with
    | zero=>exact False.elim (Nat.not_lt_zero _ h)
    | succ s=>rfl
namespace NetsEmits
lemma foldlBand {α : Type} {ea : α→List Bool} {k : α→ℕ}
    {f : ∀x,List (BooleanNetwork (k x) 1)} (hk : Emits ea unaryCode k) (hf : NetsEmits ea f) :
    NetEmits ea (fun x=>(f x).foldl BooleanNetwork.band (BooleanNetwork.constant true)):=by
  let p:=Emission.foldRightPack (f:=fun a b=>bandPack b a) 4 (by intro a b; dsimp [bandPack,compPack,pairPack,nodePack]; omega)
    (Emission.bandPackP.comp ((Procedure.second packCode packCode).pair (Procedure.first packCode packCode)))
  have hi:=(ofProcedure Emission.constantPackP).comp (hk.pair (const _ _ true))
  have hr:=(ofProcedure (Procedure.listReverse packCode emptyPack)).comp hf
  refine ⟨fun x=>((f x).map erasePack).foldl bandPack (constantPack (k x) true),
    ((ofProcedure p).comp (hr.pair hi)).congr (fun x=>by dsimp only;rw [List.foldr_reverse]),?_⟩
  intro x
  dsimp only
  have hgen : ∀(fs:List (BooleanNetwork (k x) 1)) (a:Pack) (b:BooleanNetwork (k x) 1),a.val.value=erase b→
      ((fs.map erasePack).foldl bandPack a).val.value=erase (fs.foldl BooleanNetwork.band b):=by
    intro fs
    induction fs with
    | nil=>intro a b h;exact h
    | cons c cs ih=>intro a b h;exact ih _ _ (bandPack_value _ _ _ _ h rfl)
  exact hgen _ _ _ (constantPack_value _ true)
end NetsEmits
lemma filterPrefixEmitter {α : Type} {ea : α→List Bool} {k S B C W : α→ℕ} {w : α→ℕ→ℕ}
    (prev : ∀x s,BooleanNetwork (w x (s+1)) (w x s))
    (keep : ∀x s,BooleanNetwork (k x) (w x (s+1))→BooleanNetwork (k x) 1)
    (hp : ∀x s,(prev x s).net.count=0)
    (hc : ∀x s,s<S x→∀v: BooleanNetwork (k x) (w x (s+1)),v.net.count≤B x→(keep x s v).net.count≤C x)
    (hw : ∀x s,s≤S x→w x s≤W x)
    (v : ∀x,BooleanNetwork (k x) (w x (S x))) (hv : ∀x,(v x).net.count≤B x)
    (hS : Emits ea unaryCode S) (hk : Emits ea unaryCode k) (hV : NetEmits ea v)
    (hB : PolyAt (fun x=>(ea x).length) B) (hC : PolyAt (fun x=>(ea x).length) C)
    (hW : PolyAt (fun x=>(ea x).length) W)
    (hstep : Emits (fun x:Σa,{r:FilterState (k a) (w a) // 0<r.depth}=>prodCode ea filterCode (x.1,x.2.val.code))
      filterCode (fun x=>(filterStep (prev x.1) (keep x.1) x.2.val).code)) :
    NetEmits ea (fun x=>filterPrefix (prev x) (keep x) (S x) (v x)):=by
  let R:=fun x i=>(filterStep (prev x) (keep x))^[i] (⟨S x,v x,[]⟩ : FilterState (k x) (w x))
  have h0 : Emits ea filterCode (fun x=>(R x 0).code):=
    hS.pair (hV.canonical.pair (const _ _ []))
  have hs : Emits (fun x:Σa,Fin (S a)=>prodCode ea (prodCode unaryCode filterCode) (x.1,(x.2.val,(R x.1 x.2.val).code)))
      filterCode (fun x=>(R x.1 (x.2.val+1)).code):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode filterCode))).precompose
      (fun x:Σa,Fin (S a)=>(x.1,(x.2.val,(R x.1 x.2.val).code)))
    let g : (Σa,Fin (S a))→Σa,{r:FilterState (k a) (w a) // 0<r.depth}:=fun x=>⟨x.1,R x.1 x.2.val,by
      dsimp only [R];rw [filterRun_depth];dsimp only;exact Nat.sub_pos_of_lt x.2.isLt⟩
    have hh:=hstep.comp ((hx.fst.pair hx.snd.snd).recode (g:=g) (fun _=>rfl))
    exact hh.congr (fun x=>by dsimp only [g,R];rw [Function.iterate_succ_apply'])
  have hb : PolyAt (fun x:Σa,Fin (S a+1)=>(ea x.1).length) (fun x=>(filterCode (R x.1 x.2.val).code).length):=by
    have hs:=hS.unaryPoly
    have hh:=hk.unaryPoly
    let P:= (PolyAt.const _ 104).mul ((((hh.add hB).add hW).add (PolyAt.const _ 1)).pow 2)
    let Q:= (PolyAt.const _ 104).mul ((((hh.add hC).add (PolyAt.const _ 1)).add (PolyAt.const _ 1)).pow 2)
    apply (((PolyAt.const _ 2).mul hs).add (((PolyAt.const _ 2).mul P).add
      ((hs.mul (((PolyAt.const _ 2).mul Q).add (PolyAt.const _ 2))).add (PolyAt.const _ 5)))).pull
        (fun x:Σa,Fin (S a+1)=>x.1) |>.of_le
    intro x
    obtain ⟨hd,hr,hl,hls⟩:=filterRun_bounds (prev x.1) (keep x.1) (hp x.1) (S x.1) (B x.1) (C x.1) (hc x.1) (v x.1) (hv x.1) x.2.val
    have ht:=hw x.1 (R x.1 x.2.val).depth hd
    have hraw:=packCode_bound (erasePack (R x.1 x.2.val).raw)
    have hraw' : (packCode (erasePack (R x.1 x.2.val).raw)).length≤104*(k x.1+B x.1+W x.1+1)^2:=
      hraw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [erasePack,R] at *;omega) 2))
    have hlist:=listCode_length_bound packCode ((R x.1 x.2.val).pending.map erasePack) (104*(k x.1+C x.1+1+1)^2) (by
      intro a ha;obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
      exact (packCode_bound _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
        have hh:=hls b hb;dsimp only [erasePack];omega) 2)))
    simp only [filterCode,FilterState.code,prodCode,pairBits_length,unaryCode,List.length_replicate,List.length_map] at hlist ⊢
    dsimp only [R] at *
    have hi:=x.2.isLt
    nlinarith
  have hf:=BitStackProgram.Emits.stages (F:=fun x i=>(R x i).code) hS h0 hs hb
  exact (NetsEmits.foldlBand hk hf.snd.snd).congr (fun x=>filterRun_result (prev x) (keep x) (S x) (v x))
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/DescendingStepEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma filterStepEmitter {α : Type} {ea : α→List Bool} {k : α→ℕ} {w : α→ℕ→ℕ}
    (prev : ∀x s,BooleanNetwork (w x (s+1)) (w x s))
    (keep : ∀x s,BooleanNetwork (k x) (w x (s+1))→BooleanNetwork (k x) 1)
    (hp : NetEmits (prodCode ea unaryCode) (fun x=>prev x.1 x.2))
    (hc : NetEmits (fun x:Σa,Σs,BooleanNetwork (k a) (w a (s+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2))) (fun x=>keep x.1 x.2.1 x.2.2)) :
    Emits (fun x:Σa,{r:FilterState (k a) (w a) // 0<r.depth}=>prodCode ea filterCode (x.1,x.2.val.code))
      filterCode (fun x=>(filterStep (prev x.1) (keep x.1) x.2.val).code):=by
  let ix:=Σa,Σs,BooleanNetwork (k a) (w a (s+1)) × List (BooleanNetwork (k a) 1)
  let enc:ix→List Bool:=fun x=>prodCode ea filterCode (x.1,(x.2.1+1,erasePack x.2.2.1,x.2.2.2.map erasePack))
  have hx:=(BitStackProgram.Emits.id (prodCode ea filterCode)).precompose
    (fun x:ix=>(x.1,(x.2.1+1,erasePack x.2.2.1,x.2.2.2.map erasePack)))
  have hd: Emits enc unaryCode (fun x=>x.2.1):=
    ((hx.snd.fst.unaryNat.natSub (const _ _ 1)).boundedUnary hx.snd.fst (fun _=>Nat.sub_le _ _)).congr (fun _=>by dsimp only;omega)
  have hp':=hp.compInput (hx.fst.pair hd)
  have hr:=NetEmits.ofCanonical hx.snd.snd.fst
  have hraw:=(hr.comp hp').canonical
  let g:ix→Σa,Σs,BooleanNetwork (k a) (w a (s+1)):=fun x=>⟨x.1,x.2.1,x.2.2.1⟩
  have hk:=hc.canonical.comp ((hx.fst.pair (hd.pair hx.snd.snd.fst)).recode (g:=g) (fun _=>rfl))
  have hs:=hd.pair (hraw.pair (hk.listCons hx.snd.snd.snd))
  let view:(Σa,{r:FilterState (k a) (w a) // 0<r.depth})→ix:=fun x=>⟨x.1,x.2.val.positiveView x.2.property⟩
  have h:=hs.precompose view
  have he : (fun x=>enc (view x))=(fun x:Σa,{r:FilterState (k a) (w a) // 0<r.depth}=>prodCode ea filterCode (x.1,x.2.val.code)):=by
    funext x
    have hv:=x.2.val.positiveView_eq x.2.property
    exact congrArg (fun r=>prodCode ea filterCode (x.1,r.code)) hv
  change Emits (fun x=>enc (view x)) filterCode _ at h
  rw [he] at h
  exact h.congr (by
    intro x
    have hv:=x.2.val.positiveView_eq x.2.property
    exact congrArg (fun r=>(filterStep (prev x.1) (keep x.1) r).code) hv)
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/DescendingPrefixAutomatic.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma filterPrefixEmits {α : Type} {ea : α→List Bool} {k S W : α→ℕ} {w : α→ℕ→ℕ}
    (prev : ∀x s,BooleanNetwork (w x (s+1)) (w x s))
    (keep : ∀x s,BooleanNetwork (k x) (w x (s+1))→BooleanNetwork (k x) 1)
    (hp : ∀x s,(prev x s).net.count=0)
    (hw : ∀x s,s≤S x→w x s≤W x)
    (v : ∀x,BooleanNetwork (k x) (w x (S x)))
    (hS : Emits ea unaryCode S) (hk : Emits ea unaryCode k) (hV : NetEmits ea v)
    (hW : PolyAt (fun x=>(ea x).length) W)
    (hep : NetEmits (prodCode ea unaryCode) (fun x=>prev x.1 x.2))
    (hec : NetEmits (fun x:Σa,Σs,BooleanNetwork (k a) (w a (s+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2))) (fun x=>keep x.1 x.2.1 x.2.2)) :
    NetEmits ea (fun x=>filterPrefix (prev x) (keep x) (S x) (v x)):=by
  let ix:=Σa,Σs:Fin (S a),{r:BooleanNetwork (k a) (w a (s.val+1)) // r.net.count≤(v a).net.count}
  let enc:ix→List Bool:=fun x=>prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1.val,erasePack x.2.2.val))
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
    (fun x:ix=>(x.1,(x.2.1.val,erasePack x.2.2.val)))
  let g:ix→Σa,Σs,BooleanNetwork (k a) (w a (s+1)):=fun x=>⟨x.1,x.2.1.val,x.2.2.val⟩
  have he:=hec.compInput (hx.recode (g:=g) (fun _=>rfl))
  have hb : PolyAt (fun x:ix=>(ea x.1).length) (fun x=>(enc x).length):=by
    have hbound:=(PolyAt.const _ 104).mul ((((hk.unaryPoly.add hV.countPoly).add hW).add (PolyAt.const _ 1)).pow 2)
    apply ((((PolyAt.const _ 2).mul (PolyAt.self _)).add
      (((PolyAt.const _ 2).mul hS.unaryPoly).add hbound)).add (PolyAt.const _ 2)).pull (fun x:ix=>x.1) |>.of_le
    intro x
    have hs:=x.2.1.isLt
    have hc:=x.2.2.property
    have hw':=hw x.1 (x.2.1.val+1) (by omega)
    have hp':=(packCode_bound (erasePack x.2.2.val)).trans
      (Nat.mul_le_mul_left 104 (Nat.pow_le_pow_left (show k x.1+x.2.2.val.net.count+w x.1 (x.2.1.val+1)+1≤
        k x.1+(v x.1).net.count+W x.1+1 by omega) 2))
    simp only [enc,prodCode,pairBits_length,unaryCode,List.length_replicate]
    omega
  obtain ⟨p,hp'⟩:=he.countPoly.rebase hb
  exact filterPrefixEmitter (C:=fun x=>p.eval (ea x).length) prev keep hp
    (fun x s hs r hr=>hp' ⟨x,⟨s,hs⟩,r,hr⟩) hw v (fun _=>le_rfl) hS hk hV
    hV.countPoly ⟨p,fun _=>le_rfl⟩ hW (filterStepEmitter prev keep hep hec)
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TransitionEncodingEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k n K : α→ℕ}
lemma transitionEncode {f : ∀x,Fin (K x)→BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>TransitionWords.encodeNet (f x)):=by
  apply vectorOfFn hk (hn.unaryMul (hK.unaryAdd (const _ _ 1)))
  let X:=Σa,Fin (n a*(K a+1))
  let ix:=fun x:X=>finProdFinEquiv.symm (Fin.cast (Nat.mul_comm _ _) x.2)
  let c:=fun x:X=>(ix x).1.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:X=>(x.2.val,x.1))
  have row:=hx.fst.unaryNat.natDiv (hn.comp hx.snd).unaryNat
  have col:=hx.fst.unaryNat.natMod (hn.comp hx.snd).unaryNat
  have hc : Emits (fun x:X=>prodCode unaryCode ea (x.2.val,x.1)) Procedure.boolCode (fun x=>decide (c x)):=
    row.natLt (hK.comp hx.snd).unaryNat
  apply NetEmits.splitOn c hc
  · have hy:=hx.precompose (fun x:{x:X // c x}=>x.val)
    have hp : Emits (fun x:{x:X // c x}=>prodCode unaryCode ea (x.val.2.val,x.val.1))
        (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1))
        (fun x=>(⟨x.val.1,⟨(ix x.val).1.val,x.property⟩⟩ : Σa,Fin (K a))):=by
      exact (((row.precompose (fun x:{x:X // c x}=>x.val)).boundedUnary
        (hK.comp hy.snd) (fun x=>x.property.le)).pair hy.snd).recode (by intro x;rfl)
    have hnf:=hf.compInput hp
    have hsel:=hnf.rewire (fun x (_ : Fin 1)=>(ix x.val).2)
      (((col.precompose (fun x:{x:X // c x}=>x.val)).listCons (const _ _ [])).congr
        (by intro x;simp [ix]))
    exact hsel.congr (by intro x;dsimp only [TransitionWords.encodeNet];rw [dite_eq_left x.property])
  · exact (constant (hk.comp (hx.precompose (fun x:{x:X // ¬c x}=>x.val)).snd) (const _ _ false)).congr
      (by intro x;dsimp only [TransitionWords.encodeNet];rw [dite_eq_right x.property])
end ExactQuantumFactoring.NetworkEmission.NetEmits

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalListOutputEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalListEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma sample (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.sampleNet (n x)):=
  selectSlice (ListSamplerEmission.width hn) hn (hn.unaryNat.natAdd hn.unaryNat) _ (by intros;rfl)
lemma ordinary (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.ordinaryNet (n x)):=by
  apply transitionEncode (ordinaryWidth hn) hn (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  have hn':=hn.comp hx.snd
  exact (NetEmits.tensorSelect (ListSamplerEmission.width hn') (hn'.unaryPow 5) (fun x=>x.2) hx.fst.unaryNat).comp
    (sample hn')
lemma output (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.outputNet (n x)):=
  completionOutput (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    (hn.unaryMul (hn.unaryPow 5)) (ordinary hn)
end ExactQuantumFactoring.PhysicalListEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalOrderEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalOrderEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n w b : α→ℕ}
lemma samplerZero (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderSlots.samplerZeroNet (w x) (b x)):=by
  have hi:=hw.unaryAdd hw
  exact ((identity hi).pair (zeros hi (TriangularEmission.width hb))).packNet
    (zeros hi hw) hi (OrderSamplerEmission.scratch hw hb)
lemma rawZero (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>OrderSlots.rawZeroNet (n x)):=
  (zeros (hn.unaryAdd hn) (const _ _ 2)).pair
    ((samplerZero hn ((sampleExponent hn).unaryAdd (const _ _ 2))).pair
      (zeros (hn.unaryAdd hn) (OrderSamplerEmission.guessWidth hn)))
lemma ordinaryWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.ordinaryWidth (n x)):=
  (OrderSamplerEmission.rawWidth hn (sampleExponent hn) hn).tensorWidth (hn.unaryPow 5)
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.width (n x)):=
  completionWidth (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5))
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>OrderSlots.program (n x)):=
  OpsEmits.completion (OpsEmits.tensor (OrderSamplerEmission.rawProgram hn (sampleExponent hn) hn)
    (OrderSamplerEmission.rawWidth hn (sampleExponent hn) hn) (hn.unaryPow 5))
    (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5))
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>OrderSlots.initialNet (n x)):=by
  apply completionInitial (hn.unaryAdd hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5))
  apply tensor (hn.unaryAdd hn) (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  exact rawZero (hn.comp hx.snd)
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.work (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.launchWidth (n x)):=
  ((hn.unaryAdd hn).unaryAdd (width hn)).unaryAdd (work hn)
lemma launch (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>OrderSlots.launch (n x)):=
  OpsEmits.prepared (initial hn) (hn.unaryAdd hn) (fun _=>le_rfl) (program hn)
end ExactQuantumFactoring.PhysicalOrderEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalSplitEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalSplitEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma ordersWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.ordersWidth (n x)):=
  (PhysicalOrderEmission.width hn).tensorWidth (hn.unaryPow 5)
lemma ordersProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>FixedSplit.ordersProgram (n x)):=
  OpsEmits.tensor (PhysicalOrderEmission.program hn) (PhysicalOrderEmission.width hn) (hn.unaryPow 5)
lemma listWires (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.listWires (n x)):=
  targetSelect hn (PhysicalListEmission.width hn) (PhysicalListEmission.work hn)
lemma modulusWires (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.modulusWires (n x)):=
  firstSelect hn (PhysicalListEmission.width hn) (PhysicalListEmission.work hn)
lemma base (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.baseNet (i x)):=
  ((listWires hn).comp (PhysicalListEmission.output hn)).rewireSlice hn (hn.unaryNat.natMul hi) _
    (by intro x j; change j.val+n x*(i x).val=n x*(i x).val+j.val; omega)
lemma orderInitial (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.orderInitialNet (i x)):=
  ((base hn i hi).pair (modulusWires hn)).comp (PhysicalOrderEmission.initial hn)
lemma ordersInitial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.ordersInitialNet (n x)):=by
  apply tensor (PhysicalListEmission.launchWidth hn) (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  exact orderInitial (hn.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.work (n x)):=(ordersInitial hn).count
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.width (n x)):=
  ((PhysicalListEmission.launchWidth hn).unaryAdd (ordersWidth hn)).unaryAdd (work hn)
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>FixedSplit.program (n x)):=
  OpsEmits.appendPrepared (PhysicalListEmission.launch hn) (ordersInitial hn)
    (PhysicalListEmission.launchWidth hn) (fun _=>le_rfl) (ordersProgram hn)
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.initialNet (n x)):=
  ((identity hn).packNet (zeros hn (PhysicalListEmission.width hn)) hn (PhysicalListEmission.work hn)).packNet
    (zeros hn (ordersWidth hn)) hn (work hn)
lemma launchWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.launchWork (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.launchWidth (n x)):=
  (hn.unaryAdd (width hn)).unaryAdd (launchWork hn)
lemma launch (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>FixedSplit.launch (n x)):=
  OpsEmits.prepared (initial hn) hn (fun _=>le_rfl) (program hn)
end ExactQuantumFactoring.PhysicalSplitEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/LabelRecoveryEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic OrderTrial
variable {α : Type} {ea : α→List Bool} {n w K : α→ℕ}
lemma checkedConvergent {Q B k : ∀x,BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hQ : NetEmits ea Q) (hB : NetEmits ea B) (hk : NetEmits ea k) :
    NetEmits ea (fun x=>OrderTrial.checkedConvergent (K x) (Q x) (B x) (k x)):=by
  have hc:=(hk.pair hQ).comp (convergent hw hK)
  have hd:=hc.comp (rootGuess hw)
  have hj:=hc.comp (rootModulus hw)
  have hp : NetEmits ea (fun x=>binCheckExpr.isOne ![Q x,B x,k x,
      ((k x).pair (Q x) |>.comp (convergentNet (w x) (K x))).comp (BitArithmetic.rootGuess (w x)),
      ((k x).pair (Q x) |>.comp (convergentNet (w x) (K x))).comp (BitArithmetic.rootModulus (w x))]):=by
    apply isOne (const _ _ binCheckExpr) hn hw
    intro i;fin_cases i
    · exact hQ
    · exact hB
    · exact hk
    · exact hd
    · exact hj
  exact (hp.wordMux hd (wordConst hn hw (const _ _ 0)) hw).pair
    (hp.wordMux hj (wordConst hn hw (const _ _ 0)) hw)
lemma pairChoice (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>OrderTrial.pairChoice (w x)):=by
  have hw2:=hw.unaryAdd hw
  have hl:=rootModulus hw2
  have hr:=rootGuess hw2
  exact ((hl.comp (rootModulus hw)).equalOn (wordConst (hw2.unaryAdd hw2) hw (const _ _ 0)) hw).wordMux hr hl hw2
lemma recovery {Q B k : ∀x,BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hQ : NetEmits ea Q) (hB : NetEmits ea B) (hk : NetEmits ea k) :
    NetEmits ea (fun x=>OrderTrial.recoveryNet (Q x) (B x) (k x) (K x)):=by
  apply boundedStages hK (f:=fun x j=>OrderTrial.recoveryNet (Q x) (B x) (k x) j)
  · exact (wordConst hn hw (const _ _ 0)).pair (wordConst hn hw (const _ _ 0))
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (K a)=>(x.1,(x.2.val,erasePack (OrderTrial.recoveryNet (Q x.1) (B x.1) (k x.1) x.2.val))))
    exact ((checkedConvergent (hn.comp hx.fst) (hw.comp hx.fst) hx.snd.fst
      (hQ.compInput hx.fst) (hB.compInput hx.fst) (hk.compInput hx.fst)).pair
        (ofCanonical hx.snd.snd)).comp (pairChoice (hw.comp hx.fst))
  · exact hn.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  · exact (hw.unaryPoly.add hw.unaryPoly).pull (fun x:Σa,Fin (K a+1)=>x.1)
  · exact OrderTrial.recoveryNet_poly
      (hQ.count.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1))
      (hB.count.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1))
      (hk.count.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1))
      (hw.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1))
      ((hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)).of_le (by intro x;have:=x.2.isLt;omega))
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SamplerDecodeEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.SamplerDecodeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k u b : α→ℕ}
lemma sampleY (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderTrial.sampleYNet (u x) (b x)):=
  selectSlice (OrderSamplerEmission.width hu hb) hb (hu.unaryAdd hu).unaryNat _ (by intros;rfl)
lemma sampleU (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderTrial.sampleUNet (u x) (b x)):=
  selectSlice (OrderSamplerEmission.width hu hb) hu (OrderSamplerEmission.inputWidth hu hb).unaryNat _ (by intros;rfl)
lemma triangular {y : ∀x,BooleanNetwork (k x) (b x)}
    (hk : Emits ea unaryCode k) (hb : Emits ea unaryCode b) (hy : NetEmits ea y) :
    NetEmits ea (fun x=>OrderTrial.triangularSelectedNet (y x)):=
  (hy.pair (zeros hk hb)).packNet (zeros hk (hb.unaryAdd hb)) hk (TriangularEmission.work hb)
lemma selected {a m : ∀x,BooleanNetwork (k x) (u x)} {z : ∀x,BooleanNetwork (k x) (OrderSample.width (u x) (b x))}
    (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hz : NetEmits ea z) :
    NetEmits ea (fun x=>OrderTrial.samplerSelectedNet (a x) (m x) (z x)):=
  hz.equalOn ((((ha.pair hm).pair (triangular hk hb (hz.comp (sampleY hu hb)))).packNet
    (hz.comp (sampleU hu hb)) hk (OrderSamplerEmission.scratch hu hb))) (OrderSamplerEmission.width hu hb)
end ExactQuantumFactoring.SamplerDecodeEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RawTrialLabelEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.RawTrialEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k u s n : α→ℕ}
lemma decodeSteps (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>OrderTrial.decodeSteps (s x)):=
  ((const _ _ 2).unaryMul (hs.unaryAdd (const _ _ 3))).unarySucc
lemma decodeWidth (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) :
    Emits ea unaryCode (fun x=>OrderTrial.decodeWidth (u x) (s x) (n x)):=
  ((((((hs.unaryAdd (const _ _ 3)).unaryMul (decodeSteps hs).unarySucc).unarySucc.unaryAdd hu).unaryAdd hn).unaryAdd
    (retentionBits hn)).unaryAdd (hs.unaryAdd (const _ _ 3))).unaryAdd (const _ _ 3)
variable {r : ∀x,BooleanNetwork (k x) (OrderTrial.rawWidth (u x) (s x) (n x))}
lemma recovered (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (hr : NetEmits ea r) : NetEmits ea (fun x=>OrderTrial.recoveredPairNet (r x)):=by
  have hw:=decodeWidth hu hs hn
  have hp:=NetworkEmission.Emits.powTwo (hs.unaryAdd (const _ _ 2))
  have hb:=NetworkEmission.Emits.powTwo hn
  exact recovery hk hw (decodeSteps hs) (wordConst hk hw hp) (wordConst hk hw hb)
    (((sample hu hs hn hr).comp (SamplerDecodeEmission.sampleY hu (hs.unaryAdd (const _ _ 2)))).toWidth (hs.unaryAdd (const _ _ 2)) hw)
lemma pair (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (hr : NetEmits ea r) : NetEmits ea (fun x=>OrderTrial.trialPairNet (r x)):=by
  have hw:=decodeWidth hu hs hn
  exact (((mode hu hs hn hr).toWidth (const _ _ 2) hw).wordLt (wordConst hk hw (const _ _ 2)) hw).wordMux
    (recovered hk hu hs hn hr) (((den hu hs hn hr).toWidth hn hw).pair ((num hu hs hn hr).toWidth hn hw)) (hw.unaryAdd hw)
lemma trialDen (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (hr : NetEmits ea r) : NetEmits ea (fun x=>OrderTrial.trialDenNet (r x)):=
  (pair hk hu hs hn hr).comp (left (decodeWidth hu hs hn) (decodeWidth hu hs hn))
lemma trialNum (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (hr : NetEmits ea r) : NetEmits ea (fun x=>OrderTrial.trialNumNet (r x)):=
  (pair hk hu hs hn hr).comp (right (decodeWidth hu hs hn) (decodeWidth hu hs hn))
end ExactQuantumFactoring.RawTrialEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RawTrialDecoderEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.RawTrialEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k u s n : α→ℕ}
variable {r : ∀x,BooleanNetwork (k x) (OrderTrial.rawWidth (u x) (s x) (n x))} {a m : ∀x,BooleanNetwork (k x) (u x)}
lemma accept (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawAcceptNet (a x) (m x) (r x)):=by
  have hw:=decodeWidth hu hs hn
  exact TrialControlEmission.accept hk hw hn (ha.toWidth hu hw) (hm.toWidth hu hw)
    ((mode hu hs hn hr).toWidth (const _ _ 2) hw) (trialDen hk hu hs hn hr) (trialNum hk hu hs hn hr)
    ((residue hu hs hn hr).toWidth hn hw) ((coin hu hs hn hr).toWidth (retentionBits hn) hw)
    (SamplerDecodeEmission.selected hk hu (hs.unaryAdd (const _ _ 2)) ha hm (sample hu hs hn hr))
lemma value (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.trialValueNet (a x) (m x) (r x)):=by
  have hw:=decodeWidth hu hs hn
  exact (accept hk hu hs hn ha hm hr).wordMux (trialDen hk hu hs hn hr) (wordConst hk hw (const _ _ 0)) hw
lemma smallValue (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.trialSmallValueNet (a x) (m x) (r x)):=
  (value hk hu hs hn ha hm hr).comp (resize (decodeWidth hu hs hn) hn)
end ExactQuantumFactoring.RawTrialEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalOrderOutputEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalOrderEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
variable {a m : ∀x,BooleanNetwork (k x) (n x)}
lemma usable (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>OrderSlots.usableOn (a x) (m x)):=
  (ha.wordLt hm hn).band (((ha.pair hm).comp (gcd hn)).equalOn (wordConst hk hn (const _ _ 1)) hn)
lemma result {r : ∀x,BooleanNetwork (k x) (OrderSlots.ordinaryWidth (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderSlots.orderResultNet (a x) (m x) (r x)):=by
  apply minimum hk hn (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  have hn':=hn.comp hx.snd
  have hs:=sampleExponent hn'
  exact RawTrialEmission.smallValue (hk.comp hx.snd) hn' hs hn'
    (ha.compInput hx.snd) (hm.compInput hx.snd)
    ((hr.compInput hx.snd).comp (NetEmits.tensorSelect (OrderSamplerEmission.rawWidth hn' hs hn')
      (hn'.unaryPow 5) (fun x=>x.2) hx.fst.unaryNat))
lemma ordinary {r : ∀x,BooleanNetwork (k x) (OrderSlots.ordinaryWidth (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderSlots.ordinaryOn (a x) (m x) (r x)):=
  ((usable hk hn ha hm).wordMux (result hk hn ha hm hr) (wordConst hk hn (const _ _ 0)) hn).comp
    (resize hn (transitionWidth hn))
lemma output {r : ∀x,BooleanNetwork (k x) (OrderSlots.width (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderSlots.outputOn (a x) (m x) (r x)):=by
  have hq:=ordinaryWidth hn
  have hW:=transitionWidth hn
  have ht:=(const _ _ 2).unaryMul hn
  have hd:=(hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5)
  exact (hr.comp (rareNet hq hW ht hd)).wordMux (hr.comp (guessWires hq hW ht hd))
    (ordinary hk hn ha hm (hr.comp (ordinaryWires hq hW ht hd))) hW
end ExactQuantumFactoring.PhysicalOrderEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FirstProperEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma dropOfFn_step {β : Type} {K j : ℕ} (f : Fin K→β) (hj : j<K) :
    (List.ofFn f).drop (K-(j+1))=f ⟨K-(j+1),by omega⟩ :: (List.ofFn f).drop (K-j):=by
  rw [List.drop_eq_getElem_cons (by simp only [List.length_ofFn];omega)]
  simp only [List.getElem_ofFn]
  congr 2;omega
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {k w K : α→ℕ}
lemma firstProper {m : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hm : NetEmits ea m)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.firstProperNet (m x) (List.ofFn (f x))):=by
  let F:=fun x j=>BitArithmetic.firstProperNet (m x) ((List.ofFn (f x)).drop (K x-j))
  have h0 : NetEmits ea (fun x=>F x 0):=by
    have hz : NetEmits ea (fun x=>BitArithmetic.wordConstant (n:=k x) (0 : BitVec (w x))) := by
      simpa only [BitVec.ofNat_eq_ofNat] using wordConst hk hw (const _ _ 0)
    refine hz.congr ?_
    intro x
    dsimp only [F]
    rw [Nat.sub_zero,List.drop_eq_nil_of_le (by simp only [List.length_ofFn];exact le_rfl)]
    rfl
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
    have hd:=hf.compInput hy
    have hstep:=(properOn (hk.comp hx.fst) (hw.comp hx.fst) (hm.compInput hx.fst) hd).wordMux
      hd (ofCanonical hx.snd.snd) (hw.comp hx.fst)
    convert hstep using 1
    funext x
    dsimp only [F]
    rw [dropOfFn_step _ x.2.isLt,BitArithmetic.firstProperNet]
  have hb:=hk.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hw':=hw.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hc : NetworkAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>F x.1 x.2.val):=by
    apply NetworkAt.firstProperNet (hm.countPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)) hw'
    · exact (hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)).of_le (by intro x;simp only [List.length_drop,List.length_ofFn];omega)
    · obtain ⟨p,hp⟩:=countPolyIndexed hK hf
      refine ⟨p,?_⟩
      intro x d hd
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hd)
      exact hp ⟨x.1,i⟩
  simpa only [F,Nat.sub_self,List.drop_zero] using boundedStages hK h0 hs hb hw' hc
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SuppliedDivisorEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k n e K : α→ℕ}
lemma rootOn {m : ∀x,BooleanNetwork (k x) (n x+1)}
    (hn : Emits ea unaryCode n) (he : Emits ea unaryCode e) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>BitArithmetic.rootOn (n x) (e x) (m x)):=by
  have hr:=(hn.unaryMul hn).unarySucc
  exact ((hm.comp (resize hn.unarySucc hr)).comp (boundedRoot hn he)).comp (resize hr hn.unarySucc)
lemma rootsOn {m : ∀x,BooleanNetwork (k x) (n x+1)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>BitArithmetic.rootsOn (n x) (m x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (n a+1)=>(x.2.val,x.1))
  have hf:=rootOn (hn.comp hx.snd) hx.fst (hm.compInput hx.snd)
  have h:=firstProper (f:=fun x i=>BitArithmetic.rootOn (n x) i.val (m x)) hk hn.unarySucc hn.unarySucc hm hf
  refine h.congr ?_
  intro x
  unfold BitArithmetic.rootsOn
  congr 1
  exact ofFn_nat_eq_map (n x+1) (fun i=>BitArithmetic.rootOn (n x) i (m x))
lemma ordersBits {w : α→ℕ} {m : ∀x,BooleanNetwork (k x) (w x)}
    {a : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    {r : ∀x,Fin (K x)→BooleanNetwork (k x) (e x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e)
    (hK : Emits ea unaryCode K) (hm : NetEmits ea m)
    (ha : NetEmits (fun x:Σb,Fin (K b)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>a x.1 x.2))
    (hr : NetEmits (fun x:Σb,Fin (K b)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>r x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ordersBits (m x) (List.ofFn (fun i=>(a x i,r x i)))):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σb,Fin (K b)=>(x.2.val,x.1))
  have hf:=candidateBits (hk.comp hx.snd) (hw.comp hx.snd) (he.comp hx.snd) ha (hm.compInput hx.snd) hr
  convert firstProper (f:=fun x i=>BitArithmetic.candidateBits (a x i) (m x) (r x i)) hk hw hK hm hf using 1
  funext x
  simp only [BitArithmetic.ordersBits,List.map_ofFn,Function.comp_def]
lemma suppliedBits {m : ∀x,BooleanNetwork (k x) (n x+1)}
    {a : ∀x,Fin (K x)→BooleanNetwork (k x) (n x+1)}
    {r : ∀x,Fin (K x)→BooleanNetwork (k x) (e x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (he : Emits ea unaryCode e)
    (hK : Emits ea unaryCode K) (hm : NetEmits ea m)
    (ha : NetEmits (fun x:Σb,Fin (K b)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>a x.1 x.2))
    (hr : NetEmits (fun x:Σb,Fin (K b)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>r x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.suppliedBits (n x) (m x) (List.ofFn (fun i=>(a x i,r x i)))):=by
  have roots:=rootsOn hk hn hm
  exact (evenOn hk hn.unarySucc hm).wordMux (wordConst hk hn.unarySucc (const _ _ 2))
    ((properOn hk hn.unarySucc hm roots).wordMux roots (ordersBits hk hn.unarySucc he hK hm ha hr) hn.unarySucc) hn.unarySucc
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalSplitDecoderEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.PhysicalSplitEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma launchWires (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.launchWires (n x)):=
  firstSelect (PhysicalListEmission.launchWidth hn) (ordersWidth hn) (work hn)
lemma allOrderWires (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.allOrderWires (n x)):=
  targetSelect (PhysicalListEmission.launchWidth hn) (ordersWidth hn) (work hn)
lemma modulus (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.modulusNet (n x)):=
  (launchWires hn).comp (modulusWires hn)
lemma actualBase (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.actualBaseNet (i x)):=
  (launchWires hn).comp (base hn i hi)
lemma actualOrderRaw (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.actualOrderRawNet (i x)):=
  (allOrderWires hn).comp (NetEmits.tensorSelect (PhysicalOrderEmission.width hn) (hn.unaryPow 5) i hi)
lemma actualOrder (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.actualOrderNet (i x)):=
  PhysicalOrderEmission.output (width hn) hn (actualBase hn i hi) (modulus hn) (actualOrderRaw hn i hi)
lemma divisor (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.divisorNet (n x)):=by
  apply suppliedBits (width hn) hn (BitStackProgram.Emits.transitionWidth hn) (hn.unaryPow 5)
    ((modulus hn).comp (resize hn hn.unarySucc))
  · have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
      (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
    have hN:=hn.comp hx.snd
    exact (actualBase hN (fun x=>x.2) hx.fst.unaryNat).comp (resize hN hN.unarySucc)
  · have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
      (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
    exact actualOrder (hn.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
end ExactQuantumFactoring.PhysicalSplitEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeControlEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NodeControlEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
open BitArithmetic.NodeCircuit
variable {α : Type} {ea : α→List Bool} {s w : α→ℕ}
lemma stackWidth (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : Emits ea unaryCode (fun x=>(s x+1)*w x):=hs.unarySucc.unaryMul hw
lemma width (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : Emits ea unaryCode (fun x=>BitArithmetic.NodeCircuit.width (s x) (w x)):=
  (stackWidth hs hw).unaryAdd hw
lemma pending (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.pending (s x) (w x)):=left (stackWidth hs hw) hw
lemma divisor (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.divisor (s x) (w x)):=right (stackWidth hs hw) hw
lemma top (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.top (s x) (w x)):=
  (pending hs hw).comp (blockNet hs.unarySucc hw (fun _=>0) (const _ _ 0))
lemma popped (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.popped (s x) (w x)):=
  (pending hs hw).comp (stackPop hs.unarySucc hw)
lemma quotient (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.quotient (s x) (w x)):=
  ((top hs hw).pair (divisor hs hw)).comp (div hw)
lemma isPrime (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.isPrime (s x) (w x)):=
  (top hs hw).comp (primeWord hw)
lemma isDone (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.isDone (s x) (w x)):=
  zeroWord (width hs hw) hw (top hs hw)
lemma isProper (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.isProper (s x) (w x)):=
  properOn (width hs hw) hw (top hs hw) (divisor hs hw)
lemma split (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.split (s x) (w x)):=
  stackPush (width hs hw) hs.unarySucc hw (divisor hs hw)
    (stackPush (width hs hw) hs.unarySucc hw (quotient hs hw) (popped hs hw))
lemma next (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.next (s x) (w x)):=
  (isDone hs hw).wordMux (pending hs hw) ((isPrime hs hw).wordMux (popped hs hw)
    ((isProper hs hw).wordMux (split hs hw) (pending hs hw) (stackWidth hs hw)) (stackWidth hs hw)) (stackWidth hs hw)
lemma emitted (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.emitted (s x) (w x)):=by
  exact (isPrime hs hw).wordMux (top hs hw) (by simpa only [BitVec.ofNat_eq_ofNat] using wordConst (width hs hw) hw (const _ _ 0)) hw
lemma failed (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeCircuit.failed (s x) (w x)):=
  ((isDone hs hw).bnot.band (isPrime hs hw).bnot).band (isProper hs hw).bnot
end ExactQuantumFactoring.NodeControlEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeStateEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NodeStateEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {s w : α→ℕ}
lemma width (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : Emits ea unaryCode (fun x=>BitArithmetic.NodeStateCircuit.width (s x) (w x)):=
  ((NodeControlEmission.stackWidth hs hw).unaryAdd (NodeControlEmission.stackWidth hs hw)).unarySucc
lemma inWidth (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : Emits ea unaryCode (fun x=>BitArithmetic.NodeStateCircuit.inWidth (s x) (w x)):=
  (width hs hw).unaryAdd hw
lemma pending (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.pending (s x) (w x)):=by
  exact selectSlice (width hs hw) (NodeControlEmission.stackWidth hs hw) (const _ _ 0) _ (by intros;simp only [Function.comp_apply,Fin.val_castAdd,Nat.zero_add])
lemma output (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.output (s x) (w x)):=by
  exact selectSlice (width hs hw) (NodeControlEmission.stackWidth hs hw) (NodeControlEmission.stackWidth hs hw).unaryNat _ (by intros;rfl)
lemma bad (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.bad (s x) (w x)):=
  right ((NodeControlEmission.stackWidth hs hw).unaryAdd (NodeControlEmission.stackWidth hs hw)) (const _ _ 1)
lemma top (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.top (s x) (w x)):=
  (pending hs hw).comp (blockNet hs.unarySucc hw (fun _=>0) (const _ _ 0))
lemma old (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.old (s x) (w x)):=left (width hs hw) hw
lemma supplied (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.supplied (s x) (w x)):=right (width hs hw) hw
lemma nodeInput (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.nodeInput (s x) (w x)):=
  ((old hs hw).comp (pending hs hw)).pair (supplied hs hw)
lemma nextPending (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.nextPending (s x) (w x)):=
  (nodeInput hs hw).comp (NodeControlEmission.next hs hw)
lemma emission (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.emission (s x) (w x)):=
  (nodeInput hs hw).comp (NodeControlEmission.emitted hs hw)
lemma nextOutput (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.nextOutput (s x) (w x)):=
  (zeroWord (inWidth hs hw) hw (emission hs hw)).wordMux ((old hs hw).comp (output hs hw))
    (stackPush (inWidth hs hw) hs.unarySucc hw (emission hs hw) ((old hs hw).comp (output hs hw))) (NodeControlEmission.stackWidth hs hw)
lemma nextBad (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.nextBad (s x) (w x)):=
  ((old hs hw).comp (bad hs hw)).bor ((nodeInput hs hw).comp (NodeControlEmission.failed hs hw))
lemma step (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.step (s x) (w x)):=
  ((nextPending hs hw).pair (nextOutput hs hw)).pair (nextBad hs hw)
end ExactQuantumFactoring.NodeStateEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SortingEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.SortingEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k w r : α→ℕ}
lemma paddedPair {a b : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>BitArithmetic.paddedPair (a x) (b x)):=
  (zeroWord hk hw hb).bor ((zeroWord hk hw ha).bnot.band (ha.wordLe hb hw))
lemma head (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.headNet (w x) (r x)):=left hw (hw.tensorWidth hr)
lemma tail (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.tailNet (w x) (r x)):=right hw (hw.tensorWidth hr)
lemma keepHead {a : ∀x,BooleanNetwork (tensorWidth (w x) (r x)) (tensorWidth (w x) (r x))}
    (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.keepHead (a x)):=
  (head hw hr).pair ((tail hw hr).comp ha)
lemma compareStep (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.compareStep (w x) (r x)):=by
  have ha:=head hw hr.unarySucc
  have hb:=(tail hw hr.unarySucc).comp (head hw hr)
  have hrest:=(tail hw hr.unarySucc).comp (tail hw hr)
  have hp:=paddedPair (hw.tensorWidth hr.unarySucc.unarySucc) hw ha hb
  exact (hp.wordMux ha hb hw).pair ((hp.wordMux hb ha hw).pair hrest)
lemma insert (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.insertNet (w x) (r x)):=by
  apply boundedStages hr (f:=fun x j=>BitArithmetic.SortedWords.insertNet (w x) j)
  · exact identity (hw.tensorWidth (const _ _ 1))
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (r a)=>(x.1,(x.2.val,erasePack (BitArithmetic.SortedWords.insertNet (w x.1) x.2.val))))
    exact (compareStep (hw.comp hx.fst) hx.snd.fst).comp
      (keepHead (hw.comp hx.fst) hx.snd.fst.unarySucc (ofCanonical hx.snd.snd))
  · exact ((hw.tensorWidth hr.unarySucc).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · exact ((hw.tensorWidth hr.unarySucc).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · have hb:=(hr.unaryPoly.mul (((PolyAt.const _ 498).mul hw.unaryPoly).add (PolyAt.const _ 114))).pull
      (fun x:Σa,Fin (r a+1)=>x.1)
    exact hb.of_le (by
      intro x
      exact (BitArithmetic.SortedWords.insertNet_count _ _).trans (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)))
lemma sort (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.sortNet (w x) (r x)):=by
  apply boundedStages hr (f:=fun x j=>BitArithmetic.SortedWords.sortNet (w x) j)
  · exact identity (const _ _ 0)
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (r a)=>(x.1,(x.2.val,erasePack (BitArithmetic.SortedWords.sortNet (w x.1) x.2.val))))
    exact (keepHead (hw.comp hx.fst) hx.snd.fst (ofCanonical hx.snd.snd)).comp (insert (hw.comp hx.fst) hx.snd.fst)
  · exact ((hw.tensorWidth hr).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · exact ((hw.tensorWidth hr).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · have hb:=((hr.unaryPoly.mul hr.unaryPoly).mul (((PolyAt.const _ 498).mul hw.unaryPoly).add (PolyAt.const _ 114))).pull
      (fun x:Σa,Fin (r a+1)=>x.1)
    exact hb.of_le (by
      intro x
      exact (BitArithmetic.SortedWords.sortNet_count _ _).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul (by have:=x.2.isLt;omega) (by have:=x.2.isLt;omega))))
end ExactQuantumFactoring.SortingEmission

end



end OAI
