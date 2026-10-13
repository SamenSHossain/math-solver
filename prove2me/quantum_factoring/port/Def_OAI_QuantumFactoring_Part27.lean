/-
Exact quantum factoring development (port of OpenAI's formalization), part 27 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: BitStackIteration.lean, BitStackNaturals.lean, BitStackChoice.lean, BitStackWords.lean, BitStackBooleans.lean, BitStackFold.lean, BitStackBinaryBasics.lean, BitStackUnary.lean, BitStackAdder.lean, BitStackSubtractor.lean, Procedure.lean, NetworkEmissionModel.lean, NetworkEmissionPair.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part26

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackIteration.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α : Type} {ea : α→List Bool} {f : α→α}

/-- Return the result to one fixed public register. Both word movements are
implemented by two reversals; no output-to-input renaming is a TM operation. -/
noncomputable def inplace (p : Procedure ea ea f) : Procedure ea ea f where
  K:=p.K ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (moveWord (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1))
    (.seq (p.program.relabel Sum.inl)
      (moveWord (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 8*Polynomial.X+Polynomial.C 5*p.bound+Polynomial.C 4
  runs a:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs a
    have h1:=moveWord_runs (Sum.inr 0 : p.K ⊕ Fin 2) (Sum.inl p.input) (Sum.inr 1)
      (by simp) (by simp) (by simp) (ea a)
    have h2:=hp.relabel (leftEmbed p.K (Fin 2)) (fun _=>[])
    simp only [overlay_singleton] at h2
    have h3:=moveWord_runs (Sum.inl p.output : p.K ⊕ Fin 2) (Sum.inr 0) (Sum.inr 1)
      (by simp) (by simp) (by simp) (ea (f a))
    refine ⟨(4*(ea (f a)).length+2)+cp+(4*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    have hl:=p.output_length_le a
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

lemma inplace_register (p : Procedure ea ea f) : p.inplace.output=p.inplace.input := rfl

/-- Literal repetition of an in-place subroutine by a unary counter. Each
iteration consumes one control token; the bound charges every subroutine step. -/
lemma iterate_loop_runs {L : Type} [DecidableEq L] (p : Procedure ea ea f)
    (he : p.output=p.input) (k : L) (n : ℕ) (a : α) (B : ℕ)
    (hm : ∀ i≤n,(ea ((f^[i]) a)).length≤B) (s : Store L)
    (hs : s k=List.replicate n true) :
    ∃ c,c≤n*(p.bound.eval B+1)+1 ∧
      Runs (.loop (Sum.inr k) (p.program.relabel Sum.inl) (p.program.relabel Sum.inl))
        (sumStore (singletonStore p.input (ea a)) s)
        (sumStore (singletonStore p.input (ea ((f^[n]) a))) (Function.update s k [])) c := by
  induction n generalizing a s with
  | zero =>
    have hk : Function.update s k []=s := by
      simp only [List.replicate_zero] at hs
      rw [←hs,Function.update_eq_self]
    refine ⟨1,by simp,?_⟩
    rw [Function.iterate_zero_apply,hk]
    apply Runs.loop_nil
    exact hs
  | succ n ih =>
    let t:=Function.update s k (List.replicate n true)
    have ht : t k=List.replicate n true:=by simp [t]
    have hm' : ∀ i≤n,(ea ((f^[i]) (f a))).length≤B := by
      intro i hi
      simpa only [Function.iterate_succ_apply] using hm (i+1) (by omega)
    obtain ⟨ct,hct,hrt⟩:=ih (f a) hm' t ht
    obtain ⟨cp,hcp,hrp⟩:=p.runs a
    rw [he] at hrp
    have hcall:=hrp.left t
    have hcpB : cp≤p.bound.eval B:=
      hcp.trans (eval_nat_mono p.bound (by simpa using hm 0 (by omega)))
    have hhead : sumStore (singletonStore p.input (ea a)) s (Sum.inr k)=
        true::List.replicate n true := by simpa only [sumStore_right,List.replicate_succ] using hs
    have hbody : Runs (p.program.relabel Sum.inl)
        (Function.update (sumStore (singletonStore p.input (ea a)) s)
          (Sum.inr k) (List.replicate n true))
        (sumStore (singletonStore p.input (ea (f a))) t) cp := by
      simpa only [sumStore_update_right] using hcall
    have hh:=Runs.loop_true hhead hbody hrt
    refine ⟨ct+cp+1,?_,?_⟩
    · nlinarith
    · simpa only [t,Function.update_idem,Function.iterate_succ_apply] using hh

/-- Input-length-bounded iteration. The extra hypothesis is solely a size
invariant along the already implemented iteration, not a computability oracle. -/
noncomputable def iterate (p : Procedure ea ea f) (q : Polynomial ℕ)
    (hgrowth : ∀ n a i,i≤n→(ea ((f^[i]) a)).length≤q.eval (n+(ea a).length)) :
    Procedure (prodCode (fun n=>List.replicate n true) ea) ea (fun x=>(f^[x.1]) x.2) where
  K:=p.inplace.K ⊕ Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inl p.inplace.input
  program:=.seq (unquoteMove (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))
    (.seq (moveWord (Sum.inr 0) (Sum.inl p.inplace.input) (Sum.inr 2))
      (.loop (Sum.inr 1) (p.inplace.program.relabel Sum.inl) (p.inplace.program.relabel Sum.inl)))
  bound:=Polynomial.C 11*Polynomial.X+
    Polynomial.X*(p.inplace.bound.comp q+1)+Polynomial.C 9
  runs x:=by
    let r:=p.inplace
    let s : Store (r.K ⊕ Fin 4):=singletonStore (Sum.inr 0)
      (prodCode (fun n=>List.replicate n true) ea x)
    let u : Store (r.K ⊕ Fin 4):=Function.update (singletonStore (Sum.inr 0) (ea x.2))
      (Sum.inr 1) (List.replicate x.1 true)
    let v : Store (r.K ⊕ Fin 4):=sumStore (singletonStore r.input (ea x.2))
      (singletonStore 1 (List.replicate x.1 true))
    have hparse : Runs (unquoteMove (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)) s u
        (7*x.1+6) := by
      have hh:=unquoteMove_runs (Sum.inr 0 : r.K ⊕ Fin 4) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (List.replicate x.1 true) (ea x.2) s (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      · funext k; cases k with
        | inl k => simp [s,u,singletonStore,Function.update]
        | inr k => fin_cases k <;> simp [s,u,singletonStore,Function.update]
      · simp
    have hmove : Runs (moveWord (Sum.inr 0) (Sum.inl r.input) (Sum.inr 2)) u v
        (4*(ea x.2).length+2) := by
      let emb : Fin 3 ↪ r.K ⊕ Fin 4 :=
        ⟨fun k=>if k=0 then Sum.inr 0 else if k=1 then Sum.inl r.input else Sum.inr 2,
          by intro a b; fin_cases a <;> fin_cases b <;> simp⟩
      have emb0 : emb 0=Sum.inr 0 := rfl
      have emb1 : emb 1=Sum.inl r.input := rfl
      have emb2 : emb 2=Sum.inr 2 := rfl
      have hh:=(moveWord_runs (0 : Fin 3) 1 2 (by decide) (by decide) (by decide) (ea x.2)).relabel
        emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
      -- A framed move has the counter outside its three touched registers.
      have hs' : overlay emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
          (singletonStore 0 (ea x.2))=u := by
        funext k
        cases k with
        | inl k =>
          by_cases hk : k=r.input
          · subst k
            have h:=overlay_at emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
              (singletonStore 0 (ea x.2)) 1
            simpa [emb0,emb1,emb2,u,singletonStore] using h
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2,Ne.symm hk])]
            simp [u,singletonStore]
        | inr k =>
          fin_cases k
          · simpa [emb0,emb1,emb2,u,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 0 (ea x.2)) 0
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [u,singletonStore]
          · simpa [emb0,emb1,emb2,u,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 0 (ea x.2)) 2
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [u,singletonStore]
      have ht' : overlay emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
          (singletonStore 1 (ea x.2))=v := by
        funext k
        cases k with
        | inl k =>
          by_cases hk : k=r.input
          · subst k
            simpa [emb0,emb1,emb2,v,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 1 (ea x.2)) 1
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2,Ne.symm hk])]
            simp [v,singletonStore,hk]
        | inr k =>
          fin_cases k
          · simpa [emb0,emb1,emb2,v,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 1 (ea x.2)) 0
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [v,singletonStore]
          · simpa [emb0,emb1,emb2,v,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 1 (ea x.2)) 2
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [v,singletonStore]
      rw [hs',ht'] at hh
      simpa [moveWord,reverseMove,Program.relabel,emb0,emb1,emb2] using hh
    obtain ⟨cl,hcl,hl⟩:=iterate_loop_runs r rfl (1 : Fin 4) x.1 x.2
      (q.eval (x.1+(ea x.2).length)) (hgrowth x.1 x.2)
      (singletonStore 1 (List.replicate x.1 true)) (by simp [singletonStore])
    have hfinal : sumStore (singletonStore r.input (ea ((f^[x.1]) x.2)))
        (Function.update (singletonStore (1 : Fin 4) (List.replicate x.1 true)) 1 [])=
        singletonStore (Sum.inl r.input) (ea ((f^[x.1]) x.2)) := by
      rw [sumStore_singleton_left]
      congr 1
      funext k; fin_cases k <;> simp [singletonStore,Function.update]
    rw [hfinal] at hl
    refine ⟨cl+(4*(ea x.2).length+2)+(7*x.1+6),?_,
      Runs.seq hparse (Runs.seq hmove hl)⟩
    let L:=(prodCode (fun n=>List.replicate n true) ea x).length
    have hx : x.1+(ea x.2).length≤L:=by simp only [L,prodCode,pairBits_length,List.length_replicate]; omega
    have hm:=eval_nat_mono r.bound (eval_nat_mono q hx)
    dsimp only at hm
    have hmul:=Nat.mul_le_mul (by omega : x.1≤L) (Nat.add_le_add_right hm 1)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_one,Polynomial.eval_comp]
    change cl+(4*(ea x.2).length+2)+(7*x.1+6)≤11*L+L*(r.bound.eval (q.eval L)+1)+9
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackNaturals.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma binaryValue_bits (n : ℕ) : binaryValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [binaryValue,ih,Nat.bit,Nat.add_comm]

lemma incrementWord_bits (n : ℕ) : incrementWord n.bits=(n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b
    · simp only [incrementWord,Nat.bit_false,Nat.bit1_bits]
    · simp only [incrementWord,ih,Nat.bit_true]
      rw [show 2*n+1+1=2*(n+1) by omega,Nat.bit0_bits (n+1) (by omega)]

abbrev unaryCode (n : ℕ) := List.replicate n true
namespace Procedure
noncomputable def successor : Procedure Nat.bits Nat.bits Nat.succ where
  K:=Fin 3
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=increment 0 1 2
  bound:=Polynomial.C 6*Polynomial.X+Polynomial.C 6
  runs n:=by
    have hh:=increment_runs (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
      (singletonStore 0 n.bits) (by simp [singletonStore]) (by simp [singletonStore])
    refine ⟨6*carryCount n.bits+6,?_,?_⟩
    · have hl:=carryCount_le_length n.bits
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      omega
    · simpa [singletonStore,incrementWord_bits] using hh

noncomputable def unarySuccessor : Procedure unaryCode unaryCode Nat.succ where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.push () true
  bound:=1
  runs n:=by
    refine ⟨1,by simp,?_⟩
    simpa [singletonStore,unaryCode,List.replicate_succ] using
      Runs.push (singletonStore () (unaryCode n)) () true

/-- Unary-to-binary conversion charges every carry and all word moves. -/
noncomputable def unaryToBits : Procedure unaryCode Nat.bits id := by
  let p:=successor.iterate (Polynomial.X+1) (by
    intro n a i hi
    have hlen : (a+i).bits.length≤a.bits.length+i := by
      clear hi
      induction i with
      | zero => simp
      | succ i ih =>
        have h:=incrementWord_length (a+i).bits
        rw [incrementWord_bits] at h
        simpa only [Nat.add_assoc] using (h.trans (Nat.add_le_add_right ih 1))
    simpa only [Function.iterate_succ_apply',Function.iterate_succ_apply,
      Nat.succ_iterate,Nat.size_eq_bits_len,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one] using (hlen.trans (by omega : a.bits.length+i≤n+a.bits.length+1)))
  exact (p.comp ((identity unaryCode).pair (constant unaryCode Nat.bits 0))).congrFun
    (by intro n; simp [Nat.succ_iterate])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackChoice.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def leftPublic (K L : Type) : (K ⊕ Fin 2) ↪ ((K ⊕ L) ⊕ Fin 2) where
  toFun := fun k=>match k with | .inl i=>.inl (.inl i) | .inr i=>.inr i
  inj' := by intro i j h; cases i <;> cases j <;> simp_all

def rightPublic (K L : Type) : (L ⊕ Fin 2) ↪ ((K ⊕ L) ⊕ Fin 2) where
  toFun := fun k=>match k with | .inl i=>.inl (.inr i) | .inr i=>.inr i
  inj' := by intro i j h; cases i <;> cases j <;> simp_all

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {f g : α→β}
/-- A same-wire interface, even when the input and output word encodings differ. -/
noncomputable abbrev shared (p : Procedure ea eb f) : Procedure ea eb f where
  K:=p.K ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (moveWord (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1))
    (.seq (p.program.relabel Sum.inl)
      (moveWord (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 8*Polynomial.X+Polynomial.C 5*p.bound+Polynomial.C 4
  runs a:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs a
    have h1:=moveWord_runs (Sum.inr 0 : p.K ⊕ Fin 2) (Sum.inl p.input) (Sum.inr 1)
      (by simp) (by simp) (by simp) (ea a)
    have h2:=hp.relabel (leftEmbed p.K (Fin 2)) (fun _=>[])
    simp only [overlay_singleton] at h2
    have h3:=moveWord_runs (Sum.inl p.output : p.K ⊕ Fin 2) (Sum.inr 0) (Sum.inr 1)
      (by simp) (by simp) (by simp) (eb (f a))
    refine ⟨(4*(eb (f a)).length+2)+cp+(4*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    have hl:=p.output_length_le a
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

/-- Reinterpret the domain, with its entire previous encoding still on tape. -/
def precompose (p : Procedure ea eb f) (h : γ→α) :
    Procedure (fun a=>ea (h a)) eb (fun a=>f (h a)) where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=p.runs (h a)

def congrEncoding (p : Procedure ea eb f) {ec : α→List Bool} {ed : β→List Bool}
    (ha : ∀a,ea a=ec a) (hb : ∀b,eb b=ed b) : Procedure ec ed f where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [ha,hb] using p.runs a

/-- Change the mathematical output only when its *actual encoded word* agrees. -/
def result (p : Procedure ea eb f) {ec : γ→List Bool} {h : α→γ}
    (hr : ∀a,eb (f a)=ec (h a)) : Procedure ea ec h where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [hr a] using p.runs a

noncomputable def unprefix (ea : α→List Bool) (b : Bool) :
    Procedure (fun a=>b::ea a) ea id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip .skip .skip
  bound:=Polynomial.C 2
  runs a:=by
    refine ⟨2,by simp,?_⟩
    have hu : Function.update (singletonStore () (b::ea a)) () (ea a)=
        singletonStore () (ea a):=by simp [singletonStore]
    cases b
    · exact hu ▸ Runs.cases_false (by simp [singletonStore]) (Runs.skip _)
    · exact hu ▸ Runs.cases_true (by simp [singletonStore]) (Runs.skip _)

noncomputable def chooseBit (p : Procedure ea eb f) (q : Procedure ea eb g) :
    Procedure (fun x : Bool×α=>x.1::ea x.2) eb (fun x=>if x.1 then g x.2 else f x.2) where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs x:=by
    rcases x with ⟨b,a⟩
    have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
    have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (ea a).length)
    cases b
    · obtain ⟨c,hc,hd⟩:=p.shared.runs a
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hpmono).trans (Nat.le_add_right _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    · obtain ⟨c,hc,hd⟩:=q.shared.runs a
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hqmono).trans (Nat.le_add_left _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (true::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)

abbrev boolCode (b : Bool) : List Bool := [b]
noncomputable def choose (p : Procedure ea eb f) (q : Procedure ea eb g) :
    Procedure (prodCode boolCode ea) eb (fun x=>if x.1 then g x.2 else f x.2) := by
  let pp:=p.comp (unprefix ea false)
  let qq:=q.comp (unprefix ea false)
  exact ((chooseBit pp qq).comp
    (unprefix (fun x : Bool×α=>x.1::false::ea x.2) true)).congrEncoding
      (by intro x;rfl) (by intro b;rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackWords.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α : Type}
noncomputable def prepend (ea : α→List Bool) (xs : List Bool) :
    Procedure ea (fun a=>xs++ea a) id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=pushWord () xs
  bound:=Polynomial.C (xs.length+1)
  runs a:=by
    refine ⟨xs.length+1,by simp,?_⟩
    simpa [singletonStore] using pushWord_runs () xs (singletonStore () (ea a))

noncomputable def reverse : Procedure (id : List Bool→List Bool) id List.reverse where
  K:=Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=reverseMove 0 1
  bound:=Polynomial.C 2*Polynomial.X+1
  runs xs:=by
    have hh:=reverseMove_runs (0 : Fin 2) 1 (by decide) (singletonStore 0 xs)
    refine ⟨2*xs.length+1,by simp,?_⟩
    convert hh using 1
    · funext k;fin_cases k <;> simp [singletonStore,Function.update]
    · simp [singletonStore]
    · simp [singletonStore]

noncomputable def tail : Procedure (id : List Bool→List Bool) id List.tail where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip .skip .skip
  bound:=Polynomial.C 2
  runs xs:=by
    refine ⟨2,by simp,?_⟩
    cases xs with
    | nil=>exact Runs.cases_nil (by simp [singletonStore]) (Runs.skip _)
    | cons b bs=>
      have hu : Function.update (singletonStore () (b::bs)) () bs=singletonStore () bs:=by
        simp [singletonStore]
      cases b
      · exact hu ▸ Runs.cases_false (by simp [singletonStore]) (Runs.skip _)
      · exact hu ▸ Runs.cases_true (by simp [singletonStore]) (Runs.skip _)

noncomputable def isEmpty : Procedure (id : List Bool→List Bool) boolCode List.isEmpty where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () (.push () true)
    (.seq (clear ()) (.push () false)) (.seq (clear ()) (.push () false))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C 3
  runs xs:=by
    cases xs with
    | nil=>
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (by
        simpa [singletonStore,boolCode] using Runs.push (singletonStore () []) () true)
    | cons b bs=>
      let s:=singletonStore () bs
      let u:=Function.update s () []
      have hc:=clear_runs () s
      have hp:=Runs.push u () false
      have hh:=Runs.seq hc hp
      have hu : Function.update (singletonStore () (b::bs)) () bs=s:=by simp [s,singletonStore]
      have hv : Function.update u () (false::u ())=singletonStore () [false]:=by
        funext k;cases k;simp [u,s,singletonStore]
      rw [hv] at hh
      have ht : 1+(2*(s ()).length+1)=2*bs.length+2:=by simp [s,singletonStore];omega
      rw [ht] at hh
      refine ⟨2*bs.length+3,by simp,?_⟩
      cases b
      · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)
      · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)

noncomputable def head : Procedure (id : List Bool→List Bool) boolCode (fun xs=>xs.headD false) where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () (.push () false)
    (.seq (clear ()) (.push () false)) (.seq (clear ()) (.push () true))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C 3
  runs xs:=by
    cases xs with
    | nil=>
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (by
        simpa [singletonStore,boolCode] using Runs.push (singletonStore () []) () false)
    | cons b bs=>
      let s:=singletonStore () bs
      let u:=Function.update s () []
      have hc:=clear_runs () s
      have hp:=Runs.push u () b
      have hh:=Runs.seq hc hp
      have hu : Function.update (singletonStore () (b::bs)) () bs=s:=by simp [s,singletonStore]
      have hv : Function.update u () (b::u ())=singletonStore () [b]:=by
        funext k;cases k;simp [u,s,singletonStore]
      rw [hv] at hh
      have ht : 1+(2*(s ()).length+1)=2*bs.length+2:=by simp [s,singletonStore];omega
      rw [ht] at hh
      refine ⟨2*bs.length+3,by simp,?_⟩
      cases b
      · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)
      · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)

noncomputable def append : Procedure (prodCode (id : List Bool→List Bool) id) id
    (fun x=>x.1++x.2) where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=.seq (unquoteMove 0 1 2 3) (.seq (reverseMove 1 2) (reverseMove 2 0))
  bound:=Polynomial.C 11*Polynomial.X+Polynomial.C 8
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode id id x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 x.2) 1 x.1
    let v : Store (Fin 4):=Function.update (singletonStore 0 x.2) 2 x.1.reverse
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*x.1.length+6):=by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) x.1 x.2 s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      funext k;fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (reverseMove 1 2) u v (2*x.1.length+1):=by
      have hh:=reverseMove_runs (1 : Fin 4) 2 (by decide) u
      convert hh using 1
      · funext k;fin_cases k <;> simp [u,v,singletonStore,Function.update]
      · simp [u]
    have h3 : Runs (reverseMove 2 0) v (singletonStore 0 (x.1++x.2)) (2*x.1.length+1):=by
      have hh:=reverseMove_runs (2 : Fin 4) 0 (by decide) v
      convert hh using 1
      · funext k;fin_cases k <;> simp [v,singletonStore,Function.update]
      · simp [v]
    refine ⟨(2*x.1.length+1)+(2*x.1.length+1)+(7*x.1.length+6),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length,id_eq]
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackBooleans.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {β : Type}

/-- A truth table on one Boolean has two literal finite output words. This
performs no run-time computation in its Boolean branch labels. -/
noncomputable def ofBool (eb : β→List Bool) (f : Bool→β) :
    Procedure boolCode eb f := by
  let p:=constant (fun _ : Unit=>[]) eb (f false)
  let q:=constant (fun _ : Unit=>[]) eb (f true)
  exact ((chooseBit p q).precompose (fun b=>(b,()))).congrFun
    (by intro b;cases b <;> rfl)

noncomputable def ofBool₂ (eb : β→List Bool) (f : Bool→Bool→β) :
    Procedure (prodCode boolCode boolCode) eb (fun x=>f x.1 x.2) :=
  (choose (ofBool eb (f false)) (ofBool eb (f true))).congrFun
    (by rintro ⟨b,c⟩;cases b <;> rfl)

noncomputable def ofBool₃ (eb : β→List Bool) (f : Bool→Bool→Bool→β) :
    Procedure (prodCode boolCode (prodCode boolCode boolCode)) eb
      (fun x=>f x.1 x.2.1 x.2.2) :=
  (choose (ofBool₂ eb (f false)) (ofBool₂ eb (f true))).congrFun
    (by rintro ⟨b,c,d⟩;cases b <;> rfl)

noncomputable def boolNot : Procedure boolCode boolCode not := ofBool boolCode not
noncomputable def boolAnd : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>x.1 && x.2) := ofBool₂ boolCode and
noncomputable def boolOr : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>x.1 || x.2) := ofBool₂ boolCode or
noncomputable def boolXor : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>xor x.1 x.2) := ofBool₂ boolCode xor

noncomputable def cons : Procedure (prodCode boolCode (id : List Bool→List Bool)) id
    (fun x=>x.1::x.2) := by
  let pp : Procedure (id : List Bool→List Bool) id (fun xs=>false::xs):=
    (prepend id [false]).result (by intro xs;rfl)
  let qq : Procedure (id : List Bool→List Bool) id (fun xs=>true::xs):=
    (prepend id [true]).result (by intro xs;rfl)
  exact (choose pp qq).congrFun (by rintro ⟨b,xs⟩;cases b <;> rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackFold.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
def scanStep (f g : α→α) : List Bool×α→List Bool×α
  | ([],a)=>([],a)
  | (b::bs,a)=>(bs,if b then g a else f a)

def bitAction (f g : α→α) (a : α) (b : Bool) : α := if b then g a else f a

lemma scanStep_iterate (f g : α→α) (i : ℕ) (xs : List Bool) (a : α) :
    (scanStep f g)^[i] (xs,a)=(xs.drop i,(xs.take i).foldl (bitAction f g) a) := by
  induction i generalizing xs a with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil=>simpa [scanStep] using ih [] a
    | cons b bs=>simpa [scanStep,bitAction] using ih bs (if b then g a else f a)

lemma foldl_measure {m : α→ℕ} {f g : α→α} {c : ℕ}
    (hf : ∀a,m (f a)≤ m a+c) (hg : ∀a,m (g a)≤ m a+c) (xs : List Bool) (a : α) :
    m (xs.foldl (bitAction f g) a)≤ m a+xs.length*c := by
  induction xs generalizing a with
  | nil=>simp
  | cons b bs ih=>
    simp only [List.foldl_cons,List.length_cons]
    have hh : m (bitAction f g a b)≤ m a+c:=by cases b <;> simp [bitAction,hf,hg]
    have hi:=ih (bitAction f g a b)
    nlinarith

namespace Procedure
variable {ea : α→List Bool} {f g : α→α}
noncomputable def scan (p : Procedure ea ea f) (q : Procedure ea ea g) :
    Procedure (prodCode id ea) (prodCode id ea) (scanStep f g) := by
  let fst:=first (id : List Bool→List Bool) ea
  let snd:=second (id : List Bool→List Bool) ea
  let upd:=(choose p q).comp ((head.comp fst).pair snd)
  let body:=(tail.comp fst).pair upd
  let pp:=(choose body (identity (prodCode id ea))).comp
    ((isEmpty.comp fst).pair (identity (prodCode id ea)))
  exact pp.congrFun (by
    rintro ⟨xs,a⟩
    cases xs <;> rfl)

/-- Fold a variable Boolean word. The bound covers every actual intermediate
state; all pairing, data movement and loop iterations are charged. -/
noncomputable def foldBits (p : Procedure ea ea f) (q : Procedure ea ea g)
    (bound : Polynomial ℕ)
    (hsize : ∀ (xs : List Bool) a i,(ea ((xs.take i).foldl (bitAction f g) a)).length≤
      bound.eval (xs.length+(ea a).length)) :
    Procedure (prodCode id ea) ea (fun x=>x.1.foldl (bitAction f g) x.2) := by
  let s:=scan p q
  let rep:=s.iterate (Polynomial.C 2*Polynomial.X+1+bound) (by
    intro n x i _
    rw [scanStep_iterate]
    simp only [prodCode,pairBits_length,id_eq,List.length_drop]
    have hs:=hsize x.1 x.2 i
    have hm:=eval_nat_mono bound (by omega :
      x.1.length+(ea x.2).length≤n+(2*x.1.length+(ea x.2).length+1))
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let start:=(length.comp (first (id : List Bool→List Bool) ea)).pair (identity (prodCode id ea))
  exact ((second (id : List Bool→List Bool) ea).comp (rep.comp start)).congrFun (by
    rintro ⟨xs,a⟩
    change ((scanStep f g)^[xs.length] (xs,a)).2=xs.foldl (bitAction f g) a
    rw [scanStep_iterate,List.take_length])

noncomputable def foldBitsLinear (p : Procedure ea ea f) (q : Procedure ea ea g) (c : ℕ)
    (hf : ∀a,(ea (f a)).length≤(ea a).length+c)
    (hg : ∀a,(ea (g a)).length≤(ea a).length+c) :
    Procedure (prodCode id ea) ea (fun x=>x.1.foldl (bitAction f g) x.2) :=
  foldBits p q (Polynomial.C (c+1)*Polynomial.X) (by
    intro xs a i
    have hh:=foldl_measure (m:=fun a=>(ea a).length) (f:=f) (g:=g) (c:=c) hf hg (xs.take i) a
    have hl : (xs.take i).length≤xs.length:=by simp only [List.length_take];omega
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    nlinarith)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackBinaryBasics.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma binaryValue_append (xs ys : List Bool) :
    binaryValue (xs++ys)=binaryValue xs+2^xs.length*binaryValue ys := by
  induction xs with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.cons_append,List.length_cons,binaryValue,ih,pow_succ]
    ring

lemma bigEndian_value (xs : List Bool) (a : ℕ) :
    xs.foldl (bitAction (fun n=>2*n) (fun n=>2*n+1)) a=
      binaryValue xs.reverse+2^xs.length*a := by
  induction xs generalizing a with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.foldl_cons,ih,List.reverse_cons,binaryValue_append,
      List.length_reverse,List.length_cons,pow_succ]
    cases b <;> simp [bitAction,binaryValue] <;> ring

lemma double_bits_length (n : ℕ) : (2*n).bits.length≤n.bits.length+1 := by
  by_cases h : n=0
  · subst n;simp
  · rw [Nat.bit0_bits n h,List.length_cons]
lemma doubleOne_bits_length (n : ℕ) : (2*n+1).bits.length≤n.bits.length+1 := by
  rw [Nat.bit1_bits,List.length_cons]

namespace Procedure
noncomputable def double : Procedure Nat.bits Nat.bits (fun n=>2*n) where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip (.seq (.push () false) (.push () false))
    (.seq (.push () true) (.push () false))
  bound:=Polynomial.C 3
  runs n:=by
    by_cases hn : n=0
    · subst n
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (Runs.skip _)
    · have he : n.bits≠[]:=by
        intro h
        have hv:=binaryValue_bits n
        rw [h] at hv
        exact hn hv.symm
      cases hb : n.bits with
      | nil=>exact (he hb).elim
      | cons b bs=>
        have hout : (2*n).bits=false::b::bs:=by rw [Nat.bit0_bits n hn,hb]
        have hbody : Runs (.seq (.push () b) (.push () false))
            (singletonStore () bs) (singletonStore () (false::b::bs)) 2:=by
          have hh:=Runs.seq (Runs.push (singletonStore () bs) () b)
            (Runs.push (singletonStore () (b::bs)) () false)
          simpa only [singletonStore,Function.update_self,Function.update_idem] using hh
        refine ⟨3,by simp,?_⟩
        rw [hout]
        cases b
        · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa [singletonStore] using hbody)
        · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa [singletonStore] using hbody)

noncomputable def doubleOne : Procedure Nat.bits Nat.bits (fun n=>2*n+1) :=
  (prepend Nat.bits [true]).result (by intro n;simp only [List.singleton_append,Nat.bit1_bits,id_eq])

/-- Canonicalize a binary word, charging a linear-growth bit fold. -/
noncomputable def normalize : Procedure (id : List Bool→List Bool) Nat.bits binaryValue := by
  let p:=foldBitsLinear double doubleOne 1 double_bits_length doubleOne_bits_length
  let start:=reverse.pair (constant (id : List Bool→List Bool) Nat.bits 0)
  exact (p.comp start).congrFun (by intro xs;simp [bigEndian_value])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackUnary.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def addCounter (x : ℕ×ℕ) := (x.1,x.1+x.2)
lemma addCounter_iterate (i : ℕ) (x : ℕ×ℕ) :
    addCounter^[i] x=(x.1,i*x.1+x.2) := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply',ih]
    simp only [addCounter,Prod.mk.injEq,true_and,Nat.succ_mul]
    omega

lemma pred_iterate_word (i n : ℕ) : (fun k=>k-1)^[i] n=n-i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply',ih,Nat.sub_sub]

namespace Procedure
noncomputable def unaryAdd : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1+x.2) :=
  (unarySuccessor.iterate Polynomial.X (by
    intro n a i hi
    simp only [Nat.succ_iterate,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)).congrFun (by intro x;simp [Nat.succ_iterate,Nat.add_comm])

noncomputable def unaryMul : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1*x.2) := by
  let step : Procedure (prodCode unaryCode unaryCode) (prodCode unaryCode unaryCode) addCounter:=
    ((first unaryCode unaryCode).pair unaryAdd).congrFun (by intro x;rfl)
  let rep:=step.iterate (Polynomial.X^2+Polynomial.X) (by
    intro n x i hi
    rw [addCounter_iterate]
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X]
    have hm : x.1≤n+(2*x.1+1+x.2):=by omega
    have hii : i≤n+(2*x.1+1+x.2):=by omega
    have hh:=Nat.mul_le_mul hii hm
    nlinarith)
  let fst:=first unaryCode unaryCode
  let snd:=second unaryCode unaryCode
  let start:=fst.pair (snd.pair (constant (prodCode unaryCode unaryCode) unaryCode 0))
  exact ((second unaryCode unaryCode).comp (rep.comp start)).congrFun (by
    intro x
    change (addCounter^[x.1] (x.2,0)).2=x.1*x.2
    simp [addCounter_iterate])

noncomputable def unaryPred : Procedure unaryCode unaryCode (fun n=>n-1) :=
  (tail.precompose unaryCode).result (by intro n;simp [unaryCode])

noncomputable def unarySub : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1-x.2) := by
  let p:=unaryPred.iterate Polynomial.X (by
    intro n a i _
    simp only [pred_iterate_word,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)
  exact (p.comp (swap unaryCode unaryCode)).congrFun (by intro x;simp [pred_iterate_word])

noncomputable def unaryZero : Procedure unaryCode boolCode (fun n=>decide (n=0)) :=
  (isEmpty.precompose unaryCode).congrFun (by intro n;simp [unaryCode])

noncomputable def unaryLe : Procedure (prodCode unaryCode unaryCode) boolCode
    (fun x=>decide (x.1≤x.2)) :=
  (unaryZero.comp unarySub).congrFun (by intro x;simp only [Function.comp_apply,decide_eq_decide];omega)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackAdder.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

/-- Literal full-adder truth tables, not an arithmetic oracle. -/
def sumBit (a b c : Bool) : Bool := xor a (xor b c)
def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

lemma sum_carry (a b c : Bool) :
    a.toNat+b.toNat+c.toNat=(sumBit a b c).toNat+2*(carryBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

abbrev AddState := List Bool × List Bool × Bool × List Bool
abbrev addStateCode : AddState→List Bool :=
  prodCode id (prodCode id (prodCode Procedure.boolCode id))

def addStep (s : AddState) : AddState :=
  (s.1.tail,s.2.1.tail,
    carryBit (s.1.headD false) (s.2.1.headD false) s.2.2.1,
    sumBit (s.1.headD false) (s.2.1.headD false) s.2.2.1 :: s.2.2.2)

def addMeasure (s : AddState) : ℕ := s.1.length+s.2.1.length+s.2.2.1.toNat

def residual (s : AddState) : ℕ := binaryValue s.1+binaryValue s.2.1+s.2.2.1.toNat

def addInvariant (s : AddState) : ℕ :=
  binaryValue s.2.2.2.reverse+2^s.2.2.2.length*residual s

lemma binaryValue_head_tail (xs : List Bool) :
    binaryValue xs=(xs.headD false).toNat+2*binaryValue xs.tail := by
  cases xs <;> rfl

lemma addInvariant_step (s : AddState) : addInvariant (addStep s)=addInvariant s := by
  have hx:=binaryValue_head_tail s.1
  have hy:=binaryValue_head_tail s.2.1
  have hh:=sum_carry (s.1.headD false) (s.2.1.headD false) s.2.2.1
  simp only [addInvariant,addStep,List.reverse_cons,binaryValue_append,List.length_reverse,
    binaryValue,List.length_cons,pow_succ,residual]
  rw [hx,hy]
  nlinarith [congrArg (fun n : ℕ=>2^s.2.2.2.length*n) hh]

lemma addMeasure_step (s : AddState) : addMeasure (addStep s)≤addMeasure s-1 := by
  rcases s with ⟨xs,ys,c,zs⟩
  cases xs with
  | nil=>cases ys with
    | nil=>cases c <;> simp [addMeasure,addStep,carryBit]
    | cons b bs=>cases b <;> cases c <;> simp [addMeasure,addStep,carryBit]
  | cons a as=>cases ys with
    | nil=>cases a <;> cases c <;> simp [addMeasure,addStep,carryBit]
    | cons b bs=>cases a <;> cases b <;> cases c <;>
        simp [addMeasure,addStep,carryBit] <;> omega

lemma addMeasure_iterate (i : ℕ) (s : AddState) :
    addMeasure (addStep^[i] s)≤addMeasure s-i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    exact (addMeasure_step _).trans (by omega)

lemma addInvariant_iterate (i : ℕ) (s : AddState) :
    addInvariant (addStep^[i] s)=addInvariant s := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',addInvariant_step,ih]

lemma residual_zero {s : AddState} (h : addMeasure s=0) : residual s=0 := by
  have hx : s.1=[]:=List.length_eq_zero_iff.mp (by unfold addMeasure at h;omega)
  have hy : s.2.1=[]:=List.length_eq_zero_iff.mp (by unfold addMeasure at h;omega)
  have hc : s.2.2.1.toNat=0:=by unfold addMeasure at h;omega
  simp [residual,hx,hy,hc,binaryValue]

def wordAdd (x : List Bool×List Bool) : List Bool :=
  (addStep^[x.1.length+x.2.length+1] (x.1,x.2,false,[])).2.2.2.reverse

lemma wordAdd_value (x : List Bool×List Bool) :
    binaryValue (wordAdd x)=binaryValue x.1+binaryValue x.2 := by
  let s : AddState:=(x.1,x.2,false,[])
  let i:=x.1.length+x.2.length+1
  have hz : addMeasure (addStep^[i] s)=0:=by
    have hh:=addMeasure_iterate i s
    simp only [s,i,addMeasure,Bool.toNat_false,Nat.add_zero] at hh
    dsimp only [s,i,addMeasure]
    omega
  have hh:=addInvariant_iterate i s
  simp only [addInvariant,residual_zero hz,Nat.mul_zero,Nat.add_zero] at hh
  simpa [s,i,wordAdd,residual,binaryValue] using hh

lemma addStep_size (s : AddState) :
    (addStateCode (addStep s)).length≤(addStateCode s).length+1 := by
  simp only [addStateCode,addStep,prodCode,pairBits_length,id_eq,Procedure.boolCode,
    List.length_cons,List.length_tail]
  omega

namespace Procedure
variable {α : Type} {ea : α→List Bool} {f : α→α}

noncomputable def iterateLinear (p : Procedure ea ea f) (c : ℕ)
    (hg : ∀a,(ea (f a)).length≤(ea a).length+c) :
    Procedure (prodCode unaryCode ea) ea (fun x=>f^[x.1] x.2) := by
  have hh : ∀ i a,(ea (f^[i] a)).length≤(ea a).length+i*c:=by
    intro i a
    induction i with
    | zero=>simp
    | succ i ih=>
      rw [Function.iterate_succ_apply']
      have h:=hg (f^[i] a)
      nlinarith
  exact p.iterate (Polynomial.C (c+1)*Polynomial.X) (by
    intro n a i hi
    have h:=hh i a
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    nlinarith)

noncomputable def addStepP : Procedure addStateCode addStateCode addStep := by
  let x:=first (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let rem:=second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let y:=(first (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  let bits:=(head.comp x).pair ((head.comp y).pair c)
  let newc:=(ofBool₃ boolCode carryBit).comp bits
  let newb:=(ofBool₃ boolCode sumBit).comp bits
  exact ((tail.comp x).pair ((tail.comp y).pair
    (newc.pair (cons.comp (newb.pair zs))))).congrFun (by intro s;rfl)

noncomputable def wordAddP : Procedure (prodCode (id : List Bool→List Bool) id) id wordAdd := by
  let x:=first (id : List Bool→List Bool) (id : List Bool→List Bool)
  let y:=second (id : List Bool→List Bool) (id : List Bool→List Bool)
  let len:=unarySuccessor.comp (unaryAdd.comp ((length.comp x).pair (length.comp y)))
  let start:=x.pair (y.pair ((constant (prodCode id id) boolCode false).pair
    (constant (prodCode id id) (id : List Bool→List Bool) [])))
  let rep:=addStepP.iterateLinear 1 addStep_size
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp
    (second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id)))
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  exact (reverse.comp (zs.comp (rep.comp (len.pair start)))).congrFun (by intro x;rfl)

noncomputable def binaryAdd : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1+x.2) :=
  ((normalize.comp wordAddP).precompose (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
    (by
      intro x
      change binaryValue (wordAdd (x.1.bits,x.2.bits))=x.1+x.2
      rw [wordAdd_value,binaryValue_bits,binaryValue_bits])

end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackSubtractor.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def borrowBit (a b c : Bool) : Bool := (!a && b) || (!a && c) || (b && c)

lemma difference_borrow (a b c : Bool) :
    (a.toNat : ℤ)-b.toNat-c.toNat=(sumBit a b c).toNat-2*(borrowBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

lemma binaryValue_lt (xs : List Bool) : binaryValue xs<2^xs.length := by
  induction xs with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.length_cons,binaryValue,pow_succ]
    cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

abbrev SubState := AddState
abbrev subStateCode := addStateCode

def subStep (s : SubState) : SubState :=
  (s.1.tail,s.2.1.tail,
    borrowBit (s.1.headD false) (s.2.1.headD false) s.2.2.1,
    sumBit (s.1.headD false) (s.2.1.headD false) s.2.2.1 :: s.2.2.2)

def subInvariant (s : SubState) : ℤ :=
  (binaryValue s.2.2.2.reverse : ℤ)+2^s.2.2.2.length*
    ((binaryValue s.1 : ℤ)-binaryValue s.2.1-s.2.2.1.toNat)

lemma subInvariant_step (s : SubState) : subInvariant (subStep s)=subInvariant s := by
  have hx:=binaryValue_head_tail s.1
  have hy:=binaryValue_head_tail s.2.1
  have hh:=difference_borrow (s.1.headD false) (s.2.1.headD false) s.2.2.1
  simp only [subInvariant,subStep,List.reverse_cons,binaryValue_append,List.length_reverse,
    binaryValue,List.length_cons,pow_succ]
  push_cast
  have hx' : (binaryValue s.1 : ℤ)=(s.1.headD false).toNat+2*binaryValue s.1.tail:=by
    exact_mod_cast hx
  have hy' : (binaryValue s.2.1 : ℤ)=(s.2.1.headD false).toNat+2*binaryValue s.2.1.tail:=by
    exact_mod_cast hy
  rw [hx',hy']
  nlinarith [congrArg (fun n : ℤ=>2^s.2.2.2.length*n) hh]

lemma subInvariant_iterate (i : ℕ) (s : SubState) :
    subInvariant (subStep^[i] s)=subInvariant s := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',subInvariant_step,ih]

lemma subStep_tapes (i : ℕ) (s : SubState) :
    (subStep^[i] s).1=s.1.drop i ∧ (subStep^[i] s).2.1=s.2.1.drop i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    simp only [subStep,ih.1,ih.2,List.tail_drop]
    trivial

def wordSubtract (x : List Bool×List Bool) : Bool×List Bool :=
  let s:=subStep^[x.1.length+x.2.length+1] (x.1,x.2,false,[])
  (s.2.2.1,s.2.2.2.reverse)

lemma wordSubtract_spec (x : List Bool×List Bool) :
    (binaryValue (wordSubtract x).2 : ℤ) -
      2^(wordSubtract x).2.length*((wordSubtract x).1.toNat : ℤ)=
      (binaryValue x.1 : ℤ)-binaryValue x.2 := by
  let s : SubState:=(x.1,x.2,false,[])
  let i:=x.1.length+x.2.length+1
  have hx : (subStep^[i] s).1=[]:=by
    rw [(subStep_tapes i s).1]
    exact List.drop_eq_nil_iff.mpr (by dsimp [s,i];omega)
  have hy : (subStep^[i] s).2.1=[]:=by
    rw [(subStep_tapes i s).2]
    exact List.drop_eq_nil_iff.mpr (by dsimp [s,i];omega)
  have hh:=subInvariant_iterate i s
  simp only [subInvariant,hx,hy,binaryValue,Int.natCast_zero,zero_sub] at hh
  simpa [wordSubtract,s,i,List.length_reverse,subInvariant,binaryValue,sub_eq_add_neg] using hh

lemma wordSubtract_borrow (x : List Bool×List Bool) :
    (wordSubtract x).1=decide (binaryValue x.1<binaryValue x.2) := by
  have hh:=wordSubtract_spec x
  have hl:=binaryValue_lt (wordSubtract x).2
  have hl' : (binaryValue (wordSubtract x).2 : ℤ)<2^(wordSubtract x).2.length:=by
    exact_mod_cast hl
  cases hb : (wordSubtract x).1 <;> simp only [hb,Bool.toNat_false,Bool.toNat_true,
    Int.natCast_zero,Int.natCast_one,mul_zero,mul_one,sub_zero] at hh
  · symm;apply decide_eq_false;omega
  · symm;apply decide_eq_true;omega

lemma wordSubtract_value (x : List Bool×List Bool) :
    (if (wordSubtract x).1 then 0 else binaryValue (wordSubtract x).2)=
      binaryValue x.1-binaryValue x.2 := by
  have hh:=wordSubtract_spec x
  have hb:=wordSubtract_borrow x
  cases hc : (wordSubtract x).1
  · simp only [hc,Bool.false_eq_true,ite_false,Bool.toNat_false,Int.natCast_zero,mul_zero,sub_zero] at *
    omega
  · simp only [hc,ite_true,true_eq_decide_iff] at *
    omega

lemma subStep_size (s : SubState) :
    (subStateCode (subStep s)).length≤(subStateCode s).length+1 := by
  simp only [subStateCode,addStateCode,subStep,prodCode,pairBits_length,id_eq,Procedure.boolCode,
    List.length_cons,List.length_tail]
  omega


end ExactQuantumFactoring.BitStackProgram
end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/Procedure.lean =====
namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def subStepP : Procedure subStateCode subStateCode subStep := by
  let x:=first (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let rem:=second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let y:=(first (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  let bits:=(head.comp x).pair ((head.comp y).pair c)
  let newc:=(ofBool₃ boolCode borrowBit).comp bits
  let newb:=(ofBool₃ boolCode sumBit).comp bits
  exact ((tail.comp x).pair ((tail.comp y).pair
    (newc.pair (cons.comp (newb.pair zs))))).congrFun (by intro s;rfl)

noncomputable def wordSubtractP :
    Procedure (prodCode (id : List Bool→List Bool) id) (prodCode boolCode id) wordSubtract := by
  let x:=first (id : List Bool→List Bool) (id : List Bool→List Bool)
  let y:=second (id : List Bool→List Bool) (id : List Bool→List Bool)
  let len:=unarySuccessor.comp (unaryAdd.comp ((length.comp x).pair (length.comp y)))
  let start:=x.pair (y.pair ((constant (prodCode id id) boolCode false).pair
    (constant (prodCode id id) (id : List Bool→List Bool) [])))
  let rep:=subStepP.iterateLinear 1 subStep_size
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp
    (second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id)))
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  exact ((c.pair (reverse.comp zs)).comp (rep.comp (len.pair start))).congrFun (by intro x;rfl)

noncomputable def binaryLt : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1<x.2)) :=
  (((first boolCode (id : List Bool→List Bool)).comp wordSubtractP).precompose
    (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
      (by
        intro x
        change (wordSubtract (x.1.bits,x.2.bits)).1=decide (x.1<x.2)
        rw [wordSubtract_borrow,binaryValue_bits,binaryValue_bits])

noncomputable def binaryLe : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1≤x.2)) :=
  (boolNot.comp (binaryLt.comp (swap Nat.bits Nat.bits))).congrFun (by
    intro x
    change (!(decide (x.2<x.1)))=decide (x.1≤x.2)
    simp only [← decide_not,Nat.not_lt])

noncomputable def binarySub : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1-x.2) :=
  (((choose normalize (constant (id : List Bool→List Bool) Nat.bits 0)).comp
    wordSubtractP).precompose (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
      (by
        intro x
        change (if (wordSubtract (x.1.bits,x.2.bits)).1 then 0 else
          binaryValue (wordSubtract (x.1.bits,x.2.bits)).2)=x.1-x.2
        rw [wordSubtract_value,binaryValue_bits,binaryValue_bits])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkEmissionModel.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
inductive Node where
  | constant (b : Bool)
  | copy (i : ℕ)
  | neg (i : ℕ)
  | conj (i j : ℕ)
  deriving DecidableEq, Inhabited

def Node.map (f : ℕ→ℕ) : Node→Node
  | .constant b=>.constant b
  | .copy i=>.copy (f i)
  | .neg i=>.neg (f i)
  | .conj i j=>.conj (f i) (f j)
def eraseNode {n : ℕ} : BoolNode n→Node
  | .constant b=>.constant b
  | .copy i=>.copy i.val
  | .neg i=>.neg i.val
  | .conj i j=>.conj i.val j.val
lemma eraseNode_map {n m : ℕ} (o : BoolNode n) (f : Fin n→Fin m) (g : ℕ→ℕ)
    (h : ∀i,(f i).val=g i.val) : eraseNode (o.map f)=(eraseNode o).map g := by
  cases o <;> simp only [BoolNode.map,eraseNode,Node.map,h]
def eraseNet {n k : ℕ} : BoolNet n k→List Node
  | .input=>[]
  | .add p o=>eraseNet p++[eraseNode o]
lemma eraseNet_length {n k : ℕ} (p : BoolNet n k) : (eraseNet p).length=p.count := by
  induction p with
  | input=>rfl
  | add p o ih=>simp only [eraseNet,List.length_append,List.length_singleton,BoolNet.count,ih]

def attachIndex {m k : ℕ} (ρ : Fin m→Fin k) (i : ℕ) : ℕ :=
  if h : i < m then (ρ ⟨i,h⟩).val else k+(i-m)
lemma attachIndex_input {m k : ℕ} (ρ : Fin m→Fin k) (i : Fin m) :
    attachIndex ρ i.val=(ρ i).val := dite_eq_left i.isLt
lemma attachIndex_work {m k : ℕ} (ρ : Fin m→Fin k) (i : ℕ) (h : m ≤ i) :
    attachIndex ρ i=k+(i-m) := dite_eq_right (by omega)
lemma attach_output {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m→Fin k) (b : BoolNet m l)
    (i : Fin l) : ((a.attach ρ b).2.2 i).val=attachIndex ρ i.val := by
  induction b with
  | input=>exact (attachIndex_input ρ i).symm
  | @add l b o ih=>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [BoolNet.attach,Fin.snoc_last,Fin.val_last]
      rw [attachIndex_work ρ l b.input_le]
      have hw:=(a.attach ρ b).2.1.width_eq
      have hc:=BoolNet.attach_count a ρ b
      have hb:=b.width_eq
      rw [hc] at hw
      have ha:=a.width_eq
      omega
    · simp only [BoolNet.attach,Fin.snoc_castSucc,Fin.val_castSucc]
      exact ih j
lemma attach_erase {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m→Fin k) (b : BoolNet m l) :
    eraseNet (a.attach ρ b).2.1=eraseNet a++(eraseNet b).map (Node.map (attachIndex ρ)) := by
  induction b with
  | input=>simp only [BoolNet.attach,eraseNet,List.map_nil,List.append_nil]
  | add b o ih=>
    simp only [BoolNet.attach,eraseNet,List.map_append,List.map_singleton]
    rw [ih,List.append_assoc,eraseNode_map o _ _ (attach_output a ρ b)]

structure Data where
  inputs : ℕ
  nodes : List Node
  outputs : List ℕ
  deriving Inhabited

def erase {n m : ℕ} (a : BooleanNetwork n m) : Data:=
  ⟨n,eraseNet a.net,List.ofFn (fun i=>(a.output i).val)⟩
def attachRawIndex (width : ℕ) (ρ : List ℕ) (i : ℕ) : ℕ:=
  if i<ρ.length then (ρ.drop i).headD 0 else width+(i-ρ.length)
lemma attachRawIndex_ofFn {m k : ℕ} (ρ : Fin m→Fin k) :
    attachRawIndex k (List.ofFn (fun i=>(ρ i).val))=attachIndex ρ := by
  funext i
  unfold attachRawIndex attachIndex
  simp only [List.length_ofFn]
  split_ifs with h
  · rw [List.headD_eq_head?_getD,List.head?_drop]
    simp [h]
  · rfl

def comp (a b : Data) : Data:=
  let f:=attachRawIndex (a.inputs+a.nodes.length) a.outputs
  ⟨a.inputs,a.nodes++b.nodes.map (Node.map f),b.outputs.map f⟩
lemma erase_comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l) :
    erase (a.comp b)=comp (erase a) (erase b) := by
  have hw : n+(eraseNet a.net).length=a.width := by rw [eraseNet_length];exact a.net.width_eq.symm
  simp only [erase,BooleanNetwork.comp,comp,hw,attachRawIndex_ofFn,attach_erase]
  congr 1
  rw [List.map_ofFn]
  congr 1
  funext i
  exact attach_output a.net a.output b.net (b.output i)

def select (n : ℕ) (xs : List ℕ) : Data:=⟨n,[],xs⟩
lemma erase_select {n m : ℕ} (f : Fin m→Fin n) :
    erase (BooleanNetwork.select f)=select n (List.ofFn (fun i=>(f i).val)) := rfl

def node (n : ℕ) (o : Node) : Data:=⟨n,[o],[n]⟩
lemma erase_node {n : ℕ} (o : BoolNode n) : erase (BooleanNetwork.node o)=node n (eraseNode o) := by
  simp [erase,BooleanNetwork.node,eraseNet,node,List.ofFn_succ]
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkEmissionPair.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission

def pairIndex (n width i : ℕ) : ℕ:=if i<n then i else width+(i-n)
lemma pairIndex_eq {n k : ℕ} (h : n ≤ k) :
    pairIndex n k=attachIndex (fun i : Fin n=>i.castLE h) := by
  funext i
  unfold pairIndex attachIndex
  split_ifs <;> rfl

def pair (a b : Data) : Data:=
  let f:=pairIndex a.inputs (a.inputs+a.nodes.length)
  ⟨a.inputs,a.nodes++b.nodes.map (Node.map f),a.outputs++b.outputs.map f⟩
lemma erase_pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l) :
    erase (a.pair b)=pair (erase a) (erase b) := by
  have hw : n+(eraseNet a.net).length=a.width := by rw [eraseNet_length];exact a.net.width_eq.symm
  let ρ : Fin n→Fin a.width:=fun i=>i.castLE a.net.input_le
  simp only [erase,BooleanNetwork.pair,pair,hw,pairIndex_eq a.net.input_le,attach_erase]
  congr 1
  have he : (fun i=>(Fin.append (fun j=>(a.output j).castLE (a.net.attach_le ρ b.net))
      ((a.net.attach ρ b.net).2.2 ∘ b.output) i).val)=
      Fin.append (fun j=>(a.output j).val)
        (fun j=>((a.net.attach ρ b.net).2.2 (b.output j)).val) := by
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp
  rw [he,List.ofFn_fin_append,List.map_ofFn]
  congr 2
  funext i
  exact attach_output a.net ρ b.net (b.output i)

/-- A finite output permutation/quotation involves no Boolean node. -/
def rewire (a : Data) (outputs : List ℕ) : Data:=⟨a.inputs,a.nodes,outputs⟩
lemma erase_rewire {n m l : ℕ} (a : BooleanNetwork n m) (f : Fin l→Fin m) :
    erase (a.rewire f)=rewire (erase a) (List.ofFn (fun i=>(a.output (f i)).val)) := rfl
end ExactQuantumFactoring.NetworkEmission

end


end OAI
