/-
Exact quantum factoring development (port of OpenAI's formalization), part 28 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: BitStackSums.lean, BitStackListCode.lean, BitStackListFold.lean, BitStackListOps.lean, BitStackTabulate.lean, BitStackMultiplier.lean, BitStackDivision.lean, BitStackListIndex.lean, BitStackListLength.lean, NativeAIGModel.lean, BitStackOptions.lean, BitStackAssociation.lean, NativeAIGProcedures.lean, NativeAIGGateProcedure.lean, NativeAIGBoolean.lean, NativeAIGFullAdder.lean, NativeAIGVector.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part27

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackSums.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def sumCode {α β : Type} (ea : α→List Bool) (eb : β→List Bool) : α⊕β→List Bool
  | .inl a=>false::ea a
  | .inr b=>true::eb b

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
    {f : α→γ} {g : β→γ}
noncomputable def casesSum (p : Procedure ea ec f) (q : Procedure eb ec g) :
    Procedure (sumCode ea eb) ec (Sum.elim f g) where
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
    cases x with
    | inl a=>
      have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
      obtain ⟨c,hc,hd⟩:=p.shared.runs a
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
        simpa only [hu,sumCode] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    | inr b=>
      have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (eb b).length)
      obtain ⟨c,hc,hd⟩:=q.shared.runs b
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hqmono).trans (Nat.le_add_left _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::eb b)) (Sum.inr 0) (eb b)=singletonStore (Sum.inr 0) (eb b):=by
          simp [singletonStore]
        simpa only [hu,sumCode] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=eb b) (s:=singletonStore (Sum.inr 0) (true::eb b)) (by simp [singletonStore])
          (by rw [hu];exact hh)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackListCode.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def listCode (ea : α→List Bool) : List α→List Bool
  | []=>[false]
  | a::as=>true::pairBits (ea a) (listCode ea as)

def emptyCode (_ : Unit) : List Bool := []

def listView : List α→Unit⊕(α×List α)
  | []=>.inl ()
  | a::as=>.inr (a,as)

lemma listCode_length_cons (ea : α→List Bool) (a : α) (as : List α) :
    (listCode ea (a::as)).length=2*(ea a).length+2+(listCode ea as).length := by
  simp [listCode,pairBits_length];omega

lemma listCode_length_append (ea : α→List Bool) (xs ys : List α) :
    (listCode ea (xs++ys)).length+1=(listCode ea xs).length+(listCode ea ys).length := by
  induction xs with
  | nil=>simp [listCode,Nat.add_comm]
  | cons a as ih=>simp only [List.cons_append,listCode_length_cons];omega

lemma listCode_length_rev (ea : α→List Bool) (xs : List α) :
    (listCode ea xs.reverse).length=(listCode ea xs).length := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>
    rw [List.reverse_cons]
    have hh:=listCode_length_append ea as.reverse [a]
    simp only [listCode_length_cons,ih] at hh ⊢
    have hz : (listCode ea []).length=1:=rfl
    omega

lemma listCode_length_pos (ea : α→List Bool) (xs : List α) : 0<(listCode ea xs).length := by
  cases xs <;> simp [listCode]

lemma list_length_le_code (ea : α→List Bool) (xs : List α) : xs.length≤(listCode ea xs).length := by
  induction xs with
  | nil=>simp
  | cons a as ih=>simp only [List.length_cons,listCode_length_cons];omega

lemma listCode_tail_le (ea : α→List Bool) (xs : List α) :
    (listCode ea xs.tail).length≤(listCode ea xs).length := by
  cases xs with
  | nil=>rfl
  | cons a as=>simp only [List.tail_cons,listCode_length_cons];omega

lemma code_le_of_mem (ea : α→List Bool) {a : α} {xs : List α} (h : a∈xs) :
    (ea a).length≤(listCode ea xs).length := by
  induction xs with
  | nil=>simp at h
  | cons b bs ih=>
    rw [List.mem_cons] at h
    rw [listCode_length_cons]
    rcases h with h|h
    · subst b;omega
    · have hh:=ih h;omega

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listUncons : Procedure (listCode ea)
    (sumCode emptyCode (prodCode ea (listCode ea))) listView :=
  (identity (listCode ea)).result (by intro xs;cases xs <;> rfl)

noncomputable def listCons : Procedure (prodCode ea (listCode ea)) (listCode ea)
    (fun x=>x.1::x.2) :=
  (prepend (prodCode ea (listCode ea)) [true]).result (by intro x;rfl)

noncomputable def listHead (d : α) : Procedure (listCode ea) ea (fun xs=>xs.headD d) :=
  ((casesSum (constant emptyCode ea d) (first ea (listCode ea))).comp (listUncons ea)).congrFun
    (by intro xs;cases xs <;> rfl)

noncomputable def listTail : Procedure (listCode ea) (listCode ea) List.tail :=
  ((casesSum (constant emptyCode (listCode ea) []) (second ea (listCode ea))).comp
    (listUncons ea)).congrFun (by intro xs;cases xs <;> rfl)

noncomputable def listEmpty : Procedure (listCode ea) boolCode List.isEmpty :=
  ((casesSum (constant emptyCode boolCode true) (constant (prodCode ea (listCode ea)) boolCode false)).comp
    (listUncons ea)).congrFun (by intro xs;cases xs <;> rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackListFold.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

def listScan (f : α×β→β) : List α×β→List α×β
  | ([],b)=>([],b)
  | (a::as,b)=>(as,f (a,b))

lemma listScan_iterate (f : α×β→β) (i : ℕ) (xs : List α) (b : β) :
    (listScan f)^[i] (xs,b)=(xs.drop i,(xs.take i).foldl (fun b a=>f (a,b)) b) := by
  induction i generalizing xs b with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil=>simpa [listScan] using ih [] b
    | cons a as=>simpa [listScan] using ih as (f (a,b))

lemma listCode_length_drop_le (ea : α→List Bool) (i : ℕ) (xs : List α) :
    (listCode ea (xs.drop i)).length≤(listCode ea xs).length := by
  have hh:=listCode_length_append ea (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at hh
  have hp:=listCode_length_pos ea (xs.take i)
  omega

lemma listCode_length_take_le (ea : α→List Bool) (i : ℕ) (xs : List α) :
    (listCode ea (xs.take i)).length≤(listCode ea xs).length := by
  have hh:=listCode_length_append ea (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at hh
  have hp:=listCode_length_pos ea (xs.drop i)
  omega

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {f : α×β→β}
noncomputable def listScanP (d : α) (p : Procedure (prodCode ea eb) eb f) :
    Procedure (prodCode (listCode ea) eb) (prodCode (listCode ea) eb) (listScan f) := by
  let xs:=first (listCode ea) eb
  let b:=second (listCode ea) eb
  let upd:=((listTail ea).comp xs).pair (p.comp (((listHead ea d).comp xs).pair b))
  exact ((choose upd (identity (prodCode (listCode ea) eb))).comp
    (((listEmpty ea).comp xs).pair (identity (prodCode (listCode ea) eb)))).congrFun
      (by rintro ⟨xs,b⟩;cases xs <;> rfl)

noncomputable def foldList (d : α) (p : Procedure (prodCode ea eb) eb f)
    (bound : Polynomial ℕ)
    (hsize : ∀ (xs : List α) b i,
      (eb ((xs.take i).foldl (fun b a=>f (a,b)) b)).length≤
        bound.eval ((listCode ea xs).length+(eb b).length)) :
    Procedure (prodCode (listCode ea) eb) eb (fun x=>x.1.foldl (fun b a=>f (a,b)) x.2) := by
  let s:=listScanP d p
  let rep:=s.iterate (Polynomial.C 2*Polynomial.X+1+bound) (by
    intro n x i _
    rw [listScan_iterate]
    simp only [prodCode,pairBits_length]
    have hs:=hsize x.1 x.2 i
    have hl:=listCode_length_drop_le ea i x.1
    have hm:=eval_nat_mono bound (by omega :
      (listCode ea x.1).length+(eb x.2).length≤n+(2*(listCode ea x.1).length+(eb x.2).length+1))
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let wc:=(length.precompose (listCode ea)).comp (first (listCode ea) eb)
  exact ((second (listCode ea) eb).comp (rep.comp (wc.pair (identity (prodCode (listCode ea) eb))))).congrFun
    (by
      rintro ⟨xs,b⟩
      change ((listScan f)^[(listCode ea xs).length] (xs,b)).2=xs.foldl (fun b a=>f (a,b)) b
      rw [listScan_iterate,List.take_of_length_le (list_length_le_code ea xs)])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackListOps.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

lemma fold_cons_append (xs ys : List α) : xs.foldl (fun ys a=>a::ys) ys=xs.reverse++ys := by
  induction xs generalizing ys with
  | nil=>rfl
  | cons a as ih=>simp only [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

lemma fold_map_cons_append (f : α→β) (xs : List α) (ys : List β) :
    xs.foldl (fun ys a=>f a::ys) ys=(xs.map f).reverse++ys := by
  induction xs generalizing ys with
  | nil=>rfl
  | cons a as ih=>simp only [List.foldl_cons,ih,List.map_cons,List.reverse_cons,
      List.append_assoc,List.singleton_append]

lemma listCode_length_map_bound (eb : β→List Bool) (f : α→β) (xs : List α) (B : ℕ)
    (h : ∀ a∈xs,(eb (f a)).length≤B) :
    (listCode eb (xs.map f)).length≤xs.length*(2*B+2)+1 := by
  induction xs with
  | nil=>simp [listCode]
  | cons a as ih=>
    have ha:=h a (by simp)
    have hb:=ih (by intro b hb;exact h b (by simp [hb]))
    simp only [List.map_cons,listCode_length_cons,List.length_cons]
    nlinarith

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listRevAppend (d : α) : Procedure (prodCode (listCode ea) (listCode ea))
    (listCode ea) (fun x=>x.1.reverse++x.2) :=
  (foldList d (listCons ea) Polynomial.X (by
    intro xs ys i
    rw [fold_cons_append]
    have hh:=listCode_length_append ea (xs.take i).reverse ys
    rw [listCode_length_rev] at hh
    have ht:=listCode_length_take_le ea i xs
    simp only [Polynomial.eval_X]
    omega)).congrFun (by intro x;exact fold_cons_append x.1 x.2)

noncomputable def listReverse (d : α) : Procedure (listCode ea) (listCode ea) List.reverse :=
  ((listRevAppend ea d).comp ((identity (listCode ea)).pair
    (constant (listCode ea) (listCode ea) []))).congrFun (by intro xs;exact List.append_nil _)

noncomputable def listAppend (d : α) : Procedure (prodCode (listCode ea) (listCode ea))
    (listCode ea) (fun x=>x.1++x.2) :=
  ((listRevAppend ea d).comp (((listReverse ea d).comp (first (listCode ea) (listCode ea))).pair
    (second (listCode ea) (listCode ea)))).congrFun (by intro x;exact congrArg (fun xs=>xs++x.2) (List.reverse_reverse x.1))

variable {ea} {eb : β→List Bool} {f : α→β}
noncomputable def listMap (d : α) (e : β) (p : Procedure ea eb f) :
    Procedure (listCode ea) (listCode eb) (List.map f) := by
  let step:=(listCons eb).comp ((p.comp (first ea (listCode eb))).pair (second ea (listCode eb)))
  let q:=Polynomial.X*(Polynomial.C 2*(Polynomial.X+p.bound)+Polynomial.C 2)+1+Polynomial.X
  let fold:=foldList d step q (by
    intro xs ys i
    change (listCode eb ((xs.take i).foldl (fun ys a=>f a::ys) ys)).length≤_
    rw [fold_map_cons_append]
    let L:=(listCode ea xs).length+(listCode eb ys).length
    have hh:=listCode_length_append eb ((xs.take i).map f).reverse ys
    rw [listCode_length_rev] at hh
    have hm:(listCode eb ((xs.take i).map f)).length≤(xs.take i).length*(2*(L+p.bound.eval L)+2)+1:=by
      apply listCode_length_map_bound
      intro a ha
      have hc:=(code_le_of_mem ea (List.mem_of_mem_take ha)).trans (Nat.le_add_right _ (listCode eb ys).length)
      have ho:=p.output_length_le a
      have hp:=eval_nat_mono p.bound hc
      dsimp only [L] at *
      omega
    have ht : (xs.take i).length≤L:=by
      have h1:=list_length_le_code ea xs
      simp only [List.length_take]
      dsimp [L];omega
    have hm':=(Nat.mul_le_mul_right (2*(L+p.bound.eval L)+2) ht)
    simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    change (listCode eb (((xs.take i).map f).reverse++ys)).length≤L*(2*(L+p.bound.eval L)+2)+1+L
    dsimp only [L] at *
    omega)
  let start:=(identity (listCode ea)).pair (constant (listCode ea) (listCode eb) [])
  exact ((listReverse eb e).comp (fold.comp start)).congrFun (by
    intro xs
    change (xs.foldl (fun ys a=>f a::ys) []).reverse=xs.map f
    rw [fold_map_cons_append,List.append_nil,List.reverse_reverse])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackTabulate.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def tabStep (f : α→ℕ→β) (s : ℕ×(α×List β)) : ℕ×(α×List β) :=
  (s.1+1,s.2.1,f s.2.1 s.1::s.2.2)
def tabCode (ea : α→List Bool) (eb : β→List Bool) := prodCode unaryCode (prodCode ea (listCode eb))
lemma tabStep_iterate (f : α→ℕ→β) (j i : ℕ) (a : α) (ys : List β) :
    (tabStep f)^[j] (i,a,ys)=(i+j,a,((List.range' i j).map (f a)).reverse++ys) := by
  induction j with
  | zero=>simp
  | succ j ih=>
    rw [Function.iterate_succ_apply',ih]
    simp only [tabStep,List.range'_1_concat,List.map_append,List.map_cons,List.map_nil,
      List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
    simp only [Nat.add_assoc]
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {f : α→ℕ→β}
noncomputable def tabStepP (p : Procedure (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Procedure (tabCode ea eb) (tabCode ea eb) (tabStep f) := by
  let i:=first unaryCode (prodCode ea (listCode eb))
  let rest:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp rest
  let ys:=(second ea (listCode eb)).comp rest
  exact ((unarySuccessor.comp i).pair
    (a.pair ((listCons eb).comp ((p.comp (i.pair a)).pair ys)))).congrFun (by intro s;rfl)
noncomputable def tabulate (d : β)
    (p : Procedure (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Procedure (prodCode unaryCode ea) (listCode eb)
      (fun x=>(List.range x.1).map (f x.2)) := by
  let q:=(Polynomial.X+p.bound).comp (Polynomial.C 2*Polynomial.X+1)
  have hval (a : α) (i : ℕ) : (eb (f a i)).length≤q.eval (i+(ea a).length) := by
    have ho:=p.output_length_le (i,a)
    have hm:=eval_nat_mono (Polynomial.X+p.bound)
      (show (prodCode unaryCode ea (i,a)).length≤2*(i+(ea a).length)+1 by
        simp only [prodCode,pairBits_length,unaryCode,List.length_replicate];omega)
    simp only [Polynomial.eval_add,Polynomial.eval_X] at hm
    simpa only [q,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one] using ho.trans hm
  let rep:=(tabStepP p).iterate (Polynomial.X*(Polynomial.C 2*q+Polynomial.C 5)) (by
    rintro n ⟨i,a,ys⟩ j hj
    rw [tabStep_iterate]
    have len0 : (tabCode ea eb (i,a,ys)).length=2*i+2*(ea a).length+(listCode eb ys).length+2 := by
      simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
    have hv : ∀ k∈List.range' i j,(eb (f a k)).length≤q.eval (n+(tabCode ea eb (i,a,ys)).length) := by
      intro k hk
      have hk':=List.mem_range'.mp hk
      exact (hval a k).trans (eval_nat_mono q (by rw [len0];omega))
    have hmap:=listCode_length_map_bound eb (f a) (List.range' i j) _ hv
    have happ:=listCode_length_append eb (((List.range' i j).map (f a)).reverse) ys
    rw [listCode_length_rev] at happ
    simp only [List.length_range'] at hmap
    simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X] at *
    nlinarith)
  let inputN:=first unaryCode ea
  let inputA:=second unaryCode ea
  let start:=(constant (prodCode unaryCode ea) unaryCode 0).pair
    (inputA.pair (constant (prodCode unaryCode ea) (listCode eb) []))
  let result:=((second ea (listCode eb)).comp
    (second unaryCode (prodCode ea (listCode eb)))).comp (rep.comp (inputN.pair start))
  exact ((listReverse eb d).comp result).congrFun (by
    rintro ⟨n,a⟩
    change (((tabStep f)^[n] (0,a,[])).2.2).reverse=(List.range n).map (f a)
    rw [tabStep_iterate,List.append_nil,List.reverse_reverse,List.range_eq_range'])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackMultiplier.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma bits_length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

lemma bits_length_value (xs : List Bool) : (binaryValue xs).bits.length≤xs.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact binaryValue_lt xs

lemma bits_length_add (a b : ℕ) : (a+b).bits.length≤a.bits.length+b.bits.length+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have hap : 2^a.size≤2^(a.bits.length+b.bits.length):=by
    apply Nat.pow_le_pow_right (by omega)
    simp only [Nat.size_eq_bits_len];omega
  have hbp : 2^b.size≤2^(a.bits.length+b.bits.length):=by
    apply Nat.pow_le_pow_right (by omega)
    simp only [Nat.size_eq_bits_len];omega
  rw [pow_succ]
  omega

lemma bits_length_mul (a b : ℕ) : (a*b).bits.length≤a.bits.length+b.bits.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le,pow_add]
  have h:=Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)
  simpa only [Nat.size_eq_bits_len] using h

lemma bits_length_pow2 (n : ℕ) : (2^n).bits.length=n+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_pow]

def mulZeroStep (x : ℕ×ℕ) : ℕ×ℕ := (x.1,2*x.2)
def mulOneStep (x : ℕ×ℕ) : ℕ×ℕ := (x.1,2*x.2+x.1)

lemma mul_fold (xs : List Bool) (x : ℕ×ℕ) :
    xs.foldl (bitAction mulZeroStep mulOneStep) x=
      (x.1,x.1*binaryValue xs.reverse+2^xs.length*x.2) := by
  induction xs generalizing x with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    rw [List.foldl_cons,ih]
    simp only [List.reverse_cons,binaryValue_append,List.length_reverse,List.length_cons,
      binaryValue,pow_succ]
    cases b <;> simp [bitAction,mulZeroStep,mulOneStep] <;> ring

namespace Procedure
noncomputable def mulZeroStepP : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) mulZeroStep :=
  ((first Nat.bits Nat.bits).pair (double.comp (second Nat.bits Nat.bits))).congrFun (by intro x;rfl)
noncomputable def mulOneStepP : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) mulOneStep := by
  let first:=first Nat.bits Nat.bits
  let second:=second Nat.bits Nat.bits
  exact (first.pair (binaryAdd.comp ((double.comp second).pair first))).congrFun (by intro x;rfl)

noncomputable def mulFoldP : Procedure (prodCode id (prodCode Nat.bits Nat.bits))
    (prodCode Nat.bits Nat.bits) (fun x=>x.1.foldl (bitAction mulZeroStep mulOneStep) x.2) :=
  foldBits mulZeroStepP mulOneStepP (Polynomial.C 3*Polynomial.X+Polynomial.C 3) (by
    intro xs x i
    rw [mul_fold]
    simp only [prodCode,pairBits_length]
    have hs:=bits_length_add (x.1*binaryValue (xs.take i).reverse) (2^(xs.take i).length*x.2)
    have hm:=bits_length_mul x.1 (binaryValue (xs.take i).reverse)
    have hn:=bits_length_mul (2^(xs.take i).length) x.2
    have hv:=bits_length_value (xs.take i).reverse
    rw [List.length_reverse] at hv
    rw [bits_length_pow2] at hn
    have hl : (xs.take i).length≤xs.length:=by simp only [List.length_take];omega
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega)

noncomputable def binaryMul : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1*x.2) := by
  let first:=first Nat.bits Nat.bits
  let second:=second Nat.bits Nat.bits
  let bits : Procedure Nat.bits (id : List Bool→List Bool) Nat.bits:=
    (identity (id : List Bool→List Bool)).precompose Nat.bits
  let start:=(reverse.comp (bits.comp second)).pair
    (first.pair (constant (prodCode Nat.bits Nat.bits) Nat.bits 0))
  exact ((Procedure.second Nat.bits Nat.bits).comp (mulFoldP.comp start)).congrFun (by
    intro x
    simp [mul_fold,binaryValue_bits])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackDivision.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
    {c : α→Bool} {f g : α→β}
noncomputable def conditional (test : Procedure ea boolCode c)
    (yes : Procedure ea eb f) (no : Procedure ea eb g) :
    Procedure ea eb (fun x=>if c x then f x else g x) :=
  (choose no yes).comp (test.pair (identity ea))

noncomputable def binaryZero : Procedure Nat.bits boolCode (fun n=>decide (n=0)) :=
  (isEmpty.precompose Nat.bits).congrFun (by
    intro n
    by_cases hn : n=0
    · subst n;rfl
    · have hh : n.bits≠[]:=by
        intro h
        have hy:=binaryValue_bits n
        rw [h] at hy
        exact hn hy.symm
      simp [hh,hn])
end Procedure

abbrev DivState := ℕ×ℕ×ℕ
abbrev divStateCode := prodCode Nat.bits (prodCode Nat.bits Nat.bits)

def divStep (b : Bool) (x : DivState) : DivState :=
  let t:=2*x.2.2+b.toNat
  if x.1≤t then (x.1,2*x.2.1+1,t-x.1) else (x.1,2*x.2.1,t)

lemma divStep_fst (b : Bool) (x : DivState) : (divStep b x).1=x.1 := by
  dsimp only [divStep];split <;> rfl

lemma divStep_size (b : Bool) (x : DivState) :
    (divStateCode (divStep b x)).length≤(divStateCode x).length+3 := by
  have hq : (2*x.2.1+1).bits.length≤x.2.1.bits.length+1:=doubleOne_bits_length _
  have hq0:=double_bits_length x.2.1
  have hr : (2*x.2.2+b.toNat).bits.length≤x.2.2.bits.length+1:=by
    cases b
    · simpa using double_bits_length x.2.2
    · exact doubleOne_bits_length x.2.2
  have hs : (2*x.2.2+b.toNat-x.1).bits.length≤(2*x.2.2+b.toNat).bits.length:=
    bits_length_mono (Nat.sub_le _ _)
  simp only [divStateCode,divStep,prodCode,pairBits_length]
  split <;> dsimp only <;> omega

lemma divStep_spec (b : Bool) (x : DivState) (hr : x.2.2<x.1) :
    (divStep b x).2.2<x.1 ∧
      (divStep b x).2.1*x.1+(divStep b x).2.2=
        2*(x.2.1*x.1+x.2.2)+b.toNat := by
  have hb : b.toNat≤1:=by cases b <;> decide
  dsimp only [divStep]
  split
  · rename_i h
    have ht:=Nat.sub_add_cancel h
    dsimp only
    constructor <;> nlinarith
  · rename_i h
    dsimp only
    constructor <;> nlinarith

lemma div_fold_spec (xs : List Bool) (x : DivState) (hr : x.2.2<x.1) :
    let y:=xs.foldl (bitAction (divStep false) (divStep true)) x
    y.1=x.1 ∧ y.2.2<x.1 ∧
      y.2.1*x.1+y.2.2=binaryValue xs.reverse+2^xs.length*(x.2.1*x.1+x.2.2) := by
  induction xs generalizing x with
  | nil=>simp [binaryValue,hr]
  | cons b bs ih=>
    have he : bitAction (divStep false) (divStep true) x b=divStep b x:=by cases b <;> rfl
    rw [List.foldl_cons,he]
    have H:=divStep_spec b x hr
    have hi:=ih (divStep b x) (by rw [divStep_fst];exact H.1)
    simp only [divStep_fst] at hi
    refine ⟨hi.1,hi.2.1,?_⟩
    rw [hi.2.2,H.2]
    simp only [List.reverse_cons,binaryValue_append,List.length_reverse,List.length_cons,
      binaryValue,pow_succ]
    ring

def divideRaw (x : List Bool×ℕ) : ℕ×ℕ :=
  (x.1.reverse.foldl (bitAction (divStep false) (divStep true)) (x.2,0,0)).2

lemma divideRaw_spec (x : List Bool×ℕ) (hp : 0<x.2) :
    divideRaw x=(binaryValue x.1/x.2,binaryValue x.1%x.2) := by
  have hh:=div_fold_spec x.1.reverse (x.2,0,0) hp
  simp only [List.reverse_reverse,zero_mul,mul_zero,Nat.add_zero] at hh
  have hq : binaryValue x.1/x.2=(divideRaw x).1:=by
    apply Nat.div_eq_of_lt_le <;> dsimp [divideRaw] <;> nlinarith [hh.2.1,hh.2.2]
  have hm:=Nat.mod_add_div (binaryValue x.1) x.2
  rw [hq] at hm
  apply Prod.ext
  · exact hq.symm
  · dsimp [divideRaw] at hm ⊢;nlinarith [hh.2.2]

namespace Procedure
noncomputable def divStepP (b : Bool) : Procedure divStateCode divStateCode (divStep b) := by
  let d:=first Nat.bits (prodCode Nat.bits Nat.bits)
  let qr:=second Nat.bits (prodCode Nat.bits Nat.bits)
  let q:=(first Nat.bits Nat.bits).comp qr
  let r:=(second Nat.bits Nat.bits).comp qr
  let db : Procedure Nat.bits Nat.bits (fun n=>2*n+b.toNat):=by
    cases b
    · exact double.congrFun (by intro n;simp)
    · exact doubleOne
  let t:=db.comp r
  let test:=binaryLe.comp (d.pair t)
  let yes:=d.pair ((doubleOne.comp q).pair (binarySub.comp (t.pair d)))
  let no:=d.pair ((double.comp q).pair t)
  exact (conditional test yes no).congrFun (by intro x;simp only [Function.comp_apply,divStep,decide_eq_true_eq])

noncomputable def divideRawP : Procedure (prodCode (id : List Bool→List Bool) Nat.bits)
    (prodCode Nat.bits Nat.bits) divideRaw := by
  let x:=first (id : List Bool→List Bool) Nat.bits
  let d:=second (id : List Bool→List Bool) Nat.bits
  let zero:=constant (prodCode (id : List Bool→List Bool) Nat.bits) Nat.bits 0
  let start:=(reverse.comp x).pair (d.pair (zero.pair zero))
  let fold:=foldBitsLinear (divStepP false) (divStepP true) 3 (divStep_size false) (divStep_size true)
  exact ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp (fold.comp start)).congrFun (by intro x;rfl)

noncomputable def binaryDivMod : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) (fun x=>(x.1/x.2,x.1%x.2)) := by
  let raw:=(divideRawP.precompose (fun x : ℕ×ℕ=>(x.1.bits,x.2)))
  let test:=binaryZero.comp (second Nat.bits Nat.bits)
  let zerocase:=(constant (prodCode Nat.bits Nat.bits) Nat.bits 0).pair (first Nat.bits Nat.bits)
  exact (conditional test zerocase raw).congrFun (by
    intro x
    change (if decide (x.2=0) then (0,x.1) else divideRaw (x.1.bits,x.2))=(x.1/x.2,x.1%x.2)
    by_cases hz : x.2=0
    · simp [hz]
    · simp only [hz,decide_false,Bool.false_eq_true,ite_false]
      simpa only [binaryValue_bits] using divideRaw_spec (x.1.bits,x.2) (by omega))

noncomputable def binaryDiv : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1/x.2) := (first Nat.bits Nat.bits).comp binaryDivMod
noncomputable def binaryMod : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1%x.2) := (second Nat.bits Nat.bits).comp binaryDivMod
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackListIndex.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
def dropStep : ℕ×List α→ℕ×List α
  | (n,xs)=>if n=0 then (n,xs) else (n-1,xs.tail)
lemma dropStep_iterate (i n : ℕ) (xs : List α) :
    dropStep^[i] (n,xs)=(n-i,xs.drop (min i n)) := by
  induction i generalizing n xs with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    by_cases hn : n=0
    · subst n;simp [dropStep,ih]
    · obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hn
      simp only [dropStep,Nat.succ_ne_zero,ite_false,Nat.succ_sub_one,ih]
      rw [←List.drop_one,List.drop_drop]
      congr 1
      · omega
      · congr 1; omega

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listDrop : Procedure (prodCode Nat.bits (listCode ea)) (listCode ea)
    (fun x=>x.2.drop x.1) := by
  let en:=prodCode Nat.bits (listCode ea)
  let n:=first Nat.bits (listCode ea)
  let xs:=second Nat.bits (listCode ea)
  let pred:=binarySub.comp (n.pair (constant en Nat.bits 1))
  let step:=(conditional (binaryZero.comp n) (identity en)
    (pred.pair ((listTail ea).comp xs))).congrFun (by intro x;rfl)
  have stepType : Procedure en en (dropStep (α:=α)):=
    step.congrFun (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,id_eq,dropStep])
  let rep:=stepType.iterate Polynomial.X (by
    intro k x i _
    rw [dropStep_iterate]
    simp only [en,prodCode,pairBits_length,Polynomial.eval_X]
    have hn:=bits_length_mono (Nat.sub_le x.1 i)
    have hl:=listCode_length_drop_le ea (min i x.1) x.2
    omega)
  let times:=(length.precompose (listCode ea)).comp xs
  exact (xs.comp (rep.comp (times.pair (identity en)))).congrFun (by
    intro x
    change (dropStep^[(listCode ea x.2).length] x).2=x.2.drop x.1
    rw [dropStep_iterate]
    by_cases h:x.1≤(listCode ea x.2).length
    · rw [Nat.min_eq_right h]
    · have hlen:=list_length_le_code ea x.2
      rw [Nat.min_eq_left (by omega),List.drop_eq_nil_of_le (by omega),List.drop_eq_nil_of_le (by omega)])
noncomputable def listGet (d : α) : Procedure (prodCode Nat.bits (listCode ea)) ea
    (fun x=>(x.2.drop x.1).headD d) := (listHead ea d).comp (listDrop ea)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackListLength.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
lemma fold_count (xs : List α) (n : ℕ) : xs.foldl (fun n _=>n+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil=>simp
  | cons a as ih=>simp only [List.foldl_cons,ih,List.length_cons];omega
namespace Procedure
noncomputable def listLength (ea : α→List Bool) (d : α) :
    Procedure (listCode ea) Nat.bits List.length := by
  let step:=unarySuccessor.comp (second ea unaryCode)
  let rep:=foldList d step Polynomial.X (by
    intro xs n i
    change (unaryCode ((xs.take i).foldl (fun n _=>n+1) n)).length≤_
    rw [fold_count]
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X,List.length_take]
    have hh:=list_length_le_code ea xs
    omega)
  let start:=(identity (listCode ea)).pair (constant (listCode ea) unaryCode 0)
  exact (unaryToBits.comp (rep.comp start)).congrFun (by intro xs;simpa only [Function.comp_apply,id_eq,Nat.zero_add] using fold_count xs 0)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGModel.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std Sat
abbrev Ref := ℕ × Bool
abbrev Key := Ref × Ref
/-- A literal list representation of the nodes and the (possibly incomplete)
cache. The cache is not replaced by a search through all nodes. -/
inductive Decl where
  | zero
  | atom (i : ℕ)
  | gate (a b : Ref)
  deriving DecidableEq, Inhabited
structure Graph where
  decls : List Decl
  cache : List (Key × ℕ)
  deriving Inhabited

def eraseDecl {n : ℕ} : AIG.Decl (Fin n) → Decl
  | .false => .zero
  | .atom i => .atom i.val
  | .gate a b => .gate (a.gate,a.invert) (b.gate,b.invert)
def lookup (k : Key) : List (Key × ℕ) → Option ℕ
  | [] => none
  | (a,v)::as => if k=a then some v else lookup k as

def nativeKey {n : ℕ} (k : Key) : AIG.Decl (Fin n) :=
  .gate (.mk k.1.1 k.1.2) (.mk k.2.1 k.2.2)
def Rel {n : ℕ} (r : Graph) (g : AIG (Fin n)) : Prop :=
  r.decls=g.decls.toList.map eraseDecl ∧
  ∀ k,lookup k r.cache=g.cache.val[nativeKey (n:=n) k]?
def constant (r : Graph) (a : Ref) : Option Bool :=
  match r.decls[a.1]?.getD .zero with
  | .zero => some a.2
  | _ => none

def empty : Graph := ⟨[.zero],[]⟩
def atom (r : Graph) (i : ℕ) : Graph × Ref :=
  (⟨r.decls++[.atom i],r.cache⟩,(r.decls.length,false))
def addGate (r : Graph) (a b : Ref) : Graph × Ref :=
  (⟨r.decls++[.gate a b],((a,b),r.decls.length)::r.cache⟩,(r.decls.length,false))
def go (r : Graph) (a b : Ref) : Graph × Ref :=
  match lookup (a,b) r.cache with
  | some i => (r,(i,false))
  | none =>
    match constant r a,constant r b with
    | some false,_ | _,some false => (r,(0,false))
    | some true,_ => (r,b)
    | _,some true => (r,a)
    | _,_ => if a.1=b.1 then
        if a.2=b.2 then (r,a) else (r,(0,false))
      else addGate r a b
def gate (r : Graph) (a b : Ref) : Graph × Ref :=
  if a.1<b.1 then go r a b else go r b a

def EPRel {n : ℕ} (r : Graph × Ref) (e : AIG.Entrypoint (Fin n)) : Prop :=
  Rel r.1 e.aig ∧ r.2=(e.ref.gate,e.ref.invert)

lemma cache_project {α : Type} [Hashable α] [DecidableEq α]
    {ds : Array (AIG.Decl α)} (c : AIG.Cache α ds) (d : AIG.Decl α) :
    (c.get? d).map AIG.CacheHit.idx=c.val[d]? := by
  unfold AIG.Cache.get?
  split <;> simp_all
lemma nativeKey_injective {n : ℕ} : Function.Injective (nativeKey (n:=n)) := by
  rintro ⟨⟨a,ai⟩,⟨b,bi⟩⟩ ⟨⟨c,ci⟩,⟨d,di⟩⟩ h
  simp only [nativeKey,AIG.Decl.gate.injEq] at h
  have ha:=congrArg AIG.Fanin.gate h.1
  have hai:=congrArg AIG.Fanin.invert h.1
  have hb:=congrArg AIG.Fanin.gate h.2
  have hbi:=congrArg AIG.Fanin.invert h.2
  simp only [AIG.Fanin.gate_mk,AIG.Fanin.invert_mk] at *
  simp_all
lemma empty_rel (n : ℕ) : Rel empty (AIG.empty : AIG (Fin n)) := by
  constructor
  · rfl
  · intro k;simp [empty,lookup,AIG.empty,AIG.Cache.empty]
lemma constant_eq {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (a : AIG.Ref g) :
    constant r (a.gate,a.invert)=AIG.getConstant g a := by
  unfold constant
  rw [h.1]
  simp only [List.getElem?_map,Array.getElem?_toList,Array.getElem?_eq_getElem a.hgate,Option.map_some,
    Option.getD_some]
  rw [AIG.getConstant]
  cases g.decls[a.gate]'a.hgate <;> rfl
lemma atom_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : Fin n) :
    EPRel (atom r i.val) (AIG.mkAtom g i) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · simpa only [atom,AIG.mkAtom,Array.toList_push,List.map_append,List.map_cons,List.map_nil,eraseDecl]
      using congrArg (fun ds=>ds++[Decl.atom i.val]) h.1
  · intro k;simpa only [atom,AIG.mkAtom,AIG.Cache.noUpdate] using h.2 k
  · simp only [atom,AIG.mkAtom,h.1,List.length_map,Array.length_toList]
lemma pushed_rel {n : ℕ} {r : Graph} {g g' : AIG (Fin n)} (h : Rel r g) (a b : Ref)
    (hd : g'.decls=g.decls.push (nativeKey (a,b)))
    (hc : g'.cache.val=g.cache.val.insert (nativeKey (a,b)) g.decls.size) :
    Rel (addGate r a b).1 g' := by
  constructor
  · simp only [addGate,hd,Array.toList_push,List.map_append,List.map_cons,List.map_nil,
      nativeKey,eraseDecl,AIG.Fanin.gate_mk,AIG.Fanin.invert_mk,h.1]
  · intro k
    simp only [addGate,lookup,hc,Std.HashMap.getElem?_insert]
    simp only [beq_iff_eq,(nativeKey_injective (n:=n)).eq_iff]
    by_cases hk:k=(a,b)
    · simp only [hk,↓reduceIte,h.1,List.length_map,Array.length_toList]
    · simp only [hk,Ne.symm hk,↓reduceIte,h.2]

lemma go_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (go r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (AIG.mkGateCached.go g i) := by
  let k : Key:=((i.lhs.gate,i.lhs.invert),(i.rhs.gate,i.rhs.invert))
  have hl : lookup k r.cache=(g.cache.get? (nativeKey k)).map AIG.CacheHit.idx :=
    (h.2 k).trans (cache_project _ _).symm
  unfold go AIG.mkGateCached.go
  dsimp only
  change EPRel (match lookup k r.cache with
    | some v => (r,(v,false))
    | none => _) _
  rw [hl]
  cases hc : g.cache.get? (nativeKey k) with
  | some hit =>
    simp only [Option.map_some]
    simp only [nativeKey,k] at hc
    simp only [hc]
    exact ⟨h,rfl⟩
  | none =>
    simp only [Option.map_none]
    simp only [nativeKey,k] at hc
    simp only [hc]
    rw [constant_eq h i.lhs,constant_eq h i.rhs]
    cases ha : AIG.getConstant g i.lhs with
    | some a =>
      cases a <;> cases hb : AIG.getConstant g i.rhs with
      | none => exact ⟨h,rfl⟩
      | some b => cases b <;> exact ⟨h,rfl⟩
    | none =>
      cases hb : AIG.getConstant g i.rhs with
      | some b => cases b <;> exact ⟨h,rfl⟩
      | none =>
        simp only [beq_iff_eq]
        by_cases he : i.lhs.gate=i.rhs.gate
        · simp only [he,↓reduceIte]
          by_cases hi : i.lhs.invert=i.rhs.invert <;>
            simp only [hi,↓reduceIte] <;> exact ⟨h,rfl⟩
        · simp only [he,↓reduceIte]
          refine ⟨pushed_rel h _ _ rfl ?_,?_⟩
          · simp only [AIG.Cache.insert];rfl
          · simp only [addGate,h.1,List.length_map,Array.length_toList]
lemma gate_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (gate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkGateCached i) := by
  unfold gate AIG.mkGateCached
  dsimp only
  split
  · exact go_rel h ⟨i.lhs,i.rhs⟩
  · exact go_rel h ⟨i.rhs,i.lhs⟩
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackOptions.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def optionCode (ea : α→List Bool) : Option α→List Bool
  | none=>[false]
  | some a=>true::ea a
def optionView : Option α→Unit⊕α
  | none=>.inl ()
  | some a=>.inr a
lemma optionCode_length_some (ea : α→List Bool) (a : α) :
    (optionCode ea (some a)).length=(ea a).length+1 := rfl

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool}
noncomputable def optionSome (ea : α→List Bool) : Procedure ea (optionCode ea) some :=
  (prepend ea [true]).result (by intro a;rfl)
noncomputable def optionCases {f : Unit→β} {g : α→β}
    (p : Procedure emptyCode eb f) (q : Procedure ea eb g) :
    Procedure (optionCode ea) eb (fun x=>Sum.elim f g (optionView x)) :=
  ((casesSum p q).precompose optionView).congrEncoding
    (by intro x;cases x <;> rfl) (by intro x;rfl)
noncomputable def optionGet (ea : α→List Bool) (d : α) :
    Procedure (optionCode ea) ea (fun x=>x.getD d) :=
  (optionCases (constant emptyCode ea d) (identity ea)).congrFun
    (by intro x;cases x <;> rfl)
noncomputable def optionIsSome (ea : α→List Bool) :
    Procedure (optionCode ea) boolCode Option.isSome :=
  (optionCases (constant emptyCode boolCode false) (constant ea boolCode true)).congrFun
    (by intro x;cases x <;> rfl)
noncomputable def binaryEq : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1=x.2)) := by
  let swap:=(second Nat.bits Nat.bits).pair (first Nat.bits Nat.bits)
  exact (boolAnd.comp (binaryLe.pair (binaryLe.comp swap))).congrFun
    (by intro x;apply Bool.eq_iff_iff.mpr;simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq];omega)
noncomputable def prodEq [DecidableEq α] [DecidableEq β]
    (pa : Procedure (prodCode ea ea) boolCode (fun x=>decide (x.1=x.2)))
    (pb : Procedure (prodCode eb eb) boolCode (fun x=>decide (x.1=x.2))) :
    Procedure (prodCode (prodCode ea eb) (prodCode ea eb)) boolCode
      (fun x=>decide (x.1=x.2)) := by
  let l:=first (prodCode ea eb) (prodCode ea eb)
  let r:=second (prodCode ea eb) (prodCode ea eb)
  let a:=pa.comp (((first ea eb).comp l).pair ((first ea eb).comp r))
  let b:=pb.comp (((second ea eb).comp l).pair ((second ea eb).comp r))
  exact (boolAnd.comp (a.pair b)).congrFun (by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩;apply Bool.eq_iff_iff.mpr;simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,Prod.mk.injEq])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackAssociation.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type} [DecidableEq α]
def assocLookup (k : α) : List (α×β)→Option β
  | []=>none
  | (a,v)::as=>if k=a then some v else assocLookup k as
def assocStep (x : (α×β)×(α×Option β)) : α×Option β :=
  (x.2.1,if x.2.1=x.1.1 then some x.1.2 else x.2.2)
lemma assocFold_reverse (xs : List (α×β)) (k : α) (o : Option β) :
    xs.reverse.foldl (fun s a=>assocStep (a,s)) (k,o)=
      (k,match assocLookup k xs with | none=>o | some b=>some b) := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>
    rw [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    by_cases h:k=a.1 <;> simp [assocStep,assocLookup,h]
lemma assocFold_size (ea : α→List Bool) (eb : β→List Bool)
    (xs : List (α×β)) (s : α×Option β) :
    (prodCode ea (optionCode eb) (xs.foldl (fun s a=>assocStep (a,s)) s)).length≤
      (prodCode ea (optionCode eb) s).length+(listCode (prodCode ea eb) xs).length := by
  induction xs generalizing s with
  | nil=>simp
  | cons a as ih=>
    have hh:=ih (assocStep (a,s))
    have hb : (prodCode ea (optionCode eb) (assocStep (a,s))).length≤
        (prodCode ea (optionCode eb) s).length+2*(prodCode ea eb a).length+2:=by
      unfold assocStep
      split <;> simp only [prodCode,pairBits_length,optionCode,List.length_cons] <;> omega
    simp only [List.foldl_cons,listCode_length_cons]
    omega

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool}
noncomputable def association (da : α) (db : β)
    (eqp : Procedure (prodCode ea ea) boolCode (fun x=>decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode (prodCode ea eb))) (optionCode eb)
      (fun x=>assocLookup x.1 x.2) := by
  let ent:=prodCode ea eb
  let st:=prodCode ea (optionCode eb)
  let e:=first ent st
  let s:=second ent st
  let key:=(first ea (optionCode eb)).comp s
  let ky:=(first ea eb).comp e
  let value:=(second ea eb).comp e
  let upd:=conditional (eqp.comp (key.pair ky)) ((optionSome eb).comp value)
    ((second ea (optionCode eb)).comp s)
  let step : Procedure (prodCode ent st) st (assocStep (α:=α) (β:=β)):=
    (key.pair upd).congrFun (by intro x; simp only [assocStep,Function.comp_apply,decide_eq_true_eq])
  let fold:=foldList (da,db) step Polynomial.X (by
    intro xs s i
    have hh:=assocFold_size ea eb (xs.take i) s
    have ht:=listCode_length_take_le ent i xs
    simp only [Polynomial.eval_X]
    dsimp only [ent,st] at ht ⊢
    omega)
  let start:=((listReverse ent (da,db)).comp (second ea (listCode ent))).pair
    ((first ea (listCode ent)).pair (constant (prodCode ea (listCode ent)) (optionCode eb) none))
  exact ((second ea (optionCode eb)).comp (fold.comp start)).congrFun (by
    intro x
    change (x.2.reverse.foldl (fun s a=>assocStep (a,s)) (x.1,none)).2=assocLookup x.1 x.2
    rw [assocFold_reverse]
    cases assocLookup x.1 x.2 <;> rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGProcedures.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
abbrev refCode := prodCode Nat.bits boolCode
abbrev keyCode := prodCode refCode refCode
abbrev entryCode := prodCode keyCode Nat.bits
def declView : Decl→Unit⊕(ℕ⊕Key)
  | .zero=>.inl ()
  | .atom i=>.inr (.inl i)
  | .gate a b=>.inr (.inr (a,b))
def declCode (d : Decl) := sumCode emptyCode (sumCode Nat.bits keyCode) (declView d)
def graphCode (g : Graph) := prodCode (listCode declCode) (listCode entryCode) (g.decls,g.cache)

namespace Emission
open Procedure
noncomputable def refEq : Procedure (prodCode refCode refCode) boolCode
    (fun x=>decide (x.1=x.2)) := prodEq binaryEq (ofBool₂ boolCode fun a b=>decide (a=b))
noncomputable def keyEq : Procedure (prodCode keyCode keyCode) boolCode
    (fun x=>decide (x.1=x.2)) := prodEq refEq refEq
noncomputable def lookupP : Procedure (prodCode keyCode (listCode entryCode)) (optionCode Nat.bits)
    (fun x=>lookup x.1 x.2) :=
  (association ((0,false),(0,false)) 0 keyEq).congrFun (by
    rintro ⟨k,es⟩
    induction es with
    | nil=>rfl
    | cons e es ih=>simp only [assocLookup,lookup,ih])
noncomputable def decls : Procedure graphCode (listCode declCode) Graph.decls :=
  ((first (listCode declCode) (listCode entryCode)).precompose (fun g : Graph=>(g.decls,g.cache)))
noncomputable def cache : Procedure graphCode (listCode entryCode) Graph.cache :=
  ((second (listCode declCode) (listCode entryCode)).precompose (fun g : Graph=>(g.decls,g.cache)))
noncomputable def packGraph : Procedure (prodCode (listCode declCode) (listCode entryCode)) graphCode
    (fun x=>Graph.mk x.1 x.2) := (identity _).result (by intro x;rfl)
noncomputable def atomDecl : Procedure Nat.bits declCode Decl.atom :=
  (prepend Nat.bits [true,false]).result (by intro x;rfl)
noncomputable def gateDecl : Procedure keyCode declCode (fun x=>Decl.gate x.1 x.2) :=
  (prepend keyCode [true,true]).result (by intro x;rfl)
noncomputable def zeroDecl : Procedure declCode boolCode (fun x=>decide (x=Decl.zero)) :=
  ((casesSum (Procedure.constant emptyCode boolCode true)
    (Procedure.constant (sumCode Nat.bits keyCode) boolCode false)).precompose declView).congrFun
      (by intro x;cases x <;> rfl)
noncomputable def singleton {α : Type} (ea : α→List Bool) : Procedure ea (listCode ea) (fun a=>[a]) :=
  ((listCons ea).comp ((identity ea).pair (Procedure.constant ea (listCode ea) [])))
noncomputable def emptyP : Procedure emptyCode graphCode (fun _=>empty) :=
  Procedure.constant emptyCode graphCode empty
noncomputable def atomP : Procedure (prodCode graphCode Nat.bits) (prodCode graphCode refCode)
    (fun x=>atom x.1 x.2) := by
  let r:=first graphCode Nat.bits
  let i:=second graphCode Nat.bits
  let ds:=decls.comp r
  let cs:=cache.comp r
  let nd:=(listAppend declCode .zero).comp (ds.pair ((singleton declCode).comp (atomDecl.comp i)))
  let nr:=((listLength declCode .zero).comp ds).pair (Procedure.constant _ boolCode false)
  exact ((packGraph.comp (nd.pair cs)).pair nr).congrFun (by intro x;rfl)
noncomputable def addGateP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>addGate x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let ds:=decls.comp r
  let cs:=cache.comp r
  let sz:=(listLength declCode .zero).comp ds
  let nd:=(listAppend declCode .zero).comp (ds.pair ((singleton declCode).comp (gateDecl.comp k)))
  let nc:=(listCons entryCode).comp ((k.pair sz).pair cs)
  let nr:=sz.pair (Procedure.constant _ boolCode false)
  exact ((packGraph.comp (nd.pair nc)).pair nr).congrFun (by intro x;rfl)
noncomputable def constantP : Procedure (prodCode graphCode refCode) (optionCode boolCode)
    (fun x=>constant x.1 x.2) := by
  let r:=first graphCode refCode
  let a:=second graphCode refCode
  let idx:=(first Nat.bits boolCode).comp a
  let inv:=(second Nat.bits boolCode).comp a
  let d:=(listGet declCode .zero).comp (idx.pair (decls.comp r))
  exact (conditional (zeroDecl.comp d) ((optionSome boolCode).comp inv)
    (Procedure.constant _ (optionCode boolCode) none)).congrFun (by
      rintro ⟨g,⟨i,b⟩⟩
      simp only [Function.comp_apply,decide_eq_true_eq]
      have he : (g.decls.drop i).headD Decl.zero=g.decls[i]?.getD Decl.zero := by
        rw [List.headD_eq_head?_getD,List.head?_drop]
      rw [he]
      unfold constant
      cases g.decls[i]?.getD Decl.zero <;> simp)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGGateProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG.Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def optionTrue : Procedure (optionCode boolCode) boolCode
    (fun x=>x=some true) :=
  (optionGet boolCode false).congrFun (by intro x;cases x with
    | none=>rfl
    | some b=>cases b <;> rfl)
noncomputable def optionFalse : Procedure (optionCode boolCode) boolCode
    (fun x=>x=some false) :=
  (optionCases (Procedure.constant emptyCode boolCode false) boolNot).congrFun
    (by intro x;cases x with
    | none=>rfl
    | some b=>cases b <;> rfl)
noncomputable def goP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>go x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let ca:=constantP.comp (r.pair a)
  let cb:=constantP.comp (r.pair b)
  let lk:=lookupP.comp (k.pair (cache.comp r))
  let z:=r.pair (Procedure.constant _ refCode (0,false))
  let ra:=r.pair a
  let rb:=r.pair b
  let cm:=(binaryEq.comp (((first Nat.bits boolCode).comp a).pair
    ((first Nat.bits boolCode).comp b)))
  let ci:=((ofBool₂ boolCode (fun a b=>decide (a=b))).comp
    (((second Nat.bits boolCode).comp a).pair ((second Nat.bits boolCode).comp b)))
  let twins:=conditional cm (conditional ci ra z) addGateP
  let rest:=conditional (boolOr.comp ((optionFalse.comp ca).pair (optionFalse.comp cb))) z
    (conditional (optionTrue.comp ca) rb (conditional (optionTrue.comp cb) ra twins))
  let hit:=r.pair (((optionGet Nat.bits 0).comp lk).pair (Procedure.constant _ boolCode false))
  exact (conditional ((optionIsSome Nat.bits).comp lk) hit rest).congrFun (by
    rintro ⟨g,⟨a,b⟩⟩
    simp only [Function.comp_apply]
    unfold go
    cases hl : lookup (a,b) g.cache with
    | some i=>simp
    | none=>
      simp only [Option.isSome_none,Bool.false_eq_true,↓reduceIte,Bool.or_eq_true,decide_eq_true_eq]
      cases ha : constant g a with
      | none=>
        cases hb : constant g b with
        | none=>simp
        | some bb=>cases bb <;> simp
      | some aa=>cases aa <;> cases hb : constant g b with
        | none=>simp
        | some bb=>cases bb <;> simp)
noncomputable def gateP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>gate x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let t:=binaryLt.comp (((first Nat.bits boolCode).comp a).pair ((first Nat.bits boolCode).comp b))
  exact (conditional t goP (goP.comp (r.pair (b.pair a)))).congrFun
    (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,gate])
end ExactQuantumFactoring.NativeAIG.Emission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGBoolean.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat
def notRef (a : Ref) : Ref := (a.1,!a.2)
def orGate (r : Graph) (a b : Ref) : Graph×Ref :=
  let s:=gate r (notRef a) (notRef b)
  (s.1,notRef s.2)
def xorGate (r : Graph) (a b : Ref) : Graph×Ref :=
  let s:=gate r a b
  let t:=gate s.1 (notRef a) (notRef b)
  gate t.1 (notRef s.2) (notRef t.2)
lemma or_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (orGate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkOrCached i) := by
  have hs:=gate_rel h (i.invert true true)
  simpa only [EPRel,orGate,AIG.mkOrCached,AIG.BinaryInput.invert,AIG.Ref.not,
    AIG.Ref.flip,Bool.true_xor,notRef] using And.intro hs.1 (congrArg notRef hs.2)
lemma xor_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (xorGate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkXorCached i) := by
  let s:=g.mkGateCached i
  let sr:=gate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert)
  have hs : EPRel sr s:=gate_rel h i
  let i':=i.cast (AIG.LawfulOperator.le_size (f:=AIG.mkGateCached) g i)
  let t:=s.aig.mkGateCached (i'.invert true true)
  let tr:=gate sr.1 (notRef (i.lhs.gate,i.lhs.invert)) (notRef (i.rhs.gate,i.rhs.invert))
  have ht : EPRel tr t := by
    simpa only [tr,t,i',notRef,AIG.BinaryInput.cast,AIG.BinaryInput.invert,
      AIG.Ref.cast,AIG.Ref.flip,Bool.true_xor] using gate_rel hs.1 (i'.invert true true)
  let a:=s.ref.cast (AIG.LawfulOperator.le_size (f:=AIG.mkGateCached) s.aig (i'.invert true true))
  have hh:=gate_rel ht.1 (⟨a.not,t.ref.not⟩ : AIG.BinaryInput t.aig)
  have ha : (a.not.gate,a.not.invert)=notRef sr.2 := by
    simpa only [a,AIG.Ref.cast,AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,notRef]
      using congrArg notRef hs.2.symm
  have hb : (t.ref.not.gate,t.ref.not.invert)=notRef tr.2 := by
    simpa only [AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,notRef]
      using congrArg notRef ht.2.symm
  change EPRel (gate tr.1 (a.not.gate,a.not.invert) (t.ref.not.gate,t.ref.not.invert)) _ at hh
  rw [ha,hb] at hh
  exact hh

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def notRefP : Procedure refCode refCode notRef :=
  ((first Nat.bits boolCode).pair (boolNot.comp (second Nat.bits boolCode)))
noncomputable def orP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>orGate x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let s:=gateP.comp (r.pair ((notRefP.comp a).pair (notRefP.comp b)))
  exact (((first graphCode refCode).comp s).pair
    (notRefP.comp ((second graphCode refCode).comp s))).congrFun (by intro x;rfl)
noncomputable def xorP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>xorGate x.1 x.2.1 x.2.2) := by
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let s:=gateP
  let t:=gateP.comp (((first graphCode refCode).comp s).pair
    ((notRefP.comp a).pair (notRefP.comp b)))
  exact (gateP.comp (((first graphCode refCode).comp t).pair
    ((notRefP.comp ((second graphCode refCode).comp s)).pair
      (notRefP.comp ((second graphCode refCode).comp t))))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGFullAdder.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
abbrev Triple := Ref×Ref×Ref
def fullOut (r : Graph) (a b c : Ref) : Graph×Ref :=
  let s:=xorGate r a b
  xorGate s.1 s.2 c
def fullCarry (r : Graph) (a b c : Ref) : Graph×Ref :=
  let s:=xorGate r a b
  let t:=gate s.1 s.2 c
  let u:=gate t.1 a b
  orGate u.1 t.2 u.2
def full (r : Graph) (a b c : Ref) : Graph×(Ref×Ref) :=
  let o:=fullOut r a b c
  let k:=fullCarry o.1 a b c
  (k.1,(o.2,k.2))
lemma fullOut_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g)
    (i : FullAdderInput g) :
    EPRel (fullOut r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert))
      (mkFullAdderOut g i) := by
  let s:=g.mkXorCached ⟨i.lhs,i.rhs⟩
  have hs:=xor_rel h (⟨i.lhs,i.rhs⟩ : AIG.BinaryInput g)
  have hh:=xor_rel hs.1 (⟨s.ref,i.cin.cast (AIG.LawfulOperator.le_size (f:=AIG.mkXorCached) ..)⟩ :
    AIG.BinaryInput s.aig)
  change EPRel (xorGate _ (s.ref.gate,s.ref.invert) (i.cin.gate,i.cin.invert)) _ at hh
  rw [←hs.2] at hh
  exact hh
lemma fullCarry_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g)
    (i : FullAdderInput g) :
    EPRel (fullCarry r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert))
      (mkFullAdderCarry g i) := by
  let si : AIG.BinaryInput g:=⟨i.lhs,i.rhs⟩
  let s:=g.mkXorCached si
  have hs:=xor_rel h si
  let hsub:=AIG.LawfulOperator.le_size (f:=AIG.mkXorCached) g si
  let ti : AIG.BinaryInput s.aig:=⟨s.ref,i.cin.cast hsub⟩
  let t:=s.aig.mkAndCached ti
  have ht:=gate_rel hs.1 ti
  change EPRel (gate _ (s.ref.gate,s.ref.invert) (i.cin.gate,i.cin.invert)) t at ht
  rw [←hs.2] at ht
  let hlor:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) s.aig ti
  let ui : AIG.BinaryInput t.aig:=⟨(i.lhs.cast hsub).cast hlor,(i.rhs.cast hsub).cast hlor⟩
  let u:=t.aig.mkAndCached ui
  have hu:=gate_rel ht.1 ui
  change EPRel (gate _ (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert)) u at hu
  let hror:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) t.aig ui
  have hh:=or_rel hu.1 (⟨t.ref.cast hror,u.ref⟩ : AIG.BinaryInput u.aig)
  change EPRel (orGate _ (t.ref.gate,t.ref.invert) (u.ref.gate,u.ref.invert)) _ at hh
  rw [←ht.2,←hu.2] at hh
  exact hh
lemma full_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g)
    (i : FullAdderInput g) :
    Rel (full r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert)).1
      (mkFullAdder g i).aig ∧
    (full r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert)).2 =
      (((mkFullAdder g i).out.gate,(mkFullAdder g i).out.invert),
        ((mkFullAdder g i).cout.gate,(mkFullAdder g i).cout.invert)) := by
  have ho:=fullOut_rel h i
  have hk:=fullCarry_rel ho.1 (i.cast (AIG.LawfulOperator.le_size (f:=mkFullAdderOut) g i))
  exact ⟨hk.1,congrArg₂ Prod.mk ho.2 hk.2⟩

end ExactQuantumFactoring.NativeAIG
end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGVector.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

def eraseVec {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) : List Ref :=
  List.ofFn (fun i : Fin w=>((v.get i.val i.isLt).gate,(v.get i.val i.isLt).invert))
@[simp] lemma eraseVec_length {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) :
    (eraseVec v).length=w := List.length_ofFn
@[simp] lemma eraseVec_get {n w k : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) (h : k<w) :
    ((eraseVec v).drop k).headD (0,false)=((v.get k h).gate,(v.get k h).invert) := by
  rw [List.headD_eq_head?_getD,List.head?_drop]
  simp [eraseVec,h]
@[simp] lemma eraseVec_cast {n w : ℕ} {g g' : AIG (Fin n)} (v : AIG.RefVec g w)
    (h : g.decls.size≤g'.decls.size) : eraseVec (v.cast h)=eraseVec v := rfl
@[simp] lemma eraseVec_empty {n : ℕ} (g : AIG (Fin n)) : eraseVec (AIG.RefVec.empty (aig:=g))=[] := rfl
@[simp] lemma eraseVec_push {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) (a : AIG.Ref g) :
    eraseVec (v.push a)=eraseVec v++[(a.gate,a.invert)] := by
  rw [eraseVec,List.ofFn_succ_last]
  congr 1
  · congr 1;funext i
    dsimp only [Fin.val_castSucc]
    rw [AIG.RefVec.get_push_ref_lt _ _ _ i.isLt]
  · simp

@[simp] lemma refVec_get_gate {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w)
    (idx : ℕ) (h : idx<w) : (v.get idx h).gate=v.refs[idx].gate := by
  cases v;rfl
@[simp] lemma refVec_get_invert {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w)
    (idx : ℕ) (h : idx<w) : (v.get idx h).invert=v.refs[idx].invert := by
  cases v;rfl

def VecRel {n w : ℕ} (r : Graph×List Ref) (v : AIG.RefVecEntry (Fin n) w) : Prop :=
  Rel r.1 v.aig ∧ r.2=eraseVec v.vec

def declIsZero : Decl→Bool
  | .zero=>true
  | _=>false
def known (r : Graph) (a : Ref) : Bool:=declIsZero (r.decls[a.1]?.getD .zero)
def countKnown (r : Graph) (as : List Ref) : ℕ := (as.filter (known r)).length
lemma known_eq {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (a : AIG.Ref g) :
    known r (a.gate,a.invert) = (match g.decls[a.gate]'a.hgate with | .false=>true | _=>false) := by
  unfold known
  rw [h.1]
  simp only [List.getElem?_map,Array.getElem?_toList,Array.getElem?_eq_getElem a.hgate,
    Option.map_some,Option.getD_some]
  cases g.decls[a.gate]'a.hgate <;> rfl
end ExactQuantumFactoring.NativeAIG

end



end OAI
