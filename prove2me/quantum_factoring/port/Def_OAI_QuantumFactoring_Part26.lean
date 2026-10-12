/-
Exact quantum factoring development (port of OpenAI's formalization), part 26 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: BitStackPrograms.lean, BitStackRelabel.lean, BitStackLists.lean, BitStackProcedures.lean, BitStackComposition.lean, BitStackQuotation.lean, BitStackFrames.lean, BitStackProducts.lean, BitStackBasicProcedures.lean, BitStackConstants.lean, BitStackIncrement.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted; compatibility edits for the platform Lean/Mathlib versions: in BitStackLists.lean, after `convert`, close the step-count goal with `simp only [List.length_cons, List.length_nil] <;> omega` (no longer closed automatically); in BitStackQuotation.lean, after `convert`, close the step-count goal with `simp only [List.length_cons, List.length_nil] <;> omega` (no longer closed automatically); in BitStackConstants.lean, after `convert`, close the step-count goal with `simp only [List.length_cons, List.length_nil] <;> omega` (no longer closed automatically).
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part25

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackPrograms.lean =====
namespace OAI



section

/-! A literal finite Boolean-stack compiler for circuit descriptions.
Branches inspect and consume one symbol, not an entire encoded word.
Operational derivations below count actual finite-state TM2 transitions.
-/
namespace ExactQuantumFactoring.BitStackProgram
open Turing.TM2 StateTransition

inductive Program (K : Type) where
  | skip
  | push (k : K) (b : Bool)
  | seq (p q : Program K)
  | cases (k : K) (nil ff tt : Program K)
  | loop (k : K) (ff tt : Program K)

def Node {K : Type} : Program K → Type
  | .skip | .push _ _ => Unit
  | .seq p q => Node p ⊕ Node q
  | .cases _ a b c => Unit ⊕ (Node a ⊕ (Node b ⊕ Node c))
  | .loop _ b c => Unit ⊕ (Node b ⊕ Node c)

noncomputable instance nodeFintype {K : Type} (p : Program K) : Fintype (Node p) := by
  induction p with
  | skip => exact inferInstanceAs (Fintype Unit)
  | push => exact inferInstanceAs (Fintype Unit)
  | seq p q hp hq => letI := hp; letI := hq; exact inferInstanceAs (Fintype (Node p ⊕ Node q))
  | cases k a b c ha hb hc =>
    letI := ha; letI := hb; letI := hc
    exact inferInstanceAs (Fintype (Unit ⊕ (Node a ⊕ (Node b ⊕ Node c))))
  | loop k b c hb hc =>
    letI := hb; letI := hc
    exact inferInstanceAs (Fintype (Unit ⊕ (Node b ⊕ Node c)))

def entry {K : Type} : (p : Program K) → Node p
  | .skip | .push _ _ => ()
  | .seq p _ => .inl (entry p)
  | .cases _ _ _ _ | .loop _ _ _ => .inl ()

abbrev Store (K : Type) := K → List Bool
abbrev Config (K Λ : Type) := Cfg (fun _ : K => Bool) Λ (Option Bool)
def configured {K Λ : Type} (l : Λ) (s : Store K) : Config K Λ := ⟨some l,none,s⟩
def jump {K Λ : Type} (l : Λ) : Stmt (fun _ : K => Bool) Λ (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => l))
def dispatch {K Λ : Type} (k : K) (nil ff tt : Λ) :
    Stmt (fun _ : K => Bool) Λ (Option Bool) :=
  .pop k (fun _ b => b) (.branch Option.isSome
    (.branch (fun b => b.getD false) (jump tt) (jump ff)) (jump nil))

def statement {K Λ : Type} : (p : Program K) → Λ → (Node p → Λ) → Node p →
    Stmt (fun _ : K => Bool) Λ (Option Bool)
  | .skip,e,_,_ => jump e
  | .push k b,e,_,_ => .push k (fun _ => b) (jump e)
  | .seq p q,_e,w,.inl i => statement p (w (.inr (entry q))) (w ∘ Sum.inl) i
  | .seq _ q,e,w,.inr i => statement q e (w ∘ Sum.inr) i
  | .cases k a b c,_,w,.inl _ => dispatch k
      (w (.inr (.inl (entry a)))) (w (.inr (.inr (.inl (entry b)))))
      (w (.inr (.inr (.inr (entry c)))))
  | .cases _ a _ _,e,w,.inr (.inl i) => statement a e (w ∘ Sum.inr ∘ Sum.inl) i
  | .cases _ _ b _,e,w,.inr (.inr (.inl i)) =>
      statement b e (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl) i
  | .cases _ _ _ c,e,w,.inr (.inr (.inr i)) =>
      statement c e (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr) i
  | .loop k b c,e,w,.inl _ => dispatch k e
      (w (.inr (.inl (entry b)))) (w (.inr (.inr (entry c))))
  | .loop _ b _,_,w,.inr (.inl i) =>
      statement b (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inl) i
  | .loop _ _ c,_,w,.inr (.inr i) =>
      statement c (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inr) i

inductive Runs {K : Type} [DecidableEq K] : Program K → Store K → Store K → ℕ → Prop
  | skip (s) : Runs .skip s s 1
  | push (s) (k) (b) : Runs (.push k b) s (Function.update s k (b :: s k)) 1
  | seq {p q s t u a b} : Runs p s t a → Runs q t u b → Runs (.seq p q) s u (b+a)
  | cases_nil {k p q r s t a} : s k=[] → Runs p s t a → Runs (.cases k p q r) s t (a+1)
  | cases_false {k p q r s t xs a} : s k=false::xs →
      Runs q (Function.update s k xs) t a → Runs (.cases k p q r) s t (a+1)
  | cases_true {k p q r s t xs a} : s k=true::xs →
      Runs r (Function.update s k xs) t a → Runs (.cases k p q r) s t (a+1)
  | loop_nil {k p q s} : s k=[] → Runs (.loop k p q) s s 1
  | loop_false {k p q s t u xs a b} : s k=false::xs →
      Runs p (Function.update s k xs) t a → Runs (.loop k p q) t u b →
      Runs (.loop k p q) s u (b+a+1)
  | loop_true {k p q s t u xs a b} : s k=true::xs →
      Runs q (Function.update s k xs) t a → Runs (.loop k p q) t u b →
      Runs (.loop k p q) s u (b+a+1)

lemma iterate_step {α : Type*} (f : α → Option α) (a b : α) (h : f a=some b) :
    (flip bind f)^[1] (some a) = some b := h
lemma iterate_comp {α : Type*} (f : α → Option α) (a b c : α) (k l : ℕ)
    (h : (flip bind f)^[k] (some a)=some b)
    (g : (flip bind f)^[l] (some b)=some c) :
    (flip bind f)^[l+k] (some a)=some c := by
  rw [Function.iterate_add_apply,h,g]

lemma dispatch_nil {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (hs : s k=[]) : stepAux (dispatch k a b c) none s = configured a s := by
  simp only [dispatch,stepAux,hs,List.head?_nil,List.tail_nil,Option.isSome_none,
    Bool.cond_false,jump]
  rw [← hs,Function.update_eq_self]
  rfl
lemma dispatch_false {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (xs : List Bool) (hs : s k=false::xs) :
    stepAux (dispatch k a b c) none s = configured b (Function.update s k xs) := by
  simp only [dispatch,stepAux,hs,List.head?_cons,List.tail_cons,Option.isSome_some,
    Bool.cond_true,Option.getD_some,Bool.cond_false,jump]
  rfl
lemma dispatch_true {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (xs : List Bool) (hs : s k=true::xs) :
    stepAux (dispatch k a b c) none s = configured c (Function.update s k xs) := by
  simp only [dispatch,stepAux,hs,List.head?_cons,List.tail_cons,Option.isSome_some,
    Bool.cond_true,Option.getD_some,jump]
  rfl

theorem compile_runs {K : Type} [DecidableEq K] {p : Program K}
    {s t : Store K} {c : ℕ} (h : Runs p s t c) :
    ∀ {Λ : Type} (e : Λ) (w : Node p → Λ)
      (M : Λ → Stmt (fun _ : K => Bool) Λ (Option Bool)),
      (∀ i, M (w i) = statement p e w i) →
      (flip bind (step M))^[c] (some (configured (w (entry p)) s)) = some (configured e t) := by
  induction h with
  | skip s =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w ())) none s) = _
    rw [hM ()]
    rfl
  | push s k b =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w ())) none s) = _
    rw [hM ()]
    rfl
  | @seq p q s t u a b hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (entry q))) t) _ a b
    · exact ihp _ _ M (fun i => hM (.inl i))
    · exact ihq _ _ M (fun i => hM (.inr i))
  | @cases_nil k p q r s t a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inl (entry p)))) s) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_nil _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inl i)))
  | @cases_false k p q r s t xs a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (.inl (entry q)))))
      (Function.update s k xs)) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_false _ _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inr (.inl i))))
  | @cases_true k p q r s t xs a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (.inr (entry r)))))
      (Function.update s k xs)) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_true _ _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inr (.inr i))))
  | @loop_nil k p q s hs =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w (.inl ()))) none s) = _
    rw [hM (.inl ()),statement,dispatch_nil _ _ _ _ _ hs]
  | @loop_false k p q s t u xs a b hs hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inl (entry p))))
      (Function.update s k xs)) _ 1 (b+a)
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_false _ _ _ _ _ _ hs]
    · apply iterate_comp (step M) _ (configured (w (.inl ())) t) _ a b
      · exact ihp _ _ M (fun i => hM (.inr (.inl i)))
      · exact ihq _ _ M hM
  | @loop_true k p q s t u xs a b hs hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (entry q))))
      (Function.update s k xs)) _ 1 (b+a)
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_true _ _ _ _ _ _ hs]
    · apply iterate_comp (step M) _ (configured (w (.inl ())) t) _ a b
      · exact ihp _ _ M (fun i => hM (.inr (.inr i)))
      · exact ihq _ _ M hM

noncomputable def machine {K : Type} [Fintype K] [DecidableEq K] (input output : K) (p : Program K) :
    Turing.FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := Option (Node p)
  main := some (entry p)
  σ := Option Bool
  initialState := none
  m
    | none => .halt
    | some i => statement p none some i

lemma machine_alphabets_finite {K : Type} [Fintype K] [DecidableEq K]
    (input output : K) (p : Program K) : ∀ k, Finite ((machine input output p).Γ k) :=
  fun _ => (inferInstance : Finite Bool)

def singletonStore {K : Type} [DecidableEq K] (k : K) (v : List Bool) : Store K :=
  Function.update (fun _ => []) k v

noncomputable def machine_outputs {K : Type} [Fintype K] [DecidableEq K]
    (input output : K) (p : Program K) (s t : List Bool) (c : ℕ)
    (h : Runs p (singletonStore input s) (singletonStore output t) c) :
    Turing.TM2OutputsInTime (machine input output p) s (some t) (c+1) := by
  let tm := machine input output p
  have hi : Turing.initList tm s = configured (some (entry p)) (singletonStore input s) := by
    change Turing.initList (machine input output p) s = _
    unfold machine Turing.initList configured singletonStore
    congr 1
    funext k
    by_cases hk : k=input
    · subst k; simp
    · simp [hk,Function.update]
  have hf : Turing.haltList tm t =
      (⟨none,none,singletonStore output t⟩ : Config K (Option (Node p))) := by
    change Turing.haltList (machine input output p) t = _
    unfold machine Turing.haltList singletonStore
    congr 1
    funext k
    by_cases hk : k=output
    · subst k; simp
    · simp [hk,Function.update]
  have hr := compile_runs h (none : Option (Node p)) some tm.m (fun _ => rfl)
  refine ⟨⟨c+1,?_⟩,le_rfl⟩
  change (flip bind (step tm.m))^[c+1] (some (Turing.initList tm s)) =
    some (Turing.haltList tm t)
  rw [hi,hf]
  have hend : step tm.m (configured (none : Option (Node p)) (singletonStore output t)) =
      some (⟨none,none,singletonStore output t⟩ : Config K (Option (Node p))) := rfl
  rw [Nat.add_comm c 1]
  exact iterate_comp (step tm.m) _ _ _ c 1 hr (iterate_step _ _ _ hend)
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackRelabel.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

variable {K L : Type}
def Program.relabel (f : K → L) : Program K → Program L
  | .skip => .skip
  | .push k b => .push (f k) b
  | .seq p q => .seq (p.relabel f) (q.relabel f)
  | .cases k p q r => .cases (f k) (p.relabel f) (q.relabel f) (r.relabel f)
  | .loop k p q => .loop (f k) (p.relabel f) (q.relabel f)

/-- An extension of a small register store with arbitrary untouched registers. -/
noncomputable def overlay (f : K ↪ L) (base : Store L) (s : Store K) : Store L := by
  classical
  exact fun j => if h : ∃ i, f i=j then s (Classical.choose h) else base j

lemma overlay_at (f : K ↪ L) (base : Store L) (s : Store K) (i : K) :
    overlay f base s (f i)=s i := by
  classical
  unfold overlay
  rw [dite_eq_left ⟨i,rfl⟩]
  congr 1
  apply f.injective
  exact Classical.choose_spec (show ∃ k, f k=f i from ⟨i,rfl⟩)

lemma overlay_outside (f : K ↪ L) (base : Store L) (s : Store K) (j : L)
    (h : ∀ i, f i≠j) : overlay f base s j=base j := by
  classical
  unfold overlay
  exact dite_eq_right (by simpa only [not_exists] using h)

variable [DecidableEq K] [DecidableEq L]

lemma overlay_update (f : K ↪ L) (base : Store L) (s : Store K) (k : K) (xs : List Bool) :
    overlay f base (Function.update s k xs)=Function.update (overlay f base s) (f k) xs := by
  funext j
  by_cases hj : ∃ i,f i=j
  · rcases hj with ⟨i,rfl⟩
    rw [overlay_at]
    by_cases h : i=k
    · subst i; simp
    · have hf : f i≠f k := fun h' => h (f.injective h')
      simp only [Function.update_of_ne h,Function.update_of_ne hf,overlay_at]
  · have h : ∀ i,f i≠j := by simpa only [not_exists] using hj
    rw [overlay_outside f base _ j h,Function.update_of_ne (Ne.symm (h k)),
      overlay_outside f base s j h]

omit [DecidableEq K] [DecidableEq L] in
lemma overlay_self (f : K ↪ L) (s : Store L) : overlay f s (s ∘ f)=s := by
  funext j
  by_cases h : ∃ i,f i=j
  · rcases h with ⟨i,rfl⟩
    exact overlay_at f s (s ∘ f) i
  · exact overlay_outside f s (s ∘ f) j (by simpa only [not_exists] using h)

/-- Exact-cost subroutine embedding. Scratch separation is proved, not assumed
as an extra TM operation. -/
lemma Runs.relabel {p : Program K} {s t : Store K} {c : ℕ}
    (h : Runs p s t c) (f : K ↪ L) (base : Store L) :
    Runs (p.relabel f) (overlay f base s) (overlay f base t) c := by
  induction h with
  | skip s => exact Runs.skip _
  | push s k b =>
    rw [overlay_update]
    simpa only [overlay_at, Program.relabel] using Runs.push (overlay f base s) (f k) b
  | seq hp hq ip iq => exact Runs.seq ip iq
  | @cases_nil k p q r s t a hs hr ih =>
    exact Runs.cases_nil (by rw [overlay_at,hs]) ih
  | @cases_false k p q r s t xs a hs hr ih =>
    rw [overlay_update] at ih
    exact Runs.cases_false (by rw [overlay_at,hs]) ih
  | @cases_true k p q r s t xs a hs hr ih =>
    rw [overlay_update] at ih
    exact Runs.cases_true (by rw [overlay_at,hs]) ih
  | @loop_nil k p q s hs => exact Runs.loop_nil (by rw [overlay_at,hs])
  | @loop_false k p q s t u xs a b hs hp hq ip iq =>
    rw [overlay_update] at ip
    exact Runs.loop_false (by rw [overlay_at,hs]) ip iq
  | @loop_true k p q s t u xs a b hs hp hq ip iq =>
    rw [overlay_update] at ip
    exact Runs.loop_true (by rw [overlay_at,hs]) ip iq
end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackLists.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]

/-- Reverse one stack onto another, preserving all symbols. -/
def reverseMove (a b : K) : Program K := .loop a (.push b false) (.push b true)
def clear (a : K) : Program K := .loop a .skip .skip

def duplicateReverse (a b t : K) : Program K :=
  .seq (.loop a (.seq (.push b false) (.push t false))
    (.seq (.push b true) (.push t true))) (reverseMove t a)

lemma update_comm (s : Store K) (a b : K) (x y : List Bool) (hab : a≠b) :
    Function.update (Function.update s a x) b y =
      Function.update (Function.update s b y) a x := by
  funext k
  by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all [Function.update]

lemma clear_runs (a : K) (s : Store K) :
    Runs (clear a) s (Function.update s a []) (2*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update s a []=s := by rw [←hs,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    have ht : Function.update s a xs a=xs := by simp
    have hh := ih (Function.update s a xs) ht
    cases x
    · have hr := Runs.loop_false hs (Runs.skip (Function.update s a xs)) hh
      convert hr using 1 <;> first | rfl | simp only [Function.update_idem]
    · have hr := Runs.loop_true hs (Runs.skip (Function.update s a xs)) hh
      convert hr using 1 <;> first | rfl | simp only [Function.update_idem]

lemma reverseMove_runs (a b : K) (hab : a≠b) (s : Store K) :
    Runs (reverseMove a b) s
      (Function.update (Function.update s a []) b ((s a).reverse++s b))
      (2*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update s a []) b ([].reverse++s b)=s := by
      rw [List.reverse_nil,List.nil_append,←hs,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let t := Function.update s a xs
    let u := Function.update t b (x::t b)
    have hua : u a=xs := by simp [u,t,hab]
    have htail := ih u hua
    have body : Runs (.push b x) t u 1 := Runs.push _ _ _
    have hr : Runs (reverseMove a b) s
        (Function.update (Function.update u a []) b (xs.reverse++u b)) (2*xs.length+1+1+1) := by
      cases x
      · exact Runs.loop_false (a:=1) (b:=2*xs.length+1) hs body htail
      · exact Runs.loop_true (a:=1) (b:=2*xs.length+1) hs body htail
    convert hr using 1 <;> try (simp only [List.length_cons, List.length_nil] <;> omega)
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;>
      simp_all [u,t,Function.update,List.reverse_cons,List.append_assoc]

lemma duplicateReverse_loop_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) :
    Runs (.loop a (.seq (.push b false) (.push t false))
      (.seq (.push b true) (.push t true))) s
      (Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
        t ((s a).reverse++s t)) (3*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update (Function.update s a []) b ([].reverse++s b))
        t ([].reverse++s t)=s := by
      rw [List.reverse_nil,List.nil_append,List.nil_append,←hs,Function.update_eq_self,
        Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let u := Function.update s a xs
    let w := Function.update u b (x::u b)
    let v := Function.update w t (x::w t)
    have hva : v a=xs := by simp [v,w,u,hab,hat]
    have htail := ih v hva
    have body : Runs (.seq (.push b x) (.push t x)) u v 2 :=
      Runs.seq (Runs.push _ _ _) (Runs.push _ _ _)
    have hr : Runs (.loop a (.seq (.push b false) (.push t false))
      (.seq (.push b true) (.push t true))) s
      (Function.update (Function.update (Function.update v a []) b (xs.reverse++v b))
        t (xs.reverse++v t)) (3*xs.length+1+2+1) := by
      cases x
      · exact Runs.loop_false (a:=2) (b:=3*xs.length+1) hs body htail
      · exact Runs.loop_true (a:=2) (b:=3*xs.length+1) hs body htail
    convert hr using 1 <;> try (simp only [List.length_cons, List.length_nil] <;> omega)
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht : k=t <;>
      simp_all [v,w,u,Function.update,List.reverse_cons,List.append_assoc]

lemma duplicateReverse_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) (ht : s t=[]) :
    Runs (duplicateReverse a b t) s (Function.update s b ((s a).reverse++s b))
      (5*(s a).length+2) := by
  let v := Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
    t ((s a).reverse++s t)
  have hr := reverseMove_runs t a hat.symm v
  have hh := Runs.seq (duplicateReverse_loop_runs a b t hab hat hbt s) hr
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht' : k=t <;>
      simp_all [v,Function.update]
  · simp only [v,Function.update_self,ht,List.append_nil,List.length_reverse]; omega

end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackProcedures.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]

lemma Runs.length_le {p : Program K} {s t : Store K} {c : ℕ} (h : Runs p s t c) (k : K) :
    (t k).length ≤ (s k).length+c := by
  induction h with
  | skip s => omega
  | push s a b =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self,List.length_cons]; omega
    · simp only [Function.update_of_ne hk]; omega
  | seq hp hq ip iq => omega
  | cases_nil hs hr ih => omega
  | @cases_false a p q r s t xs c hs hr ih =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ih; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ih; omega
  | @cases_true a p q r s t xs c hs hr ih =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ih; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ih; omega
  | loop_nil hs => omega
  | @loop_false a p q s t u xs c d hs hp hq ip iq =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ip; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ip; omega
  | @loop_true a p q s t u xs c d hs hp hq ip iq =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ip; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ip; omega

/-- A completely explicit finite-state Boolean-stack subroutine, with the
same clean input/output convention as the frozen TM2 uniformity target. -/
structure Procedure {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  K : Type
  finiteK : Fintype K
  decideK : DecidableEq K
  input : K
  output : K
  program : Program K
  bound : Polynomial ℕ
  runs : ∀ a, ∃ c, c ≤ bound.eval (ea a).length ∧
    @Runs K decideK program (@singletonStore K decideK input (ea a)) (@singletonStore K decideK output (eb (f a))) c

attribute [instance] Procedure.finiteK Procedure.decideK
namespace Procedure
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

lemma output_length_le (p : Procedure ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length+p.bound.eval (ea a).length := by
  obtain ⟨c,hc,hr⟩ := p.runs a
  have h := hr.length_le p.output
  simp only [singletonStore,Function.update_self] at h
  by_cases he : p.output=p.input
  · simp only [he,Function.update_self] at h; omega
  · simp only [Function.update_of_ne he,List.length_nil,Nat.zero_add] at h; omega

noncomputable def toTM2 (p : Procedure ea eb f) : Turing.TM2ComputableInPolyTime ea eb f where
  tm := machine p.input p.output p.program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := p.bound+1
  outputsFun a := by
    classical
    let c := Classical.choose (p.runs a)
    have hc := (Classical.choose_spec (p.runs a)).1
    have hr := (Classical.choose_spec (p.runs a)).2
    have h := machine_outputs p.input p.output p.program (ea a) (eb (f a)) c hr
    have ht : Turing.TM2OutputsInTime (machine p.input p.output p.program)
        (ea a) (some (eb (f a))) (p.bound.eval (ea a).length+1) :=
      ⟨h.1, h.2.trans (Nat.add_le_add_right hc 1)⟩
    convert ht using 1
    simp only [Polynomial.eval_add,Polynomial.eval_one]
    congr 1
    · exact List.map_id _
    · congr 1
      exact List.map_id _

lemma toTM2_finite (p : Procedure ea eb f) : ∀ k, Finite (p.toTM2.tm.Γ k) :=
  machine_alphabets_finite _ _ _
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackComposition.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K L : Type} [DecidableEq K] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
lemma overlay_empty (f : K ↪ L) : overlay f (fun _=>[]) (fun _=>[])=fun _=>[] := by
  funext j
  by_cases h : ∃ i,f i=j
  · rcases h with ⟨i,rfl⟩; exact overlay_at f _ _ i
  · exact overlay_outside f _ _ j (by simpa only [not_exists] using h)
lemma overlay_singleton (f : K ↪ L) (k : K) (xs : List Bool) :
    overlay f (fun _=>[]) (singletonStore k xs)=singletonStore (f k) xs := by
  rw [singletonStore,overlay_update,overlay_empty]
  rfl

/-- Move an entire word without reversing its order. Each symbol is pushed
and popped twice; this is not an atomic bulk-copy instruction. -/
def moveWord (a b t : K) : Program K := .seq (reverseMove a t) (reverseMove t b)
lemma moveWord_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t) (xs : List Bool) :
    Runs (moveWord a b t) (singletonStore a xs) (singletonStore b xs) (4*xs.length+2) := by
  let s := singletonStore a xs
  let u := Function.update (Function.update s a []) t ((s a).reverse++s t)
  have hh := Runs.seq (reverseMove_runs a t hat s) (reverseMove_runs t b hbt.symm u)
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht : k=t <;>
      simp_all [u,s,singletonStore,Function.update,Ne.symm hat,Ne.symm hab,Ne.symm hbt]
  · simp only [u,Function.update_self,s,singletonStore,Function.update_self]
    simp only [Function.update_of_ne hat.symm,List.append_nil,List.length_reverse]
    omega

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
  {f : α→β} {g : β→γ}

def joinLeft (A B : Type) : A ↪ A ⊕ (B ⊕ Unit) := ⟨Sum.inl,Sum.inl_injective⟩
def joinRight (A B : Type) : B ↪ A ⊕ (B ⊕ Unit) :=
  ⟨Sum.inr ∘ Sum.inl,Sum.inr_injective.comp Sum.inl_injective⟩

lemma eval_nat_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

/-- Checked composition for actual finite Boolean-stack procedures. This
constructs the combined program and accounts for the intermediate-word copy;
it does NOT invoke Mathlib's unproved TM2 polytime-composition declaration. -/
noncomputable def comp (q : Procedure eb ec g) (p : Procedure ea eb f) :
    Procedure ea ec (g ∘ f) where
  K := p.K ⊕ (q.K ⊕ Unit)
  finiteK := inferInstance
  decideK := inferInstance
  input := Sum.inl p.input
  output := Sum.inr (Sum.inl q.output)
  program := .seq (p.program.relabel (joinLeft p.K q.K))
    (.seq (moveWord (Sum.inl p.output) (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ())))
      (q.program.relabel (joinRight p.K q.K)))
  bound := p.bound+(Polynomial.C 4*(Polynomial.X+p.bound)+Polynomial.C 2)+
    q.bound.comp (Polynomial.X+p.bound)
  runs a := by
    obtain ⟨cp,hcp,hp⟩ := p.runs a
    obtain ⟨cq,hcq,hq⟩ := q.runs (f a)
    have hleft := hp.relabel (joinLeft p.K q.K) (fun _=>[])
    have hright := hq.relabel (joinRight p.K q.K) (fun _=>[])
    simp only [overlay_singleton] at hleft hright
    have hmove := moveWord_runs (K:=p.K ⊕ (q.K ⊕ Unit)) (Sum.inl p.output)
      (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ()))
      (by simp) (by simp) (by simp) (eb (f a))
    refine ⟨cq+(4*(eb (f a)).length+2)+cp,?_,Runs.seq hleft (Runs.seq hmove hright)⟩
    have hlen := p.output_length_le a
    have hmono := eval_nat_mono q.bound hlen
    dsimp only at hmono
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp]
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackQuotation.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

/-- Prefix-free quoting for one Boolean word. Both constructor tags and payload
bits are literal stack symbols. It is used only by the classical generator. -/
def quoteBits (xs : List Bool) : List Bool :=
  xs.flatMap (fun b=>[true,b]) ++ [false]
@[simp] lemma quoteBits_nil : quoteBits []=[false] := rfl
@[simp] lemma quoteBits_cons (b : Bool) (xs : List Bool) :
    quoteBits (b::xs)=true::b::quoteBits xs := rfl
lemma quoteBits_length (xs : List Bool) : (quoteBits xs).length=2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [quoteBits_cons,List.length_cons,ih]; omega

def pairBits (xs ys : List Bool) : List Bool := quoteBits xs++ys
lemma pairBits_length (xs ys : List Bool) :
    (pairBits xs ys).length=2*xs.length+ys.length+1 := by
  simp only [pairBits,List.length_append,quoteBits_length]; omega

variable {K : Type} [DecidableEq K]
def quoteLoop (a t : K) : Program K :=
  .loop a (.seq (.push t true) (.push t false)) (.seq (.push t true) (.push t true))
def quoteMove (a b t : K) : Program K :=
  .seq (quoteLoop a t) (.seq (.push t false) (reverseMove t b))

lemma quoteLoop_runs (a t : K) (hat : a≠t) (s : Store K) :
    Runs (quoteLoop a t) s
      (Function.update (Function.update s a []) t
        (((s a).flatMap (fun b=>[true,b])).reverse++s t)) (3*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have h : Function.update (Function.update s a []) t
        (([].flatMap (fun b=>[true,b])).reverse++s t)=s := by
      simp only [List.flatMap_nil,List.reverse_nil,List.nil_append]
      rw [←hs,Function.update_eq_self,Function.update_eq_self]
    rw [h]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let u := Function.update s a xs
    let v := Function.update u t (x::true::u t)
    have hva : v a=xs := by simp [v,u,hat]
    have hb : Runs (.seq (.push t true) (.push t x)) u v 2 := by
      have hh := Runs.seq (Runs.push u t true)
        (Runs.push (Function.update u t (true::u t)) t x)
      simpa only [Function.update_self,Function.update_idem] using hh
    have hh : Runs (quoteLoop a t) s
        (Function.update (Function.update v a []) t
          ((xs.flatMap (fun b=>[true,b])).reverse++v t)) (3*xs.length+1+2+1) := by
      cases x
      · exact Runs.loop_false (a:=2) (b:=3*xs.length+1) hs hb (ih v hva)
      · exact Runs.loop_true (a:=2) (b:=3*xs.length+1) hs hb (ih v hva)
    convert hh using 1 <;> try (simp only [List.length_cons, List.length_nil] <;> omega)
    · funext k
      by_cases ha : k=a <;> by_cases ht : k=t <;>
        simp_all [v,u,Function.update,List.reverse_cons,List.append_assoc]

lemma quoteMove_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) (ht : s t=[]) :
    Runs (quoteMove a b t) s
      (Function.update (Function.update s a []) b (quoteBits (s a)++s b))
      (7*(s a).length+5) := by
  let u := Function.update (Function.update s a []) t
    (((s a).flatMap (fun b=>[true,b])).reverse++s t)
  let v := Function.update u t (false::u t)
  have hh := Runs.seq (quoteLoop_runs a t hat s)
    (Runs.seq (Runs.push u t false) (reverseMove_runs t b hbt.symm v))
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht' : k=t <;>
      simp_all [u,v,Function.update,quoteBits,Ne.symm hat,Ne.symm hab,Ne.symm hbt]
  · simp only [v,Function.update_self,u,Function.update_self,ht,List.append_nil,
      List.length_cons,List.length_reverse]
    have hl : ((s a).flatMap (fun b=>[true,b])).length=2*(s a).length := by
      have h:=quoteBits_length (s a)
      simp only [quoteBits,List.length_append,List.length_cons,List.length_nil] at h
      omega
    rw [hl]; omega

def unquoteBody (a t c : K) : Program K :=
  .cases a .skip .skip
    (.cases a .skip (.seq (.push t false) (.push c true))
      (.seq (.push t true) (.push c true)))
def unquoteLoop (a t c : K) : Program K :=
  .loop c (unquoteBody a t c) (unquoteBody a t c)
def unquoteMove (a b t c : K) : Program K :=
  .seq (.push c true) (.seq (unquoteLoop a t c) (reverseMove t b))

lemma unquoteLoop_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (xs ys : List Bool) (s : Store K) (ha : s a=quoteBits xs++ys) (hc : s c=[true]) :
    Runs (unquoteLoop a t c) s
      (Function.update (Function.update (Function.update s a ys) c []) t (xs.reverse++s t))
      (5*xs.length+4) := by
  induction xs generalizing s with
  | nil =>
    let u := Function.update s c []
    let v := Function.update u a ys
    have hua : u a=false::ys := by simp [u,hac,ha]
    have hvc : v c=[] := by simp [v,u,hac.symm]
    have hb : Runs (unquoteBody a t c) u v 2 := Runs.cases_false hua (Runs.skip v)
    have hh := Runs.loop_true (p:=unquoteBody a t c) hc hb (Runs.loop_nil hvc)
    change Runs (.loop _ _ _) _ _ _
    convert hh using 1 <;> try (simp only [List.length_cons, List.length_nil] <;> omega)
    · funext k
      by_cases ha' : k=a <;> by_cases hc' : k=c <;> by_cases ht' : k=t <;>
        simp_all [v,u,Function.update,Ne.symm hat,Ne.symm hac,Ne.symm htc]
  | cons x xs ih =>
    let u := Function.update s c []
    let v := Function.update u a (x::quoteBits xs++ys)
    let w := Function.update v a (quoteBits xs++ys)
    let z := Function.update (Function.update w t (x::w t)) c [true]
    have hua : u a=true::x::quoteBits xs++ys := by simp [u,hac,ha]
    have hva : v a=x::quoteBits xs++ys := by simp [v]
    have hzc : z c=[true] := by simp [z]
    have hza : z a=quoteBits xs++ys := by simp [z,w,v,hat,hac]
    have hb : Runs (unquoteBody a t c) u z 4 := by
      apply Runs.cases_true hua
      have hh := Runs.seq (Runs.push w t x)
        (Runs.push (Function.update w t (x::w t)) c true)
      have hc0 : Function.update w t (x::w t) c=[] := by simp [w,v,u,htc.symm,hac.symm]
      rw [hc0] at hh
      cases x
      · exact Runs.cases_false hva hh
      · exact Runs.cases_true hva hh
    have hh := Runs.loop_true hc hb (ih z hza hzc)
    change Runs (.loop _ _ _) _ _ _
    convert hh using 1 <;> try (simp only [List.length_cons, List.length_nil] <;> omega)
    · funext k
      by_cases ha' : k=a <;> by_cases hc' : k=c <;> by_cases ht' : k=t <;>
        simp_all [z,w,v,u,Function.update,Ne.symm hat,Ne.symm hac,Ne.symm htc,
          List.reverse_cons,List.append_assoc]

lemma unquoteMove_runs (a b t c : K) (hab : a≠b) (hat : a≠t) (hac : a≠c)
    (hbt : b≠t) (hbc : b≠c) (htc : t≠c)
    (xs ys : List Bool) (s : Store K) (ha : s a=quoteBits xs++ys)
    (ht : s t=[]) (hc : s c=[]) :
    Runs (unquoteMove a b t c) s
      (Function.update (Function.update s a ys) b (xs++s b)) (7*xs.length+6) := by
  let u := Function.update s c [true]
  let v := Function.update (Function.update (Function.update u a ys) c []) t (xs.reverse++u t)
  have hua : u a=quoteBits xs++ys := by simp [u,hac,ha]
  have huc : u c=[true] := by simp [u]
  have hp : Runs (.push c true) s u 1 := by simpa only [hc] using Runs.push s c true
  have hh := Runs.seq hp (Runs.seq (unquoteLoop_runs a t c hat hac htc xs ys u hua huc)
    (reverseMove_runs t b hbt.symm v))
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha' : k=a <;> by_cases hb' : k=b <;> by_cases ht' : k=t <;> by_cases hc' : k=c <;>
      simp_all [v,u,Function.update,Ne.symm hab,Ne.symm hat,Ne.symm hac,Ne.symm hbt,
        Ne.symm hbc,Ne.symm htc]
  · simp only [v,Function.update_self,u,Function.update_of_ne htc,ht,List.append_nil,
      List.length_reverse]; omega
end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackFrames.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K L : Type}
def sumStore (s : Store K) (t : Store L) : Store (K ⊕ L) := Sum.elim s t
@[simp] lemma sumStore_left (s : Store K) (t : Store L) (k : K) :
    sumStore s t (Sum.inl k)=s k := rfl
@[simp] lemma sumStore_right (s : Store K) (t : Store L) (l : L) :
    sumStore s t (Sum.inr l)=t l := rfl
lemma sumStore_empty : sumStore (fun _ : K=>[]) (fun _ : L=>[])=fun _=>[] := by
  funext j; cases j <;> rfl

def leftEmbed (K L : Type) : K ↪ K ⊕ L := ⟨Sum.inl,Sum.inl_injective⟩
lemma overlay_left (s : Store K) (t : Store L) :
    overlay (leftEmbed K L) (sumStore (fun _=>[]) t) s=sumStore s t := by
  funext j
  cases j with
  | inl j => exact overlay_at _ _ _ j
  | inr j => exact overlay_outside _ _ _ _ (by intro i; simp [leftEmbed])

variable [DecidableEq K] [DecidableEq L]
@[simp] lemma sumStore_update_left (s : Store K) (t : Store L) (k : K) (xs : List Bool) :
    Function.update (sumStore s t) (Sum.inl k) xs=sumStore (Function.update s k xs) t := by
  funext j; cases j <;> simp [Function.update,sumStore]
@[simp] lemma sumStore_update_right (s : Store K) (t : Store L) (k : L) (xs : List Bool) :
    Function.update (sumStore s t) (Sum.inr k) xs=sumStore s (Function.update t k xs) := by
  funext j; cases j <;> simp [Function.update,sumStore]
lemma sumStore_singleton_left (k : K) (xs : List Bool) :
    singletonStore (Sum.inl k) xs=sumStore (singletonStore k xs) (fun _ : L=>[]) := by
  rw [singletonStore,←sumStore_empty,sumStore_update_left]; rfl
lemma sumStore_singleton_right (k : L) (xs : List Bool) :
    singletonStore (Sum.inr k) xs=sumStore (fun _ : K=>[]) (singletonStore k xs) := by
  rw [singletonStore,←sumStore_empty,sumStore_update_right]; rfl
lemma Runs.left {p : Program K} {s u : Store K} {c : ℕ} (h : Runs p s u c) (t : Store L) :
    Runs (p.relabel Sum.inl) (sumStore s t) (sumStore u t) c := by
  have hh := h.relabel (leftEmbed K L) (sumStore (fun _=>[]) t)
  rw [overlay_left,overlay_left] at hh
  exact hh

namespace Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f g : α→β}
def congrFun (p : Procedure ea eb f) (h : ∀ a,f a=g a) : Procedure ea eb g where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [h a] using p.runs a

noncomputable def identity (ea : α→List Bool) : Procedure ea ea id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.skip
  bound:=1
  runs a:=⟨1,by simp,Runs.skip _⟩
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackProducts.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def prodCode {α β : Type} (ea : α→List Bool) (eb : β→List Bool) (x : α×β) : List Bool :=
  pairBits (ea x.1) (eb x.2)

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool} {f : α→β}

/-- Run a procedure on the first component, keeping the second component
literally on a disjoint stack. Parsing and re-quoting are explicitly charged. -/
noncomputable def left (p : Procedure ea eb f) (ec : γ→List Bool) :
    Procedure (prodCode ea ec) (prodCode eb ec) (fun x=>(f x.1,x.2)) where
  K:=p.K ⊕ Fin 3
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (unquoteMove (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1) (Sum.inr 2))
    (.seq (p.program.relabel Sum.inl)
      (quoteMove (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 14*Polynomial.X+Polynomial.C 8*p.bound+Polynomial.C 11
  runs x:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs x.1
    let s : Store (p.K ⊕ Fin 3):=singletonStore (Sum.inr 0) (prodCode ea ec x)
    let u : Store (p.K ⊕ Fin 3):=sumStore (singletonStore p.input (ea x.1))
      (singletonStore 0 (ec x.2))
    let v : Store (p.K ⊕ Fin 3):=sumStore (singletonStore p.output (eb (f x.1)))
      (singletonStore 0 (ec x.2))
    have hparse : Runs (unquoteMove (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1) (Sum.inr 2))
        s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (Sum.inr 0 : p.K ⊕ Fin 3) (Sum.inl p.input)
        (Sum.inr 1) (Sum.inr 2) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (ea x.1) (ec x.2) s (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      funext k
      cases k with
      | inl k => by_cases hk : k=p.input <;> simp_all [s,u,singletonStore,sumStore,Function.update]
      | inr k => fin_cases k <;> simp [s,u,singletonStore,sumStore,Function.update]
    have hcall : Runs (p.program.relabel Sum.inl) u v cp := hp.left (singletonStore (0 : Fin 3) (ec x.2))
    have hquote : Runs (quoteMove (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)) v
        (singletonStore (Sum.inr 0) (pairBits (eb (f x.1)) (ec x.2)))
        (7*(eb (f x.1)).length+5) := by
      have hh:=quoteMove_runs (Sum.inl p.output : p.K ⊕ Fin 3)
        (Sum.inr 0) (Sum.inr 1) (by simp) (by simp) (by simp) v (by simp [v,singletonStore])
      convert hh using 1
      · funext k
        cases k with
        | inl k => by_cases hk : k=p.output <;>
            simp_all [v,singletonStore,sumStore,Function.update]
        | inr k => fin_cases k <;> simp [v,singletonStore,sumStore,Function.update,pairBits]
      · simp [v,singletonStore]
    refine ⟨(7*(eb (f x.1)).length+5)+cp+(7*(ea x.1).length+6),?_,
      Runs.seq hparse (Runs.seq hcall hquote)⟩
    have hlen:=p.output_length_le x.1
    have hx : (ea x.1).length≤(prodCode ea ec x).length := by
      simp only [prodCode,pairBits_length]; omega
    have hm:=eval_nat_mono p.bound hx
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

/-- Exchange two quoted word fields, without a unit-cost tuple operation. -/
noncomputable def swap (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) (prodCode eb ea) Prod.swap where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.seq (unquoteMove 0 1 2 3) (quoteMove 0 1 2)
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 11
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode ea eb x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 (eb x.2)) 1 (ea x.1)
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (ea x.1) (eb x.2) s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      funext k; fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (quoteMove 0 1 2) u (singletonStore 1 (prodCode eb ea x.swap))
        (7*(eb x.2).length+5) := by
      have hh:=quoteMove_runs (0 : Fin 4) 1 2 (by decide) (by decide) (by decide) u
        (by simp [u,singletonStore])
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,singletonStore,Function.update,prodCode,pairBits]
      · simp [u,singletonStore]
    refine ⟨(7*(eb x.2).length+5)+(7*(ea x.1).length+6),?_,Runs.seq h1 h2⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length]
    omega

/-- Two arbitrary already verified subroutines acting independently on a pair. -/
noncomputable def parallel {δ : Type} {ed : δ→List Bool} {g : γ→δ}
    (p : Procedure ea eb f) (q : Procedure ec ed g) :
    Procedure (prodCode ea ec) (prodCode eb ed) (fun x=>(f x.1,g x.2)) :=
  (((swap ed eb).comp ((q.left eb).comp ((swap eb ec).comp (p.left ec)))).congrFun
    (by intro x; rfl))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackBasicProcedures.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
  {f : α→β} {g : α→γ}

/-- Duplicate the input word and quote the first copy to represent a pair. -/
noncomputable def duplicate (ea : α→List Bool) :
    Procedure ea (prodCode ea ea) (fun a=>(a,a)) where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=3
  program:=.seq (duplicateReverse 0 1 2) (.seq (reverseMove 1 3) (quoteMove 0 3 1))
  bound:=Polynomial.C 14*Polynomial.X+Polynomial.C 8
  runs a:=by
    let s : Store (Fin 4):=singletonStore 0 (ea a)
    let u : Store (Fin 4):=Function.update s 1 (ea a).reverse
    let v : Store (Fin 4):=Function.update s 3 (ea a)
    have h1 : Runs (duplicateReverse 0 1 2) s u (5*(ea a).length+2) := by
      have hh:=duplicateReverse_runs (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
        s (by simp [s,singletonStore])
      simpa only [u,s,singletonStore,Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 4)≠0),List.append_nil] using hh
    have h2 : Runs (reverseMove 1 3) u v (2*(ea a).length+1) := by
      have hh:=reverseMove_runs (1 : Fin 4) 3 (by decide) u
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,v,s,singletonStore,Function.update]
      · simp [u]
    have h3 : Runs (quoteMove 0 3 1) v
        (singletonStore 3 (prodCode ea ea (a,a))) (7*(ea a).length+5) := by
      have hh:=quoteMove_runs (0 : Fin 4) 3 1 (by decide) (by decide) (by decide) v
        (by simp [v,s,singletonStore])
      convert hh using 1
      · funext k; fin_cases k <;> simp [v,s,singletonStore,Function.update,prodCode,pairBits]
      · simp [v,s,singletonStore]
    refine ⟨(7*(ea a).length+5)+(2*(ea a).length+1)+(5*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

noncomputable def pair (p : Procedure ea eb f) (q : Procedure ea ec g) :
    Procedure ea (prodCode eb ec) (fun a=>(f a,g a)) :=
  (p.parallel q).comp (duplicate ea)

/-- Projection parses the actual prefix code and explicitly clears its tail. -/
noncomputable def first (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) ea Prod.fst where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.seq (unquoteMove 0 1 2 3) (clear 0)
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 7
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode ea eb x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 (eb x.2)) 1 (ea x.1)
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (ea x.1) (eb x.2) s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      funext k; fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (clear 0) u (singletonStore 1 (ea x.1)) (2*(eb x.2).length+1) := by
      have hh:=clear_runs (0 : Fin 4) u
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,singletonStore,Function.update]
      · simp [u,singletonStore]
    refine ⟨(2*(eb x.2).length+1)+(7*(ea x.1).length+6),?_,Runs.seq h1 h2⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length]
    omega

noncomputable def second (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) eb Prod.snd :=
  ((first eb ea).comp (swap ea eb)).congrFun (by intro x; rfl)

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackConstants.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]
/-- A fixed finite list is part of the program, not a run-time oracle. -/
def pushWord (k : K) : List Bool→Program K
  | []=>.skip
  | b::bs=>.seq (pushWord k bs) (.push k b)
lemma pushWord_runs (k : K) (xs : List Bool) (s : Store K) :
    Runs (pushWord k xs) s (Function.update s k (xs++s k)) (xs.length+1) := by
  induction xs with
  | nil=>simpa [pushWord] using Runs.skip s
  | cons b bs ih=>
    have hh:=Runs.seq ih (Runs.push (Function.update s k (bs++s k)) k b)
    simpa only [pushWord,Function.update_self,Function.update_idem,List.cons_append,
      List.length_cons,Nat.add_comm] using hh
namespace Procedure
variable {α β : Type} (ea : α→List Bool) (eb : β→List Bool)
noncomputable def constant (b : β) : Procedure ea eb (fun _=>b) where
  K:=Fin 1
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=.seq (clear 0) (pushWord 0 (eb b))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C ((eb b).length+2)
  runs a:=by
    let s : Store (Fin 1):=singletonStore 0 (ea a)
    let u : Store (Fin 1):=Function.update s 0 []
    have hc:=clear_runs (0 : Fin 1) s
    have hp:=pushWord_runs (0 : Fin 1) (eb b) u
    have hh:=Runs.seq hc hp
    refine ⟨((eb b).length+1)+(2*(ea a).length+1),by simp;omega,?_⟩
    convert hh using 1
    · funext k;fin_cases k;simp [u,s,singletonStore]
    · simp [s,singletonStore]

noncomputable def quote (ea : α→List Bool) : Procedure ea (fun a=>quoteBits (ea a)) id where
  K:=Fin 3
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=quoteMove 0 1 2
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 5
  runs a:=by
    have hh:=quoteMove_runs (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
      (singletonStore 0 (ea a)) (by simp [singletonStore])
    refine ⟨7*(ea a).length+5,by simp,?_⟩
    convert hh using 1
    · funext k; fin_cases k <;> simp [singletonStore,Function.update]
    · simp [singletonStore]

/-- Count each actual symbol, returning a unary length. -/
noncomputable def length : Procedure (id : List Bool→List Bool)
    (fun n=>List.replicate n true) List.length where
  K:=Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.loop 0 (.push 1 true) (.push 1 true)
  bound:=Polynomial.C 2*Polynomial.X+1
  runs xs:=by
    have h : ∀ xs (s : Store (Fin 2)),s 0=xs→
        Runs (.loop 0 (.push 1 true) (.push 1 true)) s
          (Function.update (Function.update s 0 []) 1 (List.replicate xs.length true++s 1))
          (2*xs.length+1) := by
      intro ys; induction ys with
      | nil=>
        intro s hs
        have he : Function.update (Function.update s 0 []) 1
            (List.replicate ([] : List Bool).length true++s 1)=s := by
          simp only [List.length_nil,List.replicate_zero,List.nil_append]
          rw [←hs,Function.update_eq_self,Function.update_eq_self]
        rw [he];exact Runs.loop_nil hs
      | cons y ys ih=>
        intro s hs
        let u:=Function.update s 0 ys
        let v:=Function.update u 1 (true::u 1)
        have hv : v 0=ys:=by simp [v,u]
        have htail:=ih v hv
        have hh : Runs (.loop 0 (.push 1 true) (.push 1 true)) s
            (Function.update (Function.update v 0 []) 1 (List.replicate ys.length true++v 1))
            (2*ys.length+1+1+1) := by
          cases y
          · exact Runs.loop_false (a:=1) (b:=2*ys.length+1) hs (Runs.push u 1 true) htail
          · exact Runs.loop_true (a:=1) (b:=2*ys.length+1) hs (Runs.push u 1 true) htail
        convert hh using 1 <;> try (simp only [List.length_cons, List.length_nil] <;> omega)
        · funext k;fin_cases k <;> simp [u,v,Function.update,List.replicate_succ]
          rw [←List.cons_append,←List.replicate_succ,List.replicate_succ',List.append_assoc]
          rfl
    refine ⟨2*xs.length+1,by simp,?_⟩
    convert h xs (singletonStore 0 xs) (by simp [singletonStore]) using 1 <;>
      (funext k;fin_cases k <;> simp [singletonStore,Function.update])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackIncrement.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

/-- Little-endian evaluation; leading zeroes at the high end are allowed. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b::xs => b.toNat+2*binaryValue xs

def incrementWord : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => false::incrementWord xs

def carryTail : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => carryTail xs

def carryCount : List Bool → ℕ
  | [] => 0
  | false::_ => 0
  | true::xs => carryCount xs+1

lemma incrementWord_value (xs : List Bool) : binaryValue (incrementWord xs)=binaryValue xs+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [incrementWord,binaryValue,ih] <;> omega
lemma carryCount_le_length (xs : List Bool) : carryCount xs≤xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [carryCount,List.length_cons]; omega
lemma incrementWord_eq (xs : List Bool) :
    incrementWord xs=List.replicate (carryCount xs) false++carryTail xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [incrementWord,carryCount,carryTail,ih,List.replicate_succ]
lemma incrementWord_length (xs : List Bool) : (incrementWord xs).length≤xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [incrementWord,List.length_cons]; omega

variable {K : Type} [DecidableEq K]
def rippleBody (a t c : K) : Program K :=
  .cases a (.push a true) (.push a true) (.seq (.push t false) (.push c true))
def ripple (a t c : K) : Program K := .loop c (rippleBody a t c) (rippleBody a t c)
def increment (a t c : K) : Program K :=
  .seq (.push c true) (.seq (ripple a t c) (reverseMove t a))

lemma ripple_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (s : Store K) (hc : s c=[true]) :
    Runs (ripple a t c) s
      (Function.update (Function.update (Function.update s c []) a (carryTail (s a)))
        t (List.replicate (carryCount (s a)) false++s t))
      (4*(carryCount (s a)+1)) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    let u := Function.update s c []
    let v := Function.update u a [true]
    have hua : u a=[] := by simp [u,hac,hs]
    have hvc : v c=[] := by simp [v,u,hac.symm]
    have body : Runs (rippleBody a t c) u v 2 :=
      Runs.cases_nil hua (by simpa only [hua] using Runs.push u a true)
    have hh := Runs.loop_true (p:=rippleBody a t c) (a:=2) (b:=1) hc body (Runs.loop_nil hvc)
    change Runs (.loop _ _ _) _ _ _
    convert hh using 1
    · simp only [carryCount,carryTail,List.replicate_zero,List.nil_append]
      change Function.update v t (s t)=v
      rw [← show v t=s t by simp [v,u,hat.symm,htc],Function.update_eq_self]
    · rfl
  | cons x xs ih =>
    cases x
    · let u := Function.update s c []
      let w := Function.update u a xs
      let v := Function.update w a (true::xs)
      have hua : u a=false::xs := by simp [u,hac,hs]
      have hvc : v c=[] := by simp [v,w,u,hac.symm]
      have body : Runs (rippleBody a t c) u v 2 :=
        Runs.cases_false hua (by simpa only [w,Function.update_self] using Runs.push w a true)
      have hh := Runs.loop_true (p:=rippleBody a t c) (a:=2) (b:=1) hc body (Runs.loop_nil hvc)
      change Runs (.loop _ _ _) _ _ _
      convert hh using 1
      · funext k
        by_cases ha : k=a <;> by_cases ht : k=t <;> by_cases hcc : k=c <;>
          simp_all [v,w,u,Function.update,carryCount,carryTail]
      · rfl
    · let u := Function.update s c []
      let w := Function.update u a xs
      let z := Function.update w t (false::w t)
      let v := Function.update z c (true::z c)
      have hua : u a=true::xs := by simp [u,hac,hs]
      have hva : v a=xs := by simp [v,z,w,hac,hat]
      have hvc : v c=[true] := by simp [v,z,w,u,htc.symm,hac.symm]
      have body : Runs (rippleBody a t c) u v 3 :=
        Runs.cases_true (a:=2) hua (Runs.seq (Runs.push w t false) (Runs.push z c true))
      have hh := Runs.loop_true (p:=rippleBody a t c) (a:=3) (b:=4*(carryCount xs+1)) hc body (ih v hvc hva)
      change Runs (.loop _ _ _) _ _ _
      convert hh using 1
      · funext k
        by_cases ha : k=a <;> by_cases ht : k=t <;> by_cases hcc : k=c <;>
          simp_all [v,z,w,u,Function.update,carryCount,carryTail,List.replicate_succ]
        rw [← List.cons_append, ← List.replicate_succ, List.replicate_succ',List.append_assoc]
        rfl
      · simp only [carryCount]; omega

lemma increment_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (s : Store K) (ht : s t=[]) (hc : s c=[]) :
    Runs (increment a t c) s (Function.update s a (incrementWord (s a)))
      (6*carryCount (s a)+6) := by
  let u := Function.update s c [true]
  have hua : u a=s a := by simp [u,hac]
  have hut : u t=[] := by simp [u,ht,htc]
  have huc : u c=[true] := by simp [u]
  let v := Function.update (Function.update (Function.update u c []) a (carryTail (u a)))
    t (List.replicate (carryCount (u a)) false++u t)
  have hp : Runs (.push c true) s u 1 := by simpa only [hc] using Runs.push s c true
  have hh := Runs.seq hp
    (Runs.seq (ripple_runs a t c hat hac htc u huc) (reverseMove_runs t a hat.symm v))
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases htk : k=t <;> by_cases hck : k=c <;>
      simp_all [v,u,Function.update,incrementWord_eq]
  · simp only [v,Function.update_self,hut,List.append_nil,List.length_replicate,hua]
    omega

end ExactQuantumFactoring.BitStackProgram

end



end OAI
