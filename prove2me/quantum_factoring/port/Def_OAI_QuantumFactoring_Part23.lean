/-
Exact quantum factoring development (port of OpenAI's formalization), part 23 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: TreeAmplified.lean, TreeReadout.lean, FactoringInputLayout.lean, FactoringRelabel.lean, FactoringCircuit.lean, TreeFinalResources.lean, TreeReadoutResources.lean, ChildQueueBounds.lean, PolyBounds.lean, ExpressionResources.lean, RationalExpressionResources.lean, RationalHeightResources.lean, QuarterConstantResources.lean, PolynomialExpressionResources.lean, ConcreteExpressionResources.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part22

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeAmplified.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma actual_quarter_mass {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x=>(quarterFlag n (by omega)).eval x 0=true)
      ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N)))=1/4 := by
  rw [quarterProgram_state,outcomeMass_encode _ (quarterEncoding_injective n N)]
  have he : ((fun x=>(quarterFlag n (by omega)).eval x 0=true) ∘ quarterEncoding n N)=
      Quarter.passed N (paddedAccepted (N:=N) (by omega)) := by
    funext r
    exact propext (quarterFlag_eval hn hN hb r)
  rw [he]
  exact quarter_mass hn hN hb

def reflectWork (n : ℕ) (hn : 0<n) : ℕ :=
  max (quarterFlag n hn).net.count (zeroNet n).net.count
abbrev amplifiedWidth (n : ℕ) (hn : 0<n) := quarterWidth n+1+reflectWork n hn

def amplifiedProgram (n : ℕ) (hn : 0<n) : List (Instruction (amplifiedWidth n hn)) :=
  amplificationProgram (quarterProgram n) (quarterFlag n hn) (zeroNet n)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
def amplifiedZero (n N : ℕ) (hn : 0<n) : Basis (amplifiedWidth n hn) :=
  packed (reflectWork n hn) (quarterZero n N) (fun _=>false)
def amplifiedOutput (n : ℕ) (hn : 0<n) : BooleanNetwork (amplifiedWidth n hn) (n*n) :=
  (select (firstRegister (quarterWidth n) 1 (reflectWork n hn))).comp (quarterOutputNet n)

/-- An unconditional physical amplification identity for the actual program.
The only hypotheses are the manuscript's padded length and valid input. -/
theorem amplifiedProgram_state {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    (programMatrix (amplifiedProgram n (by omega))).mulVec
      (basisVector (amplifiedZero n N (by omega))) =
      encodeState (fun x=>packed (reflectWork n (by omega)) x (fun _ : Fin 1=>false))
        (fun x=> -2*goodPart (fun y=>(quarterFlag n (by omega)).eval y 0=true)
          ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) x) := by
  apply physical_quarter_amplification _ _ _ _ _
    (inputSector (inputWires n) (quarterZero n N))
    (quarterProgram_respects_input n N) _
  · intro _ _; rfl
  · exact zeroNet_sector n N
  · exact actual_quarter_mass hn hN hb

lemma prepared_nonzero_encoding {n N : ℕ} (x : Basis (quarterWidth n))
    (hx : ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) x≠0) :
    ∃ r : Quarter.Raw (PaddedRaw n) n, quarterEncoding n N r=x := by
  classical
  rw [quarterProgram_state] at hx
  by_contra hh
  exact hx (encodeState_outside _ _ x hh)

lemma quarterFlag_output_on_support {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (x : Basis (quarterWidth n))
    (hx : ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) x≠0)
    (hp : (quarterFlag n (by omega)).eval x 0=true) :
    CorrectEncoding N n (guessWords n ((quarterOutputNet n).eval x)) := by
  obtain ⟨r,rfl⟩:=prepared_nonzero_encoding x hx
  rw [quarterOutputNet_eval]
  exact quarter_output hn hN hb r ((quarterFlag_eval hn hN hb r).mp hp)

/-- Exact support on complete sorted factorizations, for the actual finite
fixed-gate program and a literal Boolean readout. This is a necessary main
proof dependency, not the missing polynomial/uniform circuit-family theorem. -/
theorem amplified_output_on_support {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (x : Basis (amplifiedWidth n (by omega)))
    (hx : ((programMatrix (amplifiedProgram n (by omega))).mulVec
      (basisVector (amplifiedZero n N (by omega)))) x≠0) :
    CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x)) := by
  classical
  rw [amplifiedProgram_state hn hN hb] at hx
  have hr : ∃ y : Basis (quarterWidth n),
      packed (reflectWork n (by omega)) y (fun _ : Fin 1=>false)=x := by
    by_contra hh
    exact hx (encodeState_outside _ _ x hh)
  obtain ⟨y,rfl⟩:=hr
  rw [encodeState_at _ (packed_injective _)] at hx
  have hg : goodPart (fun z=>(quarterFlag n (by omega)).eval z 0=true)
      ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) y≠0 := by
    intro h; exact hx (by rw [h,mul_zero])
  have hp : (quarterFlag n (by omega)).eval y 0=true := by
    by_contra hp
    exact hg (by simp only [goodPart,ite_eq_right hp])
  have hy : ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) y≠0 := by
    simpa only [goodPart,ite_eq_left hp] using hg
  have he : (amplifiedOutput n (by omega)).eval
      (packed (reflectWork n (by omega)) y (fun _ : Fin 1=>false))=(quarterOutputNet n).eval y := by
    rw [amplifiedOutput,eval_comp,eval_select,packed_first]
  rw [he]
  exact quarterFlag_output_on_support hn hN hb y hy hp

lemma amplified_mass_one {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x=>CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x)))
      ((programMatrix (amplifiedProgram n (by omega))).mulVec
        (basisVector (amplifiedZero n N (by omega))))=1 := by
  classical
  have he : ∀ x : Basis (amplifiedWidth n (by omega)),
      (if CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x)) then
        Complex.normSq (((programMatrix (amplifiedProgram n (by omega))).mulVec
          (basisVector (amplifiedZero n N (by omega)))) x) else 0)=
        Complex.normSq (((programMatrix (amplifiedProgram n (by omega))).mulVec
          (basisVector (amplifiedZero n N (by omega)))) x) := by
    intro x
    by_cases hx : ((programMatrix (amplifiedProgram n (by omega))).mulVec
      (basisVector (amplifiedZero n N (by omega)))) x=0
    · simp only [hx,Complex.normSq_zero,ite_self]
    · rw [ite_eq_left (amplified_output_on_support hn hN hb x hx)]
  simp_rw [outcomeMass,he]
  rw [unitary_mass _ (programMatrix_unitary _)]
  simp [basisVector]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeReadout.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork BitArithmetic Exactness

/-- The readout is a clean reversible Boolean network, not a classical hidden
postprocessor. The preparation's complete history is retained. -/
def readoutProgram {q m r : ℕ} (P : List (Instruction q))
    (c : BooleanNetwork q m) (hr : c.net.count≤r) : List (Instruction (q+m+r)) :=
  firstProgram m r P++oracleOn c hr

lemma readoutProgram_state {q m r : ℕ} (P : List (Instruction q))
    (c : BooleanNetwork q m) (hr : c.net.count≤r) (z : Basis q) :
    (programMatrix (readoutProgram P c hr)).mulVec
      (basisVector (packed r z (fun _=>false)))=
      encodeState (fun x=>packed r x (c.eval x)) ((programMatrix P).mulVec (basisVector z)) := by
  rw [readoutProgram,programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis]
  rw [encodeState,Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,oracleOn_basis,Bool.false_xor]
  rfl

lemma readoutProgram_length {q m r : ℕ} (P : List (Instruction q))
    (c : BooleanNetwork q m) (hr : c.net.count≤r) :
    (readoutProgram P c hr).length≤P.length+4*c.net.count+2*m := by
  have hh:=oracleOn_length c hr
  simp only [readoutProgram,List.length_append,firstProgram_length]
  omega

namespace PhysicalTree
abbrev readoutWork (n : ℕ) (hn : 0<n) := (amplifiedOutput n hn).net.count
abbrev readoutWidth (n : ℕ) (hn : 0<n) := amplifiedWidth n hn+n*n+readoutWork n hn

def factoringProgram (n : ℕ) (hn : 0<n) : List (Instruction (readoutWidth n hn)) :=
  readoutProgram (amplifiedProgram n hn) (amplifiedOutput n hn) le_rfl
def factoringZero (n N : ℕ) (hn : 0<n) : Basis (readoutWidth n hn) :=
  packed (readoutWork n hn) (amplifiedZero n N hn) (fun _=>false)
def factoringResult (n : ℕ) (hn : 0<n) (x : Basis (readoutWidth n hn)) : Basis (n*n) :=
  x ∘ targetRegister (amplifiedWidth n hn) (n*n) (readoutWork n hn)

/-- Probability ONE of complete factorization for the actual finite physical
fixed-gate program, with its clean reversible readout. Polynomial resource
bounds and finite-alphabet polynomial-time uniformity are separate properties
of the same circuit family. -/
theorem factoringProgram_exact {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x=>CorrectEncoding N n (guessWords n (factoringResult n (by omega) x)))
      ((programMatrix (factoringProgram n (by omega))).mulVec
        (basisVector (factoringZero n N (by omega))))=1 := by
  rw [factoringProgram,factoringZero,readoutProgram_state]
  have hi : Function.Injective (fun x : Basis (amplifiedWidth n (by omega))=>
      packed (readoutWork n (by omega)) x ((amplifiedOutput n (by omega)).eval x)) := by
    intro x y hxy
    have hh:=congrArg (fun z=>z ∘ firstRegister (amplifiedWidth n (by omega)) (n*n)
      (readoutWork n (by omega))) hxy
    simpa only [packed_first] using hh
  rw [outcomeMass_encode _ hi]
  have he : ((fun x : Basis (readoutWidth n (by omega))=>CorrectEncoding N n (guessWords n (factoringResult n (by omega) x))) ∘
      (fun x : Basis (amplifiedWidth n (by omega))=>packed (readoutWork n (by omega)) x ((amplifiedOutput n (by omega)).eval x)))=
      (fun x : Basis (amplifiedWidth n (by omega))=>CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x))) := by
    funext x
    simp only [Function.comp_apply,factoringResult,packed_targetRegister]
  rw [he]
  exact amplified_mass_one hn hN hb

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FactoringInputLayout.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial

lemma natBasis_apply (w N : ℕ) (i : Fin w) : natBasis w N i=N.testBit i.val := by
  simp only [natBasis,BitVec.getLsbD_ofNat,decide_true,i.isLt,Bool.true_and]

/-- The sole nondeterministic-preparation branch bit precedes the retained N;
all remaining physical input coordinates are clean. -/
def shiftedInput (q n N : ℕ) : Basis q :=
  fun i=>if 1 ≤ i.val ∧ i.val < 1+n then N.testBit (i.val-1) else false

lemma packed_shifted {q m r n N : ℕ} (hn : 1+n≤q) :
    packed r (shiftedInput q n N) (fun _ : Fin m=>false)=shiftedInput (q+m+r) n N := by
  funext i
  simp only [packed,shiftedInput]
  by_cases hq : i.val < q
  · rw [dite_eq_left hq]
  · rw [dite_eq_right hq]
    have hi : ¬(1 ≤ i.val ∧ i.val < 1+n) := by omega
    rw [ite_eq_right hi]
    split_ifs <;> rfl

namespace PhysicalTree
lemma quarterZero_input (n N : ℕ) (j : Fin n) :
    quarterZero n N
      (Fin.natAdd 1 ((Fin.castAdd (n*n+Quarter.D n))
        ((Fin.castAdd (tensorWidth n (padding n)))
          (firstRegister n (width n) (launchWork n) j))))=N.testBit j.val := by
  simp only [quarterZero,Completion.layout,productLayout_apply,Equiv.refl_apply,
    Fin.append_right,Fin.append_left,paddedZero,launchZero]
  change packed (launchWork n) (natBasis n N) (fun _ : Fin (width n) => false)
    ⟨j.val, by omega⟩ = _
  rw [packed_input]
  exact natBasis_apply n N j

lemma quarterWidth_input (n : ℕ) : 1+n≤quarterWidth n := by
  change 1+n≤1+(n+width n+launchWork n+tensorWidth n (padding n)+(n*n+Quarter.D n))
  omega

lemma quarterZero_shifted (n N : ℕ) : quarterZero n N=shiftedInput (quarterWidth n) n N := by
  funext i
  by_cases hi : 1 ≤ i.val ∧ i.val < 1+n
  · let j : Fin n:=⟨i.val-1,by omega⟩
    have he : i=Fin.natAdd 1 ((Fin.castAdd (n*n+Quarter.D n))
        ((Fin.castAdd (tensorWidth n (padding n)))
          (firstRegister n (width n) (launchWork n) j))) := by
      apply Fin.ext
      change i.val=1+(i.val-1)
      omega
    rw [he,quarterZero_input]
    change N.testBit (i.val-1)=_
    rw [←he]
    simp only [shiftedInput,ite_eq_left hi]
  · rw [quarterZero_clean n N i,shiftedInput,ite_eq_right hi]
    simpa only [inputWires,Finset.mem_filter,Finset.mem_univ,true_and] using hi

lemma amplifiedZero_shifted (n N : ℕ) (hn : 0<n) :
    amplifiedZero n N hn=shiftedInput (amplifiedWidth n hn) n N := by
  rw [amplifiedZero,quarterZero_shifted,packed_shifted (quarterWidth_input n)]

lemma factoringZero_shifted (n N : ℕ) (hn : 0<n) :
    factoringZero n N hn=shiftedInput (readoutWidth n hn) n N := by
  rw [factoringZero,amplifiedZero_shifted]
  apply packed_shifted
  have hh:=quarterWidth_input n
  change 1+n≤quarterWidth n+1+reflectWork n hn
  omega
end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FactoringRelabel.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
/-- Move the physical input after the branch bit to the front, and place the
readout immediately after the true input. The retained history is permuted,
never erased or initialized with input-dependent advice. -/
def relocateVal (A m ℓ i : ℕ) : ℕ :=
  if i=0 then ℓ+m else if i≤ℓ then i-1 else if i<A then i+m
  else if i<A+m then ℓ+(i-A) else i

lemma relocateVal_lt {A m ℓ r i : ℕ} (hl : ℓ+1≤A) (hi : i<A+m+r) :
    relocateVal A m ℓ i<A+m+r := by
  unfold relocateVal
  split_ifs <;> omega

lemma relocateVal_injective {A m ℓ r : ℕ} (hl : ℓ+1≤A) :
    Function.Injective (fun i : Fin (A+m+r) => relocateVal A m ℓ i.val) := by
  intro i j h
  apply Fin.ext
  have hi:=i.isLt
  have hj:=j.isLt
  dsimp only at h
  unfold relocateVal at h
  split_ifs at h <;> omega

def relocate (A m ℓ r : ℕ) (hl : ℓ+1≤A) : Register (A+m+r) (A+m+r) where
  toFun i:=⟨relocateVal A m ℓ i.val,relocateVal_lt hl i.isLt⟩
  inj' := by
    intro i j h
    exact relocateVal_injective hl (congrArg Fin.val h)

lemma relocate_input (A m ℓ r N : ℕ) (hl : ℓ+1≤A) :
    inputBasis (A+m+r) ℓ N ∘ relocate A m ℓ r hl = shiftedInput (A+m+r) ℓ N := by
  funext i
  change (if relocateVal A m ℓ i.val < ℓ then N.testBit (relocateVal A m ℓ i.val) else false)=_
  unfold shiftedInput relocateVal
  split_ifs <;> simp_all <;> omega

lemma relocate_output (A m ℓ r : ℕ) (hl : ℓ+1≤A) (j : Fin m) :
    (relocate A m ℓ r hl) ⟨A+j.val,by omega⟩=⟨ℓ+j.val,by have:=j.isLt;omega⟩ := by
  apply Fin.ext
  change relocateVal A m ℓ (A+j.val)=ℓ+j.val
  have hj:=j.isLt
  unfold relocateVal
  split_ifs <;> omega

lemma shiftedInput_pad (q n ℓ N : ℕ) (hl : ℓ≤n) (hb : N<2^ℓ) :
    shiftedInput q ℓ N=shiftedInput q n N := by
  funext i
  unfold shiftedInput
  by_cases hi : 1 ≤ i.val ∧ i.val < 1+ℓ
  · rw [ite_eq_left hi,ite_eq_left (by omega)]
  · rw [ite_eq_right hi]
    split_ifs with hj
    · have hb' : N<2^(i.val-1) := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow hb']
    · rfl
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FactoringCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma paddedLength_pos (ℓ : ℕ) : 0<paddedLength ℓ := by
  unfold paddedLength;omega
lemma finalRegister_bound (ℓ : ℕ) :
    ℓ+1≤amplifiedWidth (paddedLength ℓ) (paddedLength_pos ℓ) := by
  have h:=quarterWidth_input (paddedLength ℓ)
  have hl : ℓ≤paddedLength ℓ:=le_max_right _ _
  change ℓ+1≤quarterWidth (paddedLength ℓ)+1+reflectWork (paddedLength ℓ) (paddedLength_pos ℓ)
  omega

def finalRegister (ℓ : ℕ) : Register
    (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ))
    (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) :=
  relocate (amplifiedWidth (paddedLength ℓ) (paddedLength_pos ℓ))
    (paddedLength ℓ*paddedLength ℓ) ℓ
    (readoutWork (paddedLength ℓ) (paddedLength_pos ℓ)) (finalRegister_bound ℓ)

def finalCircuit (ℓ : ℕ) : Circuit where
  qubits:=readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)
  instructions:=(factoringProgram (paddedLength ℓ) (paddedLength_pos ℓ)).map
    (Instruction.place (finalRegister ℓ))

lemma final_input (ℓ N : ℕ) (hb : N<2^ℓ) :
    inputBasis (finalCircuit ℓ).qubits ℓ N ∘ finalRegister ℓ=
      factoringZero (paddedLength ℓ) N (paddedLength_pos ℓ) := by
  dsimp only [finalCircuit]
  rw [finalRegister,relocate_input]
  rw [shiftedInput_pad _ (paddedLength ℓ) ℓ N (le_max_right _ _) hb]
  exact (factoringZero_shifted _ _ _).symm

lemma final_register_output (ℓ : ℕ) (j : Fin (paddedLength ℓ*paddedLength ℓ)) :
    finalRegister ℓ (targetRegister (amplifiedWidth (paddedLength ℓ) (paddedLength_pos ℓ))
      (paddedLength ℓ*paddedLength ℓ) (readoutWork (paddedLength ℓ) (paddedLength_pos ℓ)) j)=
    ⟨ℓ+j.val,by have:=j.isLt;have:=finalRegister_bound ℓ;dsimp only [readoutWidth];omega⟩ := by
  exact relocate_output _ _ _ _ _ j

lemma final_output (ℓ : ℕ) (z : Basis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)))
    (x : Basis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ))) :
    outputList ℓ ((finalRegister ℓ).replace z x)=
      guessWords (paddedLength ℓ) (factoringResult (paddedLength ℓ) (paddedLength_pos ℓ) x) := by
  dsimp only [outputList,guessWords]
  apply congrArg List.ofFn
  funext a
  rw [bitsValue_toNat,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  let k : Fin (paddedLength ℓ*paddedLength ℓ):=finProdFinEquiv (a,j)
  have hk : k.val=a.val*paddedLength ℓ+j.val:=by
    change j.val+paddedLength ℓ*a.val=a.val*paddedLength ℓ+j.val
    ring
  have hh:=final_register_output ℓ k
  have hb : ℓ+a.val*paddedLength ℓ+j.val<readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ) := by
    have hi:=(finalRegister ℓ (targetRegister _ _ _ k)).isLt
    rw [hh] at hi
    dsimp only at hi
    omega
  simp only [readBit,dite_eq_left hb]
  have he : (⟨ℓ+a.val*paddedLength ℓ+j.val,hb⟩ : Fin (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)))=
      finalRegister ℓ (targetRegister _ _ _ k) := by
    rw [hh];apply Fin.ext;dsimp only;omega
  rw [he,Register.replace_inside]
  change (if x (targetRegister _ _ _ k) then 2^j.val else 0)=
    2^j.val*(x (targetRegister _ _ _ k)).toNat
  cases x (targetRegister _ _ _ k) <;> simp

lemma finalCircuit_qubits (ℓ : ℕ) :
    ℓ+(paddedLength ℓ)^2≤(finalCircuit ℓ).qubits := by
  have h:=finalRegister_bound ℓ
  change ℓ+(paddedLength ℓ)^2≤amplifiedWidth _ _+paddedLength ℓ*paddedLength ℓ+readoutWork _ _
  rw [pow_two]
  omega

theorem finalCircuit_exact (ℓ N : ℕ) (hN : 2≤N) (hb : N<2^ℓ) :
    (finalCircuit ℓ).correctProbability ℓ N=1 := by
  have hh : 128≤paddedLength ℓ:=le_max_left _ _
  have hb' : N<2^paddedLength ℓ:=lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  change outcomeMass (fun x=>CorrectEncoding N (paddedLength ℓ) (outputList ℓ x))
    ((finalCircuit ℓ).apply (basisVector (inputBasis (finalCircuit ℓ).qubits ℓ N)))=1
  rw [Circuit.apply_eq_matrix]
  change outcomeMass (fun x : Basis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ))=>
      CorrectEncoding N (paddedLength ℓ) (outputList ℓ x))
    ((programMatrix ((factoringProgram (paddedLength ℓ) (paddedLength_pos ℓ)).map
      (Instruction.place (finalRegister ℓ)))).mulVec
      (basisVector (inputBasis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) ℓ N)))=1
  rw [Register.placed_basis_state]
  have hin := final_input ℓ N hb
  change inputBasis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) ℓ N ∘ finalRegister ℓ = _ at hin
  rw [hin]
  rw [outcomeMass_encode _ (Register.replace_injective _ _)]
  have he : ((fun x=>CorrectEncoding N (paddedLength ℓ) (outputList ℓ x)) ∘
      ((finalRegister ℓ).replace (inputBasis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) ℓ N)))=
      (fun x=>CorrectEncoding N (paddedLength ℓ)
        (guessWords (paddedLength ℓ) (factoringResult (paddedLength ℓ) (paddedLength_pos ℓ) x))) := by
    funext x
    simp only [Function.comp_apply,final_output]
  rw [he]
  exact factoringProgram_exact hh hN hb'

/-- Discharges exactly the input/output clause for one explicit length-only
family. This does NOT assert the outstanding resource or TM2-uniformity clauses. -/
theorem finalCircuit_spec (ℓ N : ℕ) (hN : 2≤N) (hs : N.size=ℓ) :
    ℓ+(paddedLength ℓ)^2≤(finalCircuit ℓ).qubits ∧
      (finalCircuit ℓ).correctProbability ℓ N=1 := by
  refine ⟨finalCircuit_qubits ℓ,finalCircuit_exact ℓ N hN ?_⟩
  rw [←hs]
  exact Nat.lt_size_self N

lemma finalCircuit_length (ℓ : ℕ) :
    (finalCircuit ℓ).instructions.length=
      (factoringProgram (paddedLength ℓ) (paddedLength_pos ℓ)).length := by
  exact List.length_map _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeFinalResources.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma amplifiedProgram_length (n : ℕ) (hn : 0<n) :
    (amplifiedProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+8*(zeroNet n).net.count+12 :=
  amplificationProgram_length _ _ _ _ _

lemma amplifiedOutput_count (n : ℕ) (hn : 0<n) :
    (amplifiedOutput n hn).net.count=(quarterOutputNet n).net.count := by
  simp only [amplifiedOutput,count_comp,count_select,Nat.zero_add]

lemma paddedHistory_count (n : ℕ) : (paddedHistory n).net.count=0 := by
  simp only [paddedHistory,launchHistory,count_comp,count_select,Nat.zero_add]

lemma paddedOutputNet_count (n : ℕ) :
    (paddedOutputNet n).net.count=(rootFlat n (2*n^2)).net.count := by
  simp only [paddedOutputNet,count_comp,paddedHistory_count,Nat.zero_add]

lemma quarterOutputNet_count (n : ℕ) :
    (quarterOutputNet n).net.count≤(rootFlat n (2*n^2)).net.count+7*(n*n)+118 := by
  have h:=Completion.outputNet_count (paddedOutputNet n) 1 (n^11)
  rw [paddedOutputNet_count] at h
  change (Completion.outputNet (paddedOutputNet n) 1 (n^11)).net.count≤_
  omega

lemma factoringProgram_length (n : ℕ) (hn : 0<n) :
    (factoringProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+8*(zeroNet n).net.count+
      4*(quarterOutputNet n).net.count+2*(n*n)+12 := by
  have h₁:=readoutProgram_length (amplifiedProgram n hn) (amplifiedOutput n hn) le_rfl
  have h₂:=amplifiedProgram_length n hn
  have hc:=amplifiedOutput_count n hn
  change (readoutProgram (amplifiedProgram n hn) (amplifiedOutput n hn) le_rfl).length≤_
  omega

lemma readoutWidth_bound (n : ℕ) (hn : 0<n) :
    readoutWidth n hn≤quarterWidth n+1+(quarterFlag n hn).net.count+
      (zeroNet n).net.count+n*n+(quarterOutputNet n).net.count := by
  have hc:=amplifiedOutput_count n hn
  change quarterWidth n+1+max (quarterFlag n hn).net.count (zeroNet n).net.count+
    n*n+(amplifiedOutput n hn).net.count≤_
  omega

/-- Concrete reduction of the remaining whole-program resource obligation to
its literal preparation, accepted-event network, and root readout. These are
counts of actual gates/wires, not an assumed big-O charge for arithmetic. -/
theorem factoringProgram_resources (n : ℕ) (hn : 0<n) :
    (factoringProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+16*quarterWidth n+
      4*(rootFlat n (2*n^2)).net.count+30*(n*n)+492 ∧
    readoutWidth n hn≤3*quarterWidth n+(quarterFlag n hn).net.count+
      (rootFlat n (2*n^2)).net.count+8*(n*n)+120 := by
  have h₁:=factoringProgram_length n hn
  have h₂:=readoutWidth_bound n hn
  have h₃:=zeroNet_count n
  have h₄:=quarterOutputNet_count n
  constructor <;> omega

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TreeReadoutResources.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PhysicalTree

lemma flattenWords_count (n : ℕ) : (flattenWords n).net.count=0 := by
  have h:=wordBlocks_count (fun i : Fin n=>tensorSelect n n i)
    (c:=0) (fun _=>by simp only [tensorSelect,count_select,le_refl])
  change (flattenWords n).net.count≤n*n*0 at h
  omega

lemma rootFlat_count (n t : ℕ) :
    (rootFlat n t).net.count≤n*n+PhysicalNode.resultBound n := by
  cases t with
  | zero=>simp only [rootFlat,Completion.zeros_count];omega
  | succ t=>
    have h:=nodeResult_count n
    simp only [rootFlat,rootResult,count_comp,NodeMachine.firstNodeNet_count,
      flattenWords_count,Nat.zero_add,Nat.add_zero]
    omega

/-- All readout overhead is now bounded by an explicit polynomial expression;
the two remaining size estimates are preparation and same-history flagging. -/
theorem factoringProgram_resources_reduced (n : ℕ) (hn : 0<n) :
    (factoringProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+16*quarterWidth n+
      4*PhysicalNode.resultBound n+34*(n*n)+492 ∧
    readoutWidth n hn≤3*quarterWidth n+(quarterFlag n hn).net.count+
      PhysicalNode.resultBound n+9*(n*n)+120 := by
  have h₁:=factoringProgram_resources n hn
  have h₂:=rootFlat_count n (2*n^2)
  constructor <;> omega

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ChildQueueBounds.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.ChildQueue
open BooleanNetwork

lemma wordMember_count {k w c : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (wordMember a as).net.count ≤ as.length*(2*c+96*w+25)+1 := by
  have h := any_count (as.map (fun b=>(a.pair b).comp (wordEq w))) (c:=2*c+96*w+21) (by
    intro d hd
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hd
    have hh := hs b hb
    have he := wordEq_count w
    simp only [count_comp,count_pair]
    omega)
  simpa only [wordMember,List.length_map,Nat.add_assoc] using h

lemma active_count {k w c : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (active a as).net.count ≤ c+49*w+11+as.length*(2*c+96*w+25) := by
  have hm := wordMember_count a as ha hs
  have hl := wordLt_count (wordConstant (n:=k) (BitVec.ofNat w 2)) a
  rw [wordConstant_count] at hl
  simp only [active,count_band,count_bnot]
  omega

def oneBound (s w c r : ℕ) := c+49*w+11+r*(2*c+96*w+25)+s*w*(c+159*w+6)+7*(s*w)

lemma pushOne_count {k w c : ℕ} (s : ℕ) (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (pushOne s a as).net.count ≤ oneBound s w c as.length := by
  have hac := active_count a as ha hs
  have hsub := sub_count w
  have hh : ((((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))).net.count ≤
      c+159*w+6 := by
    simp only [count_comp,count_pair,liftWord,source,count_select,zero_add,wordConstant_count]
    omega
  have hpush := stackPush_count (((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))
    (queue k s w)
  simp only [queue,count_select,add_zero] at hpush
  have hpush' := hpush.trans (Nat.mul_le_mul_left (s*w) hh)
  simp only [pushOne,count_pair,wordMux_count,count_comp,source,queue,count_select,zero_add,add_zero]
  dsimp only [oneBound]
  omega

lemma oneBound_mono (s w c : ℕ) {r t : ℕ} (h : r ≤ t) : oneBound s w c r ≤ oneBound s w c t := by
  have hh := Nat.mul_le_mul_right (2*c+96*w+25) h
  dsimp only [oneBound]
  omega

/-- The all-child queue update is quadratic in the number of prime fields,
not an exponentially duplicated expression. Bounds hold on ALL inputs. -/
theorem pushAll_count {k w c : ℕ} (s : ℕ) (as : List (BooleanNetwork k w))
    (hs : ∀ b∈as,b.net.count ≤ c) :
    (pushAll s as).net.count ≤ as.length*oneBound s w c as.length := by
  induction as with
  | nil=>simp [pushAll,count_select]
  | cons a as ih=>
    have ha := hs a (by simp)
    have ht : ∀ b∈as,b.net.count ≤ c := fun b hb=> hs b (by simp [hb])
    have hi := ih ht
    have hp := pushOne_count s a as ha ht
    have hb := oneBound_mono s w c (Nat.le_succ as.length)
    simp only [pushAll,count_comp,List.length_cons]
    calc
      _ ≤ as.length*oneBound s w c as.length+oneBound s w c as.length := Nat.add_le_add hi hp
      _ ≤ as.length*oneBound s w c (as.length+1)+oneBound s w c (as.length+1) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hb) hb
      _ = _ := by ring

end ExactQuantumFactoring.BitArithmetic.ChildQueue


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PolyBounds.lean =====
namespace OAI



section

namespace ExactQuantumFactoring

/-- A worst-case bound for all input lengths, with nonnegative coefficients. -/
def PolyBound (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n

namespace PolyBound
lemma const (c : ℕ) : PolyBound (fun _ => c) :=
  ⟨Polynomial.C c, fun _ => by simp⟩
lemma id : PolyBound (fun n => n) := ⟨Polynomial.X, fun _ => by simp⟩
lemma add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n + g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p+q, fun n => by simpa using Nat.add_le_add (hp n) (hq n)⟩
lemma mul {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n * g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p*q, fun n => by simpa using Nat.mul_le_mul (hp n) (hq n)⟩
lemma pow {f : ℕ → ℕ} (hf : PolyBound f) (k : ℕ) :
    PolyBound (fun n => f n ^ k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k, fun n => by simpa using Nat.pow_le_pow_left (hp n) k⟩
lemma of_le {f g : ℕ → ℕ} (hg : PolyBound g) (h : ∀ n, f n ≤ g n) : PolyBound f := by
  obtain ⟨p,hp⟩ := hg
  exact ⟨p, fun n => (h n).trans (hp n)⟩
lemma max {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _,Nat.le_add_left _ _⟩)
lemma sub {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n-g n) :=
  hf.of_le (fun _ => Nat.sub_le _ _)
lemma div {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n/g n) :=
  hf.of_le (fun _ => Nat.div_le_self _ _)
lemma mod {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n%g n) :=
  hf.of_le (fun _ => Nat.mod_le _ _)
lemma ite {f g : ℕ → ℕ} (p : ℕ → Prop) [∀ n, Decidable (p n)]
    (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => if p n then f n else g n) :=
  (hf.max hg).of_le (fun n => by split_ifs <;> omega)

lemma eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

lemma comp {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f (g n)) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  refine ⟨p.comp q, fun n => ?_⟩
  rw [Polynomial.eval_comp]
  exact (hp (g n)).trans (eval_mono p (hq n))

lemma natSize {f : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => (f n).size) :=
  hf.of_le (fun _ => Nat.size_le.mpr (Nat.lt_two_pow_self))
end PolyBound

syntax "poly_bound" : tactic
macro_rules
  | `(tactic| poly_bound) => `(tactic|
    first
    | assumption
    | exact PolyBound.id
    | exact PolyBound.const _
    | (apply PolyBound.add <;> poly_bound)
    | (apply PolyBound.mul <;> poly_bound)
    | (apply PolyBound.pow <;> poly_bound)
    | (apply PolyBound.max <;> poly_bound)
    | (apply PolyBound.sub <;> poly_bound)
    | (apply PolyBound.div <;> poly_bound)
    | (apply PolyBound.mod <;> poly_bound)
    | (apply PolyBound.natSize <;> poly_bound))



end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExpressionResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring

lemma nat_size_max (a b : ℕ) : (max a b).size = max a.size b.size := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Nat.size_le_size h)]
  · rw [max_eq_left h, max_eq_left (Nat.size_le_size h)]

namespace NatExpr
variable {v : Type*}

/-- Actual syntax length, sharing-sensitive compiler cost and constant bit size. -/
def weight (e : NatExpr v) : ℕ := e.size + e.sharedCost + e.maxConst.size
@[simp] lemma weight_var (a : v) : (var a).weight = 2 := rfl
@[simp] lemma weight_const (a : ℕ) : (const (v:=v) a).weight = a.size+2 := by
  simp [weight,size,sharedCost,maxConst]; omega
lemma weight_add (a b : NatExpr v) : (add a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_sub (a b : NatExpr v) : (sub a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_mul (a b : NatExpr v) : (mul a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_div (a b : NatExpr v) : (div a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_mod (a b : NatExpr v) : (mod a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_iteLe (a b c d : NatExpr v) :
    (iteLe a b c d).weight ≤ 2*(a.weight+b.weight+c.weight+d.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_pos (a : NatExpr v) : 0<a.weight := by
  have := a.size_pos
  dsimp only [weight]
  omega
lemma size_le_weight (a : NatExpr v) : a.size ≤ a.weight := by dsimp [weight]; omega
lemma sharedCost_le_weight (a : NatExpr v) : a.sharedCost ≤ a.weight := by dsimp [weight]; omega
lemma constSize_le_weight (a : NatExpr v) : a.maxConst.size ≤ a.weight := by dsimp [weight]; omega
lemma weight_pow (a : NatExpr v) (k : ℕ) :
    (a.pow k).weight ≤ (k+1)*(a.weight+3) := by
  have h := Nat.size_le_size (pow_maxConst a k)
  rw [nat_size_max, Nat.size_one] at h
  have h' : (a.pow k).maxConst.size ≤ a.maxConst.size+1 := h.trans (by omega)
  simp only [weight,pow_size,pow_sharedCost]
  nlinarith
lemma templateWidth_le (a : NatExpr v) (b : ℕ) :
    a.templateWidth b ≤ (b+a.weight+1)*a.weight := by
  exact Nat.mul_le_mul (by have := a.constSize_le_weight; omega) a.size_le_weight

lemma template_weight_count {k b c : ℕ} (a : NatExpr v)
    (vars : v → BooleanNetwork k b) (hc : ∀ i, (vars i).net.count ≤ c) :
    (a.template vars).net.count ≤
      a.weight*(operationBound ((b+a.weight+1)*a.weight)+c+(b+a.weight+1)*a.weight) := by
  have h := a.template_shared_count vars hc
  apply h.trans
  apply Nat.mul_le_mul a.sharedCost_le_weight
  have hw := a.templateWidth_le b
  dsimp [operationBound]
  gcongr
end NatExpr

/-- Uniform polynomial growth of a family of literal natural expressions.
Nothing here bounds the values of dynamic variables or assumes arithmetic is free. -/
def NatExprPoly {v : ℕ → Type*} (f : ∀ n, NatExpr (v n)) : Prop :=
  PolyBound (fun n => (f n).weight)

namespace NatExprPoly
variable {v : ℕ → Type*} {a b c d : ∀ n, NatExpr (v n)}
lemma var (i : ∀ n, v n) : NatExprPoly (fun n => .var (i n)) := by
  simpa only [NatExprPoly,NatExpr.weight_var] using PolyBound.const 2
lemma const {f : ℕ → ℕ} (h : PolyBound (fun n => (f n).size)) :
    NatExprPoly (fun n => NatExpr.const (f n) : ∀ n, NatExpr (v n)) := by
  simpa only [NatExprPoly,NatExpr.weight_const] using h.add (PolyBound.const 2)
lemma add (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .add (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_add (a n) (b n))
lemma sub (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .sub (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_sub (a n) (b n))
lemma mul (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .mul (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_mul (a n) (b n))
lemma div (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .div (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_div (a n) (b n))
lemma mod (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .mod (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_mod (a n) (b n))
lemma iteLe (ha : NatExprPoly a) (hb : NatExprPoly b) (hc : NatExprPoly c) (hd : NatExprPoly d) :
    NatExprPoly (fun n => .iteLe (a n) (b n) (c n) (d n)) :=
  ((PolyBound.const 2).mul ((((PolyBound.add ha hb).add hc).add hd).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_iteLe (a n) (b n) (c n) (d n))
lemma pow {f : ℕ → ℕ} (ha : NatExprPoly a) (hf : PolyBound f) :
    NatExprPoly (fun n => (a n).pow (f n)) :=
  ((hf.add (PolyBound.const 1)).mul (PolyBound.add ha (PolyBound.const 3))).of_le
    (fun n => NatExpr.weight_pow (a n) (f n))
lemma templateWidth {f : ℕ → ℕ} (ha : NatExprPoly a) (hf : PolyBound f) :
    PolyBound (fun n => (a n).templateWidth (f n)) :=
  (((hf.add ha).add (PolyBound.const 1)).mul ha).of_le
    (fun n => NatExpr.templateWidth_le (a n) (f n))
end NatExprPoly
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RationalExpressionResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring

namespace PolyBound
lemma twoPowSize {f : ℕ → ℕ} (hf : PolyBound f) :
    PolyBound (fun n => (2^(f n)).size) := by
  simpa only [Nat.size_pow] using hf.add (PolyBound.const 1)
end PolyBound

namespace NatExprPoly
variable {v : ℕ → Type*}
lemma ite (p : ℕ → Prop) [∀ n, Decidable (p n)] {a b : ∀ n, NatExpr (v n)}
    (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => if p n then a n else b n) := by
  change PolyBound _
  convert PolyBound.ite p ha hb using 1
  funext n; dsimp only; split_ifs <;> rfl
lemma constPoly {f : ℕ → ℕ} (hf : PolyBound f) :
    NatExprPoly (fun n => NatExpr.const (f n) : ∀ n, NatExpr (v n)) := const hf.natSize
end NatExprPoly

/-- All balanced integer components have polynomial literal circuit syntax. -/
def IntExprPoly {v : ℕ → Type*} (a : ∀ n, IntExpr (v n)) : Prop :=
  NatExprPoly (fun n => (a n).pos) ∧ NatExprPoly (fun n => (a n).neg)
namespace IntExprPoly
variable {v : ℕ → Type*} {a b c d : ∀ n, IntExpr (v n)}
lemma ofNat {f : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) :
    IntExprPoly (fun n => IntExpr.ofNat (f n)) :=
  ⟨hf, NatExprPoly.constPoly (PolyBound.const 0)⟩
lemma ofInt {f : ℕ → ℤ} (hf : PolyBound (fun n => (f n).natAbs.size)) :
    IntExprPoly (fun n => IntExpr.ofInt (f n) : ∀ n, IntExpr (v n)) := by
  constructor <;> apply NatExprPoly.const
  · exact hf.of_le (fun n => Nat.size_le_size (by omega))
  · exact hf.of_le (fun n => Nat.size_le_size (by omega))
lemma negation (ha : IntExprPoly a) : IntExprPoly (fun n => (a n).negation) := ⟨ha.2,ha.1⟩
lemma add (ha : IntExprPoly a) (hb : IntExprPoly b) : IntExprPoly (fun n => (a n).add (b n)) :=
  ⟨ha.1.add hb.1,ha.2.add hb.2⟩
lemma sub (ha : IntExprPoly a) (hb : IntExprPoly b) : IntExprPoly (fun n => (a n).sub (b n)) :=
  ha.add hb.negation
lemma mul (ha : IntExprPoly a) (hb : IntExprPoly b) : IntExprPoly (fun n => (a n).mul (b n)) :=
  ⟨(ha.1.mul hb.1).add (ha.2.mul hb.2),(ha.2.mul hb.1).add (ha.1.mul hb.2)⟩
lemma scale {f : ∀ n, NatExpr (v n)} (ha : IntExprPoly a) (hf : NatExprPoly f) :
    IntExprPoly (fun n => (a n).scale (f n)) := ha.mul (ofNat hf)
lemma toNat (ha : IntExprPoly a) : NatExprPoly (fun n => (a n).toNat) := ha.1.sub ha.2
lemma natAbs (ha : IntExprPoly a) : NatExprPoly (fun n => (a n).natAbs) :=
  (ha.1.sub ha.2).add (ha.2.sub ha.1)
lemma iteLe {f g : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) (hg : NatExprPoly g)
    (hc : IntExprPoly c) (hd : IntExprPoly d) :
    IntExprPoly (fun n => IntExpr.iteLe (f n) (g n) (c n) (d n)) :=
  ⟨hf.iteLe hg hc.1 hd.1,hf.iteLe hg hc.2 hd.2⟩
lemma ifLe (ha : IntExprPoly a) (hb : IntExprPoly b)
    (hc : IntExprPoly c) (hd : IntExprPoly d) :
    IntExprPoly (fun n => IntExpr.ifLe (a n) (b n) (c n) (d n)) :=
  iteLe (ha.1.add hb.2) (hb.1.add ha.2) hc hd
lemma ite (p : ℕ → Prop) [∀ n, Decidable (p n)] (ha : IntExprPoly a) (hb : IntExprPoly b) :
    IntExprPoly (fun n => if p n then a n else b n) := by
  constructor
  · convert NatExprPoly.ite p ha.1 hb.1 using 1; funext n; dsimp only; split_ifs <;> rfl
  · convert NatExprPoly.ite p ha.2 hb.2 using 1; funext n; dsimp only; split_ifs <;> rfl
lemma signedPower {f : ℕ → ℕ} (ha : IntExprPoly a) (hf : PolyBound f) :
    IntExprPoly (fun n => (a n).signedPower (f n)) :=
  ite (fun n => Even (f n)) (ofNat (ha.natAbs.pow hf))
    (iteLe ha.2 ha.1 (ofNat (ha.natAbs.pow hf)) (ofNat (ha.natAbs.pow hf)).negation)
lemma ceilRatioNat {f : ∀ n, NatExpr (v n)} (ha : IntExprPoly a) (hf : NatExprPoly f) :
    NatExprPoly (fun n => (a n).ceilRatioNat (f n)) :=
  ((ha.toNat.add hf).sub (NatExprPoly.constPoly (PolyBound.const 1))).div hf
lemma floorRatio {f : ∀ n, NatExpr (v n)} (ha : IntExprPoly a) (hf : NatExprPoly f) :
    IntExprPoly (fun n => (a n).floorRatio (f n)) :=
  (ofNat (ha.toNat.div hf)).sub (ofNat (ha.negation.ceilRatioNat hf))
end IntExprPoly

/-- Polynomial literal numerator and denominator syntax; no bound on dynamic values is assumed. -/
def RatExprPoly {v : ℕ → Type*} (a : ∀ n, RatExpr (v n)) : Prop :=
  IntExprPoly (fun n => (a n).num) ∧ NatExprPoly (fun n => (a n).den)
namespace RatExprPoly
variable {v : ℕ → Type*} {a b c d : ∀ n, RatExpr (v n)}
lemma ofNat {f : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) :
    RatExprPoly (fun n => RatExpr.ofNat (f n)) :=
  ⟨IntExprPoly.ofNat hf,NatExprPoly.constPoly (PolyBound.const 1)⟩
lemma ofInt {f : ∀ n, IntExpr (v n)} (hf : IntExprPoly f) :
    RatExprPoly (fun n => RatExpr.ofInt (f n)) :=
  ⟨hf,NatExprPoly.constPoly (PolyBound.const 1)⟩
lemma const {f : ℕ → ℚ} (hn : PolyBound (fun n => (f n).num.natAbs.size))
    (hd : PolyBound (fun n => (f n).den.size)) :
    RatExprPoly (fun n => RatExpr.const (f n) : ∀ n, RatExpr (v n)) :=
  ⟨IntExprPoly.ofInt hn,NatExprPoly.const hd⟩
lemma constant (r : ℚ) : RatExprPoly (fun _ => RatExpr.const r : ∀ n, RatExpr (v n)) :=
  const (PolyBound.const _) (PolyBound.const _)
lemma normalize (ha : RatExprPoly a) : RatExprPoly (fun n => (a n).normalize) :=
  ⟨IntExprPoly.iteLe ha.2 (NatExprPoly.constPoly (PolyBound.const 0))
    (IntExprPoly.ofInt (PolyBound.const 0)) ha.1,
   ha.2.iteLe (NatExprPoly.constPoly (PolyBound.const 0))
    (NatExprPoly.constPoly (PolyBound.const 1)) ha.2⟩
lemma add (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).add (b n)) :=
  ⟨(ha.normalize.1.scale hb.normalize.2).add (hb.normalize.1.scale ha.normalize.2),
    ha.normalize.2.mul hb.normalize.2⟩
lemma negation (ha : RatExprPoly a) : RatExprPoly (fun n => (a n).negation) := ⟨ha.1.negation,ha.2⟩
lemma sub (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).sub (b n)) :=
  ha.add hb.negation
lemma mul (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).mul (b n)) :=
  ⟨ha.1.mul hb.1,ha.2.mul hb.2⟩
lemma inverse (ha : RatExprPoly a) : RatExprPoly (fun n => (a n).inverse) :=
  ⟨ha.1.scale ha.2,ha.1.natAbs.mul ha.1.natAbs⟩
lemma div (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).div (b n)) :=
  ha.mul hb.inverse
lemma pow (ha : RatExprPoly a) (k : ℕ) : RatExprPoly (fun n => (a n).pow k) := by
  induction k with
  | zero => exact constant 1
  | succ k ih => exact ih.mul ha
lemma signedPower {f : ℕ → ℕ} (ha : RatExprPoly a) (hf : PolyBound f) :
    RatExprPoly (fun n => (a n).signedPower (f n)) := ⟨ha.1.signedPower hf,ha.2.pow hf⟩
lemma repeatedSuccess {f : ℕ → ℕ} (ha : RatExprPoly a) (hf : PolyBound f) :
    RatExprPoly (fun n => (a n).repeatedSuccess (f n)) :=
  (constant 1).sub (((constant 1).sub ha).signedPower hf)
lemma ifNatLe {f g : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) (hg : NatExprPoly g)
    (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifNatLe (f n) (g n) (c n) (d n)) :=
  ⟨IntExprPoly.iteLe hf hg hc.1 hd.1,hf.iteLe hg hc.2 hd.2⟩
lemma ifIntLe {f g : ∀ n, IntExpr (v n)} (hf : IntExprPoly f) (hg : IntExprPoly g)
    (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifIntLe (f n) (g n) (c n) (d n)) :=
  ifNatLe (hf.1.add hg.2) (hg.1.add hf.2) hc hd
lemma ifLe (ha : RatExprPoly a) (hb : RatExprPoly b) (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifLe (a n) (b n) (c n) (d n)) :=
  ifIntLe (ha.normalize.1.scale hb.normalize.2) (hb.normalize.1.scale ha.normalize.2) hc hd
lemma ifLt (ha : RatExprPoly a) (hb : RatExprPoly b) (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifLt (a n) (b n) (c n) (d n)) := hb.ifLe ha hd hc
lemma ifEq (ha : RatExprPoly a) (hb : RatExprPoly b) (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifEq (a n) (b n) (c n) (d n)) := ha.ifLe hb (hb.ifLe ha hc hd) hd
lemma max (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).max (b n)) :=
  ha.ifLe hb hb ha
lemma min (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).min (b n)) :=
  ha.ifLe hb ha hb
lemma ceilNat (ha : RatExprPoly a) : NatExprPoly (fun n => (a n).ceilNat) := ha.1.ceilRatioNat ha.2
lemma floor (ha : RatExprPoly a) : IntExprPoly (fun n => (a n).floor) := ha.1.floorRatio ha.2
lemma ceil (ha : RatExprPoly a) : IntExprPoly (fun n => (a n).ceil) := ha.negation.floor.negation
end RatExprPoly
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RationalHeightResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
lemma nat_size_mul_le (a b : ℕ) : (a*b).size ≤ a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.size_le.mp (le_refl b.size)).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.size_le.mp (le_refl a.size)) (by positivity))
lemma nat_size_add_le (a b : ℕ) : (a+b).size ≤ a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha : a<2^(a.size+b.size) :=
    (Nat.size_le.mp (le_refl a.size)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hb : b<2^(a.size+b.size) :=
    (Nat.size_le.mp (le_refl b.size)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  rw [pow_succ]
  omega
lemma nat_size_pow_le (a k : ℕ) : (a^k).size ≤ k*a.size+1 := by
  apply Nat.size_le.mpr
  have h : a^k ≤ (2^a.size)^k := Nat.pow_le_pow_left (Nat.size_le.mp (le_refl a.size)).le k
  rw [← pow_mul,Nat.mul_comm a.size] at h
  rw [pow_succ]
  have hp : 0<2^(k*a.size) := by positivity
  omega

namespace PolyBound
lemma sizeMul {f g : ℕ → ℕ} (hf : PolyBound (fun n => (f n).size))
    (hg : PolyBound (fun n => (g n).size)) : PolyBound (fun n => (f n*g n).size) :=
  (hf.add hg).of_le (fun n => nat_size_mul_le (f n) (g n))
lemma sizeAdd {f g : ℕ → ℕ} (hf : PolyBound (fun n => (f n).size))
    (hg : PolyBound (fun n => (g n).size)) : PolyBound (fun n => (f n+g n).size) :=
  ((hf.add hg).add (const 1)).of_le (fun n => nat_size_add_le (f n) (g n))
lemma sizePow {f g : ℕ → ℕ} (hf : PolyBound (fun n => (f n).size))
    (hg : PolyBound g) : PolyBound (fun n => (f n^g n).size) :=
  ((hg.mul hf).add (const 1)).of_le (fun n => nat_size_pow_le (f n) (g n))
end PolyBound

/-- Bit-length bounds for exact normalized rational constants appearing in the
emitted circuit. These are not bounds on their exponentially large values. -/
def RatHeightPoly (a : ℕ → ℚ) : Prop :=
  PolyBound (fun n => (a n).num.natAbs.size) ∧ PolyBound (fun n => (a n).den.size)
namespace RatHeightPoly
variable {a b : ℕ → ℚ}
lemma constant (q : ℚ) : RatHeightPoly (fun _=>q) := ⟨PolyBound.const _,PolyBound.const _⟩
lemma natCast {f : ℕ → ℕ} (hf : PolyBound (fun n=>(f n).size)) :
    RatHeightPoly (fun n => (f n : ℚ)) := by
  constructor
  · simpa using hf
  · exact PolyBound.of_le (PolyBound.const 1) (fun n => by simp)
lemma intCast {f : ℕ → ℤ} (hf : PolyBound (fun n=>(f n).natAbs.size)) :
    RatHeightPoly (fun n => (f n : ℚ)) := by
  constructor
  · simpa using hf
  · exact PolyBound.of_le (PolyBound.const 1) (fun n => by simp)
lemma add (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n+b n) := by
  constructor
  · apply ((ha.1.sizeMul hb.2).sizeAdd (hb.1.sizeMul ha.2)).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.num_add]
    apply (Int.natAbs_ediv_le_natAbs _ _).trans
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using
      (Int.natAbs_add_le ((a n).num*(b n).den) ((b n).num*(a n).den))
  · apply (ha.2.sizeMul hb.2).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.den_add]
    exact Nat.div_le_self _ _
lemma neg (ha : RatHeightPoly a) : RatHeightPoly (fun n=> -(a n)) := by
  constructor
  · simpa only [Rat.neg_num,Int.natAbs_neg] using ha.1
  · simpa only [Rat.neg_den] using ha.2
lemma sub (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n-b n) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg
lemma mul (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n*b n) := by
  constructor
  · apply (ha.1.sizeMul hb.1).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.mul_num]
    convert Int.natAbs_ediv_le_natAbs ((a n).num*(b n).num) _ using 1
    exact (Int.natAbs_mul _ _).symm
  · apply (ha.2.sizeMul hb.2).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.mul_den]
    exact Nat.div_le_self _ _
lemma inv (ha : RatHeightPoly a) : RatHeightPoly (fun n=>(a n)⁻¹) := by
  constructor
  · apply ha.2.of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_sign]
    split_ifs <;> simp
  · apply (ha.1.add (PolyBound.const 1)).of_le
    intro n
    rw [Rat.den_inv]
    split_ifs
    · simp only [Nat.size_one]; omega
    · omega
lemma div (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n/b n) := by
  simpa only [div_eq_mul_inv] using ha.mul hb.inv
lemma pow {f : ℕ→ℕ} (ha : RatHeightPoly a) (hf : PolyBound f) :
    RatHeightPoly (fun n=>(a n)^(f n)) := by
  constructor
  · simpa only [Rat.num_pow,Int.natAbs_pow] using ha.1.sizePow hf
  · simpa only [Rat.den_pow] using ha.2.sizePow hf
lemma constExpr {v : ℕ→Type*} (ha : RatHeightPoly a) :
    RatExprPoly (fun n=>RatExpr.const (a n) : ∀ n,RatExpr (v n)) :=
  RatExprPoly.const ha.1 ha.2
end RatHeightPoly
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/QuarterConstantResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
namespace RatHeightPoly
variable {a : ℕ→ℚ}
lemma floor (ha : RatHeightPoly a) : PolyBound (fun n=>(Int.floor (a n)).natAbs.size) := by
  apply ha.1.of_le
  intro n
  apply Nat.size_le_size
  rw [Rat.floor_def']
  exact Int.natAbs_ediv_le_natAbs _ _
end RatHeightPoly
namespace Exactness
lemma completionCoeff_height {E : ℕ→ℕ} {z A : ℕ→ℚ} (hE : PolyBound E)
    (hz : RatHeightPoly z) (hA : RatHeightPoly A) :
    RatHeightPoly (fun n=>completionCoeff (E n) (z n) (A n)) := by
  have hpow:=(RatHeightPoly.constant 2).pow hE
  exact (RatHeightPoly.intCast (hpow.mul (hz.div hA)).floor).div hpow
lemma quarterCoeff_height {J : ℕ→ℕ} {p : ℕ→ℚ} (hJ : PolyBound J) (hp : RatHeightPoly p) :
    RatHeightPoly (fun n=>quarterCoeff (J n) (p n)) :=
  completionCoeff_height (hJ.add (PolyBound.const 2)) (RatHeightPoly.constant (1/2)) hp
lemma quarterRemainder_height {J : ℕ→ℕ} {p : ℕ→ℚ} (hJ : PolyBound J) (hp : RatHeightPoly p) :
    RatHeightPoly (fun n=>quarterRemainder (J n) (p n)) :=
  (RatHeightPoly.constant (1/4)).sub ((hp.mul (quarterCoeff_height hJ hp)).div (RatHeightPoly.constant 2))
lemma knownProbability_height : RatHeightPoly knownProbability :=
  ((RatHeightPoly.constant 1).sub ((RatHeightPoly.constant 1).div
    ((RatHeightPoly.constant 2).pow PolyBound.id))).pow (PolyBound.id.pow 10)
end Exactness
namespace Quarter
lemma retention_height : RatHeightPoly retention :=
  Exactness.quarterCoeff_height (PolyBound.id.mul PolyBound.id) Exactness.knownProbability_height
lemma guessRetention_height : RatHeightPoly guessRetention :=
  ((RatHeightPoly.constant 2).pow ((PolyBound.id.mul PolyBound.id).add (PolyBound.const 1))).mul
    (Exactness.quarterRemainder_height (PolyBound.id.mul PolyBound.id) Exactness.knownProbability_height)
lemma D_poly : PolyBound D := by
  unfold D Completion.coinBits
  poly_bound
end Quarter
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PolynomialExpressionResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
namespace RatExprPoly
variable {v : ℕ → Type*}
lemma ite (p : ℕ → Prop) [∀ n, Decidable (p n)] {a b : ∀ n, RatExpr (v n)}
    (ha : RatExprPoly a) (hb : RatExprPoly b) :
    RatExprPoly (fun n => if p n then a n else b n) := by
  constructor
  · convert IntExprPoly.ite p ha.1 hb.1 using 1; funext n; dsimp only; split_ifs <;> rfl
  · convert NatExprPoly.ite p ha.2 hb.2 using 1; funext n; dsimp only; split_ifs <;> rfl
lemma sum {f : ℕ → ∀ n, RatExpr (v n)} (hf : ∀ i, RatExprPoly (f i)) (k : ℕ) :
    RatExprPoly (fun n => RatExpr.sum (fun i => f i n) k) := by
  induction k with
  | zero => exact constant 0
  | succ k ih => exact ih.add (hf k)
end RatExprPoly

/-- Every fixed-index coefficient of this family has polynomial syntax. -/
def PolyExprPoly {v : ℕ → Type*} (a : ∀ n, PolyExpr (v n)) : Prop :=
  ∀ k, RatExprPoly (fun n => (a n).coeff k)
namespace PolyExprPoly
variable {v : ℕ → Type*} {a b : ∀ n, PolyExpr (v n)}
lemma C {r : ∀ n, RatExpr (v n)} (hr : RatExprPoly r) : PolyExprPoly (fun n => .C (r n)) := by
  intro k
  by_cases h : k=0
  · simpa only [PolyExpr.coeff,ite_eq_left h] using hr
  · simpa only [PolyExpr.coeff,ite_eq_right h] using (RatExprPoly.constant (v:=v) 0)
lemma X : PolyExprPoly (fun _ => PolyExpr.X : ∀ n, PolyExpr (v n)) := by
  intro k
  by_cases h : k=1
  · simpa only [PolyExpr.coeff,ite_eq_left h] using (RatExprPoly.constant (v:=v) 1)
  · simpa only [PolyExpr.coeff,ite_eq_right h] using (RatExprPoly.constant (v:=v) 0)
lemma constant (r : ℚ) : PolyExprPoly (fun _ => PolyExpr.const r : ∀ n, PolyExpr (v n)) :=
  C (RatExprPoly.constant r)
lemma add (ha : PolyExprPoly a) (hb : PolyExprPoly b) : PolyExprPoly (fun n => (a n).add (b n)) :=
  fun k => (ha k).add (hb k)
lemma negation (ha : PolyExprPoly a) : PolyExprPoly (fun n => (a n).negation) :=
  fun k => (ha k).negation
lemma sub (ha : PolyExprPoly a) (hb : PolyExprPoly b) : PolyExprPoly (fun n => (a n).sub (b n)) :=
  ha.add hb.negation
lemma mul (ha : PolyExprPoly a) (hb : PolyExprPoly b) : PolyExprPoly (fun n => (a n).mul (b n)) :=
  fun k => RatExprPoly.sum (fun i => (ha i).mul (hb (k-i))) (k+1)
lemma pow (ha : PolyExprPoly a) (k : ℕ) : PolyExprPoly (fun n => (a n).pow k) := by
  induction k with
  | zero => exact constant 1
  | succ k ih => exact ih.mul ha
end PolyExprPoly

namespace OrderTrial.Expressions
variable {v : Type*}
lemma coveringPow_maxConst (d : NatExpr v) (k : ℕ) :
    (coveringPow d k).maxConst ≤ max d.maxConst (2^k) := by
  induction k with
  | zero => exact le_max_right _ _
  | succ k ih =>
    have h : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact max_le (max_le (le_max_left _ _) (h.trans (le_max_right _ _)))
      (max_le (ih.trans (max_le_max_left _ h)) (le_max_right _ _))
lemma coveringPow_weight (d : NatExpr v) (k : ℕ) :
    (coveringPow d k).weight ≤ (k+1)*(d.weight+7) := by
  have h := Nat.size_le_size (coveringPow_maxConst d k)
  rw [nat_size_max,Nat.size_pow] at h
  have hh : (coveringPow d k).maxConst.size ≤ d.maxConst.size+k+1 := h.trans (by omega)
  simp only [NatExpr.weight,coveringPow_size,coveringPow_sharedCost]
  nlinarith
lemma coveringPow_poly {v : ℕ → Type*} {d : ∀ n, NatExpr (v n)} {f : ℕ → ℕ}
    (hd : NatExprPoly d) (hf : PolyBound f) :
    NatExprPoly (fun n => coveringPow (d n) (f n)) :=
  ((hf.add (PolyBound.const 1)).mul (PolyBound.add hd (PolyBound.const 7))).of_le
    (fun n => coveringPow_weight (d n) (f n))
end OrderTrial.Expressions

syntax "expr_poly" : tactic
macro_rules
  | `(tactic| expr_poly) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact NatExprPoly.var _
    | exact RatExprPoly.constant _
    | exact PolyExprPoly.X
    | exact PolyExprPoly.constant _
    | (apply RatExprPoly.ofNat; expr_poly)
    | (apply RatExprPoly.ofInt; expr_poly)
    | (apply RatExprPoly.normalize; expr_poly)
    | (apply RatExprPoly.add <;> expr_poly)
    | (apply RatExprPoly.sub <;> expr_poly)
    | (apply RatExprPoly.mul <;> expr_poly)
    | (apply RatExprPoly.negation; expr_poly)
    | (apply RatExprPoly.inverse; expr_poly)
    | (apply RatExprPoly.div <;> expr_poly)
    | (apply RatExprPoly.pow; expr_poly)
    | (apply RatExprPoly.ifNatLe <;> expr_poly)
    | (apply RatExprPoly.ifIntLe <;> expr_poly)
    | (apply RatExprPoly.ifLe <;> expr_poly)
    | (apply RatExprPoly.ifLt <;> expr_poly)
    | (apply RatExprPoly.ifEq <;> expr_poly)
    | (apply RatExprPoly.max <;> expr_poly)
    | (apply RatExprPoly.min <;> expr_poly)
    | (apply IntExprPoly.ofNat; expr_poly)
    | (apply IntExprPoly.add <;> expr_poly)
    | (apply IntExprPoly.sub <;> expr_poly)
    | (apply IntExprPoly.mul <;> expr_poly)
    | (apply IntExprPoly.scale <;> expr_poly)
    | (apply IntExprPoly.negation; expr_poly)
    | (apply IntExprPoly.iteLe <;> expr_poly)
    | (apply IntExprPoly.ifLe <;> expr_poly)
    | (apply IntExprPoly.toNat; expr_poly)
    | (apply IntExprPoly.natAbs; expr_poly)
    | (apply IntExprPoly.ceilRatioNat <;> expr_poly)
    | (apply IntExprPoly.floorRatio <;> expr_poly)
    | (apply RatExprPoly.ceilNat; expr_poly)
    | (apply RatExprPoly.floor; expr_poly)
    | (apply RatExprPoly.ceil; expr_poly)
    | (apply PolyExprPoly.C; expr_poly)
    | (apply PolyExprPoly.add <;> expr_poly)
    | (apply PolyExprPoly.sub <;> expr_poly)
    | (apply PolyExprPoly.mul <;> expr_poly)
    | (apply PolyExprPoly.negation; expr_poly)
    | (apply PolyExprPoly.pow; expr_poly)
    | (apply NatExprPoly.add <;> expr_poly)
    | (apply NatExprPoly.sub <;> expr_poly)
    | (apply NatExprPoly.mul <;> expr_poly)
    | (apply NatExprPoly.div <;> expr_poly)
    | (apply NatExprPoly.mod <;> expr_poly)
    | (apply NatExprPoly.iteLe <;> expr_poly)
    | (apply NatExprPoly.const; poly_bound))
end ExactQuantumFactoring

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ConcreteExpressionResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
namespace PolyExpr
variable {v : Type*}
lemma comp_X (a : PolyExpr v) : a.comp X=a := by
  induction a with
  | C c => rfl
  | X => rfl
  | add a b ia ib => simp only [comp,ia,ib]
  | negation a ia => simp only [comp,ia]
  | mul a b ia ib => simp only [comp,ia,ib]
lemma comp_comp (a b c : PolyExpr v) : (a.comp b).comp c=a.comp (b.comp c) := by
  induction a with
  | C r => rfl
  | X => rfl
  | add a b ia ib => simp only [comp,ia,ib]
  | negation a ia => simp only [comp,ia]
  | mul a b ia ib => simp only [comp,ia,ib]
end PolyExpr

/-- Substitution-stable, fixed-depth polynomial schemas. In particular this
controls the literal syntax of every fixed coefficient, not just its denotation. -/
def PolySchemaPoly {v : ℕ → Type*} (a : ∀ n, PolyExpr (v n)) : Prop :=
  ∀ b : ∀ n, PolyExpr (v n), PolyExprPoly b → PolyExprPoly (fun n => (a n).comp (b n))

end ExactQuantumFactoring
end

end OAI
