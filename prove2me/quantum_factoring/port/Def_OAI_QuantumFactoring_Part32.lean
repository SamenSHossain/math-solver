/-
Exact quantum factoring development (port of OpenAI's formalization), part 32 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: NativeAIGBinaryInputs.lean, AIGBitArithmeticEmission.lean, ExpressionPostfix.lean, BitStackSumInjection.lean, ExpressionSyntaxEmission.lean, EmissionCombinators.lean, NetworkResizeEmission.lean, NetworkEmissionCombinators.lean, EmissionFurther.lean, ExpressionTokenProcedure.lean, ExpressionTemplateEmission.lean, EmissionLists.lean, NetworkExpressionEmission.lean, NetworkLoopEmission.lean, NetworkIndexedEmission.lean, NetworkModularEmission.lean, NetworkPredicateEmission.lean, BitStackBoundedPrime.lean, Emits.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part31

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGBinaryInputs.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure Std.Sat
lemma rawInputs_bound (n : ℕ) : Bounded (n+1) (rawInputs n):=by
  refine ⟨by simp [rawInputs],by simp [rawInputs],?_,by simp [rawInputs]⟩
  intro d hd
  simp only [rawInputs,List.mem_cons,List.mem_map] at hd
  rcases hd with rfl | ⟨i,hi,rfl⟩
  · trivial
  · have hi:=List.mem_range.mp hi
    change i≤n+1
    omega

def rawWord (offset w : ℕ) : List Ref:=(List.range w).map (fun i=>(offset+i+1,false))
lemma rawWord_bound (o w : ℕ) : RefsBound (o+w+1) (rawWord o w):=by
  refine ⟨by simp [rawWord];omega,?_⟩
  intro a ha
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
  have hi:=List.mem_range.mp hi
  dsimp only
  omega
def binaryInput (w : ℕ) : BinaryState:=⟨⟨⟨w+w+1,rawInputs (w+w),rawWord 0 w,rawWord w w,0,(0,false),[]⟩,
  rawInputs_bound _,(rawWord_bound 0 w).mono (by change 0+w+1≤w+w+1;omega),rawWord_bound w w,
  Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩,by simp [rawWord]⟩
lemma eraseVec_binaryInputs_lhs (w : ℕ) : eraseVec (BitArithmetic.binaryInputs w).lhs=rawWord 0 w:=by
  unfold eraseVec BitArithmetic.binaryInputs
  simp only [AIGCompiler.refVector_get,inputs_ref,Fin.val_castAdd]
  rw [rawWord,←ofFn_val_range,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply,Nat.zero_add]
lemma eraseVec_binaryInputs_rhs (w : ℕ) : eraseVec (BitArithmetic.binaryInputs w).rhs=rawWord w w:=by
  unfold eraseVec BitArithmetic.binaryInputs
  simp only [AIGCompiler.refVector_get,inputs_ref,Fin.val_natAdd]
  rw [rawWord,←ofFn_val_range,List.map_ofFn]
  rfl
namespace Emission
noncomputable def rawWordP : Procedure (prodCode unaryCode unaryCode) (listCode refCode)
    (fun x=>rawWord x.1 x.2):=by
  let p:=(successor.comp (binaryAdd.comp
    ((unaryToBits.comp (second unaryCode unaryCode)).pair (unaryToBits.comp (first unaryCode unaryCode))))).pair
      (Procedure.constant _ boolCode false)
  exact ((tabulate (f:=fun o i=>(o+i+1,false)) (0,false) p).comp
    ((second unaryCode unaryCode).pair (first unaryCode unaryCode))).congrFun (by intro x;rfl)
noncomputable def binaryInputP : Procedure unaryCode binaryStateCode binaryInput:=by
  let w:=identity unaryCode
  let two:=unaryAdd.comp (w.pair w)
  let b:=unarySuccessor.comp two
  let g:=inputsP.comp two
  let l:=rawWordP.comp ((Procedure.constant _ unaryCode 0).pair w)
  let r:=rawWordP.comp (w.pair w)
  exact (packAddP.comp (b.pair (g.pair (l.pair (r.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro n;rfl)
noncomputable def inputAddP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>add (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (addP.comp (((identity addStateCode).precompose (fun s:BinaryState=>s.val)).comp binaryInputP)).congrFun ?_
  intro w
  change add (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputMulP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>mul (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (mulP.comp binaryInputP).congrFun ?_
  intro w
  change mul (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputSubP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>sub (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (subP.comp binaryInputP).congrFun ?_
  intro w
  change sub (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputDivP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>divide (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (divideP.comp binaryInputP).congrFun ?_
  intro w
  change divide (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputModP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>remainder (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (remainderP.comp binaryInputP).congrFun ?_
  intro w
  change remainder (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AIGBitArithmeticEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open BitStackProgram BitStackProgram.Procedure NetworkEmission

def binaryPack (op : NativeAIG.Graph→List NativeAIG.Ref→List NativeAIG.Ref→NativeAIG.Graph×List NativeAIG.Ref)
    (w : ℕ) : Pack:=
  let r:=op (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)
  compilePack (w+w) r.1.decls r.2
lemma binaryPack_value (op : NativeAIG.Graph→List NativeAIG.Ref→List NativeAIG.Ref→NativeAIG.Graph×List NativeAIG.Ref)
    (w : ℕ) (res : AIG.RefVecEntry (Fin (w+w)) w)
    (hr : NativeAIG.VecRel (op (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)) res) :
    (binaryPack op w).val.value=erase (AIGCompiler.compileVec res.aig res.vec):=by
  dsimp only [binaryPack]
  rw [hr.2]
  exact compilePack_value hr.1 _
lemma addPack_value (w : ℕ) : (binaryPack NativeAIG.add w).val.value=erase (BitArithmetic.add w):=by
  apply binaryPack_value
  have hh:=NativeAIG.add_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma mulPack_value (w : ℕ) : (binaryPack NativeAIG.mul w).val.value=erase (BitArithmetic.mul w):=by
  apply binaryPack_value
  have hh:=NativeAIG.mul_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma subPack_value (w : ℕ) : (binaryPack NativeAIG.sub w).val.value=erase (BitArithmetic.sub w):=by
  apply binaryPack_value
  have hh:=NativeAIG.sub_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma divPack_value (w : ℕ) : (binaryPack NativeAIG.divide w).val.value=erase (BitArithmetic.div w):=by
  apply binaryPack_value
  have hh:=NativeAIG.divide_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma modPack_value (w : ℕ) : (binaryPack NativeAIG.remainder w).val.value=erase (BitArithmetic.mod w):=by
  apply binaryPack_value
  have hh:=NativeAIG.remainder_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh

def ultPack (w : ℕ) : Pack:=
  let r:=NativeAIG.ult (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)
  compilePack (w+w) r.1.decls [r.2]
lemma ultPack_value (w : ℕ) : (ultPack w).val.value=erase (BitArithmetic.ult w):=by
  have hr:=NativeAIG.ult_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simp only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] at hr
  unfold ultPack BitArithmetic.ult
  have hh:=compilePack_value hr.1 (fun _ : Fin 1=>(Std.Tactic.BVDecide.BVPred.mkUlt
    (AIGCompiler.inputs (w+w)).1 (BitArithmetic.binaryInputs w)).ref)
  simpa only [List.ofFn_succ,List.ofFn_zero,hr.2] using hh

namespace Emission
noncomputable def binaryPackP
    {op : NativeAIG.Graph→List NativeAIG.Ref→List NativeAIG.Ref→NativeAIG.Graph×List NativeAIG.Ref}
    (p : Procedure unaryCode (prodCode NativeAIG.graphCode (listCode NativeAIG.refCode))
      (fun w=>op (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w))) :
    Procedure unaryCode packCode (binaryPack op):=by
  let width:=unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  let graph:=(first NativeAIG.graphCode (listCode NativeAIG.refCode)).comp p
  let ds:=NativeAIG.Emission.decls.comp graph
  let refs:=(second NativeAIG.graphCode (listCode NativeAIG.refCode)).comp p
  exact compilePackP.comp ((width.pair ds).pair refs)
noncomputable def addPackP : Procedure unaryCode packCode (binaryPack NativeAIG.add):=binaryPackP NativeAIG.Emission.inputAddP
noncomputable def mulPackP : Procedure unaryCode packCode (binaryPack NativeAIG.mul):=binaryPackP NativeAIG.Emission.inputMulP
noncomputable def subPackP : Procedure unaryCode packCode (binaryPack NativeAIG.sub):=binaryPackP NativeAIG.Emission.inputSubP
noncomputable def divPackP : Procedure unaryCode packCode (binaryPack NativeAIG.divide):=binaryPackP NativeAIG.Emission.inputDivP
noncomputable def modPackP : Procedure unaryCode packCode (binaryPack NativeAIG.remainder):=binaryPackP NativeAIG.Emission.inputModP
noncomputable def inputUltP : Procedure unaryCode (prodCode NativeAIG.graphCode NativeAIG.refCode)
    (fun w=>NativeAIG.ult (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)):=by
  refine (NativeAIG.Emission.ultP.comp (((identity NativeAIG.addStateCode).precompose
    (fun s:NativeAIG.BinaryState=>s.val)).comp NativeAIG.Emission.binaryInputP)).congrFun ?_
  intro w
  change NativeAIG.ult (NativeAIG.binaryInput w).val.val.graph (NativeAIG.binaryInput w).val.val.lhs
    (NativeAIG.binaryInput w).val.val.rhs=_
  congr 1
noncomputable def ultPackP : Procedure unaryCode packCode ultPack:=by
  let width:=unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  let ds:=NativeAIG.Emission.decls.comp ((first NativeAIG.graphCode NativeAIG.refCode).comp inputUltP)
  let ref:=(second NativeAIG.graphCode NativeAIG.refCode).comp inputUltP
  let refs:=(listCons NativeAIG.refCode).comp (ref.pair (Procedure.constant _ (listCode NativeAIG.refCode) []))
  exact compilePackP.comp ((width.pair ds).pair refs)
end Emission
end ExactQuantumFactoring.AIGNetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExpressionPostfix.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
open AIGNetworkEmission

/-- Variables, scalar constants, and the fixed algebra instruction vocabulary. -/
abbrev ExprToken (v : Type) := v ⊕ (ℕ ⊕ ℕ)
def exprTokenCode {v : Type} (ev : v→List Bool) : ExprToken v→List Bool:=sumCode ev (sumCode Nat.bits Nat.bits)
def pairToken {v : Type} : ExprToken v:=.inr (.inr 0)
def compToken {v : Type} : ExprToken v:=.inr (.inr 1)
def opToken {v : Type} (j : ℕ) : ExprToken v:=.inr (.inr (j+2))
def primPack (w : ℕ) : ℕ→Pack
  | 0=>binaryPack NativeAIG.add w
  | 1=>binaryPack NativeAIG.mul w
  | 2=>binaryPack NativeAIG.sub w
  | 3=>binaryPack NativeAIG.divide w
  | 4=>binaryPack NativeAIG.remainder w
  | 5=>ultPack w
  | 6=>nodePack 1 (.neg 0) (by simp [Node.Bound])
  | _=>vectorPack (1+w+w) ((List.range w).map (fun i=>muxPack (bitPack (1+w+w) 0)
      (bitPack (1+w+w) (1+i)) (bitPack (1+w+w) (1+w+i))))
def tokenOp {v : Type} (n w : ℕ) (vars : v→Pack) : ExprToken v→StackOp
  | .inl i=>.inl (vars i)
  | .inr (.inl c)=>.inl (wordConstPack n w c)
  | .inr (.inr 0)=>.inr false
  | .inr (.inr 1)=>.inr true
  | .inr (.inr (j+2))=>.inl (primPack w j)
def exprRun {v : Type} (n w : ℕ) (vars : v→Pack) (ts : List (ExprToken v)) (s : List Pack) : List Pack:=
  (ts.map (tokenOp n w vars)).foldl (fun s o=>stackStep o s) s
lemma exprRun_append {v : Type} (n w : ℕ) (vars : v→Pack) (ts us : List (ExprToken v)) (s : List Pack) :
    exprRun n w vars (ts++us) s=exprRun n w vars us (exprRun n w vars ts s):=by
  simp only [exprRun,List.map_append,List.foldl_append]
def Produces {v : Type} (n w : ℕ) (vars : v→Pack) (ts : List (ExprToken v)) (p : Pack) : Prop:=
  ∀s,exprRun n w vars ts s=p::s
lemma produces_var {v : Type} (n w : ℕ) (vars : v→Pack) (i : v) : Produces n w vars [.inl i] (vars i):=by
  intro s;rfl
lemma produces_const {v : Type} (n w : ℕ) (vars : v→Pack) (c : ℕ) :
    Produces n w vars [.inr (.inl c)] (wordConstPack n w c):=by intro s;rfl
lemma produces_op {v : Type} {n w : ℕ} {vars : v→Pack} {ts : List (ExprToken v)} {a : Pack}
    (ha : Produces n w vars ts a) (j : ℕ) :
    Produces n w vars (ts++[opToken j,compToken]) (compPack a (primPack w j)):=by
  intro s;rw [exprRun_append,ha];rfl
lemma produces_pair {v : Type} {n w : ℕ} {vars : v→Pack} {ts us : List (ExprToken v)} {a b : Pack}
    (ha : Produces n w vars ts a) (hb : Produces n w vars us b) :
    Produces n w vars (ts++us++[pairToken]) (pairPack a b):=by
  intro s;rw [exprRun_append,exprRun_append,ha,hb];rfl
lemma produces_binary {v : Type} {n w : ℕ} {vars : v→Pack} {ts us : List (ExprToken v)} {a b : Pack}
    (ha : Produces n w vars ts a) (hb : Produces n w vars us b) (j : ℕ) :
    Produces n w vars ((ts++us++[pairToken])++[opToken j,compToken]) (compPack (pairPack a b) (primPack w j)):=
  produces_op (produces_pair ha hb) j

def leTokens {v : Type} (a b : List (ExprToken v)) : List (ExprToken v):=
  ((b++a++[pairToken])++[opToken 5,compToken])++[opToken 6,compToken]
def muxTokens {v : Type} (c a b : List (ExprToken v)) : List (ExprToken v):=
  (((c++a++[pairToken])++b++[pairToken])++[opToken 7,compToken])
def lePack (w : ℕ) (a b : Pack) : Pack:=bnotPack (compPack (pairPack b a) (ultPack w))
lemma produces_le {v : Type} {n w : ℕ} {vars : v→Pack} {ts us : List (ExprToken v)} {a b : Pack}
    (ha : Produces n w vars ts a) (hb : Produces n w vars us b) :
    Produces n w vars (leTokens ts us) (lePack w a b):=
  produces_op (produces_binary hb ha 5) 6
lemma produces_mux {v : Type} {n w : ℕ} {vars : v→Pack} {ts us vs : List (ExprToken v)} {c a b : Pack}
    (hc : Produces n w vars ts c) (ha : Produces n w vars us a) (hb : Produces n w vars vs b) :
    Produces n w vars (muxTokens ts us vs) (wordMuxPack w c a b):=
  produces_op (produces_pair (produces_pair hc ha) hb) 7

def exprTokens {v : Type} : NatExpr v→List (ExprToken v)
  | .var i=>[.inl i]
  | .const c=>[.inr (.inl c)]
  | .add a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 0,compToken])
  | .mul a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 1,compToken])
  | .sub a b=>muxTokens (leTokens (exprTokens b) (exprTokens a))
      ((exprTokens a++exprTokens b++[pairToken])++[opToken 2,compToken]) [.inr (.inl 0)]
  | .div a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 3,compToken])
  | .mod a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 4,compToken])
  | .iteLe a b c d=>muxTokens (leTokens (exprTokens a) (exprTokens b)) (exprTokens c) (exprTokens d)
def exprPack {v : Type} (n w : ℕ) (vars : v→Pack) : NatExpr v→Pack
  | .var i=>vars i
  | .const c=>wordConstPack n w c
  | .add a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.add w)
  | .mul a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.mul w)
  | .sub a b=>wordMuxPack w (lePack w (exprPack n w vars b) (exprPack n w vars a))
      (compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.sub w)) (wordConstPack n w 0)
  | .div a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.divide w)
  | .mod a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.remainder w)
  | .iteLe a b c d=>wordMuxPack w (lePack w (exprPack n w vars a) (exprPack n w vars b))
      (exprPack n w vars c) (exprPack n w vars d)
lemma exprTokens_produces {v : Type} (n w : ℕ) (vars : v→Pack) (e : NatExpr v) :
    Produces n w vars (exprTokens e) (exprPack n w vars e):=by
  induction e with
  | var i=>exact produces_var n w vars i
  | const c=>exact produces_const n w vars c
  | add a b ha hb=>exact produces_binary ha hb 0
  | mul a b ha hb=>exact produces_binary ha hb 1
  | div a b ha hb=>exact produces_binary ha hb 3
  | mod a b ha hb=>exact produces_binary ha hb 4
  | sub a b ha hb=>exact produces_mux (produces_le hb ha) (produces_binary ha hb 2) (produces_const n w vars 0)
  | iteLe a b c d ha hb hc hd=>exact produces_mux (produces_le ha hb) hc hd
lemma lePack_value {n w : ℕ} (a b : Pack) (f g : BooleanNetwork n w)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (lePack w a b).val.value=erase (BitArithmetic.wordLe f g):=
  bnotPack_value _ _ (compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ hb ha) (ultPack_value w))
lemma exprPack_value {v : Type} {n w : ℕ} (vars : v→Pack) (fs : v→BooleanNetwork n w)
    (hf : ∀i,(vars i).val.value=erase (fs i)) (e : NatExpr v) :
    (exprPack n w vars e).val.value=erase (e.compile fs):=by
  induction e with
  | var i=>exact hf i
  | const c=>exact wordConstPack_value n w c
  | add a b ha hb=>exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ ha hb) (addPack_value w)
  | mul a b ha hb=>exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ ha hb) (mulPack_value w)
  | div a b ha hb=>exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ ha hb) (divPack_value w)
  | mod a b ha hb=>exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ ha hb) (modPack_value w)
  | sub a b ha hb=>
    exact wordMuxPack_value _ _ _ _ _ _ (lePack_value _ _ _ _ hb ha)
      (compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ ha hb) (subPack_value w)) (wordConstPack_value n w 0)
  | iteLe a b c d ha hb hc hd=>exact wordMuxPack_value _ _ _ _ _ _ (lePack_value _ _ _ _ ha hb) hc hd
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackSumInjection.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Procedure
noncomputable def sumLeft {α β : Type} (ea : α→List Bool) (eb : β→List Bool) :
    Procedure ea (sumCode ea eb) Sum.inl:=
  (prepend ea [false]).result (by intro a;rfl)
noncomputable def sumRight {α β : Type} (ea : α→List Bool) (eb : β→List Bool) :
    Procedure eb (sumCode ea eb) Sum.inr:=
  (prepend eb [true]).result (by intro a;rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExpressionSyntaxEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
variable {v : Type}
def exprView (e : NatExpr v) := (e.size,e.maxConst,exprTokens e)
def exprPayload (ev : v→List Bool):=prodCode unaryCode (prodCode Nat.bits (listCode (exprTokenCode ev)))
def exprCode (ev : v→List Bool) (e : NatExpr v):=exprPayload ev (exprView e)
namespace Emission
variable (ev : v→List Bool)
noncomputable def exprViewP : Procedure (exprCode ev) (exprPayload ev) exprView:=
  (identity (exprPayload ev)).precompose exprView
noncomputable def exprSizeP : Procedure (exprCode ev) unaryCode NatExpr.size:=
  (first unaryCode _).comp (exprViewP ev)
noncomputable def exprMaxP : Procedure (exprCode ev) Nat.bits NatExpr.maxConst:=
  (first Nat.bits _).comp ((second unaryCode _).comp (exprViewP ev))
noncomputable def exprTokensP : Procedure (exprCode ev) (listCode (exprTokenCode ev)) exprTokens:=
  (second Nat.bits _).comp ((second unaryCode _).comp (exprViewP ev))
noncomputable def binaryMax : Procedure (prodCode Nat.bits Nat.bits) Nat.bits (fun x=>max x.1 x.2):=
  (conditional binaryLe (second Nat.bits Nat.bits) (first Nat.bits Nat.bits)).congrFun (by
    intro x;simp only [decide_eq_true_eq];split_ifs with h
    · exact (max_eq_right h).symm
    · exact (max_eq_left (by omega)).symm)
noncomputable def exprVarP : Procedure ev (exprCode ev) NatExpr.var:=by
  let token:=(sumLeft ev (sumCode Nat.bits Nat.bits))
  let ts:=(listCons (exprTokenCode ev)).comp (token.pair (Procedure.constant ev (listCode (exprTokenCode ev)) []))
  exact ((Procedure.constant ev unaryCode 1).pair ((Procedure.constant ev Nat.bits 0).pair ts)).result (by intro i;rfl)
noncomputable def constTokenP : Procedure Nat.bits (exprTokenCode ev) (fun c=>Sum.inr (Sum.inl c)):=
  (sumRight ev (sumCode Nat.bits Nat.bits)).comp (sumLeft Nat.bits Nat.bits)
noncomputable def exprConstP : Procedure Nat.bits (exprCode ev) NatExpr.const:=by
  let ts:=(listCons (exprTokenCode ev)).comp ((constTokenP ev).pair (Procedure.constant Nat.bits (listCode (exprTokenCode ev)) []))
  exact ((Procedure.constant Nat.bits unaryCode 1).pair ((identity Nat.bits).pair ts)).result (by intro i;rfl)
noncomputable def tokensAppendP : Procedure (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
    (listCode (exprTokenCode ev)) (fun x=>x.1++x.2):=listAppend _ (opToken 0)
noncomputable def tokensPairP : Procedure (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
    (listCode (exprTokenCode ev)) (fun x=>x.1++x.2++[pairToken]):=
  (tokensAppendP ev).comp ((tokensAppendP ev).pair (Procedure.constant _ _ [pairToken]))
noncomputable def tokensOpP (j : ℕ) : Procedure (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))
    (fun ts=>ts++[opToken j,compToken]):=
  (tokensAppendP ev).comp ((identity _).pair (Procedure.constant _ _ [opToken j,compToken]))
noncomputable def tokensLeP : Procedure (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
    (listCode (exprTokenCode ev)) (fun x=>leTokens x.1 x.2):=
  (tokensOpP ev 6).comp ((tokensOpP ev 5).comp ((tokensPairP ev).comp
    ((second _ _).pair (first _ _))))
noncomputable def tokensMuxP : Procedure (prodCode (listCode (exprTokenCode ev))
    (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))))
    (listCode (exprTokenCode ev)) (fun x=>muxTokens x.1 x.2.1 x.2.2):=by
  let a:=first (listCode (exprTokenCode ev)) (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
  let rs:=second (listCode (exprTokenCode ev)) (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
  let b:=(first (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))).comp rs
  let c:=(second (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))).comp rs
  exact (tokensOpP ev 7).comp ((tokensPairP ev).comp (((tokensPairP ev).comp (a.pair b)).pair c))
noncomputable def exprBinaryP (j : ℕ) (f : NatExpr v→NatExpr v→NatExpr v)
    (hs : ∀a b,(f a b).size=a.size+b.size+1)
    (hm : ∀a b,(f a b).maxConst=max a.maxConst b.maxConst)
    (ht : ∀a b,exprTokens (f a b)=exprTokens a++exprTokens b++[pairToken]++[opToken j,compToken]) :
    Procedure (prodCode (exprCode ev) (exprCode ev)) (exprCode ev) (fun x=>f x.1 x.2):=by
  let a:=first (exprCode ev) (exprCode ev)
  let b:=second (exprCode ev) (exprCode ev)
  let sz:=unarySuccessor.comp (unaryAdd.comp (((exprSizeP ev).comp a).pair ((exprSizeP ev).comp b)))
  let mx:=binaryMax.comp (((exprMaxP ev).comp a).pair ((exprMaxP ev).comp b))
  let ts:=(tokensOpP ev j).comp ((tokensPairP ev).comp (((exprTokensP ev).comp a).pair ((exprTokensP ev).comp b)))
  exact (sz.pair (mx.pair ts)).result (by intro x;simp only [exprCode,exprView,hs,hm,ht];rfl)
noncomputable def exprAddP:=exprBinaryP ev 0 NatExpr.add (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprMulP:=exprBinaryP ev 1 NatExpr.mul (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprDivP:=exprBinaryP ev 3 NatExpr.div (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprModP:=exprBinaryP ev 4 NatExpr.mod (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprSubP : Procedure (prodCode (exprCode ev) (exprCode ev)) (exprCode ev) (fun x=>NatExpr.sub x.1 x.2):=by
  let a:=first (exprCode ev) (exprCode ev)
  let b:=second (exprCode ev) (exprCode ev)
  let sz:=unarySuccessor.comp (unaryAdd.comp (((exprSizeP ev).comp a).pair ((exprSizeP ev).comp b)))
  let mx:=binaryMax.comp (((exprMaxP ev).comp a).pair ((exprMaxP ev).comp b))
  let as':=(exprTokensP ev).comp a
  let bs:=(exprTokensP ev).comp b
  let test:=(tokensLeP ev).comp (bs.pair as')
  let sub:=(tokensOpP ev 2).comp ((tokensPairP ev).comp (as'.pair bs))
  let z:=Procedure.constant (prodCode (exprCode ev) (exprCode ev)) (listCode (exprTokenCode ev)) [.inr (.inl 0)]
  exact (sz.pair (mx.pair ((tokensMuxP ev).comp (test.pair (sub.pair z))))).result (by intro x;rfl)
noncomputable def exprIteP : Procedure (prodCode (exprCode ev) (prodCode (exprCode ev) (prodCode (exprCode ev) (exprCode ev))))
    (exprCode ev) (fun x=>NatExpr.iteLe x.1 x.2.1 x.2.2.1 x.2.2.2):=by
  let a:=first (exprCode ev) (prodCode (exprCode ev) (prodCode (exprCode ev) (exprCode ev)))
  let rs:=second (exprCode ev) (prodCode (exprCode ev) (prodCode (exprCode ev) (exprCode ev)))
  let b:=(first (exprCode ev) (prodCode (exprCode ev) (exprCode ev))).comp rs
  let rt:=(second (exprCode ev) (prodCode (exprCode ev) (exprCode ev))).comp rs
  let c:=(first (exprCode ev) (exprCode ev)).comp rt
  let d:=(second (exprCode ev) (exprCode ev)).comp rt
  let sz:=unarySuccessor.comp (unaryAdd.comp ((unaryAdd.comp ((unaryAdd.comp (((exprSizeP ev).comp a).pair
    ((exprSizeP ev).comp b))).pair ((exprSizeP ev).comp c))).pair ((exprSizeP ev).comp d)))
  let mx:=binaryMax.comp ((binaryMax.comp (((exprMaxP ev).comp a).pair ((exprMaxP ev).comp b))).pair
    (binaryMax.comp (((exprMaxP ev).comp c).pair ((exprMaxP ev).comp d))))
  let test:=(tokensLeP ev).comp (((exprTokensP ev).comp a).pair ((exprTokensP ev).comp b))
  let ts:=(tokensMuxP ev).comp (test.pair (((exprTokensP ev).comp c).pair ((exprTokensP ev).comp d)))
  exact (sz.pair (mx.pair ts)).result (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/EmissionCombinators.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
/-- Existence of a charged, clean, finite-alphabet stack procedure. -/
def Emits {α β : Type} (ea : α→List Bool) (eb : β→List Bool) (f : α→β) : Prop :=
  Nonempty (Procedure ea eb f)
namespace Emits
variable {α β γ δ : Type} {ea : α→List Bool} {eb : β→List Bool}
  {ec : γ→List Bool} {ed : δ→List Bool}
lemma ofProcedure {f : α→β} (p : Procedure ea eb f) : Emits ea eb f:=⟨p⟩
lemma id (e : α→List Bool) : Emits e e (fun x=>x):=⟨Procedure.identity e⟩
lemma const (ea : α→List Bool) (eb : β→List Bool) (b : β) : Emits ea eb (fun _=>b):=⟨Procedure.constant ea eb b⟩
lemma comp {f : α→β} {g : β→γ} (g' : Emits eb ec g) (f' : Emits ea eb f) :
    Emits ea ec (fun x=>g (f x)):=by
  obtain ⟨p⟩:=f';obtain ⟨q⟩:=g';exact ⟨q.comp p⟩
lemma pair {f : α→β} {g : α→γ} (h : Emits ea eb f) (j : Emits ea ec g) :
    Emits ea (prodCode eb ec) (fun x=>(f x,g x)):=by
  obtain ⟨p⟩:=h;obtain ⟨q⟩:=j;exact ⟨p.pair q⟩
lemma fst {f : α→β×γ} (h : Emits ea (prodCode eb ec) f) : Emits ea eb (fun x=>(f x).1):=
  (ofProcedure (Procedure.first eb ec)).comp h
lemma snd {f : α→β×γ} (h : Emits ea (prodCode eb ec) f) : Emits ea ec (fun x=>(f x).2):=
  (ofProcedure (Procedure.second eb ec)).comp h
lemma congr {f g : α→β} (h : Emits ea eb f) (hh : ∀x,f x=g x) : Emits ea eb g:=by
  obtain ⟨p⟩:=h;exact ⟨p.congrFun hh⟩
lemma precompose {f : β→γ} (h : Emits eb ec f) (g : α→β) : Emits (fun x=>eb (g x)) ec (fun x=>f (g x)):=by
  obtain ⟨p⟩:=h;exact ⟨p.precompose g⟩
lemma natAdd {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x+g x):=(ofProcedure Procedure.binaryAdd).comp (h.pair j)
lemma natSub {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x-g x):=(ofProcedure Procedure.binarySub).comp (h.pair j)
lemma natMul {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x*g x):=(ofProcedure Procedure.binaryMul).comp (h.pair j)
lemma natDiv {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x/g x):=(ofProcedure Procedure.binaryDiv).comp (h.pair j)
lemma natMod {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x%g x):=(ofProcedure Procedure.binaryMod).comp (h.pair j)
lemma natMax {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>max (f x) (g x)):=(ofProcedure NetworkEmission.Emission.binaryMax).comp (h.pair j)
lemma unaryNat {f : α→ℕ} (h : Emits ea unaryCode f) : Emits ea Nat.bits f:=
  (ofProcedure Procedure.unaryToBits).comp h
end Emits
end ExactQuantumFactoring.BitStackProgram

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
lemma nvar {f : α→v} (h : BitStackProgram.Emits ea ev f) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.var (f x)):=
  (ofProcedure (Emission.exprVarP ev)).comp h
lemma nconst {f : α→ℕ} (h : BitStackProgram.Emits ea Nat.bits f) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.const (f x)):=
  (ofProcedure (Emission.exprConstP ev)).comp h
lemma nadd {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.add (f x) (g x)):=
  (ofProcedure (Emission.exprAddP ev)).comp (h.pair j)
lemma nsub {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.sub (f x) (g x)):=
  (ofProcedure (Emission.exprSubP ev)).comp (h.pair j)
lemma nmul {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.mul (f x) (g x)):=
  (ofProcedure (Emission.exprMulP ev)).comp (h.pair j)
lemma ndiv {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.div (f x) (g x)):=
  (ofProcedure (Emission.exprDivP ev)).comp (h.pair j)
lemma nmod {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.mod (f x) (g x)):=
  (ofProcedure (Emission.exprModP ev)).comp (h.pair j)
lemma nite {a b c d : α→NatExpr v} (ha : BitStackProgram.Emits ea (exprCode ev) a)
    (hb : BitStackProgram.Emits ea (exprCode ev) b)
    (hc : BitStackProgram.Emits ea (exprCode ev) c)
    (hd : BitStackProgram.Emits ea (exprCode ev) d) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.iteLe (a x) (b x) (c x) (d x)):=
  (ofProcedure (Emission.exprIteP ev)).comp (ha.pair (hb.pair (hc.pair hd)))
end Emits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkResizeEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def resizePack (u w : ℕ) : Pack:=vectorPack u ((List.range w).map
  (fun i=>if i<u then bitPack u i else constantPack u false))
lemma resizePack_value (u w : ℕ) : (resizePack u w).val.value=erase (BitArithmetic.resizeWord u w):=by
  unfold resizePack BitArithmetic.resizeWord
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  dsimp only [Function.comp_apply]
  by_cases h : i.val<u
  · simp only [h,↓reduceIte,↓reduceDIte]
    exact bitPack_value ⟨i.val,h⟩
  · simp only [h,↓reduceIte,↓reduceDIte]
    exact constantPack_value _ _
namespace Emission
noncomputable def resizePackP : Procedure (prodCode unaryCode unaryCode) packCode (fun x=>resizePack x.1 x.2):=by
  let i:=unaryToBits.comp (first unaryCode unaryCode)
  let u:=second unaryCode unaryCode
  let test:=binaryLt.comp (i.pair (unaryToBits.comp u))
  let step:=conditional test (bitPackP.comp (u.pair i))
    (constantPackP.comp (u.pair (Procedure.constant _ boolCode false)))
  let step' : Procedure (prodCode unaryCode unaryCode) packCode
      (fun x=>if x.1<x.2 then bitPack x.2 x.1 else constantPack x.2 false):=
    step.congrFun (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,id_eq])
  let xs:=(tabulate (f:=fun u i=>if i<u then bitPack u i else constantPack u false) emptyPack step').comp ((second unaryCode unaryCode).pair (first unaryCode unaryCode))
  exact vectorPackP.comp ((first unaryCode unaryCode).pair xs)
noncomputable def exprWidthP {vars : Type} (ev : vars→List Bool) : Procedure (prodCode unaryCode (exprCode ev)) unaryCode
    (fun x=>x.2.templateWidth x.1):=by
  let b:=first unaryCode (exprCode ev)
  let e:=second unaryCode (exprCode ev)
  let sz:=(exprSizeP ev).comp e
  let mc:=(exprMaxP ev).comp e
  let sizeP : Procedure Nat.bits unaryCode Nat.size:=
    (Procedure.length.precompose Nat.bits).congrFun (by intro n;exact n.size_eq_bits_len)
  let bitlen:=sizeP.comp mc
  exact unaryMul.comp ((unarySuccessor.comp (unaryAdd.comp (b.pair bitlen))).pair sz)
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkEmissionCombinators.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
/-- Exact, syntactic network emission. Pack budgets are internal certificates,
not additional generator advice. -/
def NetEmits {α : Type} (ea : α→List Bool) {n m : α→ℕ}
    (f : ∀x,BooleanNetwork (n x) (m x)) : Prop:=
  ∃p : α→Pack,BitStackProgram.Emits ea packCode p ∧ ∀x,(p x).val.value=erase (f x)
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m l : α→ℕ}
lemma ofPack {f : ∀x,BooleanNetwork (n x) (m x)} {p : α→Pack}
    (hp : BitStackProgram.Emits ea packCode p) (hf : ∀x,(p x).val.value=erase (f x)) : NetEmits ea f:=⟨p,hp,hf⟩
lemma comp {f : ∀x,BooleanNetwork (n x) (m x)} {g : ∀x,BooleanNetwork (m x) (l x)}
    (hf : NetEmits ea f) (hg : NetEmits ea g) : NetEmits ea (fun x=>(f x).comp (g x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  obtain ⟨q,hq,eq⟩:=hg
  refine ⟨fun x=>compPack (p x) (q x),(ofProcedure Emission.compPackP).comp (hp.pair hq),?_⟩
  intro x
  rw [compPack_value]
  · rw [ep,eq];exact (erase_comp _ _).symm
  · rw [ep,eq];simp [erase]
lemma pair {f : ∀x,BooleanNetwork (n x) (m x)} {g : ∀x,BooleanNetwork (n x) (l x)}
    (hf : NetEmits ea f) (hg : NetEmits ea g) : NetEmits ea (fun x=>(f x).pair (g x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  obtain ⟨q,hq,eq⟩:=hg
  refine ⟨fun x=>pairPack (p x) (q x),(ofProcedure Emission.pairPackP).comp (hp.pair hq),?_⟩
  intro x
  rw [pairPack_value]
  · rw [ep,eq];exact (erase_pair _ _).symm
  · rw [ep,eq];rfl
lemma rewire {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f)
    (is : ∀x,Fin (l x)→Fin (m x))
    (hi : BitStackProgram.Emits ea (listCode Nat.bits) (fun x=>List.ofFn (fun j=>(is x j).val))) :
    NetEmits ea (fun x=>(f x).rewire (is x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  refine ⟨fun x=>rewirePack (p x) (List.ofFn (fun j=>(is x j).val)),
    (ofProcedure Emission.rewirePackP).comp (hp.pair hi),?_⟩
  intro x;exact rewirePack_value _ _ _ (ep x)
lemma identity (hn : BitStackProgram.Emits ea unaryCode n) : NetEmits ea (fun x=>BooleanNetwork.select (id : Fin (n x)→Fin (n x))):=
  ⟨fun x=>identityPack (n x),(ofProcedure Emission.identityPackP).comp hn,fun _=>identityPack_value _⟩
lemma select (hn : BitStackProgram.Emits ea unaryCode n) (is : ∀x,Fin (m x)→Fin (n x))
    (hi : BitStackProgram.Emits ea (listCode Nat.bits) (fun x=>List.ofFn (fun j=>(is x j).val))) :
    NetEmits ea (fun x=>BooleanNetwork.select (is x)):=
  (identity hn).rewire is hi
lemma constant (hn : BitStackProgram.Emits ea unaryCode n) {b : α→Bool}
    (hb : BitStackProgram.Emits ea Procedure.boolCode b) :
    NetEmits ea (fun x=>BooleanNetwork.constant (n:=n x) (b x)):=
  ⟨fun x=>constantPack (n x) (b x),(ofProcedure Emission.constantPackP).comp (hn.pair hb),fun _=>constantPack_value _ _⟩
lemma bit (hn : BitStackProgram.Emits ea unaryCode n) (i : ∀x,Fin (n x))
    (hi : BitStackProgram.Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>BooleanNetwork.bit (i x)):=
  ⟨fun x=>bitPack (n x) (i x).val,(ofProcedure Emission.bitPackP).comp (hn.pair hi),fun _=>bitPack_value _⟩
lemma resize (hn : BitStackProgram.Emits ea unaryCode n) (hm : BitStackProgram.Emits ea unaryCode m) :
    NetEmits ea (fun x=>BitArithmetic.resizeWord (n x) (m x)):=
  ⟨fun x=>resizePack (n x) (m x),(ofProcedure Emission.resizePackP).comp (hn.pair hm),fun _=>resizePack_value _ _⟩
lemma bnot {f : ∀x,BooleanNetwork (n x) 1} (hf : NetEmits ea f) :
    NetEmits ea (fun x=>BooleanNetwork.bnot (f x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  exact ⟨fun x=>bnotPack (p x),(ofProcedure Emission.bnotPackP).comp hp,fun x=>bnotPack_value _ _ (ep x)⟩
lemma band {f g : ∀x,BooleanNetwork (n x) 1} (hf : NetEmits ea f) (hg : NetEmits ea g) :
    NetEmits ea (fun x=>BooleanNetwork.band (f x) (g x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  obtain ⟨q,hq,eq⟩:=hg
  exact ⟨fun x=>bandPack (p x) (q x),(ofProcedure Emission.bandPackP).comp (hp.pair hq),
    fun x=>bandPack_value _ _ _ _ (ep x) (eq x)⟩
lemma wordConst (hn : BitStackProgram.Emits ea unaryCode n) (hm : BitStackProgram.Emits ea unaryCode m)
    {c : α→ℕ} (hc : BitStackProgram.Emits ea Nat.bits c) :
    NetEmits ea (fun x=>BitArithmetic.wordConstant (n:=n x) (BitVec.ofNat (m x) (c x))):=
  ⟨fun x=>wordConstPack (n x) (m x) (c x),
    (ofProcedure Emission.wordConstPackP).comp (hn.pair (hm.pair hc)),fun _=>wordConstPack_value _ _ _⟩
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/EmissionFurther.lean =====
namespace OAI

section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

namespace Emission
noncomputable def combineStackP : Procedure (prodCode boolCode (listCode packCode)) (listCode packCode)
    (fun x=>stackStep (.inr x.1) x.2):=by
  let sw:=first boolCode (listCode packCode)
  let s:=second boolCode (listCode packCode)
  let tl:=(listTail (ea:=packCode)).comp s
  let a:=(listHead packCode emptyPack).comp tl
  let b:=(listHead packCode emptyPack).comp s
  let o:=conditional sw (compPackP.comp (a.pair b)) (pairPackP.comp (a.pair b))
  exact ((listCons packCode).comp (o.pair ((listTail (ea:=packCode)).comp tl))).congrFun (by intro x;rfl)
noncomputable def stackStepP : Procedure (prodCode stackOpCode (listCode packCode)) (listCode packCode)
    (fun x=>stackStep x.1 x.2):=by
  let o:=first stackOpCode (listCode packCode)
  let s:=second stackOpCode (listCode packCode)
  let tag:=(casesSum (Procedure.constant packCode boolCode false) (Procedure.constant boolCode boolCode true)).comp o
  let p:=(casesSum (identity packCode) (Procedure.constant boolCode packCode emptyPack)).comp o
  let b:=(casesSum (Procedure.constant packCode boolCode false) (identity boolCode)).comp o
  exact (conditional tag (combineStackP.comp (b.pair s)) ((listCons packCode).comp (p.pair s))).congrFun (by
    rintro ⟨o,s⟩;cases o <;> rfl)
noncomputable def stackFoldP : Procedure (prodCode (listCode stackOpCode) (listCode packCode)) (listCode packCode)
    (fun x=>x.1.foldl (fun s o=>stackStep o s) x.2):=
  foldList (.inr false) stackStepP (Polynomial.X*(Polynomial.C 208*(Polynomial.X+1)^2+2)+1) (by
    intro ops s i
    let t:=(ops.take i).foldl (fun s o=>stackStep o s) s
    have hb:=stackFold_budget (ops.take i) s
    have hs:=packBudgets_le_code s
    have ho:=(opWeights_le_code (ops.take i)).trans (listCode_length_take_le stackOpCode i ops)
    have hlen:=stackFold_length (ops.take i) s
    have hop:=(list_length_le_code stackOpCode (ops.take i)).trans (listCode_length_take_le stackOpCode i ops)
    have hss:=list_length_le_code packCode s
    have hB : stackBudget t+1≤(listCode stackOpCode ops).length+(listCode packCode s).length+1:=by
      change stackBudget s≤_ at hs
      dsimp only [t];omega
    have hL : t.length≤(listCode stackOpCode ops).length+(listCode packCode s).length:=by dsimp only [t];omega
    have hh:=stackCode_bound t
    have hm:=Nat.mul_le_mul hL (Nat.add_le_add_right (Nat.mul_le_mul_left 208 (Nat.pow_le_pow_left hB 2)) 2)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_pow,Polynomial.eval_one,Polynomial.eval_ofNat]
    exact hh.trans (Nat.add_le_add_right hm 1))
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExpressionTokenProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure AIGNetworkEmission
namespace Emission
noncomputable def primPackP : Procedure (prodCode unaryCode Nat.bits) packCode (fun x=>primPack x.1 x.2):=by
  let w:=first unaryCode Nat.bits
  let j:=second unaryCode Nat.bits
  let eq (i:ℕ):=binaryEq.comp (j.pair (Procedure.constant _ Nat.bits i))
  let a:=AIGNetworkEmission.Emission.addPackP.comp w
  let b:=AIGNetworkEmission.Emission.mulPackP.comp w
  let c:=AIGNetworkEmission.Emission.subPackP.comp w
  let d:=AIGNetworkEmission.Emission.divPackP.comp w
  let e:=AIGNetworkEmission.Emission.modPackP.comp w
  let f:=AIGNetworkEmission.Emission.ultPackP.comp w
  let g:=Procedure.constant (prodCode unaryCode Nat.bits) packCode (nodePack 1 (.neg 0) (by simp [Node.Bound]))
  let h:=muxVectorPackP.comp w
  exact (conditional (eq 0) a (conditional (eq 1) b (conditional (eq 2) c (conditional (eq 3) d
    (conditional (eq 4) e (conditional (eq 5) f (conditional (eq 6) g h))))))).congrFun (by
    rintro ⟨w,j⟩
    rcases j with _|j <;> simp only [Function.comp_apply,decide_eq_true_eq,primPack]
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    simp)

def tokenTag : ExprToken ℕ→ℕ | .inl _=>0 | .inr (.inl _)=>1 | .inr (.inr _)=>2
def tokenPayload : ExprToken ℕ→ℕ | .inl i=>i | .inr (.inl c)=>c | .inr (.inr j)=>j
noncomputable def tokenTagP : Procedure (exprTokenCode Nat.bits) Nat.bits tokenTag:=
  (casesSum (Procedure.constant Nat.bits Nat.bits 0)
    (casesSum (Procedure.constant Nat.bits Nat.bits 1) (Procedure.constant Nat.bits Nat.bits 2))).congrFun (by
      intro t;rcases t with i|c|j <;> rfl)
noncomputable def tokenPayloadP : Procedure (exprTokenCode Nat.bits) Nat.bits tokenPayload:=
  (casesSum (identity Nat.bits) (casesSum (identity Nat.bits) (identity Nat.bits))).congrFun (by
    intro t;rcases t with i|c|j <;> rfl)
abbrev exprEnvCode:=prodCode unaryCode (prodCode unaryCode (listCode packCode))
abbrev ExprEnv:=ℕ×ℕ×List Pack
def envVars (xs : List Pack) (i : ℕ) : Pack:=(xs.drop i).headD emptyPack
noncomputable def tokenOpP : Procedure (prodCode exprEnvCode (exprTokenCode Nat.bits)) stackOpCode
    (fun x=>tokenOp x.1.1 x.1.2.1 (envVars x.1.2.2) x.2):=by
  let env:=first exprEnvCode (exprTokenCode Nat.bits)
  let n:=(first unaryCode (prodCode unaryCode (listCode packCode))).comp env
  let rest:=(second unaryCode (prodCode unaryCode (listCode packCode))).comp env
  let w:=(first unaryCode (listCode packCode)).comp rest
  let vs:=(second unaryCode (listCode packCode)).comp rest
  let tok:=second exprEnvCode (exprTokenCode Nat.bits)
  let tag:=tokenTagP.comp tok
  let val:=tokenPayloadP.comp tok
  let eq (i:ℕ) (p:Procedure (prodCode exprEnvCode (exprTokenCode Nat.bits)) Nat.bits (fun x=>i)):=
    binaryEq.comp (tag.pair p)
  let v:=(sumLeft packCode boolCode).comp ((listGet packCode emptyPack).comp (val.pair vs))
  let c:=(sumLeft packCode boolCode).comp (wordConstPackP.comp (n.pair (w.pair val)))
  let op:=(sumLeft packCode boolCode).comp (primPackP.comp (w.pair (binarySub.comp (val.pair (Procedure.constant _ Nat.bits 2)))))
  let inst:=conditional (binaryEq.comp (val.pair (Procedure.constant _ Nat.bits 0)))
    (Procedure.constant _ stackOpCode (.inr false))
    (conditional (binaryEq.comp (val.pair (Procedure.constant _ Nat.bits 1))) (Procedure.constant _ stackOpCode (.inr true)) op)
  exact (conditional (eq 0 (Procedure.constant _ Nat.bits 0)) v
    (conditional (eq 1 (Procedure.constant _ Nat.bits 1)) c inst)).congrFun (by
      rintro ⟨⟨n,w,vs⟩,t⟩
      rcases t with i|c|j
      · rfl
      · rfl
      rcases j with _|j
      · rfl
      rcases j with _|j
      · rfl
      simp only [Function.comp_apply,tokenTag,tokenPayload,tokenOp,decide_eq_true_eq,
        Nat.add_one_ne_zero,↓reduceIte]
      rfl)
noncomputable def exprRunP : Procedure (prodCode exprEnvCode (listCode (exprTokenCode Nat.bits))) (listCode packCode)
    (fun x=>exprRun x.1.1 x.1.2.1 (envVars x.1.2.2) x.2 []):=by
  let ops:=listMapWith (f:=fun (env : ExprEnv) t=>tokenOp env.1 env.2.1 (envVars env.2.2) t) (Sum.inl 0) (Sum.inr false) tokenOpP
  let start:=(ops.pair (Procedure.constant _ (listCode packCode) []))
  exact stackFoldP.comp start
noncomputable def exprResultP : Procedure (prodCode exprEnvCode (listCode (exprTokenCode Nat.bits))) packCode
    (fun x=>(exprRun x.1.1 x.1.2.1 (envVars x.1.2.2) x.2 []).headD emptyPack):=
  (listHead packCode emptyPack).comp exprRunP
/-- Compiler runs in polynomial time in the expanded source syntax, dimensions
and input networks. The environment contains no circuit-generation oracle. -/
noncomputable def exprPackP : Procedure
    (fun x : ExprEnv×NatExpr ℕ=>prodCode exprEnvCode (listCode (exprTokenCode Nat.bits)) (x.1,exprTokens x.2)) packCode
    (fun x=>exprPack x.1.1 x.1.2.1 (envVars x.1.2.2) x.2):=
  (exprResultP.precompose (fun x : ExprEnv×NatExpr ℕ=>(x.1,exprTokens x.2))).congrFun (by
    intro x
    change (exprRun _ _ _ (exprTokens x.2) []).headD emptyPack=_
    rw [exprTokens_produces];rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExpressionTemplateEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
variable {v : Type}
def tokenMap (f : v→ℕ) : ExprToken v→ExprToken ℕ:=Sum.map f id
lemma tokenMap_code (f : v→ℕ) (t : ExprToken v) :
    exprTokenCode Nat.bits (tokenMap f t)=exprTokenCode (fun i=>(f i).bits) t:=by
  rcases t with i|c|j <;> rfl
lemma tokenMap_listCode (f : v→ℕ) (ts : List (ExprToken v)) :
    listCode (exprTokenCode Nat.bits) (ts.map (tokenMap f))=
    listCode (exprTokenCode (fun i=>(f i).bits)) ts:=by
  induction ts with
  | nil=>rfl
  | cons t ts ih=>simp only [List.map_cons,listCode,tokenMap_code,ih]
lemma tokenMap_op (f : v→ℕ) (n w : ℕ) (vs : ℕ→Pack) (t : ExprToken v) :
    tokenOp n w vs (tokenMap f t)=tokenOp n w (fun i=>vs (f i)) t:=by
  rcases t with i|c|j
  · rfl
  · rfl
  · rcases j with _|j <;> try rfl
    rcases j with _|j <;> rfl
lemma tokenMap_run (f : v→ℕ) (n w : ℕ) (vs : ℕ→Pack) (ts : List (ExprToken v)) (s : List Pack) :
    exprRun n w vs (ts.map (tokenMap f)) s=exprRun n w (fun i=>vs (f i)) ts s:=by
  simp only [exprRun,List.map_map,Function.comp_def,tokenMap_op]
namespace Emission
noncomputable def genericExprResultP (f : v→ℕ) : Procedure
    (prodCode exprEnvCode (listCode (exprTokenCode (fun i=>(f i).bits)))) packCode
    (fun x=>(exprRun x.1.1 x.1.2.1 (fun i=>envVars x.1.2.2 (f i)) x.2 []).headD emptyPack):=by
  let p:=exprResultP.precompose (fun x : ExprEnv×List (ExprToken v)=>(x.1,x.2.map (tokenMap f)))
  exact (p.congrEncoding (by intro x;dsimp only [prodCode];rw [tokenMap_listCode]) (by intro x;rfl)).congrFun (by
    intro x;dsimp only [Function.comp_apply];rw [tokenMap_run])
noncomputable def genericExprPackP (f : v→ℕ) : Procedure
    (prodCode exprEnvCode (exprCode (fun i=>(f i).bits))) packCode
    (fun x=>exprPack x.1.1 x.1.2.1 (fun i=>envVars x.1.2.2 (f i)) x.2):=
  ((genericExprResultP f).comp ((first _ _).pair ((exprTokensP _).comp (second _ _)))).congrFun (by
    intro x;change (exprRun _ _ _ (exprTokens x.2) []).headD emptyPack=_
    rw [exprTokens_produces];rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/EmissionLists.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma listNil : Emits ea (listCode eb) (fun _=> ([] : List β)):=const _ _ _
lemma listCons {f : α→β} {g : α→List β} (hf : Emits ea eb f) (hg : Emits ea (listCode eb) g) :
    Emits ea (listCode eb) (fun x=>f x::g x):=(ofProcedure (Procedure.listCons eb)).comp (hf.pair hg)
lemma listAppend (b : β) {f g : α→List β} (hf : Emits ea (listCode eb) f) (hg : Emits ea (listCode eb) g) :
    Emits ea (listCode eb) (fun x=>f x++g x):=(ofProcedure (Procedure.listAppend eb b)).comp (hf.pair hg)
lemma ofFn {k : ℕ} {f : α→Fin k→β} (h : ∀i,Emits ea eb (fun x=>f x i)) :
    Emits ea (listCode eb) (fun x=>List.ofFn (f x)):=by
  induction k with
  | zero=>simpa only [List.ofFn_zero] using (listNil (ea:=ea) (eb:=eb))
  | succ k ih=>
    have ht:=ih (f:=fun x i=>f x i.succ) (fun i=>h i.succ)
    exact ((h 0).listCons ht).congr (by intro x;exact List.ofFn_succ.symm)
lemma unaryAdd {f g : α→ℕ} (h : Emits ea unaryCode f) (j : Emits ea unaryCode g) :
    Emits ea unaryCode (fun x=>f x+g x):=(ofProcedure Procedure.unaryAdd).comp (h.pair j)
lemma unaryMul {f g : α→ℕ} (h : Emits ea unaryCode f) (j : Emits ea unaryCode g) :
    Emits ea unaryCode (fun x=>f x*g x):=(ofProcedure Procedure.unaryMul).comp (h.pair j)
lemma unarySucc {f : α→ℕ} (h : Emits ea unaryCode f) :
    Emits ea unaryCode (fun x=>f x+1):=(ofProcedure Procedure.unarySuccessor).comp h
lemma conditional {c : α→Bool} {f g : α→β} (hc : Emits ea boolCode c)
    (hf : Emits ea eb f) (hg : Emits ea eb g) : Emits ea eb (fun x=>if c x then f x else g x):=by
  obtain ⟨p⟩:=hc;obtain ⟨q⟩:=hf;obtain ⟨r⟩:=hg
  exact ⟨Procedure.conditional p q r⟩
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkExpressionEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w b : α→ℕ}
lemma precompose {β : Type} {eb : β→List Bool} {n m : β→ℕ}
    {f : ∀x,BooleanNetwork (n x) (m x)} (h : NetEmits eb f) (g : α→β) :
    NetEmits (fun x=>eb (g x)) (fun x=>f (g x)):=by
  obtain ⟨p,hp,he⟩:=h
  exact ⟨fun x=>p (g x),hp.precompose g,fun x=>he (g x)⟩
lemma congr {f g : ∀x,BooleanNetwork (n x) (w x)} (h : NetEmits ea f) (he : ∀x,f x=g x) :
    NetEmits ea g:=by
  obtain ⟨p,hp,hh⟩:=h
  exact ⟨p,hp,fun x=>(hh x).trans (congrArg erase (he x))⟩
lemma bor {f g : ∀x,BooleanNetwork (n x) 1} (hf : NetEmits ea f) (hg : NetEmits ea g) :
    NetEmits ea (fun x=>BooleanNetwork.bor (f x) (g x)):=((hf.bnot).band hg.bnot).bnot
lemma compile {k : ℕ} {e : α→NatExpr (Fin k)}
    (he : BitStackProgram.Emits ea (exprCode (fun i:Fin k=>i.val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hw : BitStackProgram.Emits ea unaryCode w)
    {fs : ∀x,Fin k→BooleanNetwork (n x) (w x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).compile (fs x)):=by
  classical
  choose p hp ep using hf
  let ps (x:α):=List.ofFn (fun i=>p i x)
  have hps : BitStackProgram.Emits ea (listCode packCode) ps:=BitStackProgram.Emits.ofFn hp
  let out (x:α):=exprPack (n x) (w x) (fun i:Fin k=>Emission.envVars (ps x) i.val) (e x)
  refine ⟨out,(ofProcedure (Emission.genericExprPackP Fin.val)).comp ((hn.pair (hw.pair hps)).pair he),?_⟩
  intro x
  apply exprPack_value
  intro i
  have hh : Emission.envVars (ps x) i.val=p i x:=by
    simp [Emission.envVars,ps,List.headD_eq_head?_getD,List.head?_drop,i.isLt]
  rw [hh];exact ep i x
lemma template {k : ℕ} {e : α→NatExpr (Fin k)}
    (he : BitStackProgram.Emits ea (exprCode (fun i:Fin k=>i.val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hb : BitStackProgram.Emits ea unaryCode b)
    {fs : ∀x,Fin k→BooleanNetwork (n x) (b x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).template (fs x)):=by
  have hw : BitStackProgram.Emits ea unaryCode (fun x=>(e x).templateWidth (b x)):=
    (ofProcedure (Emission.exprWidthP _)).comp (hb.pair he)
  exact compile he hn hw (fun i=>(hf i).comp (resize hb hw))
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkLoopEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma fold_budget_extra (f : Pack→Pack→Pack) (c : ℕ)
    (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget+c)
    (xs : List Pack) (a : Pack) :
    (xs.foldl (fun b a=>f a b) a).val.budget=a.val.budget+(xs.map (fun s=>s.val.budget)).sum+c*xs.length:=by
  induction xs generalizing a with
  | nil=>simp
  | cons s xs ih=>rw [List.foldl_cons,ih,h,List.map_cons,List.sum_cons,List.length_cons];ring
namespace Emission
noncomputable def foldRightPack {f : Pack→Pack→Pack} (c : ℕ)
    (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget+c)
    (p : Procedure (prodCode packCode packCode) packCode (fun x=>f x.1 x.2)) :
    Procedure (prodCode (listCode packCode) packCode) packCode (fun x=>x.1.foldr f x.2):=by
  let fold:=foldList emptyPack p (Polynomial.C 104*(Polynomial.C (c+1)*Polynomial.X+1)^2) (by
    intro xs a i
    have hh:=packCode_bound ((xs.take i).foldl (fun b a=>f a b) a)
    rw [fold_budget_extra f c h] at hh
    have hb:=packBudget_le_code a
    have hx:=(packBudgets_le_code (xs.take i)).trans (listCode_length_take_le packCode i xs)
    have hl:=(list_length_le_code packCode (xs.take i)).trans (listCode_length_take_le packCode i xs)
    have hm:=Nat.pow_le_pow_left (show a.val.budget+((xs.take i).map (fun s=>s.val.budget)).sum+c*(xs.take i).length+1≤
      (c+1)*((listCode packCode xs).length+(packCode a).length)+1 by nlinarith) 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    exact hh.trans (Nat.mul_le_mul_left _ hm))
  let input:=((listReverse packCode emptyPack).comp (first (listCode packCode) packCode)).pair
    (second (listCode packCode) packCode)
  exact (fold.comp input).congrFun (by intro x;exact List.foldl_reverse)
noncomputable def allPackP : Procedure (prodCode unaryCode (listCode packCode)) packCode
    (fun x=>x.2.foldr bandPack (constantPack x.1 true)):=by
  let start:=constantPackP.comp ((first unaryCode (listCode packCode)).pair (Procedure.constant _ boolCode true))
  exact (foldRightPack 4 (by intros;rfl) bandPackP).comp ((second unaryCode (listCode packCode)).pair start)
noncomputable def anyPackP : Procedure (prodCode unaryCode (listCode packCode)) packCode
    (fun x=>x.2.foldr borPack (constantPack x.1 false)):=by
  let start:=constantPackP.comp ((first unaryCode (listCode packCode)).pair (Procedure.constant _ boolCode false))
  exact (foldRightPack 13 (by intros;dsimp [borPack,bnotPack,bandPack,compPack,pairPack,nodePack];omega) borPackP).comp
    ((second unaryCode (listCode packCode)).pair start)
end Emission
lemma allPack_value {n : ℕ} (ps : List Pack) (fs : List (BooleanNetwork n 1))
    (h : List.Forall₂ (fun p f=>p.val.value=erase f) ps fs) :
    (ps.foldr bandPack (constantPack n true)).val.value=erase (BooleanNetwork.all fs):=by
  induction h with
  | nil=>exact constantPack_value n true
  | cons hp hs ih=>exact bandPack_value _ _ _ _ hp ih
lemma anyPack_value {n : ℕ} (ps : List Pack) (fs : List (BooleanNetwork n 1))
    (h : List.Forall₂ (fun p f=>p.val.value=erase f) ps fs) :
    (ps.foldr borPack (constantPack n false)).val.value=erase (BooleanNetwork.any fs):=by
  induction h with
  | nil=>exact constantPack_value n false
  | cons hp hs ih=>exact borPack_value _ _ _ _ hp ih
lemma ofFn_nat_eq_map {β : Type} (k : ℕ) (f : ℕ→β) :
    List.ofFn (fun i:Fin k=>f i.val)=(List.range k).map f:=by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp

namespace NetEmits
open BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {n m : α→ℕ}
lemma compInput {n m : β→ℕ} {f : ∀x,BooleanNetwork (n x) (m x)} {g : α→β}
    (hf : NetEmits eb f) (hg : BitStackProgram.Emits ea eb g) : NetEmits ea (fun x=>f (g x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  exact ⟨fun x=>p (g x),hp.comp hg,fun x=>ep (g x)⟩
lemma rangePack {f : ∀x,ℕ→BooleanNetwork (n x) (m x)} {k : α→ℕ}
    (hf : NetEmits (prodCode unaryCode ea) (fun x=>f x.2 x.1)) (hk : BitStackProgram.Emits ea unaryCode k) :
    ∃p : α→List Pack, BitStackProgram.Emits ea (listCode packCode) p ∧
      ∀x,List.Forall₂ (fun p y=>p.val.value=erase y) (p x) ((List.range (k x)).map (f x)):=by
  obtain ⟨q,⟨hp⟩,ep⟩:=hf
  refine ⟨fun x=>(List.range (k x)).map (fun i=>q (i,x)),
    (ofProcedure (Procedure.tabulate (f:=fun x i=>q (i,x)) emptyPack hp)).comp (hk.pair (id ea)),?_⟩
  intro x
  dsimp only
  induction List.range (k x) with
  | nil=>exact .nil
  | cons i is ih=>exact .cons (ep (i,x)) ih
lemma allRange {f : ∀x,ℕ→BooleanNetwork (n x) 1} {k : α→ℕ}
    (hn : BitStackProgram.Emits ea unaryCode n)
    (hf : NetEmits (prodCode unaryCode ea) (fun x=>f x.2 x.1)) (hk : BitStackProgram.Emits ea unaryCode k) :
    NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (fun i:Fin (k x)=>f x i.val))):=by
  obtain ⟨p,hp,ep⟩:=rangePack hf hk
  refine ⟨fun x=>(p x).foldr bandPack (constantPack (n x) true),
    (ofProcedure Emission.allPackP).comp (hn.pair hp),?_⟩
  intro x;dsimp only;rw [ofFn_nat_eq_map (k x) (f x)];exact allPack_value _ _ (ep x)
lemma anyRange {f : ∀x,ℕ→BooleanNetwork (n x) 1} {k : α→ℕ}
    (hn : BitStackProgram.Emits ea unaryCode n)
    (hf : NetEmits (prodCode unaryCode ea) (fun x=>f x.2 x.1)) (hk : BitStackProgram.Emits ea unaryCode k) :
    NetEmits ea (fun x=>BooleanNetwork.any (List.ofFn (fun i:Fin (k x)=>f x i.val))):=by
  obtain ⟨p,hp,ep⟩:=rangePack hf hk
  refine ⟨fun x=>(p x).foldr borPack (constantPack (n x) false),
    (ofProcedure Emission.anyPackP).comp (hn.pair hp),?_⟩
  intro x;dsimp only;rw [ofFn_nat_eq_map (k x) (f x)];exact anyPack_value _ _ (ep x)
lemma vectorRange {f : ∀x,ℕ→BooleanNetwork (n x) 1} {k : α→ℕ}
    (hn : BitStackProgram.Emits ea unaryCode n)
    (hf : NetEmits (prodCode unaryCode ea) (fun x=>f x.2 x.1)) (hk : BitStackProgram.Emits ea unaryCode k) :
    NetEmits ea (fun x=>BooleanNetwork.vector (fun i:Fin (k x)=>f x i.val)):=by
  obtain ⟨q,⟨hp⟩,ep⟩:=hf
  refine ⟨fun x=>vectorPack (n x) ((List.range (k x)).map (fun i=>q (i,x))),
    (ofProcedure Emission.vectorPackP).comp (hn.pair ((ofProcedure (Procedure.tabulate (f:=fun x i=>q (i,x)) emptyPack hp)).comp (hk.pair (id ea)))),?_⟩
  intro x
  dsimp only
  rw [←ofFn_nat_eq_map (k x) (fun i=>q (i,x))]
  exact vectorPack_value _ _ (fun i=>ep (i.val,x))
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkIndexedEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma ofFn_forall₂ {α β : Type} {k : ℕ} (f : Fin k→α) (g : Fin k→β)
    (R : α→β→Prop) (h : ∀i,R (f i) (g i)) : List.Forall₂ R (List.ofFn f) (List.ofFn g):=by
  induction k with
  | zero=>simp
  | succ k ih=>rw [List.ofFn_succ,List.ofFn_succ];exact .cons (h 0) (ih _ _ (fun i=>h i.succ))
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma allIndexed {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k) (p : α→ℕ→Pack)
    (hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1))
    (he : ∀x i,(p x i.val).val.value=erase (f x i)) :
    NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (f x))):=by
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=p) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (p x)).foldr bandPack (constantPack (n x) true),
    (ofProcedure Emission.allPackP).comp (hn.pair hps),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact allPack_value _ _ (ofFn_forall₂ _ _ _ (he x))
lemma vectorIndexed {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k) (p : α→ℕ→Pack)
    (hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1))
    (he : ∀x i,(p x i.val).val.value=erase (f x i)) :
    NetEmits ea (fun x=>BooleanNetwork.vector (f x)):=by
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=p) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>vectorPack (n x) ((List.range (k x)).map (p x)),
    (ofProcedure Emission.vectorPackP).comp (hn.pair hps),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact vectorPack_value _ _ (he x)
lemma selectSlice (hn : Emits ea unaryCode n) (hm : Emits ea unaryCode m)
    {s : α→ℕ} (hs : Emits ea Nat.bits s) (is : ∀x,Fin (m x)→Fin (n x))
    (hi : ∀x i,(is x i).val=s x+i.val) : NetEmits ea (fun x=>BooleanNetwork.select (is x)):=by
  apply select hn is
  have h := (ofProcedure (Procedure.listMapWith (f:=fun s i=>s+i) 0 0 Procedure.binaryAdd)).comp
    (hs.pair ((ofProcedure Emission.rangeP).comp hm))
  exact h.congr (by intro x;rw [←ofFn_nat_eq_map];congr 1;funext i;exact (hi x i).symm)
lemma rewireSlice {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f)
    (hk : Emits ea unaryCode k) {s : α→ℕ} (hs : Emits ea Nat.bits s)
    (is : ∀x,Fin (k x)→Fin (m x)) (hi : ∀x i,(is x i).val=s x+i.val) :
    NetEmits ea (fun x=>(f x).rewire (is x)):=by
  apply hf.rewire is
  have h := (ofProcedure (Procedure.listMapWith (f:=fun s i=>s+i) 0 0 Procedure.binaryAdd)).comp
    (hs.pair ((ofProcedure Emission.rangeP).comp hk))
  exact h.congr (by intro x;rw [←ofFn_nat_eq_map];congr 1;funext i;exact (hi x i).symm)
lemma padRight (hn : Emits ea unaryCode n) (hm : Emits ea unaryCode m) :
    NetEmits ea (fun x=>BooleanNetwork.padRight (n x) (m x)):=by
  let p : α→ℕ→Pack:=fun x i=>if i<n x then bitPack (n x) i else constantPack (n x) false
  have he:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hi:=he.fst.unaryNat
  have hN:=hn.comp he.snd
  have hc:=(ofProcedure Procedure.binaryLt).comp (hi.pair hN.unaryNat)
  obtain ⟨pc⟩:=hc
  obtain ⟨pa⟩:=(ofProcedure Emission.bitPackP).comp (hN.pair hi)
  obtain ⟨pb⟩:=(ofProcedure Emission.constantPackP).comp (hN.pair (const _ _ false))
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1):=
    ofProcedure ((Procedure.conditional pc pa pb).congrFun (by intro x;simp only [p,decide_eq_true_eq]))
  exact vectorIndexed hn (hn.unaryAdd hm) p hp (by
    intro x i
    dsimp only [p]
    split
    · rename_i hi
      simpa only [BooleanNetwork.padRight,hi,dite_true] using bitPack_value (⟨i.val,hi⟩ : Fin (n x))
    · rename_i hi
      exact constantPack_value _ _)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkModularEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w : α→ℕ}
lemma mul (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.mul (w x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.mul (w x),
    (ofProcedure AIGNetworkEmission.Emission.mulPackP).comp hw,fun x=>AIGNetworkEmission.mulPack_value (w x)⟩
lemma mod (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.mod (w x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.remainder (w x),
    (ofProcedure AIGNetworkEmission.Emission.modPackP).comp hw,fun x=>AIGNetworkEmission.modPack_value (w x)⟩
lemma mulMod {a b c : ∀x,BooleanNetwork (n x) (w x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hc : NetEmits ea c)
    (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.mulMod (a x) (b x) (c x)):=by
  have hp:=padRight hw hw
  exact (((((ha.comp hp).pair (hb.comp hp)).comp (mul (hw.unaryAdd hw))).pair
    (hc.comp hp)).comp (mod (hw.unaryAdd hw))).rewireSlice hw (const _ _ 0)
      (fun _=>Fin.castAdd _) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma wordMux {c : ∀x,BooleanNetwork (n x) 1} {a b : ∀x,BooleanNetwork (n x) (w x)}
    (hc : NetEmits ea c) (ha : NetEmits ea a) (hb : NetEmits ea b)
    (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.wordMux (c x) (a x) (b x)):=by
  obtain ⟨p,hp,ep⟩:=hc;obtain ⟨q,hq,eq⟩:=ha;obtain ⟨r,hr,er⟩:=hb
  exact ⟨fun x=>wordMuxPack (w x) (p x) (q x) (r x),
    (ofProcedure Emission.wordMuxPackP).comp (hw.pair (hp.pair (hq.pair hr))),
    fun x=>wordMuxPack_value _ _ _ (c x) (a x) (b x) (ep x) (eq x) (er x)⟩
end NetEmits

open BitArithmetic
lemma powerStep_emission : ∃p : (ℕ×ℕ)→ℕ→Pack,
    Emits (prodCode unaryCode (prodCode unaryCode unaryCode)) packCode (fun x=>p x.2 x.1) ∧
    ∀w b (i : Fin b),(p (w,b) i.val).val.value=erase (powerStep w i):=by
  let ea:=prodCode unaryCode (prodCode unaryCode unaryCode)
  have hx:=BitStackProgram.Emits.id ea
  have hi:=hx.fst
  have hw:=hx.snd.fst
  have hb:=hx.snd.snd
  have hW:=((hw.unaryAdd hw).unaryAdd hb).unaryAdd hw
  have hB : NetEmits ea (fun x=>powerBase x.2.1 x.2.2):=
    NetEmits.selectSlice hW hw (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
  have hM : NetEmits ea (fun x=>powerModulus x.2.1 x.2.2):=
    NetEmits.selectSlice hW hw hw.unaryNat _ (by intros;simp only [Fin.val_castAdd,Fin.val_natAdd])
  have hA : NetEmits ea (fun x=>powerAcc x.2.1 x.2.2):=
    NetEmits.selectSlice hW hw ((hw.unaryAdd hw).unaryAdd hb).unaryNat _ (by intros;simp only [Fin.val_natAdd])
  have hS:=hA.mulMod hA hM hw
  have hP:=hS.mulMod hB hM hw
  have hF : NetEmits ea (fun x=>BooleanNetwork.select
      (Fin.castAdd x.2.1 : Fin ((x.2.1+x.2.1)+x.2.2)→Fin (powerWidth x.2.1 x.2.2))):=
    NetEmits.selectSlice hW ((hw.unaryAdd hw).unaryAdd hb) (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
  obtain ⟨s,hs,es⟩:=hS
  obtain ⟨q,hq,eq⟩:=hP
  obtain ⟨f,hf,ef⟩:=hF
  let c:=fun x:ℕ×(ℕ×ℕ)=>bitPack (powerWidth x.2.1 x.2.2) ((x.2.1+x.2.1)+x.1)
  have hc : Emits ea packCode c:=(ofProcedure Emission.bitPackP).comp
    (hW.pair ((hw.unaryNat.natAdd hw.unaryNat).natAdd hi.unaryNat))
  let p:=fun wb i=>pairPack (f (i,wb)) (wordMuxPack wb.1 (c (i,wb)) (q (i,wb)) (s (i,wb)))
  refine ⟨p,(ofProcedure Emission.pairPackP).comp (hf.pair
    ((ofProcedure Emission.wordMuxPackP).comp (hw.pair (hc.pair (hq.pair hs))))),?_⟩
  intro w b i
  apply pairPack_spec _ _ _ _ (ef _)
  exact wordMuxPack_value _ _ _ (powerBit w i)
    (mulMod (mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b)) (powerBase w b) (powerModulus w b))
    (mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b))
    (bitPack_value ((Fin.natAdd (w+w) i).castAdd w)) (eq _) (es _)
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkPredicateEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
namespace Emission
noncomputable def swapIndicesP : Procedure unaryCode (listCode Nat.bits)
    (fun w=>List.ofFn (fun i:Fin (w+w)=>(Fin.addCases (Fin.natAdd w) (Fin.castAdd w) i : Fin (w+w)).val)):=by
  let step:=binaryAdd.comp ((unaryToBits.comp (second unaryCode unaryCode)).pair
    (unaryToBits.comp (first unaryCode unaryCode)))
  let a:=(tabulate (f:=fun w i=>w+i) 0 step).comp ((identity unaryCode).pair (identity unaryCode))
  let b:=(tabulate (f:=fun (_:ℕ) i=>i) 0 (unaryToBits.comp (first unaryCode unaryCode))).comp
    ((identity unaryCode).pair (identity unaryCode))
  exact ((Procedure.listAppend Nat.bits 0).comp (a.pair b)).congrFun (by
    intro w
    change (List.range w).map (fun i=>w+i)++(List.range w).map id=_
    rw [←ofFn_val_range,List.map_ofFn,List.map_id,List.ofFn_add]
    congr 1 <;> apply congrArg List.ofFn <;> funext i
    · change w+i.val=(Fin.addCases (Fin.natAdd w) (Fin.castAdd w) (i.castAdd w) : Fin (w+w)).val
      rw [Fin.addCases_left];rfl
    · rw [Fin.addCases_right];rfl)
end Emission
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w : α→ℕ}
lemma ult (hw : BitStackProgram.Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.ult (w x)):=
  ⟨fun x=>AIGNetworkEmission.ultPack (w x),(ofProcedure AIGNetworkEmission.Emission.ultPackP).comp hw,
    fun x=>AIGNetworkEmission.ultPack_value (w x)⟩
lemma wordEq (hw : BitStackProgram.Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.wordEq (w x)):=by
  have hs : NetEmits ea (fun x=>BooleanNetwork.select
      (Fin.addCases (Fin.natAdd (w x)) (Fin.castAdd (w x)))):=
    select (hw.unaryAdd hw) _ ((ofProcedure Emission.swapIndicesP).comp hw)
  exact ((ult hw).bor (hs.comp (ult hw))).bnot
lemma equalOn {f g : ∀x,BooleanNetwork (n x) (w x)}
    (hf : NetEmits ea f) (hg : NetEmits ea g) (hw : BitStackProgram.Emits ea unaryCode w) :
    NetEmits ea (fun x=>BitArithmetic.equalOn (f x) (g x)):=(hf.pair hg).comp (wordEq hw)
lemma isOne {k : ℕ} {b : α→ℕ} {e : α→NatExpr (Fin k)}
    (he : BitStackProgram.Emits ea (exprCode (fun i:Fin k=>i.val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hb : BitStackProgram.Emits ea unaryCode b)
    {fs : ∀x,Fin k→BooleanNetwork (n x) (b x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).isOne (fs x)):=by
  have hw : BitStackProgram.Emits ea unaryCode (fun x=>(e x).templateWidth (b x)):=
    (ofProcedure (Emission.exprWidthP _)).comp (hb.pair he)
  exact (template he hn hb hf).equalOn (wordConst hn hw (const _ _ 1)) hw
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackBoundedPrime.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma boolFold_eq (xs : List Bool) (b : Bool) :
    xs.foldl (fun b a=>a&&b) b=(xs.all id && b):=by
  induction xs generalizing b with
  | nil=>simp
  | cons a xs ih=>simp only [List.foldl_cons,ih,List.all_cons,id_eq];cases a <;> cases b <;> simp
namespace Procedure
noncomputable def boolListAll : Procedure (listCode boolCode) boolCode (fun xs=>xs.all id):=by
  let fold:=foldList false boolAnd (Polynomial.C 1) (by intro xs b i;simp only [boolCode,List.length_singleton,Polynomial.eval_C];rfl)
  exact (fold.comp ((identity _).pair (constant _ boolCode true))).congrFun (by intro xs;change xs.foldl (fun b a=>a&&b) true=xs.all id;rw [boolFold_eq];simp)
noncomputable def unaryPrime : Procedure unaryCode boolCode (fun n=>decide (Nat.Prime n)):=by
  let i:=(unaryToBits.comp (first unaryCode Nat.bits))
  let n:=second unaryCode Nat.bits
  let small:=binaryLt.comp (i.pair (constant _ Nat.bits 2))
  let nondvd:=boolNot.comp (binaryEq.comp ((binaryMod.comp (n.pair i)).pair (constant _ Nat.bits 0)))
  let test:=boolOr.comp (small.pair nondvd)
  let table:=tabulate (f:=fun n i=>decide (i<2) || !decide (n%i=0)) false test
  let all:=(boolListAll.comp table).comp ((identity unaryCode).pair unaryToBits)
  let large:=boolNot.comp (binaryLt.comp (unaryToBits.pair (constant unaryCode Nat.bits 2)))
  exact (boolAnd.comp (large.pair all)).congrFun (by
    intro n
    apply Bool.eq_iff_iff.mpr
    change ((!decide (n<2)) && ((List.range n).map (fun i=>decide (i<2) || !decide (n%i=0))).all id)=true ↔ _
    simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,List.all_eq_true,List.mem_map,
      id_eq,decide_eq_true_eq]
    rw [Nat.prime_def_lt']
    constructor
    · rintro ⟨hn,h⟩
      refine ⟨by omega,?_⟩
      intro m hm hmn hd
      have ht:=h _ ⟨m,List.mem_range.mpr hmn,rfl⟩
      simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not] at ht
      exact ht.elim (by omega) (fun h=>h (Nat.dvd_iff_mod_eq_zero.mp hd))
    · rintro ⟨hn,h⟩
      refine ⟨by omega,?_⟩
      rintro b ⟨m,hm,rfl⟩
      simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]
      by_cases hlt : m<2
      · exact Or.inl hlt
      · exact Or.inr (fun hz=>h m (by omega) (List.mem_range.mp hm) (Nat.dvd_iff_mod_eq_zero.mpr hz)))
end Procedure

end ExactQuantumFactoring.BitStackProgram
end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/Emits.lean =====
namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Emits
open Procedure
variable {α : Type} {ea : α→List Bool}
lemma natLt {f g : α→ℕ} (hf : Emits ea Nat.bits f) (hg : Emits ea Nat.bits g) :
    Emits ea boolCode (fun x=>decide (f x<g x)):=(ofProcedure binaryLt).comp (hf.pair hg)
lemma natEq {f g : α→ℕ} (hf : Emits ea Nat.bits f) (hg : Emits ea Nat.bits g) :
    Emits ea boolCode (fun x=>decide (f x=g x)):=(ofProcedure binaryEq).comp (hf.pair hg)
lemma boolNot {f : α→Bool} (hf : Emits ea boolCode f) : Emits ea boolCode (fun x=>!f x):=
  (ofProcedure Procedure.boolNot).comp hf
lemma boolAnd {f g : α→Bool} (hf : Emits ea boolCode f) (hg : Emits ea boolCode g) :
    Emits ea boolCode (fun x=>f x&&g x):=(ofProcedure Procedure.boolAnd).comp (hf.pair hg)
lemma boolOr {f g : α→Bool} (hf : Emits ea boolCode f) (hg : Emits ea boolCode g) :
    Emits ea boolCode (fun x=>f x||g x):=(ofProcedure Procedure.boolOr).comp (hf.pair hg)
lemma unaryPrime {f : α→ℕ} (hf : Emits ea unaryCode f) : Emits ea boolCode (fun x=>decide (Nat.Prime (f x))):=
  (ofProcedure Procedure.unaryPrime).comp hf
end Emits
end ExactQuantumFactoring.BitStackProgram

end



end OAI
