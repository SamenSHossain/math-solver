/-
Exact quantum factoring development (port of OpenAI's formalization), part 33 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: BitStackListFlatten.lean, CircuitEmissionModel.lean, CircuitBooleanEmission.lean, BitStackListWords.lean, BitStackBoundedUnary.lean, CircuitEmissionEncoding.lean, BitStackListMapIdx.lean, CircuitEmissionBasic.lean, CircuitProgramEmission.lean, CircuitFinalEmission.lean, CircuitCleanEmission.lean, BitStackDependentChoice.lean, NetworkDependentEmission.lean, NetworkSequenceEmission.lean, EmissionPolynomialUnary.lean, WordBlocksEmission.lean, EmissionBoundedRecursion.lean, EmissionGeneralStages.lean, TriangularNetworkEmission.lean, NetworkModularPowerEmission.lean, BitStackPowers.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part32

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackListFlatten.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
lemma fold_append_flatten (xss : List (List α)) (xs : List α) :
    xss.foldl (fun xs ys=>xs++ys) xs=xs++xss.flatten:=by
  induction xss generalizing xs with
  | nil=>simp
  | cons ys yss ih=>simp [ih,List.append_assoc]
lemma listCode_length_flatten_le (ea : α→List Bool) (xss : List (List α)) :
    (listCode ea xss.flatten).length≤(listCode (listCode ea) xss).length:=by
  induction xss with
  | nil=>simp [listCode]
  | cons xs xss ih=>
    simp only [List.flatten_cons,listCode_length_cons]
    have hh:=listCode_length_append ea xs xss.flatten
    omega
namespace Procedure
noncomputable def listFlatten (ea : α→List Bool) (d : α) :
    Procedure (listCode (listCode ea)) (listCode ea) List.flatten:=by
  let step:=(listAppend ea d).comp ((second (listCode ea) (listCode ea)).pair
    (first (listCode ea) (listCode ea)))
  let p:=foldList [] step Polynomial.X (by
    intro xss xs i
    change (listCode ea ((xss.take i).foldl (fun xs ys=>xs++ys) xs)).length≤_
    rw [fold_append_flatten]
    have hh:=listCode_length_append ea xs (xss.take i).flatten
    have hl:=listCode_length_flatten_le ea (xss.take i)
    have ht:=listCode_length_take_le (listCode ea) i xss
    simp only [Polynomial.eval_X];omega)
  exact (p.comp ((identity (listCode (listCode ea))).pair (constant _ (listCode ea) []))).congrFun (by
    intro xss;exact fold_append_flatten xss [])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitEmissionModel.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
structure Op where
  gate : Gate
  wires : List ℕ

def eraseOp {q : ℕ} (o : Instruction q) : Op:=⟨o.gate,List.ofFn (fun i=>(o.wire i).val)⟩
def Op.encode (o : Op) : List Bool:=
  natWord o.gate.primitive.code++[o.gate.inverse,o.gate.controlled]++o.wires.flatMap natWord
lemma eraseOp_encode {q : ℕ} (o : Instruction q) : (eraseOp o).encode=o.encode := rfl

def Op.map (f : ℕ→ℕ) (o : Op) : Op:=⟨o.gate,o.wires.map f⟩
def Op.reverse (o : Op) : Op:=⟨o.gate.reverse,o.wires⟩
lemma eraseOp_place {q r : ℕ} (w : Register q r) (o : Instruction q) (f : ℕ→ℕ)
    (h : ∀i,(w i).val=f i.val) : eraseOp (o.place w)=(eraseOp o).map f := by
  simp only [eraseOp,Instruction.place,Op.map,List.map_ofFn,Function.comp_apply,h]
  rfl
lemma eraseOp_reverse {q : ℕ} (o : Instruction q) : eraseOp o.reverse=(eraseOp o).reverse := rfl

structure Data where
  qubits : ℕ
  ops : List Op

def erase (c : Circuit) : Data:=⟨c.qubits,c.instructions.map eraseOp⟩
def Data.encode (c : Data) : List Bool:=natWord c.qubits++natWord c.ops.length++c.ops.flatMap Op.encode
lemma erase_encode (c : Circuit) : (erase c).encode=c.encode := by
  simp only [erase,Data.encode,Circuit.encode,List.length_map,List.flatMap_map,eraseOp_encode]

def primitiveCode (p : Primitive) : List Bool:=BitStackProgram.unaryCode p.code
def gateView (g : Gate):= (g.primitive,g.inverse,g.controlled)
def gatePayload:=BitStackProgram.prodCode primitiveCode
  (BitStackProgram.prodCode BitStackProgram.Procedure.boolCode BitStackProgram.Procedure.boolCode)
def gateCode (g : Gate) : List Bool:=gatePayload (gateView g)
def opView (o : Op):=(o.gate,o.wires)
def opPayload:=BitStackProgram.prodCode gateCode (BitStackProgram.listCode Nat.bits)
def opCode (o : Op) : List Bool:=opPayload (opView o)
def dataView (c : Data):=(c.qubits,c.ops)
def dataPayload:=BitStackProgram.prodCode BitStackProgram.unaryCode (BitStackProgram.listCode opCode)
def dataCode (c : Data) : List Bool:=dataPayload (dataView c)

def Op.encodeClipped (cap : ℕ) (o : Op) : List Bool:=
  natWord o.gate.primitive.code++[o.gate.inverse,o.gate.controlled]++
    o.wires.flatMap (fun i=>natWord (min cap i))
def Data.encodeClipped (c : Data) : List Bool:=natWord c.qubits++natWord c.ops.length++
  c.ops.flatMap (Op.encodeClipped c.qubits)
lemma eraseOp_encodeClipped {q : ℕ} (o : Instruction q) :
    (eraseOp o).encodeClipped q=o.encode := by
  unfold Op.encodeClipped eraseOp Instruction.encode
  congr 1
  apply List.flatMap_congr
  intro i hi
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi
  rw [min_eq_right (Nat.le_of_lt (o.wire j).isLt)]
lemma erase_encodeClipped (c : Circuit) : (erase c).encodeClipped=c.encode := by
  simp only [erase,Data.encodeClipped,Circuit.encode,List.length_map,List.flatMap_map,
    eraseOp_encodeClipped]
end ExactQuantumFactoring.CircuitEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitBooleanEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open NetworkEmission

def notOp (t : ℕ) : Op:=⟨plainGate .not,[t]⟩
def cnotOp (a t : ℕ) : Op:=⟨plainGate .cnot,[a,t]⟩
def toffoliOp (a b t : ℕ) : Op:=⟨plainGate .toffoli,[a,b,t]⟩
lemma erase_notAt {q : ℕ} (t : Fin q) : eraseOp (notAt t)=notOp t.val:=rfl
lemma erase_cnotAt {q : ℕ} (a t : Fin q) (h : a≠t) : eraseOp (cnotAt a t h)=cnotOp a.val t.val:=rfl
lemma erase_toffoliAt {q : ℕ} (a b t : Fin q) (h : a≠b) (ha : a≠t) (hb : b≠t) :
    eraseOp (toffoliAt a b t h ha hb)=toffoliOp a.val b.val t.val:=rfl

def nodeOps (t : ℕ) : Node→List Op
  | .constant false=>[]
  | .constant true=>[notOp t]
  | .copy a=>[cnotOp a t]
  | .neg a=>[cnotOp a t,notOp t]
  | .conj a b=>if a=b then [cnotOp a t] else [toffoliOp a b t]
lemma erase_node_compile {n q : ℕ} (h : n+1≤q) (o : BoolNode n) :
    (o.compileOp h).compile.map eraseOp=nodeOps n (eraseNode o):=by
  cases o with
  | constant b=>cases b <;> rfl
  | copy a=>rfl
  | neg a=>rfl
  | conj a b=>
    simp only [BoolNode.compileOp,BooleanOp.compile,eraseNode,nodeOps]
    simp only [Fin.ext_iff,Fin.val_castLE]
    split_ifs <;> rfl

def netOps (n : ℕ) (xs : List Node) : List Op:=
  (xs.mapIdx (fun i o=>nodeOps (n+i) o)).flatten
lemma netOps_append_one (n : ℕ) (xs : List Node) (o : Node) :
    netOps n (xs++[o])=netOps n xs++nodeOps (n+xs.length) o:=by
  simp [netOps]
lemma erase_net_compile {n k q : ℕ} (p : BoolNet n k) (h : k≤q) :
    (p.program h).compile.map eraseOp=netOps n (eraseNet p):=by
  induction p with
  | input=>rfl
  | @add k p o ih=>
    simp only [BoolNet.program,BooleanProgram.compile,List.flatMap_append,List.flatMap_singleton,
      List.map_append,eraseNet,netOps_append_one]
    rw [←BooleanProgram.compile,ih,erase_node_compile,eraseNet_length,←p.width_eq]

def copyOps (k : ℕ) (xs : List ℕ) : List Op:=xs.mapIdx (fun i a=>cnotOp a (k+i))
lemma erase_copyPrefix {k m : ℕ} (f : Fin m→Fin k) (t : ℕ) (h : t ≤ m) :
    (BooleanNetwork.copyPrefix f t h).compile.map eraseOp=
      copyOps k (List.ofFn (fun i : Fin t=>(f (i.castLE h)).val)):=by
  induction t with
  | zero=>rfl
  | succ t ih=>
    simp only [BooleanNetwork.copyPrefix,BooleanProgram.compile,List.flatMap_append,
      List.flatMap_singleton,List.map_append]
    rw [←BooleanProgram.compile,ih]
    rw [List.ofFn_succ',List.concat_eq_append]
    simp only [copyOps,List.mapIdx_append_one,List.length_ofFn]
    rfl

def oracleOps (a : NetworkEmission.Data) : List Op:=
  let p:=netOps a.inputs a.nodes
  p++copyOps (a.inputs+a.nodes.length) a.outputs++p.reverse.map Op.reverse
lemma erase_oracle {n m : ℕ} (a : BooleanNetwork n m) :
    a.oracle.map eraseOp=oracleOps (NetworkEmission.erase a):=by
  simp only [BooleanNetwork.oracle,List.map_append,List.map_map,List.map_reverse]
  have hr : (eraseOp ∘ (Instruction.reverse : Instruction (a.width+m)→_))=Op.reverse ∘ eraseOp:=rfl
  rw [hr,←List.map_map,erase_net_compile,erase_copyPrefix]
  have hw:=a.net.width_eq
  simp only [oracleOps,NetworkEmission.erase,eraseNet_length,←hw,copyOps]
  simp only [Fin.castLE_rfl,List.map_reverse,id_eq]
end ExactQuantumFactoring.CircuitEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackListWords.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma flatten_length_le_code (xs : List (List Bool)) :
    xs.flatten.length ≤ (listCode (id : List Bool→List Bool) xs).length := by
  induction xs with
  | nil=>simp [listCode]
  | cons x xs ih=>
    simp only [List.flatten_cons,List.length_append,listCode_length_cons,id_eq]
    omega
lemma fold_append_words (xs : List (List Bool)) (ys : List Bool) :
    xs.foldl (fun ys x=>ys++x) ys=ys++xs.flatten := by
  induction xs generalizing ys with
  | nil=>simp
  | cons x xs ih=>simp [ih,List.append_assoc]
namespace Procedure
noncomputable def listJoinWords : Procedure (listCode (id : List Bool→List Bool)) id List.flatten := by
  let step:=(append.comp (swap (id : List Bool→List Bool) id))
  let rep:=foldList [] step Polynomial.X (by
    intro xs ys i
    change ((xs.take i).foldl (fun ys x=>ys++x) ys).length ≤ _
    rw [fold_append_words,List.length_append]
    have hh:=flatten_length_le_code (xs.take i)
    have ht:=listCode_length_take_le (id : List Bool→List Bool) i xs
    simp only [Polynomial.eval_X,id_eq]
    omega)
  exact (rep.comp ((identity (listCode (id : List Bool→List Bool))).pair
    (constant (listCode (id : List Bool→List Bool)) id []))).congrFun (by
      intro xs;change xs.foldl (fun ys x=>ys++x) []=xs.flatten
      simpa only [List.nil_append] using fold_append_words xs [])
noncomputable def listFlatMapWords {α : Type} {ea : α→List Bool} {f : α→List Bool}
    (d : α) (p : Procedure ea id f) : Procedure (listCode ea) id (fun xs=>xs.flatMap f) :=
  (listJoinWords.comp (listMap d [] p)).congrFun (by intro xs;rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackBoundedUnary.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def unaryDecodeStep (s : ℕ×ℕ) : ℕ×ℕ := if s.1=0 then s else (s.1-1,s.2+1)
lemma unaryDecodeStep_iterate (k : ℕ) (s : ℕ×ℕ) :
    (unaryDecodeStep^[k]) s=(s.1-k,s.2+min k s.1) := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>
    rw [Function.iterate_succ_apply,ih]
    unfold unaryDecodeStep
    split
    · rename_i hz
      apply Prod.ext <;> dsimp only <;> omega
    · rename_i hz
      apply Prod.ext <;> dsimp only <;> omega
namespace Procedure
noncomputable def unaryDecodeStepP : Procedure (prodCode Nat.bits unaryCode) (prodCode Nat.bits unaryCode)
    unaryDecodeStep := by
  let x:=first Nat.bits unaryCode
  let y:=second Nat.bits unaryCode
  let next:=(binarySub.comp (x.pair (Procedure.constant _ Nat.bits 1))).pair (unarySuccessor.comp y)
  exact (conditional (binaryZero.comp x) (identity _) next).congrFun (by
    intro s;unfold unaryDecodeStep;split <;> simp_all)
noncomputable def clippedUnary : Procedure (prodCode unaryCode Nat.bits) unaryCode (fun x=>min x.1 x.2) := by
  let rep:=unaryDecodeStepP.iterate Polynomial.X (by
    intro n s i hi
    rw [unaryDecodeStep_iterate]
    have hbits:=bits_length_mono (Nat.sub_le s.1 i)
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)
  let inp:=(first unaryCode Nat.bits).pair
    ((second unaryCode Nat.bits).pair (Procedure.constant _ unaryCode 0))
  exact ((second Nat.bits unaryCode).comp (rep.comp inp)).congrFun (by
    intro x;dsimp only [Function.comp_def];rw [unaryDecodeStep_iterate];simp)
noncomputable def boundedUnary {α : Type} {ea : α→List Bool} {f B : α→ℕ}
    (p : Procedure ea Nat.bits f) (b : Procedure ea unaryCode B) (h : ∀a,f a ≤ B a) :
    Procedure ea unaryCode f :=
  (clippedUnary.comp (b.pair p)).congrFun (by intro a;exact min_eq_right (h a))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitEmissionEncoding.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def natWordP : Procedure unaryCode id natWord :=
  ((append.comp ((identity (id : List Bool→List Bool)).pair
    (Procedure.constant (id : List Bool→List Bool) id [false]))).precompose unaryCode).congrFun (by intro n;rfl)
noncomputable def gateViewP : Procedure gateCode gatePayload gateView:=
  (identity gatePayload).precompose gateView
noncomputable def gatePrimitiveP : Procedure gateCode primitiveCode Gate.primitive:=
  (first primitiveCode _).comp gateViewP
noncomputable def gateInverseP : Procedure gateCode boolCode Gate.inverse:=
  (first boolCode boolCode).comp ((second primitiveCode _).comp gateViewP)
noncomputable def gateControlledP : Procedure gateCode boolCode Gate.controlled:=
  (second boolCode boolCode).comp ((second primitiveCode _).comp gateViewP)
noncomputable def gateHeaderP : Procedure gateCode id
    (fun g=>natWord g.primitive.code++[g.inverse,g.controlled]) := by
  let primitiveWord:=(natWordP.precompose Primitive.code).comp gatePrimitiveP
  let c:=cons.comp (gateControlledP.pair (Procedure.constant gateCode id []))
  let tail:=cons.comp (gateInverseP.pair c)
  exact (append.comp (primitiveWord.pair tail)).congrFun (by intro g;rfl)
noncomputable def opViewP : Procedure opCode opPayload opView:=
  (identity opPayload).precompose opView
noncomputable def opGateP : Procedure opCode gateCode Op.gate:=
  (first gateCode (listCode Nat.bits)).comp opViewP
noncomputable def opWiresP : Procedure opCode (listCode Nat.bits) Op.wires:=
  (second gateCode (listCode Nat.bits)).comp opViewP
noncomputable def wireWordsP : Procedure (prodCode unaryCode (listCode Nat.bits)) id
    (fun x=>x.2.flatMap (fun i=>natWord (min x.1 i))) :=
  (listJoinWords.comp (listMapWith (f:=fun cap i=>natWord (min cap i)) 0 []
    (natWordP.comp clippedUnary))).congrFun (by intro x;rfl)
noncomputable def opEncodeClippedP : Procedure (prodCode unaryCode opCode) id
    (fun x=>x.2.encodeClipped x.1) := by
  let cap:=first unaryCode opCode
  let o:=second unaryCode opCode
  let header:=gateHeaderP.comp (opGateP.comp o)
  let wires:=wireWordsP.comp (cap.pair (opWiresP.comp o))
  exact (append.comp (header.pair wires)).congrFun (by intro x;rfl)
noncomputable def dataViewP : Procedure dataCode dataPayload dataView:=
  (identity dataPayload).precompose dataView
noncomputable def qubitsP : Procedure dataCode unaryCode Data.qubits:=
  (first unaryCode (listCode opCode)).comp dataViewP
noncomputable def opsP : Procedure dataCode (listCode opCode) Data.ops:=
  (second unaryCode (listCode opCode)).comp dataViewP
noncomputable def encodeClippedP : Procedure dataCode id Data.encodeClipped := by
  let qword:=natWordP.comp qubitsP
  let len:=(NativeAIG.Emission.listUnaryLength opCode ⟨plainGate .not,[]⟩).comp opsP
  let nword:=natWordP.comp len
  let words:=(listMapWith (f:=fun cap (o : Op)=>o.encodeClipped cap)
    ⟨plainGate .not,[]⟩ [] opEncodeClippedP).comp (qubitsP.pair opsP)
  let payload:=listJoinWords.comp words
  exact (append.comp ((append.comp (qword.pair nword)).pair payload)).congrFun (by intro x;rfl)
end Emission

/-- This reduction charges all unary description writing, including every wire.
It is useful only with an actual finite-stack emitter for the literal erased family. -/
theorem uniform_of_emitter (family : ℕ→Circuit)
    (p : Procedure unaryCode dataCode (fun n=>erase (family n))) : Uniform family := by
  let pp : Procedure unaryCode Circuit.encode family:=
    (Emission.encodeClippedP.comp p).result (by intro n;exact erase_encodeClipped (family n))
  exact ⟨pp.toTM2,pp.toTM2_finite⟩
end ExactQuantumFactoring.CircuitEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackListMapIdx.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β γ : Type}
lemma map_range_getD_index (xs : List β) (d : β) (f : ℕ→β→γ) :
    (List.range xs.length).map (fun i=>f i ((xs.drop i).headD d))=xs.mapIdx f:=by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i<xs.length:=by simpa using h1
    simp only [List.getElem_map,List.getElem_range,List.getElem_mapIdx]
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi,Option.getD_some]
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool} {f : α→ℕ→β→γ}
noncomputable def listMapIdxWith (d : β) (e : γ)
    (p : Procedure (prodCode ea (prodCode Nat.bits eb)) ec (fun x=>f x.1 x.2.1 x.2.2)) :
    Procedure (prodCode ea (listCode eb)) (listCode ec) (fun x=>x.2.mapIdx (f x.1)):=by
  let i:=unaryToBits.comp (first unaryCode (prodCode ea (listCode eb)))
  let env:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp env
  let xs:=(second ea (listCode eb)).comp env
  let get:=(listGet eb d).comp (i.pair xs)
  let step:=p.comp (a.pair (i.pair get))
  let len:=(NativeAIG.Emission.listUnaryLength eb d).comp (second ea (listCode eb))
  exact ((tabulate (f:=fun (env : α×List β) i=>f env.1 i ((env.2.drop i).headD d)) e step).comp
    (len.pair (identity (prodCode ea (listCode eb))))).congrFun (by
      intro x;exact map_range_getD_index x.2 d (f x.1))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitEmissionBasic.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def opPackP : Procedure opPayload opCode (fun x=>Op.mk x.1 x.2):=
  (identity opPayload).result (by intro x;rfl)
noncomputable def dataPackP : Procedure dataPayload dataCode (fun x=>Data.mk x.1 x.2):=
  (identity dataPayload).result (by intro x;rfl)
noncomputable def gatePackP : Procedure gatePayload gateCode (fun x=>Gate.mk x.1 x.2.1 x.2.2):=
  (identity gatePayload).result (by intro x;rfl)
noncomputable def gateReverseP : Procedure gateCode gateCode Gate.reverse:=
  gatePackP.comp (gatePrimitiveP.pair ((boolNot.comp gateInverseP).pair gateControlledP))
noncomputable def opReverseP : Procedure opCode opCode Op.reverse:=
  opPackP.comp ((gateReverseP.comp opGateP).pair opWiresP)
noncomputable def opsReverseP : Procedure (listCode opCode) (listCode opCode)
    (fun xs=>xs.reverse.map Op.reverse):=
  (listMap ⟨plainGate .not,[]⟩ ⟨plainGate .not,[]⟩ opReverseP).comp (listReverse opCode ⟨plainGate .not,[]⟩)
noncomputable def opMapWith {α : Type} {ea : α→List Bool} {f : α→ℕ→ℕ}
    (p : Procedure (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea opCode) opCode (fun x=>x.2.map (f x.1)):=by
  let a:=first ea opCode
  let o:=second ea opCode
  exact opPackP.comp ((opGateP.comp o).pair (((listMapWith 0 0 p)).comp (a.pair (opWiresP.comp o))))
noncomputable def opsMapWith {α : Type} {ea : α→List Bool} {f : α→ℕ→ℕ}
    (p : Procedure (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea (listCode opCode)) (listCode opCode) (fun x=>x.2.map (Op.map (f x.1))):=
  listMapWith (f:=fun (a : α) (o : Op)=>o.map (f a)) ⟨plainGate .not,[]⟩ ⟨plainGate .not,[]⟩ (opMapWith p)
noncomputable def opsAppendP : Procedure (prodCode (listCode opCode) (listCode opCode)) (listCode opCode)
    (fun x=>x.1++x.2):=listAppend opCode ⟨plainGate .not,[]⟩
noncomputable def notOpP : Procedure Nat.bits opCode notOp:=by
  let wires:=(listCons Nat.bits).comp ((identity Nat.bits).pair (Procedure.constant _ (listCode Nat.bits) []))
  exact opPackP.comp ((Procedure.constant Nat.bits gateCode (plainGate .not)).pair wires)
noncomputable def cnotOpP : Procedure (prodCode Nat.bits Nat.bits) opCode (fun x=>cnotOp x.1 x.2):=by
  let a:=first Nat.bits Nat.bits
  let b:=second Nat.bits Nat.bits
  let tail:=(listCons Nat.bits).comp (b.pair (Procedure.constant _ (listCode Nat.bits) []))
  let wires:=(listCons Nat.bits).comp (a.pair tail)
  exact opPackP.comp ((Procedure.constant _ gateCode (plainGate .cnot)).pair wires)
noncomputable def toffoliOpP : Procedure (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) opCode
    (fun x=>toffoliOp x.1 x.2.1 x.2.2):=by
  let a:=first Nat.bits (prodCode Nat.bits Nat.bits)
  let rs:=second Nat.bits (prodCode Nat.bits Nat.bits)
  let b:=(first Nat.bits Nat.bits).comp rs
  let c:=(second Nat.bits Nat.bits).comp rs
  let tail:=(listCons Nat.bits).comp (c.pair (Procedure.constant _ (listCode Nat.bits) []))
  let mid:=(listCons Nat.bits).comp (b.pair tail)
  let wires:=(listCons Nat.bits).comp (a.pair mid)
  exact opPackP.comp ((Procedure.constant _ gateCode (plainGate .toffoli)).pair wires)
noncomputable def opSingletonP : Procedure opCode (listCode opCode) (fun o=>[o]):=
  (listCons opCode).comp ((identity opCode).pair (Procedure.constant opCode (listCode opCode) []))
noncomputable def nodeOpsP : Procedure (prodCode Nat.bits NetworkEmission.nodeCode) (listCode opCode)
    (fun x=>nodeOps x.1 x.2):=by
  let t:=first Nat.bits NetworkEmission.nodeCode
  let o:=second Nat.bits NetworkEmission.nodeCode
  let tag:=NetworkEmission.Emission.nodeTagP.comp o
  let eq (i : ℕ):=binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits i))
  let a:=NetworkEmission.Emission.nodeLhsP.comp o
  let b:=NetworkEmission.Emission.nodeRhsP.comp o
  let n:=opSingletonP.comp (notOpP.comp t)
  let c:=opSingletonP.comp (cnotOpP.comp (a.pair t))
  let neg:=opsAppendP.comp (c.pair n)
  let conj:=conditional (binaryEq.comp (a.pair b)) c
    (opSingletonP.comp (toffoliOpP.comp (a.pair (b.pair t))))
  let const:=conditional (NetworkEmission.Emission.nodeBoolP.comp o) n (Procedure.constant _ (listCode opCode) [])
  exact (conditional (eq 0) const (conditional (eq 1) c (conditional (eq 2) neg conj))).congrFun (by
    rintro ⟨t,o⟩
    cases o with
    | constant b=>cases b <;> rfl
    | copy i=>rfl
    | neg i=>rfl
    | conj a b=>simp only [Function.comp_apply,NetworkEmission.nodeView,decide_eq_true_eq,nodeOps];rfl)
noncomputable def netOpsP : Procedure (prodCode Nat.bits (listCode NetworkEmission.nodeCode)) (listCode opCode)
    (fun x=>netOps x.1 x.2):=by
  let n:=first Nat.bits (prodCode Nat.bits NetworkEmission.nodeCode)
  let rs:=second Nat.bits (prodCode Nat.bits NetworkEmission.nodeCode)
  let i:=(first Nat.bits NetworkEmission.nodeCode).comp rs
  let o:=(second Nat.bits NetworkEmission.nodeCode).comp rs
  let step:=nodeOpsP.comp ((binaryAdd.comp (n.pair i)).pair o)
  let xs:=listMapIdxWith (f:=fun n i o=>nodeOps (n+i) o) (.constant false) [] step
  exact (listFlatten opCode ⟨plainGate .not,[]⟩).comp xs
noncomputable def copyOpsP : Procedure (prodCode Nat.bits (listCode Nat.bits)) (listCode opCode)
    (fun x=>copyOps x.1 x.2):=by
  let n:=first Nat.bits (prodCode Nat.bits Nat.bits)
  let rs:=second Nat.bits (prodCode Nat.bits Nat.bits)
  let i:=(first Nat.bits Nat.bits).comp rs
  let a:=(second Nat.bits Nat.bits).comp rs
  let step:=cnotOpP.comp (a.pair (binaryAdd.comp (n.pair i)))
  exact listMapIdxWith (f:=fun n i a=>cnotOp a (n+i)) 0 ⟨plainGate .not,[]⟩ step
noncomputable def oracleOpsP : Procedure NetworkEmission.dataCode (listCode opCode) oracleOps:=by
  let n:=NetworkEmission.Emission.dataInputP
  let xs:=NetworkEmission.Emission.dataNodesP
  let os:=NetworkEmission.Emission.dataOutputsP
  let w:=NetworkEmission.Emission.dataWidthP
  let p:=netOpsP.comp (n.pair xs)
  exact opsAppendP.comp ((opsAppendP.comp (p.pair (copyOpsP.comp (w.pair os)))).pair (opsReverseP.comp p))
end Emission
end ExactQuantumFactoring.CircuitEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitProgramEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
namespace NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n m : α→ℕ}
lemma data {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    Emits ea dataCode (fun x=>erase (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  exact ((ofProcedure Emission.packValueP).comp hp).congr he
lemma count {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    Emits ea unaryCode (fun x=>(f x).net.count):=by
  exact ((ofProcedure ((NativeAIG.Emission.listUnaryLength nodeCode (.constant false)).comp
    Emission.dataNodesP)).comp hf.data).congr (by intro x;exact eraseNet_length _)
lemma outLength {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    Emits ea unaryCode m:=by
  exact ((ofProcedure ((NativeAIG.Emission.listUnaryLength Nat.bits 0).comp
    Emission.dataOutputsP)).comp hf.data).congr (by intro x;exact List.length_ofFn)
end NetworkEmission.NetEmits

namespace CircuitEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits

def oracleOnOps (a : NetworkEmission.Data) : List Op:=
  (oracleOps a).map (Op.map (BooleanNetwork.oracleIndex a.inputs a.outputs.length a.width))
lemma erase_oracleOn {n m r : ℕ} (a : BooleanNetwork n m) (hr : a.net.count≤r) :
    (BooleanNetwork.oracleOn a hr).map eraseOp=oracleOnOps (NetworkEmission.erase a):=by
  simp only [BooleanNetwork.oracleOn,List.map_map]
  rw [show (eraseOp ∘ Instruction.place (BooleanNetwork.oraclePlacement a hr))=
    (fun o=>(eraseOp o).map (BooleanNetwork.oracleIndex n m a.width)) by
      funext o;exact eraseOp_place _ _ _ (fun _=>rfl)]
  change List.map ((Op.map (BooleanNetwork.oracleIndex n m a.width)) ∘ eraseOp) a.oracle=_
  rw [←List.map_map,erase_oracle]
  simp only [oracleOnOps,NetworkEmission.erase,List.length_ofFn,NetworkEmission.Data.width,
    NetworkEmission.eraseNet_length,←a.net.width_eq]
lemma erase_firstProgram {n m r : ℕ} (ops : List (Instruction n)) :
    (firstProgram m r ops).map eraseOp=ops.map eraseOp:=by
  simp only [firstProgram,List.map_map]
  apply List.map_congr_left
  intro o ho
  rw [Function.comp_apply,eraseOp_place _ _ id (fun _=>rfl)]
  simp [Op.map]
lemma erase_reverseProgram {q : ℕ} (ops : List (Instruction q)) :
    (ops.reverse.map Instruction.reverse).map eraseOp=(ops.map eraseOp).reverse.map Op.reverse:=by
  simp only [List.map_map,List.map_reverse]
  rfl

def phaseOp (n : ℕ) : Op:=⟨plainGate .phase,[n]⟩
lemma erase_phaseAt {q : ℕ} (i : Fin q) : eraseOp (phaseAt i)=phaseOp i.val:=rfl

def phaseOps (a : NetworkEmission.Data) : List Op:=
  oracleOnOps a++[phaseOp a.inputs,phaseOp a.inputs]++oracleOnOps a
lemma erase_phaseOracle {n r : ℕ} (a : BooleanNetwork n 1) (hr : a.net.count≤r) :
    (BooleanNetwork.phaseOracle a hr).map eraseOp=phaseOps (NetworkEmission.erase a):=by
  simp only [BooleanNetwork.phaseOracle,List.map_append,List.map_cons,List.map_nil,erase_oracleOn,
    erase_phaseAt,BooleanNetwork.phaseTarget,phaseOps,NetworkEmission.erase]

def amplifyOps (ps : List Op) (a z : NetworkEmission.Data) : List Op:=
  ps++phaseOps a++ps.reverse.map Op.reverse++phaseOps z++ps
lemma erase_amplification {n r : ℕ} (ops : List (Instruction n))
    (a z : BooleanNetwork n 1) (ha : a.net.count≤r) (hz : z.net.count≤r) :
    (amplificationProgram ops a z ha hz).map eraseOp=
      amplifyOps (ops.map eraseOp) (NetworkEmission.erase a) (NetworkEmission.erase z):=by
  simp only [amplificationProgram,List.map_append,erase_firstProgram,erase_phaseOracle,
    erase_reverseProgram,amplifyOps]

namespace Emission
noncomputable def oracleIndexP : Procedure
    (prodCode (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits) Nat.bits
    (fun x=>BooleanNetwork.oracleIndex x.1.1 x.1.2.1 x.1.2.2 x.2):=by
  let e:=first (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let i:=second (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let n:=(first Nat.bits (prodCode Nat.bits Nat.bits)).comp e
  let m:=(first Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let w:=(second Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let input:=binaryLt.comp (i.pair n)
  let work:=binaryLt.comp (i.pair w)
  let wi:=binaryAdd.comp ((binaryAdd.comp (n.pair m)).pair (binarySub.comp (i.pair n)))
  let oi:=binaryAdd.comp (n.pair (binarySub.comp (i.pair w)))
  exact (conditional input i (conditional work wi oi)).congrFun (by intro x;simp [BooleanNetwork.oracleIndex])
noncomputable def oracleOnOpsP : Procedure NetworkEmission.dataCode (listCode opCode) oracleOnOps:=by
  let env:=NetworkEmission.Emission.dataInputP.pair
    (((listLength Nat.bits 0).comp NetworkEmission.Emission.dataOutputsP).pair NetworkEmission.Emission.dataWidthP)
  exact (opsMapWith (f:=fun (e:ℕ×ℕ×ℕ) i=>BooleanNetwork.oracleIndex e.1 e.2.1 e.2.2 i) oracleIndexP).comp (env.pair oracleOpsP)
noncomputable def phaseOpP : Procedure Nat.bits opCode phaseOp:=
  opPackP.comp ((constant Nat.bits gateCode (plainGate .phase)).pair
    ((listCons Nat.bits).comp ((identity Nat.bits).pair (constant Nat.bits (listCode Nat.bits) []))))
noncomputable def phaseOpsP : Procedure NetworkEmission.dataCode (listCode opCode) phaseOps:=by
  let p:=phaseOpP.comp NetworkEmission.Emission.dataInputP
  let mid:=(listCons opCode).comp (p.pair ((listCons opCode).comp (p.pair (constant _ (listCode opCode) []))))
  exact opsAppendP.comp ((opsAppendP.comp (oracleOnOpsP.pair mid)).pair oracleOnOpsP)
end Emission

abbrev OpsEmits {α : Type} (ea : α→List Bool) {q : α→ℕ} (p : ∀x,List (Instruction (q x))) : Prop:=
  Emits ea (listCode opCode) (fun x=>(p x).map eraseOp)
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {q m r : α→ℕ}
lemma congr {p s : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (h : ∀x,p x=s x) : OpsEmits ea s:=
  BitStackProgram.Emits.congr hp (fun x=>congrArg (List.map eraseOp) (h x))
lemma append {p s : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (hs : OpsEmits ea s) :
    OpsEmits ea (fun x=>p x++s x):=
  (hp.listAppend ⟨plainGate .not,[]⟩ hs).congr (fun _=>List.map_append.symm)
lemma first {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (m r : α→ℕ) :
    OpsEmits ea (fun x=>firstProgram (m x) (r x) (p x)):=BitStackProgram.Emits.congr hp (fun _=>(erase_firstProgram _).symm)
lemma reverse {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) :
    OpsEmits ea (fun x=>(p x).reverse.map Instruction.reverse):=
  ((ofProcedure Emission.opsReverseP).comp hp).congr (fun _=>(erase_reverseProgram _).symm)
lemma oracleOn {f : ∀x,BooleanNetwork (q x) (m x)} (hf : NetworkEmission.NetEmits ea f)
    (h : ∀x,(f x).net.count≤r x) : OpsEmits ea (fun x=>BooleanNetwork.oracleOn (f x) (h x)):=
  ((ofProcedure Emission.oracleOnOpsP).comp hf.data).congr (fun _=>(erase_oracleOn _ _).symm)
lemma phase {f : ∀x,BooleanNetwork (q x) 1} (hf : NetworkEmission.NetEmits ea f)
    (h : ∀x,(f x).net.count≤r x) : OpsEmits ea (fun x=>BooleanNetwork.phaseOracle (f x) (h x)):=
  ((ofProcedure Emission.phaseOpsP).comp hf.data).congr (fun _=>(erase_phaseOracle _ _).symm)
lemma amplify {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    {f g : ∀x,BooleanNetwork (q x) 1} (hf : NetworkEmission.NetEmits ea f) (hg : NetworkEmission.NetEmits ea g)
    (h : ∀x,(f x).net.count≤r x) (j : ∀x,(g x).net.count≤r x) :
    OpsEmits ea (fun x=>amplificationProgram (p x) (f x) (g x) (h x) (j x)):=
  ((((hp.first (fun _=>1) r).append (hf |> fun hf=>phase hf h)).append
    (hp.reverse.first (fun _=>1) r)).append (phase hg j)).append (hp.first (fun _=>1) r)
lemma readout {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    {f : ∀x,BooleanNetwork (q x) (m x)} (hf : NetworkEmission.NetEmits ea f)
    (h : ∀x,(f x).net.count≤r x) : OpsEmits ea (fun x=>readoutProgram (p x) (f x) (h x)):=
  (hp.first m r).append (oracleOn hf h)
end OpsEmits
end CircuitEmission
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitFinalEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α : Type} {ea : α→List Bool}
lemma unaryMax {f g : α→ℕ} (hf : Emits ea unaryCode f) (hg : Emits ea unaryCode g) :
    Emits ea unaryCode (fun x=>max (f x) (g x)):=by
  exact ((ofProcedure clippedUnary).comp ((hf.unaryAdd hg).pair
    (hf.unaryNat.natMax hg.unaryNat))).congr (by intro x;exact min_eq_right (max_le (by omega) (by omega)))
lemma range {f : α→ℕ} (hf : Emits ea unaryCode f) : Emits ea (listCode Nat.bits) (fun x=>List.range (f x)):=
  (ofProcedure NetworkEmission.Emission.rangeP).comp hf
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {q r : α→ℕ}
lemma place {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    (w : ∀x,Register (q x) (r x)) (f : α→ℕ→ℕ)
    (hw : ∀x i,(w x i).val=f x i.val)
    (hf : Emits (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    OpsEmits ea (fun x=>(p x).map (Instruction.place (w x))):=by
  obtain ⟨pf⟩:=hf
  exact ((ofProcedure (Emission.opsMapWith pf)).comp ((BitStackProgram.Emits.id ea).pair hp)).congr (by
    intro x
    simp only [List.map_map]
    apply List.map_congr_left
    intro o ho
    exact (eraseOp_place (w x) o (f x) (hw x)).symm)
end OpsEmits
namespace Emission
noncomputable def relocateValP : Procedure
    (prodCode (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits) Nat.bits
    (fun x=>relocateVal x.1.1 x.1.2.1 x.1.2.2 x.2):=by
  let e:=first (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let i:=second (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let a:=(first Nat.bits (prodCode Nat.bits Nat.bits)).comp e
  let m:=(first Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let l:=(second Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let z:=binaryEq.comp (i.pair (constant _ Nat.bits 0))
  let il:=boolNot.comp (binaryLt.comp (l.pair i))
  let ia:=binaryLt.comp (i.pair a)
  let iam:=binaryLt.comp (i.pair (binaryAdd.comp (a.pair m)))
  let case0:=binaryAdd.comp (l.pair m)
  let case1:=binarySub.comp (i.pair (constant _ Nat.bits 1))
  let case2:=binaryAdd.comp (i.pair m)
  let case3:=binaryAdd.comp (l.pair (binarySub.comp (i.pair a)))
  exact (conditional z case0 (conditional il case1 (conditional ia case2 (conditional iam case3 i)))).congrFun (by
    intro x;simp only [Function.comp_apply,decide_eq_true_eq,relocateVal,Bool.not_eq_true',decide_eq_false_iff_not,not_lt])
end Emission
end ExactQuantumFactoring.CircuitEmission

namespace ExactQuantumFactoring.UniformResources.PhysicalTree
open BitStackProgram BitStackProgram.Emits NetworkEmission CircuitEmission
open ExactQuantumFactoring.PhysicalTree

/-- A precise remaining syntax boundary. All post-quarter amplification,
clean oracle synthesis, readout, relocation, and unary serialization are actual
charged finite-stack procedures; none is a generation-time oracle. -/
theorem uniform_of_quarter_emitters
    (hw : Emits unaryCode unaryCode (fun l=>quarterWidth (paddedLength l)))
    (hp : OpsEmits unaryCode (fun l=>quarterProgram (paddedLength l)))
    (hf : NetEmits unaryCode (fun l=>quarterFlag (paddedLength l) (paddedLength_pos l)))
    (hz : NetEmits unaryCode (fun l=>zeroNet (paddedLength l)))
    (ho : NetEmits unaryCode (fun l=>quarterOutputNet (paddedLength l))) :
    Uniform finalCircuit:=by
  have hr : Emits unaryCode unaryCode (fun l=>reflectWork (paddedLength l) (paddedLength_pos l)):=hf.count.unaryMax hz.count
  have ha : Emits unaryCode unaryCode (fun l=>amplifiedWidth (paddedLength l) (paddedLength_pos l)):=hw.unarySucc.unaryAdd hr
  have hs : NetEmits unaryCode (fun l=>BooleanNetwork.select
      (firstRegister (quarterWidth (paddedLength l)) 1 (reflectWork (paddedLength l) (paddedLength_pos l)))):=by
    apply NetEmits.select ha
    exact hw.range.congr (by intro l;change List.range (quarterWidth (paddedLength l))=List.ofFn (fun i:Fin (quarterWidth (paddedLength l))=>i.val);exact (ofFn_val_range _).symm)
  have hao : NetEmits unaryCode (fun l=>amplifiedOutput (paddedLength l) (paddedLength_pos l)):=hs.comp ho
  have hap : OpsEmits unaryCode (fun l=>amplifiedProgram (paddedLength l) (paddedLength_pos l)):=
    hp.amplify hf hz (fun _=>Nat.le_max_left _ _) (fun _=>Nat.le_max_right _ _)
  have hfact : OpsEmits unaryCode (fun l=>factoringProgram (paddedLength l) (paddedLength_pos l)):=
    hap.readout hao (fun _=>le_rfl)
  have hn : Emits unaryCode unaryCode paddedLength:=
    (const unaryCode unaryCode 128).unaryMax (BitStackProgram.Emits.id unaryCode)
  have hm:=hn.unaryMul hn
  have hq : Emits unaryCode unaryCode (fun l=>readoutWidth (paddedLength l) (paddedLength_pos l)):=
    (ha.unaryAdd hm).unaryAdd hao.count
  have hrel : Emits (prodCode unaryCode Nat.bits) Nat.bits
      (fun x=>relocateVal (amplifiedWidth (paddedLength x.1) (paddedLength_pos x.1))
        (paddedLength x.1*paddedLength x.1) x.1 x.2):=by
    have he:=(BitStackProgram.Emits.id (prodCode unaryCode Nat.bits)).fst
    have hi:=(BitStackProgram.Emits.id (prodCode unaryCode Nat.bits)).snd
    exact (ofProcedure CircuitEmission.Emission.relocateValP).comp
      (((ha.unaryNat.comp he).pair ((hm.unaryNat.comp he).pair he.unaryNat)).pair hi)
  have hP : OpsEmits unaryCode (fun l=>(finalCircuit l).instructions):=
    hfact.place finalRegister
      (fun l i=>relocateVal (amplifiedWidth (paddedLength l) (paddedLength_pos l))
        (paddedLength l*paddedLength l) l i) (fun _ _=>rfl) hrel
  obtain ⟨pp⟩:=(ofProcedure CircuitEmission.Emission.dataPackP).comp (hq.pair hP)
  exact CircuitEmission.uniform_of_emitter finalCircuit pp
end ExactQuantumFactoring.UniformResources.PhysicalTree

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitCleanEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma ite {c : α→Bool} {a b : α→β} (hc : Emits ea boolCode c)
    (ha : Emits ea eb a) (hb : Emits ea eb b) :
    Emits ea eb (fun x=>if c x then a x else b x):=by
  obtain ⟨pc⟩:=hc;obtain ⟨pa⟩:=ha;obtain ⟨pb⟩:=hb
  exact ofProcedure (Procedure.conditional pc pa pb)
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {n m : β→ℕ}
lemma input {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits eb f)
    {g : α→β} (hg : Emits ea eb g) : NetEmits ea (fun x=>f (g x)):=by
  obtain ⟨p,hp,he⟩:=hf
  exact ⟨fun x=>p (g x),hp.comp hg,fun x=>he (g x)⟩
end NetEmits
namespace PhysicalTreeEmission
open PhysicalTree
lemma zeroNet {α : Type} {ea : α→List Bool} {n : α→ℕ}
    (hn : Emits ea unaryCode n) (hw : Emits ea unaryCode (fun x=>quarterWidth (n x))) :
    NetEmits ea (fun x=>PhysicalTree.zeroNet (n x)):=by
  let p : α→ℕ→Pack:=fun x i=>if (1 ≤ i) ∧ (i < 1+n x) then constantPack (quarterWidth (n x)) true
    else bnotPack (bitPack (quarterWidth (n x)) i)
  have he:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hi:=he.fst.unaryNat
  have hN:=hn.comp he.snd
  have hW:=hw.comp he.snd
  have hc:=((hi.natLt (const _ _ 1)).boolNot).boolAnd
    (hi.natLt ((const _ _ 1).natAdd hN.unaryNat))
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1):=by
    have ha:=(ofProcedure Emission.constantPackP).comp (hW.pair (const _ _ true))
    have hb:=(ofProcedure Emission.bnotPackP).comp
      ((ofProcedure Emission.bitPackP).comp (hW.pair hi))
    exact (hc.ite ha hb).congr (by
      intro x
      simp only [p,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,not_lt,decide_eq_true_eq])
  apply NetEmits.allIndexed hw hw p hp
  intro x i
  simp only [inputWires,Finset.mem_filter,Finset.mem_univ,true_and]
  dsimp only [p]
  split
  · exact constantPack_value _ _
  · exact bnotPack_value _ _ (bitPack_value i)
end PhysicalTreeEmission
end ExactQuantumFactoring.NetworkEmission

namespace ExactQuantumFactoring.UniformResources.PhysicalTree
open BitStackProgram BitStackProgram.Emits NetworkEmission CircuitEmission
open ExactQuantumFactoring.PhysicalTree
theorem uniform_of_quarter_emitters_clean
    (hw : Emits unaryCode unaryCode (fun l=>quarterWidth (paddedLength l)))
    (hp : OpsEmits unaryCode (fun l=>quarterProgram (paddedLength l)))
    (hf : NetEmits unaryCode (fun l=>quarterFlag (paddedLength l) (paddedLength_pos l)))
    (ho : NetEmits unaryCode (fun l=>quarterOutputNet (paddedLength l))) :
    Uniform finalCircuit:=by
  have hn : Emits unaryCode unaryCode paddedLength:=
    (const unaryCode unaryCode 128).unaryMax (BitStackProgram.Emits.id unaryCode)
  exact uniform_of_quarter_emitters hw hp hf (PhysicalTreeEmission.zeroNet hn hw) ho
end ExactQuantumFactoring.UniformResources.PhysicalTree

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackDependentChoice.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f : α→β}
noncomputable def chooseBitD (c : α→Prop) [DecidablePred c]
    (p : Procedure (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val))
    (q : Procedure (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val)) :
    Procedure (fun a=>decide (c a)::ea a) eb f where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs a:=by
    have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
    have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (ea a).length)
    by_cases h:c a
    · obtain ⟨t,ht,hd⟩:=q.shared.runs ⟨a,h⟩
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨t+1,?_,?_⟩
      · simpa only [List.length_cons,Polynomial.eval_add,Polynomial.eval_one] using
          Nat.add_le_add_right ((ht.trans hqmono).trans (Nat.le_add_left
            (q.shared.bound.eval ((ea a).length+1)) (p.shared.bound.eval ((ea a).length+1)))) 1
      · simp only [h,decide_true]
        have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (true::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    · obtain ⟨t,ht,hd⟩:=p.shared.runs ⟨a,h⟩
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨t+1,?_,?_⟩
      · simpa only [List.length_cons,Polynomial.eval_add,Polynomial.eval_one] using
          Nat.add_le_add_right ((ht.trans hpmono).trans (Nat.le_add_right
            (p.shared.bound.eval ((ea a).length+1)) (q.shared.bound.eval ((ea a).length+1)))) 1
      · simp only [h,decide_false]
        have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
noncomputable def splitOn (c : α→Prop) [DecidablePred c]
    (test : Procedure ea boolCode (fun a=>decide (c a)))
    (yes : Procedure (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val))
    (no : Procedure (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val)) : Procedure ea eb f:=by
  let p:=no.comp (unprefix (fun x:{a // ¬c a}=>ea x.val) false)
  let q:=yes.comp (unprefix (fun x:{a // c a}=>ea x.val) false)
  let choice:=(chooseBitD c p q).comp (unprefix (fun a=>decide (c a)::false::ea a) true)
  let input:= (test.pair (identity ea)).result (ec:=fun a=>true::decide (c a)::false::ea a)
    (h:=id) (by intro a;rfl)
  exact choice.comp input
end ExactQuantumFactoring.BitStackProgram.Procedure

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f : α→β}
lemma splitOn (c : α→Prop) [DecidablePred c]
    (test : Emits ea Procedure.boolCode (fun a=>decide (c a)))
    (yes : Emits (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val))
    (no : Emits (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val)) : Emits ea eb f:=by
  obtain ⟨p⟩:=test;obtain ⟨q⟩:=yes;obtain ⟨r⟩:=no
  exact ⟨Procedure.splitOn c p q r⟩
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkDependentEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma extendPack (hk : Emits ea unaryCode k)
    (p : (Σx,Fin (k x))→Pack)
    (hp : Emits (fun x:Σx,Fin (k x)=>prodCode unaryCode ea (x.2.val,x.1)) packCode p) :
    ∃q : α→ℕ→Pack, Emits (prodCode unaryCode ea) packCode (fun x=>q x.2 x.1) ∧
      ∀x i,q x i.val=p ⟨x,i⟩:=by
  let c:=fun x:ℕ×α=>x.1<k x.2
  let q:=fun x i=>if h:i<k x then p ⟨x,⟨i,h⟩⟩ else emptyPack
  have he:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hc:=(ofProcedure Procedure.binaryLt).comp
    (he.fst.unaryNat.pair (hk.comp he.snd).unaryNat)
  have hy : Emits (fun x:{a:ℕ×α // c a}=>prodCode unaryCode ea x.val) packCode
      (fun x=>q x.val.2 x.val.1):=by
    have h:=hp.precompose (fun x:{a:ℕ×α // c a}=>(⟨x.val.2,⟨x.val.1,x.property⟩⟩ : Σx,Fin (k x)))
    exact h.congr (by intro x;dsimp only [q];rw [dite_eq_left x.property])
  have hn : Emits (fun x:{a:ℕ×α // ¬c a}=>prodCode unaryCode ea x.val) packCode
      (fun x=>q x.val.2 x.val.1):=by
    exact (const _ _ emptyPack).congr (by intro x;dsimp only [q];rw [dite_eq_right x.property])
  exact ⟨q,BitStackProgram.Emits.splitOn c hc hy hn,by intro x i;simp only [q,i.isLt,dite_eq_left]⟩
lemma allOfFn {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σx,Fin (k x)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (f x))):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hk p hp
  exact allIndexed hn hk q hq (by intro x i;rw [eq];exact he ⟨x,i⟩)
lemma vectorOfFn {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σx,Fin (k x)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BooleanNetwork.vector (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hk p hp
  exact vectorIndexed hn hk q hq (by intro x i;rw [eq];exact he ⟨x,i⟩)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkSequenceEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emission
open Procedure
noncomputable def foldReverseCompP : Procedure (prodCode (listCode packCode) packCode) packCode
    (fun x=>x.1.foldl (fun a b=>compPack b a) x.2):=
  foldPack (by intros;change _+_=_+_;omega)
    (compPackP.comp ((second packCode packCode).pair (first packCode packCode)))
end Emission
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma anyOfFn {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σx,Fin (k x)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BooleanNetwork.any (List.ofFn (f x))):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hk p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (q x)).foldr borPack (constantPack (n x) false),
    (ofProcedure Emission.anyPackP).comp (hn.pair hps),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact anyPack_value _ _ (ofFn_forall₂ _ _ _ (fun i=>by rw [eq];exact he ⟨x,i⟩))
lemma iterate {f : ∀x,BooleanNetwork (n x) (n x)}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k) (hf : NetEmits ea f) :
    NetEmits ea (fun x=>(f x).iterate (k x)):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨pp⟩:=hp.comp (BitStackProgram.Emits.id (prodCode unaryCode ea)).snd
  have hps:=(ofProcedure (Procedure.tabulate (f:=fun x _=>p x) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (fun _=>p x)).foldr compPack (identityPack (n x)),
    (ofProcedure (Emission.foldRightPack 0 (by intros;rfl) Emission.compPackP)).comp
      (hps.pair ((ofProcedure Emission.identityPackP).comp hn)),?_⟩
  intro x
  suffices ∀j,(((List.range j).map (fun _=>p x)).foldr compPack (identityPack (n x))).val.value=
      erase ((f x).iterate j) from this (k x)
  intro j
  simp only [List.map_const',List.length_range,BooleanNetwork.iterate]
  induction j with
  | zero=>exact identityPack_value _
  | succ j ih=>
    simp only [List.replicate_succ,List.foldr_cons,BooleanNetwork.sequence] at *
    exact compPack_spec _ _ _ _ (he x) ih
lemma ite {c : α→Bool} {f g : ∀x,BooleanNetwork (n x) (m x)}
    (hc : Emits ea Procedure.boolCode c) (hf : NetEmits ea f) (hg : NetEmits ea g) :
    NetEmits ea (fun x=>if c x then f x else g x):=by
  obtain ⟨p,hp,he⟩:=hf;obtain ⟨q,hq,eq⟩:=hg
  exact ⟨fun x=>if c x then p x else q x,hc.ite hp hq,by
    intro x;dsimp only;split
    · exact he x
    · exact eq x⟩
lemma add (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>BitArithmetic.add (n x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.add (n x),
    (ofProcedure AIGNetworkEmission.Emission.addPackP).comp hn,fun _=>AIGNetworkEmission.addPack_value _⟩
lemma wordLt {a b : ∀x,BooleanNetwork (n x) (m x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : Emits ea unaryCode m) :
    NetEmits ea (fun x=>BitArithmetic.wordLt (a x) (b x)):=(ha.pair hb).comp (ult hm)
lemma wordLe {a b : ∀x,BooleanNetwork (n x) (m x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : Emits ea unaryCode m) :
    NetEmits ea (fun x=>BitArithmetic.wordLe (a x) (b x)):=(wordLt hb ha hm).bnot
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/EmissionPolynomialUnary.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool}
lemma unaryPow {f : α→ℕ} (hf : Emits ea unaryCode f) (k : ℕ) : Emits ea unaryCode (fun x=>(f x)^k):=by
  induction k with
  | zero=>simpa only [pow_zero] using (const ea unaryCode 1)
  | succ k ih=>simpa only [pow_succ] using ih.unaryMul hf
lemma unaryPolynomial (p : Polynomial ℕ) {f : α→ℕ} (hf : Emits ea unaryCode f) :
    Emits ea unaryCode (fun x=>p.eval (f x)):=by
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>simpa only [Polynomial.eval_add] using hp.unaryAdd hq
  | monomial k c=>simpa only [Polynomial.eval_monomial] using (const ea unaryCode c).unaryMul (hf.unaryPow k)
lemma boundedUnary {f B : α→ℕ} (hf : Emits ea Nat.bits f) (hB : Emits ea unaryCode B)
    (h : ∀x,f x≤B x) : Emits ea unaryCode f:=by
  obtain ⟨p⟩:=hf;obtain ⟨q⟩:=hB
  exact ⟨Procedure.boundedUnary p q h⟩
lemma ofPolyAt {f len : α→ℕ} (hf : Emits ea Nat.bits f) (hl : Emits ea unaryCode len) (hb : PolyAt len f) :
    Emits ea unaryCode f:=by
  obtain ⟨p,hp⟩:=hb
  exact hf.boundedUnary (unaryPolynomial p hl) hp
lemma ofPolyBound {f : ℕ→ℕ} (hf : Emits unaryCode Nat.bits f) (hb : PolyBound f) :
    Emits unaryCode unaryCode f:=hf.ofPolyAt (id _) hb
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/WordBlocksEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
lemma result {f : α→β} {g : α→γ} (hf : Emits ea eb f) (h : ∀x,eb (f x)=ec (g x)) :
    Emits ea ec g:=by
  obtain ⟨p⟩:=hf
  exact ⟨p.result h⟩
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n s w : α→ℕ}
lemma blockNet (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (i : ∀x,Fin (s x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    NetEmits ea (fun x=>BitArithmetic.blockNet (s x) (w x) (i x)):=
  selectSlice (hs.unaryMul hw) hw (hw.unaryNat.natMul hi) _ (by intro x j;change j.val+w x*(i x).val=w x*(i x).val+j.val;omega)
lemma wordBlocks {f : ∀x,Fin (s x)→BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (hf : NetEmits (fun x:Σx,Fin (s x)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.wordBlocks (f x)):=by
  let eb:=fun x:Σx,Fin (s x*w x)=>prodCode unaryCode ea (x.2.val,x.1)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σx,Fin (s x*w x)=>(x.2.val,x.1))
  have hW:=hw.comp hx.snd
  have hI:=hx.fst.unaryNat
  have hdiv:= (hI.natDiv hW.unaryNat).boundedUnary hx.fst (by intro x;exact Nat.div_le_self _ _)
  have harg : Emits eb (fun x:Σx,Fin (s x)=>prodCode unaryCode ea (x.2.val,x.1))
      (fun x=>⟨x.1,(finProdFinEquiv.symm x.2).1⟩):=
    (hdiv.pair hx.snd).result (by intro x;rfl)
  have hF:=hf.input harg
  have ho:=hI.natMod hW.unaryNat
  have hb:=hF.rewireSlice (const _ _ 1) ho (fun x _=>(finProdFinEquiv.symm x.2).2)
    (by
      intro x i
      change x.2.val % w x.1 = x.2.val % w x.1 + i.val
      have := i.isLt
      omega)
  exact vectorOfFn hn (hs.unaryMul hw) hb
lemma arrayConstant {f : ∀x,Fin (s x)→ℕ}
    (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (hf : Emits (fun x:Σx,Fin (s x)=>prodCode unaryCode ea (x.2.val,x.1)) Nat.bits (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.arrayConstant (n:=n x) (s x) (w x) (f x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σx,Fin (s x)=>(x.2.val,x.1))
  exact wordBlocks hn hs hw (wordConst (hn.comp hx.snd) (hw.comp hx.snd) hf)
lemma addMod {a b m : ∀x,BooleanNetwork (n x) (w x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : NetEmits ea m) (hw : Emits ea unaryCode w) :
    NetEmits ea (fun x=>BitArithmetic.addMod (a x) (b x) (m x)):=by
  have hp:=padRight hw (const _ _ 1)
  exact (((((ha.comp hp).pair (hb.comp hp)).comp (add hw.unarySucc)).pair
    (hm.comp hp)).comp (mod hw.unarySucc)).rewireSlice hw (const _ _ 0)
      (fun _=>Fin.castAdd 1) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/EmissionBoundedRecursion.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}

def recursionCode (K : α→ℕ) (f : α→ℕ→β) (x : Σa,Fin (K a+1)) : List Bool:=
  prodCode ea (prodCode unaryCode eb) (x.1,(x.2.val,f x.1 x.2.val))
def recursionNext (K : α→ℕ) (x : Σa,Fin (K a+1)) : Σa,Fin (K a+1):=
  ⟨x.1,⟨min (x.2.val+1) (K x.1),by omega⟩⟩
lemma recursionNext_iterate (K : α→ℕ) (x : Σa,Fin (K a+1)) (j : ℕ) :
    ((recursionNext K)^[j]) x=⟨x.1,⟨min (x.2.val+j) (K x.1),by omega⟩⟩:=by
  rcases x with ⟨a,i⟩
  induction j with
  | zero=>
    change (⟨a,i⟩ : Σa,Fin (K a+1))=⟨a,_⟩
    apply congrArg (fun i:Fin (K a+1)=>(⟨a,i⟩ : Σa,Fin (K a+1)))
    apply Fin.ext
    dsimp only
    have := i.isLt
    omega
  | succ j ih=>
    rw [Function.iterate_succ_apply',ih]
    dsimp only [recursionNext]
    apply congrArg (fun i:Fin (K a+1)=>(⟨a,i⟩ : Σa,Fin (K a+1)))
    apply Fin.ext
    dsimp only
    omega
/-- A charged finite-stack loop over an explicitly implemented next-stage
construction. The size invariant is a bound on actual intermediate encodings,
not an assumption that an arbitrary bounded function is computable. -/
lemma boundedRecursion (K : α→ℕ) (f : α→ℕ→β)
    (hK : Emits ea unaryCode K) (h0 : Emits ea eb (fun x=>f x 0))
    (hs : Emits (recursionCode (ea:=ea) (eb:=eb) K f) eb
      (fun x=>f x.1 (min (x.2.val+1) (K x.1))))
    (hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length)
      (fun x=>(eb (f x.1 x.2.val)).length)) :
    Emits ea eb (fun x=>f x (K x)):=by
  let ec:=recursionCode (ea:=ea) (eb:=eb) K f
  have hx : Emits ec (prodCode ea (prodCode unaryCode eb))
      (fun x=>(x.1,(x.2.val,f x.1 x.2.val))):=
    (id (prodCode ea (prodCode unaryCode eb))).precompose _
  have hcount:=hx.snd.fst
  have hk:=hK.comp hx.fst
  have hi : Emits ec unaryCode (fun x=>min (x.2.val+1) (K x.1)):=
    ((ofProcedure clippedUnary).comp (hk.pair hcount.unarySucc.unaryNat)).congr (by intro x;exact Nat.min_comm _ _)
  have hn : Emits ec ec (recursionNext K):=
    (hx.fst.pair (hi.pair hs)).result (by intro x;rfl)
  obtain ⟨pn⟩:=hn
  obtain ⟨pk⟩:=hK
  obtain ⟨P,hP⟩:=hb
  let Q : Polynomial ℕ:=Polynomial.C 4*Polynomial.X+Polynomial.C 2*pk.bound+P+Polynomial.C 4
  have bound : ∀x:Σa,Fin (K a+1),(ec x).length≤Q.eval (ea x.1).length:=by
    intro x
    have ha:=pk.output_length_le x.1
    have hv:=hP x
    dsimp only at hv
    have hi:=x.2.isLt
    simp only [unaryCode,List.length_replicate] at ha
    simp only [ec,recursionCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
    simp only [Q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  let pi:=pn.iterate Q (by
    intro j x i hi
    rw [recursionNext_iterate]
    apply (bound _).trans
    apply eval_nat_mono
    simp only [ec,recursionCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
    omega)
  have hz : Emits ea ec (fun x=>(⟨x,⟨0,by omega⟩⟩ : Σa,Fin (K a+1))):=
    ((id ea).pair ((const ea unaryCode 0).pair h0)).result (by intro x;rfl)
  have hout:=hx.snd.snd.comp ((ofProcedure pi).comp ((ofProcedure pk).pair hz))
  exact hout.congr (by intro x;dsimp only;rw [recursionNext_iterate];simp only [Nat.zero_add,min_self])
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/EmissionGeneralStages.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {K : α→ℕ} {F : α→ℕ→β}
lemma stages (hK : Emits ea unaryCode K) (h0 : Emits ea eb (fun x=>F x 0))
    (hs : Emits (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode eb) (x.1,(x.2.val,F x.1 x.2.val))) eb
      (fun x=>F x.1 (x.2.val+1)))
    (hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>(eb (F x.1 x.2.val)).length)) :
    Emits ea eb (fun x=>F x (K x)):=by
  let ec:=recursionCode (ea:=ea) (eb:=eb) K F
  let c:=fun x:Σa,Fin (K a+1)=>x.2.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode eb))).precompose
    (fun x:Σa,Fin (K a+1)=>(x.1,(x.2.val,F x.1 x.2.val)))
  have htest:=hx.snd.fst.unaryNat.natLt (hK.comp hx.fst).unaryNat
  have hy : Emits (fun x:{a:Σa,Fin (K a+1) // c a}=>ec x.val) eb
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    have h:=hs.precompose (fun x:{a:Σa,Fin (K a+1) // c a}=>(⟨x.val.1,⟨x.val.2.val,x.property⟩⟩ : Σa,Fin (K a)))
    exact h.congr (by intro x;rw [Nat.min_eq_left (by have:=x.property;dsimp only [c] at this;omega)])
  have hz : Emits (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>ec x.val) eb
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    exact (hx.snd.snd.precompose (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>x.val)).congr (by
      intro x
      change F x.val.1 x.val.2.val=F x.val.1 _
      congr 1
      have := x.property
      have := x.val.2.isLt
      dsimp only [c] at *
      omega)
  exact boundedRecursion K F hK h0 (splitOn c htest hy hz) hb
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TriangularNetworkEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {p b : α→ℕ}
lemma sub (hb : Emits ea unaryCode b) : NetEmits ea (fun x=>BitArithmetic.sub (b x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.sub (b x),
    (ofProcedure AIGNetworkEmission.Emission.subPackP).comp hb,fun _=>AIGNetworkEmission.subPack_value _⟩
lemma translateInput {f : ∀x,BooleanNetwork (p x) (b x)} (hf : NetEmits ea f)
    (hp : Emits ea unaryCode p) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>ControlledTranslation.addInput (f x)):=
  (selectSlice (hp.unaryAdd hb) hb hp.unaryNat (fun x=>Fin.natAdd (p x)) (by intros;rfl)).pair
    ((selectSlice (hp.unaryAdd hb) hp (const _ _ 0) (fun x i=>i.castAdd (b x)) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])).comp hf)
lemma translateForward {f : ∀x,BooleanNetwork (p x) (b x)} (hf : NetEmits ea f)
    (hp : Emits ea unaryCode p) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>ControlledTranslation.forward (f x)):=
  (selectSlice (hp.unaryAdd hb) hp (const _ _ 0) (fun x i=>i.castAdd (b x)) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])).pair
    ((translateInput hf hp hb).comp (add hb))
lemma translateBackward {f : ∀x,BooleanNetwork (p x) (b x)} (hf : NetEmits ea f)
    (hp : Emits ea unaryCode p) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>ControlledTranslation.backward (f x)):=
  (selectSlice (hp.unaryAdd hb) hp (const _ _ 0) (fun x i=>i.castAdd (b x)) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])).pair
    ((translateInput hf hp hb).comp (sub hb))
lemma triangularRow (hb : Emits ea unaryCode b) (j : ∀x,Fin (b x))
    (hj : Emits ea Nat.bits (fun x=>(j x).val)) : NetEmits ea (fun x=>Triangular.rowNetwork (j x)):=by
  let f : α→ℕ→Pack:=fun x i=>if (j x).val ≤ i ∧ i<b x-1 then
    bandPack (bitPack (b x) ((b x-1+(j x).val-i)%b x)) (bitPack (b x) (j x).val)
    else constantPack (b x) false
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hn:=hb.comp hx.snd
  have hi:=hx.fst.unaryNat
  have hJ:=hj.comp hx.snd
  have hB:=hn.unaryNat.natSub (const _ _ 1)
  have hc:=((hi.natLt hJ).boolNot).boolAnd (hi.natLt hB)
  have hr:=((hB.natAdd hJ).natSub hi).natMod hn.unaryNat
  have hA:=(ofProcedure Emission.bitPackP).comp (hn.pair hr)
  have hD:=(ofProcedure Emission.bitPackP).comp (hn.pair hJ)
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>f x.2 x.1):=by
    exact (hc.ite ((ofProcedure Emission.bandPackP).comp (hA.pair hD))
      ((ofProcedure Emission.constantPackP).comp (hn.pair (const _ _ false)))).congr (by
        intro x;simp only [f,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,not_lt,decide_eq_true_eq])
  apply vectorIndexed hb hb f hp
  intro x i
  dsimp only [f,Triangular.rowNetwork]
  split
  · exact bandPack_value _ _ _ _ (bitPack_value (Triangular.rowIndex (j x) i)) (bitPack_value (j x))
  · exact constantPack_value _ _
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkModularPowerEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
lemma modularPower_emission : NetEmits (prodCode unaryCode unaryCode) (fun x=>modularPower x.1 x.2):=by
  obtain ⟨p,hp,ep⟩:=powerStep_emission
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode unaryCode)
  have hw:=hx.fst
  have hb:=hx.snd
  have hI:=((hw.unaryAdd hw).unaryAdd hb)
  have hW:=hI.unaryAdd hw
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=p) emptyPack pp)).comp (hb.pair hx)
  let q:=fun wb k=>((List.range k).map (p wb)).foldl compPack (identityPack (powerWidth wb.1 wb.2))
  have hq : Emits (prodCode unaryCode unaryCode) packCode (fun wb=>q wb wb.2):=
    (ofProcedure Emission.foldCompP).comp (hps.pair ((ofProcedure Emission.identityPackP).comp hW))
  have eq : ∀w b k (hk:k ≤ b),(q (w,b) k).val.value=erase (powerPrefix w b k hk):=by
    intro w b k
    induction k with
    | zero=>intro hk;exact identityPack_value _
    | succ k ih=>
      intro hk
      dsimp only [q]
      rw [List.range_succ,List.map_append,List.foldl_append,List.map_singleton,List.foldl_cons,List.foldl_nil]
      exact compPack_spec _ _ _ _ (ih (by omega)) (ep w b ⟨k,by omega⟩)
  have hprefix : NetEmits (prodCode unaryCode unaryCode) (fun x=>powerPrefix x.1 x.2 x.2 le_rfl):=
    ⟨fun x=>q x x.2,hq,fun x=>eq x.1 x.2 x.2 le_rfl⟩
  have hstart:= (NetEmits.identity hI).pair (NetEmits.wordConst hI hw (const _ _ 1))
  exact hstart.comp (hprefix.rewireSlice hw hI.unaryNat _ (by intros;rfl))
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {w b : α→ℕ}
lemma modularPower (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BitArithmetic.modularPower (w x) (b x)):=by
  obtain ⟨pack, hpack, hvalue⟩ := modularPower_emission
  exact ⟨fun value => pack (w value, b value),
    hpack.comp (hw.pair hb), fun value => hvalue (w value, b value)⟩
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackPowers.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma bits_length_pow (a k : ℕ) : (a^k).bits.length≤k*a.bits.length+1:=by
  induction k with
  | zero=>simp
  | succ k ih=>
    have h:=bits_length_mul (a^k) a
    rw [pow_succ];nlinarith

def powerStep (s : ℕ×ℕ) : ℕ×ℕ:=(s.1,s.2*s.1)
lemma powerStep_iterate (s : ℕ×ℕ) (i : ℕ) : (powerStep^[i]) s=(s.1,s.2*s.1^i):=by
  induction i with
  | zero=>simp
  | succ i ih=>rw [Function.iterate_succ_apply',ih];simp [powerStep,pow_succ,Nat.mul_assoc]
namespace Procedure
noncomputable def binaryPow : Procedure (prodCode unaryCode Nat.bits) Nat.bits (fun x=>x.2^x.1):=by
  let a:=first Nat.bits Nat.bits
  let b:=second Nat.bits Nat.bits
  let step : Procedure (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) powerStep:=
    a.pair (binaryMul.comp (b.pair a))
  let rep:=step.iterate (Polynomial.X^2+Polynomial.C 3*Polynomial.X+1) (by
    intro n s i hi
    rw [powerStep_iterate]
    have hm:=bits_length_mul s.2 (s.1^i)
    have hp:=bits_length_pow s.1 i
    simp only [prodCode,pairBits_length,Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one]
    nlinarith)
  let e:=first unaryCode Nat.bits
  let x:=second unaryCode Nat.bits
  exact ((second Nat.bits Nat.bits).comp (rep.comp (e.pair (x.pair (constant _ Nat.bits 1))))).congrFun (by
    intro x;change ((powerStep^[x.1]) (x.2,1)).2=x.2^x.1
    rw [powerStep_iterate];simp)
end Procedure
namespace Emits
variable {α : Type} {ea : α→List Bool}
lemma natPow {f k : α→ℕ} (hf : Emits ea Nat.bits f) (hk : Emits ea unaryCode k) :
    Emits ea Nat.bits (fun x=>(f x)^(k x)):=(ofProcedure Procedure.binaryPow).comp (hk.pair hf)
lemma natEven {f : α→ℕ} (hf : Emits ea Nat.bits f) : Emits ea Procedure.boolCode (fun x=>decide (Even (f x))):=by
  have h:=(ofProcedure Procedure.binaryEq).comp ((hf.natMod (const _ _ 2)).pair (const _ _ 0))
  exact h.congr (by intro x;simp only [Nat.even_iff])
end Emits
end ExactQuantumFactoring.BitStackProgram

end



end OAI
