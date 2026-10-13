import Mathlib

/-!
# Exact integer multiplication on deterministic multitape Turing machines

Shared model for the integer-multiplication complexity missions.

Machine conventions follow A. Montanaro, *Computational Complexity* lecture notes
(Cambridge, 2012), §3 (Turing machines), §3.4 (multiple-tape machines), §3.3 (big-O),
§4 (time-bounded computation).  The multiplication task follows Harvey–van der Hoeven 2021, §1,
and OpenAI, *Integer multiplication below n log n*, §1.
-/

namespace IntMul

/-- Head movements `←`, `−`, `→`. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq

/-- A deterministic `k`-tape Turing machine (Montanaro §3, §3.4).

* `Σ` is a finite alphabet containing the blank `□`, the start symbol `▷`, and the symbols
  `0`, `1`, `#` used for the input and output; these five symbols are pairwise distinct.
* `K` is a finite set of states with a start state `START` and a halting state `HALT ≠ START`.
* There are `k ≥ 2` tapes: tape `0` is the input tape, tape `1` is the output tape, and the
  remaining `k - 2` tapes are work tapes.  Every tape is infinite in one direction (cells
  `0, 1, 2, …`), with cell `0` holding `▷`.
* `δ : K × Σᵏ → K × (Σ × {←, −, →})ᵏ` is the transition function.

The conditions are those of the notes: on a cell holding `▷` the machine rewrites `▷` and does
not move left; `▷` is never written anywhere else, so it occurs only in cell `0` of each tape;
in state `HALT` the configuration no longer changes; and the input tape is read-only. -/
structure MultitapeTM where
  /-- the alphabet `Σ` -/
  Sym : Type
  [instFintypeSym : Fintype Sym]
  /-- the blank symbol `□` -/
  blank : Sym
  /-- the start symbol `▷` -/
  startSym : Sym
  /-- the symbol for the bit `0` -/
  zero : Sym
  /-- the symbol for the bit `1` -/
  one : Sym
  /-- the separator `#` between the two inputs -/
  sep : Sym
  syms_distinct : [blank, startSym, zero, one, sep].Nodup
  /-- the set of states `K` -/
  K : Type
  [instFintypeK : Fintype K]
  /-- the start state `START` -/
  qStart : K
  /-- the halting state `HALT` -/
  qHalt : K
  start_ne_halt : qStart ≠ qHalt
  /-- the number of tapes -/
  k : ℕ
  two_le_k : 2 ≤ k
  /-- the transition function `δ : K × Σᵏ → K × (Σ × {←, −, →})ᵏ` -/
  δ : K → (Fin k → Sym) → K × (Fin k → Sym × Move)
  /-- the head never erases `▷` and never moves left from it -/
  start_preserved : ∀ q a i, a i = startSym →
    ((δ q a).2 i).1 = startSym ∧ ((δ q a).2 i).2 ≠ Move.left
  /-- `▷` is never written on a cell that does not already hold it, so `▷` stays at the start
  of each tape only -/
  start_only_at_start : ∀ q a i, a i ≠ startSym → ((δ q a).2 i).1 ≠ startSym
  /-- `δ(HALT, σ) = (HALT, σ, −)`: once halted, the machine no longer changes its configuration -/
  halt_fixed : ∀ a, δ qHalt a = (qHalt, fun i => (a i, Move.stay))
  /-- the input tape is read-only -/
  input_readonly : ∀ q a, ((δ q a).2 ⟨0, by omega⟩).1 = a ⟨0, by omega⟩

attribute [instance] MultitapeTM.instFintypeSym MultitapeTM.instFintypeK

namespace MultitapeTM

variable (M : MultitapeTM)

/-- The input tape (tape `0`). -/
def inTape : Fin M.k := ⟨0, by have := M.two_le_k; omega⟩

/-- The output tape (tape `1`). -/
def outTape : Fin M.k := ⟨1, by have := M.two_le_k; omega⟩

/-- A configuration: the current state, the contents of every tape (cell `p` of tape `i` is
`cells i p`), and the position of every head. -/
structure Cfg where
  state : M.K
  cells : Fin M.k → ℕ → M.Sym
  head : Fin M.k → ℕ

/-- One step: with state `q` and scanned symbols `a`, if `δ(q, a) = (q', (σᵢ, dᵢ)ᵢ)` then each
tape `i` has the scanned cell overwritten by `σᵢ`, its head moves according to `dᵢ`, and the
state becomes `q'`. -/
def step (c : M.Cfg) : M.Cfg :=
  let r := M.δ c.state (fun i => c.cells i (c.head i))
  { state := r.1
    cells := fun i => Function.update (c.cells i) (c.head i) (r.2 i).1
    head := fun i =>
      match (r.2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1 }

/-- Encoding of a bit as a symbol. -/
def bitSym (b : Bool) : M.Sym := if b then M.one else M.zero

/-- Tape contents `▷ w □ □ …`: `▷` in cell `0`, the symbols of `w` in cells `1, …, |w|`, and
blanks everywhere after. -/
def tapeOf (w : List M.Sym) : ℕ → M.Sym
  | 0 => M.startSym
  | p + 1 => w.getD p M.blank

/-- The initial configuration on input `x#y`: state `START`; the input tape holds
`▷ x # y □ □ …`; every other tape holds `▷ □ □ …`; every head is on cell `0`. -/
def initCfg (x y : List Bool) : M.Cfg where
  state := M.qStart
  cells := fun i =>
    if i = M.inTape then M.tapeOf (x.map M.bitSym ++ M.sep :: y.map M.bitSym)
    else M.tapeOf []
  head := fun _ => 0

/-- On input `x#y`, after `t` steps the machine is in state `HALT` and the output tape holds
exactly `▷ w □ □ …` (output `w`). Since `HALT` freezes the configuration, this holds for some
`t ≤ T` iff the machine halts with output `w` using at most `T` steps. -/
def HaltsWithOutput (x y : List Bool) (t : ℕ) (w : List Bool) : Prop :=
  (M.step^[t] (M.initCfg x y)).state = M.qHalt ∧
    (M.step^[t] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)

end MultitapeTM

/-- `val x`: the nonnegative integer whose binary representation is `x`,
leftmost bit most significant (`val [] = 0`). -/
def val (x : List Bool) : ℕ :=
  x.foldl (fun a b => 2 * a + b.toNat) 0

/-- `bin k z`: the binary representation of `z` padded on the left to length `k`
(most significant bit first). Meaningful for `z < 2 ^ k`. -/
def bin (k z : ℕ) : List Bool :=
  List.ofFn fun i : Fin k => z.testBit (k - 1 - i)

/-- `lg n = max (⌈log₂ n⌉, 1)`. -/
def lg (n : ℕ) : ℕ := max (Nat.clog 2 n) 1

/-- `M` multiplies `n`-bit integers within `T(n)` steps: for all `x, y ∈ {0,1}ⁿ`, on input
`x#y` the machine halts with output `bin_{2n}(val x · val y)` using at most `T(n)` steps. -/
def MultipliesAt (M : MultitapeTM) (n : ℕ) (T : ℝ) : Prop :=
  ∀ x y : List Bool, x.length = n → y.length = n →
    ∃ t : ℕ, (t : ℝ) ≤ T ∧ M.HaltsWithOutput x y t (bin (2 * n) (val x * val y))

/-- Exact integer multiplication is possible in time `O(g(n))` (Montanaro §3.3, §4): there is a
single machine `M` that, for every `n ≥ 1` and all `x, y ∈ {0,1}ⁿ`, halts on input `x#y` with
output `bin_{2n}(val x · val y)`, and whose worst-case running time `T(n)` satisfies
`T(n) ≤ c · g(n)` for all `n ≥ n₀`, for some constant `c > 0` and some `n₀`. -/
def MulTimeBound (g : ℕ → ℝ) : Prop :=
  ∃ M : MultitapeTM,
    (∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, MultipliesAt M n T) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → MultipliesAt M n (c * g n)

/-- Multiplication in time `O(n (lg n)^{1-κ})`. -/
def KappaBound (κ : ℝ) : Prop :=
  MulTimeBound fun n => (n : ℝ) * ((lg n : ℝ) ^ (1 - κ))

end IntMul
