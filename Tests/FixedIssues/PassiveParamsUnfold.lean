import Lean
import Blaster
import Tests.Utils

namespace Tests.PassiveParamsUnfold

-- Issue: a recursive call is not unfolded when an argument is a `structure` with a symbolic
--        field, even when the function never inspects that argument, e.g., an accumulator:
--          sumTo 3 ⟨t⟩  stays  sumTo 3 ⟨t⟩  instead of reducing to  ⟨t + 6⟩
--        A typical case is a cost accumulated along a run whose costs depend on symbolic inputs.
--
-- Diagnosis: `allExplicitParamsAreCtor` (OptimizeMatch.lean) requires every explicit argument
--            to be a constructor, and counts a `structure` constructor only when all its
--            leaves are constructors (`isFullyAppliedStructure`). That rule keeps unfolding
--            from running away on a structure whose fields decide the recursion (see `drain`
--            below), but it also holds back arguments that cannot affect it.
--
-- Fix: a parameter is passive when the function's unfolding equation never inspects it: it
--      occurs in no match discriminant, `if` condition or recursor application, a recursive
--      call passes it on only in its own position, and it never shares a (non-constructor)
--      application with a recursive call. `allExplicitParamsAreCtor` no longer requires a
--      passive argument to be a constructor (`isPassiveParam`).

set_option warn.sorry false

structure Total where
  total : Nat

/-- `acc` is only passed on: passive. -/
def sumTo (n : Nat) (acc : Total) : Total :=
  match n with
  | 0 => acc
  | k + 1 => sumTo k ⟨acc.total + (k + 1)⟩

structure Budget where
  cpu : Nat
  mem : Nat

/-- A cost accumulator with two fields: passive. -/
def spend (n : Nat) (b : Budget) : Budget :=
  match n with
  | 0 => b
  | k + 1 => spend k ⟨b.cpu + 16000, b.mem + 100⟩

/-- The list drives the recursion, `acc` is only passed on: passive. -/
def sumList (l : List Nat) (acc : Total) : Total :=
  match l with
  | [] => acc
  | x :: xs => sumList xs ⟨acc.total + x⟩

structure Cnt where
  v : Nat

/-- `s` decides the recursion, and its measure is the only one: not passive. Unfolding with a
    symbolic `s` would never stop. -/
def drain (tag : Bool) (s : Cnt) : Nat :=
  if h : s.v = 0 then 0 else drain tag ⟨s.v - 1⟩ + 1
termination_by s.v

def pick (b : Total) (k : Nat → Nat) : Nat := if b.total > 0 then k b.total else 0

/-- `acc` is in no condition, but it shares an application with the recursive call, so it
    can steer the recursion: not passive. -/
def steer (n : Nat) (acc : Total) : Nat :=
  match n with
  | 0 => acc.total
  | k + 1 => pick acc (fun m => steer k ⟨m - 1⟩)

-- passive accumulators with symbolic fields: used to stay folded
#testOptimize ["PassiveAccumulator"] ∀ (t : Nat), sumTo 3 ⟨t⟩ = ⟨t + 6⟩ ===> True

#testOptimize ["PassiveBudget"]
  ∀ (c m : Nat), spend 2 ⟨c, m⟩ = ⟨c + 32000, m + 200⟩ ===> True

#testOptimize ["PassiveBesideList"]
  ∀ (a b t : Nat), sumList [a, b] ⟨t⟩ = ⟨t + a + b⟩ ===> True

-- inspected arguments with symbolic fields: must stay folded (and optimization must terminate)
#testOptimize ["InspectedStaysFolded"]
  ∀ (t : Nat), drain true ⟨t⟩ = t ===> ∀ (t : Nat), t = drain true ⟨t⟩

#testOptimize ["SteeringStaysFolded"] (norm-result: 1)
  ∀ (t : Nat), steer 3 ⟨t⟩ = t ===> ∀ (t : Nat), t = steer 3 ⟨t⟩

/-! The same through the `blaster` tactic and the `#blaster` command. These verdicts were already
    reached before, with the solver unrolling the folded calls; they must not change now that
    the optimizer unfolds them. -/

theorem sumTo_total : ∀ (t : Nat), (sumTo 3 ⟨t⟩).total = t + 6 := by blaster

theorem spend_cost :
  ∀ (c m : Nat), c ≤ (spend 2 ⟨c, m⟩).cpu ∧ m + 200 = (spend 2 ⟨c, m⟩).mem :=
    by blaster

#blaster [∀ (a b t : Nat), (sumList [a, b] ⟨t⟩).total ≥ t]

-- must be falsified, not merely undetermined
#blaster (gen-cex: 0) (solve-result: 1) [∀ (t : Nat), (sumTo 3 ⟨t⟩).total = t + 5]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a b t : Nat), (sumList [a, b] ⟨t⟩).total > t]

end Tests.PassiveParamsUnfold
