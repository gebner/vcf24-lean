import Mathlib.Algebra.Ring.Nat
import Mathlib.Tactic.Linarith

/-
  Tactics produce either a single new tactic state, or fail.

  A tactic state is essentially a list of goals.
-/

theorem p1_1 {a b : Prop} : a → b → b ∧ a := by
  intros ha hb
  apply And.intro
  assumption
  assumption

-- we can freely mix tactics and expressions
theorem p1_2 {a b : Prop} : a → b → b ∧ a :=
  fun ha hb => ⟨by assumption, by assumption⟩

theorem p1_3 {a b : Prop} : a → b → b ∧ a :=
  fun ha hb => ⟨by assumption, by rfl⟩ -- failing tactics are underlined in red

theorem p1_4 {a b : Prop} : a → b → b ∧ a := by
  intros ha hb
  apply And.intro
  -- repeats a tactic until it fails
  repeat assumption

theorem p1_6 {a b : Prop} : a → b → b ∧ a := by
  -- <;> executes the right tactic on all new goals
  intros ha hb <;> apply And.intro <;> assumption

theorem p2 (x : ℕ) : true ∧ x = x := by
  -- the (first | | ) operator allows backtracking
  constructor <;> first | apply And.intro | rfl

/-
  Rewriting
-/

theorem p3 (f : ℕ → ℕ) (a b : ℕ) (h : f (1 * (0 + a)) = f b) : f a = f (0 + b) := by
  -- The `rw` tactic takes a (quantified) equation and rewrites the goal using it
  rw [zero_add]
  -- You can also pass it multiple equations, and rewrite hypotheses
  rw [zero_add, one_mul] at h
  assumption

/-
  Induction
-/

theorem p4 {α : Type} (xs ys : List α) : (xs.append ys).length = xs.length + ys.length := by
  induction xs <;> simp only [List.append, List.length]
  case nil => rw [zero_add]
  case cons x xs ih =>
    rw [ih]
    linarith

/-
  Tactics are Lean terms as well ("meta-programs")
-/

open Lean Meta Elab Tactic in
elab "intro_and_cases" : tactic =>
  -- Tactics are written using the `TacticM` monad:
  liftMetaTactic fun mainGoal => do
  let (h, mainGoal) ← mainGoal.intro `h  -- `h is a name literal
  logInfo m!"intro_and_cases: {mainGoal}" -- printf-style debugging is usually the easiest option
  let newGoals ← mainGoal.cases h
  return newGoals.toList.map fun s => s.mvarId

example (a b : Prop) : a ∧ b → a := by
  intro_and_cases
  assumption
