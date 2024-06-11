import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable def f (x : ℝ) : ℝ :=
  1 / (1 + x^2)

theorem differentiableAt_f : DifferentiableAt ℝ f x := sorry

theorem deriv_f : deriv f x = sorry := sorry
