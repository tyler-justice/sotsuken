import Mathlib

/- 
高校数学の sample
-/

example (x : ℝ) (h : x*x - 3*x + 2 = 0) : x = 1 ∨ x=2 := by 
  have h1 : (x - 1) * (x - 2) = 0 :=
    calc
      (x - 1) * (x - 2) = (x*x - 3*x + 2) := by ring
      _ = 0 := by exact h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2 | h2 --3.5.Disjunctionを参考にした
  left
  apply sub_eq_zero.mp h2
  right
  apply sub_eq_zero.mp h2
