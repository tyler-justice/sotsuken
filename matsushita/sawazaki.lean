import Mathlib

def add_square (n : ℕ) : ℚ  := (1/6)*n*(n+1)*(2*n + 1)

/- 1/6 を先頭に出すと正しく計算してくれなくなる -/

#eval add_square 2

example (a : ℕ → ℝ) (h : ∀ n, a (n+1) = a n + (n+1)^2) (h0 :a 0 = 0):
  a n = (1/6)*n*(n+1)*(2*n + 1) := by
  induction' n with n ih
  · simp [h0]
  simp at *
  rw [Nat.succ_eq_add_one]
  specialize h (n)
  nth_rewrite 1 [ih] at h
  rw [h]
  ring


