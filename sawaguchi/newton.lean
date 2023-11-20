import Mathlib



def aa : ℕ → ℚ
  | 0 => 1
  | n + 1 => (1/2) * (aa n + 2 / aa n)
#eval aa 4

/-def a : ℕ → ℚ
  | 0 => α0
  | n + 1 => (1/2) * (a n + N / a n)-/

/-|a 1 - sqrt N| < (1/2)*|a 0 - sqrt N| を示す-/

/-
f(x) = x² - N (N > 0)のときf(x) = 0 となるxをニュートン法で求める
-/

example (a : ℕ → ℝ) (α0 : ℝ) (N : ℝ) (h2 : N > 0) (h1 : α0 > Real.sqrt N) (h0 : a 0 = α0)
        (h : ∀n , a (n+1) = (1/2)*(a n + N / a n)) :
        |a 1 - Real.sqrt N| < (1/2) * |a 0 - Real.sqrt N| := by
  rw [h, h0]
  have h' : N / Real.sqrt N = Real.sqrt N := by
    nth_rewrite 1 [← Real.mul_self_sqrt (le_of_lt h2)]
    rw [mul_div_cancel]
    exact Iff.mpr Real.sqrt_ne_zero' h2
  have h'' : N / α0 < Real.sqrt N := by
    rw [← h']
    apply div_lt_div_of_lt_left h2
    exact Real.sqrt_pos.mpr h2
    exact h1
  have h''' : Real.sqrt N - 2 * Real.sqrt N = - Real.sqrt N := by ring
  have h'''' : N / α0 - 2 * Real.sqrt N < - Real.sqrt N := by
    rw [←h''', sub_eq_add_neg]
    apply add_lt_add_right h''
  have h3 : (0 : ℝ) < 1 / 2 := by linarith
  have h4 : 1 / 2 * |α0 + (N / α0 - 2 * Real.sqrt N)| < 1 / 2 * |α0 + -Real.sqrt N| := by
    apply (mul_lt_mul_left h3).mpr
    apply lt_abs.mpr
    left
    rw [abs_of_nonneg]
    apply add_lt_add_left h''''
    --0 < α0 + (N / α0 - 2 * Real.sqrt N)の証明
    sorry
  calc
    |1 / 2 * (α0 + N / α0) - Real.sqrt N| = |1 / 2 * (α0 + N / α0 - 2 * Real.sqrt N)| := by ring_nf
                                        _ = |1 / 2| * |α0 + N / α0 - 2 * Real.sqrt N| := by rw [abs_mul]
                                        _ = 1 / 2 * |α0 + N / α0 - 2 * Real.sqrt N|   := by rw [abs_of_pos]
                                                                                            apply h3
                                        _ = 1 / 2 * |α0 + (N / α0 - 2 * Real.sqrt N)| := by rw [add_sub_assoc]
                                        _ < 1 / 2 * |α0 + -Real.sqrt N|               := by apply h4
                                        _ = 1 / 2 * |α0 - Real.sqrt N|                := by rw [←sub_eq_add_neg]
