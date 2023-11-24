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

/-lemma ooo (j k l: ℝ) (h : j < k) : (l + j) ^ 2 < (l + k) ^ 2 := by
  have h' :  (l + k) ^ 2 - (l + j) ^ 2 > 0 := by
    calc
      (l + k) ^ 2 - (l + j) ^ 2 = l^2 + 2*k*l + k^2 - (l^2 + 2*j*l + j^2) := by ring_nf
                              _ = 2*(k - j)*l + k^2 -j^2    := by ring_nf
  sorry-/

lemma n0 (a : ℕ → ℝ) (α0 : ℝ) (N : ℝ) (h2 : N > 0) (h1 : α0 > Real.sqrt N) (h0 : a 0 = α0)
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
  have h5 : α0 ≠ 0 := by --N > 0 → Real.sqrt N > 0 → α0 > Real.sqrt N → α0 > 0 → α0 ≠ 0
    apply pos_iff_ne_zero.mp α0 --なぜかこれが通らない
  have h4 : 1 / 2 * |α0 + (N / α0 - 2 * Real.sqrt N)| < 1 / 2 * |α0 + -Real.sqrt N| := by
    apply (mul_lt_mul_left h3).mpr
    apply sq_lt_sq.mp
    apply pow_lt_pow_of_lt_left
    · apply add_lt_add_left h''''
    · calc
        α0 + (N / α0 - 2 * Real.sqrt N) = α0 + N / α0 - 2 * Real.sqrt N                 := by rw [←add_sub_assoc]
                                      _ ≥ 2 * Real.sqrt (α0 * N / α0) - 2 * Real.sqrt N := by sorry --相加相乗平均のコマンドがあれば使いたい
                                      _ = 2 * Real.sqrt N - 2 * Real.sqrt N             := by rw [mul_div_cancel_left N h5]
                                      _ = 0                                             := by ring
    · linarith

  calc
    |1 / 2 * (α0 + N / α0) - Real.sqrt N| = |1 / 2 * (α0 + N / α0 - 2 * Real.sqrt N)| := by ring_nf
                                        _ = |1 / 2| * |α0 + N / α0 - 2 * Real.sqrt N| := by rw [abs_mul]
                                        _ = 1 / 2 * |α0 + N / α0 - 2 * Real.sqrt N|   := by rw [abs_of_pos]
                                                                                            apply h3
                                        _ = 1 / 2 * |α0 + (N / α0 - 2 * Real.sqrt N)| := by rw [add_sub_assoc]
                                        _ < 1 / 2 * |α0 + -Real.sqrt N|               := by apply h4
                                        _ = 1 / 2 * |α0 - Real.sqrt N|                := by rw [←sub_eq_add_neg]

example (a : ℕ → ℝ) (α0 : ℝ) (N : ℝ) (h2 : N > 0) (h1 : α0 > Real.sqrt N) (h0 : a 0 = α0)
        (h : ∀n , a (n+1) = (1/2)*(a n + N / a n)) :
        |a (n + 1) - Real.sqrt N| < (1/2) * |a n - Real.sqrt N| := by
  induction' n with n ih
  · simp
    rw [←mul_one 2⁻¹, inv_mul_eq_div]
    apply n0
    apply h2
