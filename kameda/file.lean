/-亀田が作ったファイル-/
import Mathlib
--import Mathlib.Data.Nat.Sqrt

--sample（二次方程式）
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


--上のsampleを参考に、簡単な問題をLeanで書いてみる
--一次不等式
example (x : ℝ) (h : -3 < x ∧ x < 5)
  : -6 < 2 * x ∧ 2 * x < 10 := by
  rcases h with ⟨h0, h1⟩
  constructor
  . show -6 < 2 * x
    have h2 : 2 * (-3) < 2 * x := by
      apply (mul_lt_mul_left _).2
      exact h0
      norm_num
    calc
      -6 = 2 * (-3) := by norm_num
      _ < 2 * x := by apply h2
  . show 2 * x < 10
    have h2 : 2 * x < 2 * 5 := by
      apply (mul_lt_mul_left _).2
      exact h1
      norm_num
    calc
      2 * x < 2 * 5 := by apply h2
      _ = 10        := by norm_num


#check(pow_two)
#check(div_pow)--累乗に関する定理はAlgebra>GroupPower>Basic.leanにある。
#check(sq 2)--pow_twoと同じ
--平方根の表現はできる？Sqrt.leanが気になる。複数あるので注意
#check(Nat.sqrt 8)
#eval Nat.sqrt 8--Data>Nat>Basic.leanより。平方根を越えない最大の整数を与える
#check(Real.sqrt)--Analysis>SpecialFunctions>Sqrt.leanのやつ
#check(Real.sqrt 5)
--↓わかったら解いてみたい↓(そもそも証明のためのものだから、計算を絡めると難しいところがあったりする？)
/-
example (x : ℝ) (h : x + 1 / x = 2) : x ^ 2 + (1 / x ^ 2) = 3 := by 
  sorry

example (x : ℤ) (h : x ^ 2 = 25) /-(h1 : x > 0)-/: x = 5 ∨ x = -5 := by 
  left
  sorry
-/
