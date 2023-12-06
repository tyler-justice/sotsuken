import Mathlib

/- 
高校数学の sample
test
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

/- 入試問題　-/
-- 等比数列
example (α p : ℤ) (a : ℕ → ℤ)--妥協してℝをℤにした。これをℝで上手くいかないか考えたい
  --(h1 : a n+1 = p*(a n)) --a nで書いた方が使いやすそうなので、一旦h2に書き直してみた（後で戻したい）
--  (h2 : a n = p*(a (n-1)))
  (h2 : ∀ n ,a n.succ = p * (a n))--n+1をn.succにした
  (h0 : a 0 = α)
  : a n = (p^n)*α := by--ここ、本来はp^(n-1)だったが、多分p^nだと思うので変えた（または左辺をa n+1にするか）
  induction' n with n ih--↑nって何？→整数になってTypeが変わっている
  . simp at *
    rw [h0]
  . have H : p * (a n) = p ^ (n + 1) * α := by--ℝをℤに変えた今、これは必要ないかも。後で書き替えてみたい
      rw [ih]
      rw [←mul_assoc]
      nth_rewrite 1 [←pow_one p]
      rw [←pow_add]
      rw [add_comm 1 n]
    rw [h2]
    rw [H]
/-
10/6のまとめ
↑nは、αやpがℝで、aがℕ→ℝの写像だからこうなったと考えられる。
今回は、いろいろ試した末に、妥協してℝをℤ 変えた。
つまり、αやpをℤに、aをℕ→ℤの写像にした。
その結果、証明することはできた。
今後はℝのままで証明することができないか考えたい。
-/
/-試行錯誤の痕跡
    --specialize h2 n
--    rcases h2 with ⟨n, h3⟩
    rw [ih] at h2--
    --nth_rewriteが0からじゃなく1始まりになった
    --goalの左側もNat.succから変形したい
    rw [←mul_assoc] at h2
    nth_rewrite 1 [←pow_one p] at h2
    rw [←pow_add] at h2
    rw [add_comm 1 n] at h2
--  have h3 : Nat.succ n = n + 1 := rfl
--  rw [h3]
--    rw [h2]
    --矢印をどうにかしたい
    
#check(Nat.succ )
-/