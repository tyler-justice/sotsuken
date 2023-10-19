import Mathlib.Tactic.Ring  --ring_nfなど

/-2021年北大理系4
a 1 = 2, b 1 = 1,
a (n+1) = 2*a n + 3*b n, b(n+1)=a n + 2*b n,
c n = a n * b nとする
(1)c 2を求めよ
(2)c nは偶数であることを示せ
(3)nが偶数のとき、c nは28で割り切れることを示せ

leanの帰納法は0から始まるので、問題を書き換える
a 0 = 2, b 0 = 1,
a (n+1) = 2*a n + 3*b n, b(n+1)=a n + 2*b n,
c n = a n * b nとする
(1)c 1を求めよ
(2)c nは偶数であることを示せ
(3)nが奇数のとき、c nは28で割り切れることを示せ
-/
--(1)
example (a b c: ℕ → ℕ) (ha0 : a 0 = 2) (hb0 : b 0 = 1)
  (ha : ∀n, a (n+1) = 2*a n + 3*b n) (hb : ∀n, b (n+1) = a n + 2*b n)
  (hc : ∀n, c n = a n * b n):
  c 1 = 28:= by
  calc
    c 1 = a 1 * b 1 := by rw [hc]
    _ = (2*a 0 + 3*b 0) * (a 0 + 2*b 0) := by rw [ha, (hb 0)]
    _ = (2*2 + 3*1) * (2 + 2*1) := by rw [ha0, hb0]
    _ = 28 := by ring_nf

--(2)
example (a b c: ℕ → ℕ) (ha0 : a 0 = 2) (hb0 : b 0 = 1)
  (ha : ∀n, a (n+1) = 2*a n + 3*b n) (hb : ∀n, b (n+1) = a n + 2*b n)
  (hc : ∀n, c n = a n * b n):
  2 ∣ c n := by 
  induction' n with n ih
  . simp
    rw [hc, ha0, hb0]
  . have : ∀n, Nat.succ n = n+1 := by simp
    rw [this]
    rcases ih with ⟨m, hm⟩
    use a n ^ 2 + 3 * b n ^ 2 + 7 * m
    calc
      c (n + 1) = a (n+1) * b (n+1) := by rw [hc]
      _ = (2*a (n) + 3*b (n)) * (a (n) + 2*b (n)) := by rw [ha, hb]
      _ = 2*a (n)^2 + 6*b (n)^2 + 7*(a (n) * b (n)) := by ring_nf
      _ = 2*a (n)^2 + 6*b (n)^2 + 7*c (n) := by rw [hc]
      _ = 2*a (n)^2 + 6*b (n)^2 + 7*(2*m) := by rw [hm]
      _ = 2 * (a n ^ 2 + 3 * b n ^ 2 + 7 * m) := by ring_nf

--(3)
example (a b c: ℕ → ℕ) (ha0 : a 0 = 2) (hb0 : b 0 = 1)
  (ha : ∀n, a (n+1) = 2*a n + 3*b n) (hb : ∀n, b (n+1) = a n + 2*b n)
  (hc : ∀n, c n = a n * b n):
  (28 ∣ c (2*n+1)) := by 
  induction' n with n ih
  . simp
    rw [hc, ha, hb, ha0, hb0]
  . have : ∀n, Nat.succ n = n+1 := by simp
    rw [this]
    rcases ih with ⟨m, hm⟩
    use a (2*n+1)^2 + 3*b (2*n+1)^2 + 97*m
    ring_nf
    calc
      c (3+n*2) = c (2*n+3) := by rw [add_comm, mul_comm]
      _ = a (2*n+3) * b (2*n+3) := by rw [hc]
      _ = (2*a (2*n+2) + 3*b (2*n+2)) * (a (2*n+2) + 2*b (2*n+2)) := by rw [ha (2*n+2), hb (2*n+2)]
      _ = 7*(a (2*n+2) * b (2*n+2)) + 2*a (2*n+2)^2 + 6*b (2*n+2)^2 := by ring_nf
      _ = 7*((2*a (2*n+1) + 3*b (2*n+1)) * (a (2*n+1) + 2*b (2*n+1))) + 2*(2*a (2*n+1) + 3*b (2*n+1))^2 + 6*(a (2*n+1) + 2*b (2*n+1))^2 := by rw [ha (2*n+1), hb (2*n+1)]
      _ = 28*a (2*n+1)^2 + 84*b (2*n+1)^2 + 97*(a (2*n+1) * b (2*n+1)) := by ring_nf
      _ = 28*a (2*n+1)^2 + 84*b (2*n+1)^2 + 97*c (2*n+1) := by rw [hc]
      _ = 28*a (2*n+1)^2 + 84*b (2*n+1)^2 + 97*(28*m) := by rw [hm]
      _ = a (1 + n * 2) ^ 2 * 28 + b (1 + n * 2) ^ 2 * 84 + m * 2716 := by ring_nf

--副産物（結局使わなかったけど、今後どこかで使えるかも）
theorem my_lemma_2021Q4_2_ab (a b n : ℕ) (h : n ∣ a):
  n ∣ a * b := by
  rw [←Nat.mul_one n]
  apply Nat.mul_dvd_mul _ _
  apply h
  simp

theorem my_lemma_2021Q4_2_abc (a b: ℕ) (h : c = a * b):
  n ∣ a ∨ n ∣ b → n ∣ c := by
  intro h0
  rcases h0 with ⟨d, h0.left⟩ | ⟨d, h0.right⟩
  rw [h]
  apply my_lemma_2021Q4_2_ab
  . rw [h0.left]
    simp
  . rw [h]
    rw [mul_comm]
    apply my_lemma_2021Q4_2_ab
    rw [h0.right]
    simp

theorem my_lemma_2021Q4_3_abc (a b: ℕ) (h : c = a * b):
  n ∣ a ∧ m ∣ b → n * m ∣ c := by 
  rintro ⟨h0, h0'⟩
  rw [h]
  rcases h0 with ⟨d, h0d⟩
  rcases h0' with ⟨e, h0'e⟩
  rw [h0d, h0'e]
  use (d * e)
  ring_nf