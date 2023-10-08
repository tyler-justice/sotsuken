import Mathlib

/-
 このファイルは Atiyah-MacDonald の Introduction to commutative algebra 
 の内容を Lean で記述する試みを記録したものです.
-/

/-
A 環, x nonunit → x を含む極大イデアルが存在

-/
universe u

variable (A : Type u) [CommRing A]

example (x : A) (h : ¬IsUnit x) : ∃m, Ideal.IsMaximal m ∧ x ∈ m := by
  sorry 

/-
 A 環, m A のイデアルで ∀x ∈ A \ m は unit → A local ring, m maximal
-/

example (m : Ideal A) (H : ∀(x : A), x ∉  m → IsUnit x) : 
  LocalRing A:= by
  sorry

/-
  m : A のイデアル, 1 + m の元は unit → A は local ring
-/

example (m : Ideal A) (H : ∀(x : A), x ∈ m → IsUnit (1 + x)) : 
  LocalRing A := by
  sorry 

example (m n : ℕ) (h : c ∈ Finset.range (m+n+ 1)) : (0 ≤ c ∧ c ≤ m )∨ (m < c ∧ c ≤ m + n) := by
  sorry
    
example  (b : A) (m n c : ℕ)  (H : n ≥ c ): b^(m + n - c) = b^(m + (n-c)) := by
  rw [Nat.add_sub_assoc ?h m]
  assumption 

example  (m n c : ℕ) (h : n  ≥ c) : m + n - c = m + (n-c) := by
    rw  [Nat.add_sub_assoc ?h m]
    assumption 
  
example (m n : ℕ) (h : m - n ≥ 0) : m ≥ n := by 
  apply?
  
example  : 3 - 5 = -2 := by exact rfl

variable (m n c : ℕ)

#check n+m-c 

/-
 n : A の冪零元からなる集合 → n は素イデアル, A/n に冪零元なし
-/
def mynilradical (I : Ideal A) : Ideal A where
  carrier := { a | ∃n : ℕ, a^n = 0}
  zero_mem' := by
    simp 
    use 1 
    rw [pow_one]

  add_mem' := by
    simp
    intros a b 
    intros m Ha
    intros n Hb
    use m+n
    rw [add_pow]
    have Term :
          ∀ c ∈ Finset.range (Nat.succ (m + n)), a ^ c * b ^ (m + n - c) * Nat.choose (m + n) c = 0
          := by
          intros c H 
          by_cases P : c ≤ m
          · have BC : b^(m + n - c) = 0  := by
              have HN : b^n*b^(m - c) = b^(n + m - c):= by 
                rw [←pow_add]
                rw [Nat.add_sub_assoc ?P n]
                assumption
              rw [add_comm]
              rw [← HN]
              rw [Hb]
              simp
            rw [BC]
            simp
          
          have nP : c > m := by exact not_le.mp P 
          have BC2 : a^c = 0 := by 
            have HNN : a^m * a^(c-m) = a^c  := by
              rw [← pow_add]              
              rw [← Nat.add_sub_assoc ?nP m]
              rw [add_comm]
              rw [Nat.add_sub_self_right]
              exact Nat.le_of_lt nP
          rw [BC2]
          simp           
    exact Finset.sum_eq_zero Term
          
  /- fun {x y} ⟨m, hxmi⟩ ⟨n, hyni⟩ =>
    ⟨m + n,
      (add_pow x y (m + n)).symm ▸ I.sum_mem <|
        show
          ∀ c ∈ Finset.range (Nat.succ (m + n)), x ^ c * y ^ (m + n - c) * Nat.choose (m + n) c = 0
          from fun c _ =>
          Or.casesOn (le_total c m) (fun hcm =>
              I.mul_mem_right _ <|
                I.mul_mem_left _ <|
                  Nat.add_comm n m ▸
                    (add_tsub_assoc_of_le hcm n).symm ▸
                      (pow_add y n (m - c)).symm ▸ I.mul_mem_right _ hyni) (fun hmc =>
               I.mul_mem_right _ <|
                I.mul_mem_right _ <|
                  add_tsub_cancel_of_le hmc ▸ (pow_add x m (c - m)).symm ▸ I.mul_mem_right _ hxmi)⟩
  -/
  -- smul_mem' {r s} := by exact fun ⟨n, h⟩ ↦ ⟨n,(mul_pow r s n).symm ▸ (r^n) h⟩
  smul_mem' := by
    intros r s 
    dsimp 
    intro H 
    rcases H with ⟨n,H⟩ 
    use n 
    rw [mul_pow]
    rw [H]
    simp
    




/-
  n A の冪零元からなる集合 ∘ n は A の全ての素イデアルの共通集合
-/

/-
  定義 A 環, Jacobson 根基とは A の極大イデアル全部の共通集合
-/

/-
  I A の Jacobson 根基とする. x ∈ I ↔ ∀ y ∈ A, 1 - xy が単元
-/

/-
 A 環, I_1, ... , I_n A のイデアル
 φ : A → ∏ A/I_i に関して
 1. φ が全射 ↔ ∀ i ≠ j, I_i + I_j = (1)
 2. φ が単射 ↔ ⋂ I_i = (0)
-/