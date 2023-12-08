import Mathlib

open Nat
open Finset
open List

#eval (countP Nat.Prime (dedup (factors 20)))


theorem coprime_consecutive (n : ℕ) : Nat.coprime n (n + 1) :=by
 rw [coprime_self_add_right]
 apply coprime_one_right

theorem a (k : ℕ) (kge2 : 2 ≤ k) (N : ℕ → ℕ) (hN0 : N 0 = k)
  (hN : ∀ m, N (m + 1) = N m * (N m + 1))
  : countP Nat.Prime (dedup (factors (N (m + 1)))) ≥ m + 2 := by


 induction' m with i ih
 rw [hN,zero_eq,hN0,zero_add]

 have h1 : factors (k * (k + 1)) ~ factors k ++ factors (k + 1)
 { apply perm_factors_mul_of_coprime
   apply coprime_consecutive k }

 have h2 : dedup (factors (k * (k + 1))) ~ dedup ((factors k) ++ factors (k + 1))
 { apply Perm.dedup h1 }

 rw [Perm.countP_eq _ h2]

 have fkn0 : factors k ≠ [] :=by
  by_contra fke0
  rw [factors_eq_nil] at fke0
  have kge2_not_fke0 : ¬ (k = 0 ∨ k = 1) :=by
   push_neg
   exact Iff.mp (two_le_iff k) kge2
  contradiction

 have fk1n0 : factors (k + 1) ≠ [] :=by
  by_contra fk1e0
  have k1g2 : 2 < k + 1
  { have succg : k < k  + 1
    {linarith}
    exact lt_of_le_of_lt kge2 succg }
  have k1ge2 : 2 ≤ k + 1 :=by
   apply le_of_lt
   exact k1g2
  rw [factors_eq_nil] at fk1e0
  have k1g2_not_fk1e0 : ¬ (k + 1 = 0 ∨ k + 1 = 1) :=by
   push_neg
   exact Iff.mp (two_le_iff (k + 1)) k1ge2
  contradiction

 set l1 := factors k
 set l2 := factors (k + 1)

 have dup_coprime : dedup (l1 ++ l2) = dedup l1 ++ dedup l2 :=by sorry

 rw [dup_coprime , countP_append]

theorem primes_infinite (k : ℕ)(kge2 : k ≥ 2 ) (N : ℕ → ℕ ) (hN0 : N 0 = k)
 (hN : ∀ m, N (m+1) = N m * (N m + 1)) : ∀ n, ∃ p > n, Nat.Prime p := by
 intro n
