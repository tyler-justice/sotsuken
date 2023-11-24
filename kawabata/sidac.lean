import Mathlib

open Nat
open Finset

theorem coprime_consecutive (n : ℕ) : Nat.coprime n (n + 1) :=by
 rw [coprime_self_add_right]
 apply coprime_one_right

theorem primes_infinite (k : ℕ)(kge2 : k ≥ 2 ) (N : ℕ → ℕ ) (hN0 : N 0 = k)
   (hN : ∀ m, N (m+1) = N m * (N m + 1)):
    ∀ n, ∃ p > n, Nat.Prime p := by
 have List.count factors k ≥ 1 :=by
