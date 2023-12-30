
import Mathlib

open Nat
open List

#eval (card ((factors 20)))

lemma coprime_consecutive (n : ℕ) : Nat.coprime n (n + 1) :=by
 rw [coprime_self_add_right]
 apply coprime_one_right

lemma Perm.card_eq {l1 : List ℕ} {l2 : List ℕ} (s : List.Perm l1 l2) : List.card l1 = List.card l2 :=by
 apply card_eq_of_equiv
 refine equiv_iff_subset_and_subset.mpr ?h.a
 constructor
 exact Perm.subset s
 rw [perm_comm] at s
 exact Perm.subset s

/-ここからメインの証明-/

theorem saidak (k : ℕ) (kge2 : 2 ≤ k) (N : ℕ → ℕ) (hN0 : N 0 = k)
               (hN : ∀ m, N (m + 1) = N m * (N m + 1))
               : m + 2 ≤ card (factors (N (m + 1))) := by

 induction' m with i card3
 rw [hN,zero_eq,hN0,zero_add]

 /-ここから0-/

 have h1 : factors (k * (k + 1)) ~ factors k ++ factors (k + 1) :=by
  apply perm_factors_mul_of_coprime ; apply coprime_consecutive k

 rw [Perm.card_eq h1]

 have l1n0 : factors k ≠ [] :=by
  by_contra l1e0
  rw [factors_eq_nil] at l1e0
  have : ¬ (k = 0 ∨ k = 1) :=by
  { push_neg ; exact Iff.mp (two_le_iff k) kge2 }
  contradiction

 have l2n0 : factors (k + 1) ≠ [] :=by
  by_contra l2e0
  rw [factors_eq_nil] at l2e0
  have k1ge2 : 2 ≤ k + 1 :=by exact le_step kge2
  have : ¬ (k + 1 = 0 ∨ k + 1 = 1) :=by
  { push_neg ; exact Iff.mp (two_le_iff (k + 1)) k1ge2 }
  contradiction

 set l1 := factors k
 set l2 := factors (k + 1)

 have disjoint : Disjoint l1 l2 :=by
  apply coprime_factors_disjoint
  apply coprime_consecutive

 rw [card_append_disjoint disjoint]

 have l1ex : ∃ (a : ℕ) , a ∈ l1 :=by
  apply exists_mem_of_ne_nil ; exact l1n0

 rcases l1ex with ⟨a , amem⟩

 have l2ex : ∃ (b : ℕ) , b ∈ l2 :=by
  apply exists_mem_of_ne_nil ; exact l2n0

 rcases l2ex with ⟨b , bmem⟩

 have l1sub : [a] ⊆ l1 :=by
  rw [subset_def] ; intro a'
  rw [mem_singleton]
  intro h ; rw [h]
  exact amem

 have l2sub : [b] ⊆ l2 :=by
  rw [subset_def] ; intro b'
  rw [mem_singleton]
  intro h ; rw [h]
  exact bmem

 have card1 : 1 ≤ card l1 :=by
  have : card [a] = 1 :=by exact rfl
  rw [←this]
  apply card_subset_le l1sub

 have card2 : 1 ≤ card l2 :=by
  have : card [b] = 1 :=by exact rfl
  rw [←this]
  apply card_subset_le l2sub

 rw [← one_add_one_eq_two]
 exact Nat.add_le_add card1 card2

 /-ここからsucc-/

 have nsucc : N (succ i + 1) = N (i + 1) * (N (i + 1) + 1) :=by
  rw [succ_eq_add_one] ; exact hN (i + 1)

 rw [nsucc]

 have h2 : factors (N (i + 1) * (N (i + 1) + 1)) ~ factors (N (i + 1)) ++ factors (N (i + 1) + 1) :=by
  apply perm_factors_mul_of_coprime
  apply coprime_consecutive (N (i + 1))

 rw [Perm.card_eq h2]

 set l3 := factors (N (succ i))
 set l4 := factors (N (succ i) + 1)

 have disjoint : Disjoint l3 l4 :=by
  apply coprime_factors_disjoint
  apply coprime_consecutive

 rw [card_append_disjoint disjoint , succ_eq_add_one]

 have : i + 1 + 2 = i + 2 + 1 :=by { exact rfl }
 rw [this]

 have l4n0 : factors (N (i + 1) + 1) ≠ [] :=by
  by_contra l4e0
  rw [factors_eq_nil] at l4e0
  have : ¬ ((N (i + 1) + 1) = 0 ∨ (N (i + 1) + 1) = 1) := by
   push_neg
   have : 2 ≤ N (i + 1) + 1 :=by
    apply le_add_of_sub_le
    induction' (i + 1) with j jh
    rw [zero_eq , hN0]
    exact one_le_of_lt kge2
    rw [succ_eq_add_one , hN]
    refine le_mul_of_le_of_one_le jh ?ha'
    exact Nat.le_add_left 1 (N j)
   exact Iff.mp (two_le_iff (N (i + 1) + 1)) this
  contradiction

 have l4ex : ∃ (d : ℕ) , d ∈ l4 :=by
  apply exists_mem_of_ne_nil ; exact l4n0

 rcases l4ex with ⟨d , dmem⟩

 have l4sub : [d] ⊆ l4 :=by
  rw [subset_def] ; intro d'
  rw [mem_singleton]
  intro h ; rw [h]
  exact dmem

 have card4 : 1 ≤ card l4 :=by
  have : card [d] = 1 :=by exact rfl
  rw [←this]
  apply card_subset_le l4sub

 rw [← one_add_one_eq_two]
 exact Nat.add_le_add card3 card4
