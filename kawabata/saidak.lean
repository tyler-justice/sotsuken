import Mathlib

open Nat
open List

#eval (countP Nat.Prime (dedup (factors 20)))

lemma coprime_consecutive (n : ℕ) : Nat.coprime n (n + 1) :=by
 rw [coprime_self_add_right]
 apply coprime_one_right

lemma coprime_consecutive' (n : ℕ) : Nat.coprime (n + 1) n :=by
 rw [coprime_self_add_left]
 apply coprime_one_right


lemma disjoint_dedup  (l1 l2 : List ℕ) (h : Disjoint l1 l2) :
                      dedup (l1++l2) = dedup l1 ++ dedup l2 := by
 induction' l1 with a l1' IH;
 rw [dedup_nil] ; exact rfl
 by_cases Ha : a ∈ l1'
 rw [dedup_cons_of_mem , cons_append , dedup_cons_of_mem , ←IH]
 exact disjoint_of_disjoint_cons_left h
 exact mem_append_left l2 Ha ; exact Ha
 rw [dedup_cons_of_not_mem , cons_append , dedup_cons_of_not_mem]
 rw [cons_append , cons_inj]
 apply IH ; exact disjoint_of_disjoint_cons_left h
 have aux : a ∉ l2 :=by
 { by_contra
   apply h
   exact List.mem_cons_self a l1'
   assumption
 }
 exact not_mem_append Ha aux
 exact Ha

/-ここからメインの証明-/

theorem saidak (k : ℕ) (kge2 : 2 ≤ k) (N : ℕ → ℕ) (hN0 : N 0 = k)
               (hN : ∀ m, N (m + 1) = N m * (N m + 1))
               : countP Nat.Prime (dedup (factors (N (m + 1)))) ≥ m + 2 := by

 induction' m with i ih
 rw [hN,zero_eq,hN0,zero_add]

 /-ここから0-/

 have : factors (k * (k + 1)) ~ factors k ++ factors (k + 1) :=by
  apply perm_factors_mul_of_coprime ; apply coprime_consecutive k

 have h1 : dedup (factors (k * (k + 1))) ~ dedup ((factors k) ++ factors (k + 1)) :=by
  apply Perm.dedup this

 rw [Perm.countP_eq _ h1]

 have l1n0 : factors k ≠ [] :=by
  by_contra l1e0
  rw [factors_eq_nil] at l1e0
  have kge2_not_l1e0 : ¬ (k = 0 ∨ k = 1) :=by
  { push_neg ; exact Iff.mp (two_le_iff k) kge2 }
  contradiction

 have l2n0 : factors (k + 1) ≠ [] :=by
  by_contra l2e0
  have k1g2 : 2 < k + 1
  { have succg : k < k  + 1 :=by {linarith}
    exact lt_of_le_of_lt kge2 succg }
  have k1ge2 : 2 ≤ k + 1 :=by
  { apply le_of_lt ; exact k1g2 }
  rw [factors_eq_nil] at l2e0
  have k1g2_not_l2e0 : ¬ (k + 1 = 0 ∨ k + 1 = 1) :=by
  { push_neg ; exact Iff.mp (two_le_iff (k + 1)) k1ge2 }
  contradiction

 set l1 := factors k
 set l2 := factors (k + 1)

 have dup_coprime : dedup (l1 ++ l2) = dedup l1 ++ dedup l2 :=by
  apply disjoint_dedup
  refine List.Disjoint.symm (coprime_factors_disjoint ?hab')
  apply coprime_consecutive'

 rw [dup_coprime , countP_append , ge_iff_le]

 have l1ex : ∃ (a' : ℕ) , a' ∈ l1 :=by
  apply exists_mem_of_ne_nil ; exact l1n0

 rcases l1ex with ⟨a' , a'mem⟩

 have dl1ex : ∃ (a : ℕ) , a ∈ dedup l1:=by
  use a' ; rw [mem_dedup] ; exact a'mem

 rcases dl1ex with ⟨a , amem⟩

 have ap : Nat.Prime a :=by
  have : a ∈ factors k :=by { rw [←mem_dedup] ; exact amem }
  apply prime_of_mem_factors ; exact this

 have l2ex : ∃ (b' : ℕ) , b' ∈ l2 :=by
  apply exists_mem_of_ne_nil ; exact l2n0

 rcases l2ex with ⟨b' , b'mem⟩

 have dl2ex : ∃ (b : ℕ) , b ∈ dedup l2:=by
  use b' ; rw [mem_dedup] ; exact b'mem

 rcases dl2ex with ⟨b , bmem⟩

 have bp : Nat.Prime b :=by
  have : b ∈ factors (k+1) :=by { rw [←mem_dedup] ; exact bmem }
  apply prime_of_mem_factors ; exact this

 have countP1 : 1 ≤ countP Nat.Prime (dedup l1) :=by
  rw [←lt_iff_add_one_le , countP_pos] ; use a
  constructor
  exact amem
  exact decide_eq_true ap

 have countP2 : 1 ≤ countP Nat.Prime (dedup l2) :=by
  rw [←lt_iff_add_one_le , countP_pos] ; use b
  constructor
  exact bmem
  exact decide_eq_true bp

 rw [← one_add_one_eq_two]
 exact Nat.add_le_add countP1 countP2

--ここからsucc--

 have nsucc : N (succ i + 1) =N (i + 1) * (N (i + 1) + 1) :=by
  rw [succ_eq_add_one] ; exact hN (i + 1)

 rw [nsucc]

 have : factors (N (i + 1) * (N (i + 1) + 1)) ~ factors (N (i + 1)) ++ factors (N (i + 1) + 1) :=by
  apply perm_factors_mul_of_coprime
  apply coprime_consecutive (N (i + 1))

 have h2 : dedup (factors ((N (i + 1)) * (N (i + 1) + 1))) ~ dedup ((factors (N (i + 1))) ++ factors ((N (i + 1)) + 1))
 { apply Perm.dedup this }

 rw [Perm.countP_eq _ h2]

 have l4n0 : factors (N (i + 1) + 1) ≠ [] :=by
  by_contra l4e0
  rw [factors_eq_nil] at l4e0
  have kge2_not_l4e0 : ¬ ((N (i + 1) + 1) = 0 ∨ (N (i + 1) + 1) = 1) := by
   push_neg
   constructor
   exact succ_ne_zero (N (i + 1))
   have Ngt0 : N (i + 1) ≥ 1 :=by
   { induction' (i + 1) with j jh
     rw [zero_eq , hN0]
     exact one_le_of_lt kge2
     rw [succ_eq_add_one]
     rw [hN]
     refine le_mul_of_le_of_one_le jh ?ha'
     exact Nat.le_add_left 1 (N j) }
   have : N (i + 1) + 1 ≥ 2 :=by { exact le_add_of_sub_le Ngt0 }
   exact Nat.ne_of_gt this
  contradiction

 set l3 := factors (N (succ i))
 set l4 := factors (N (succ i) + 1)

 have dup_coprime : dedup (l3 ++ l4) = dedup l3 ++ dedup l4 :=by
  apply disjoint_dedup
  refine List.Disjoint.symm (coprime_factors_disjoint ?hab'')
  apply coprime_consecutive'

 rw [dup_coprime , countP_append , ge_iff_le , succ_eq_add_one]
 have : i + 1 + 2 = i + 2 + 1 :=by { exact rfl }
 rw [this]
 rw [ge_iff_le] at ih

 have l4ex : ∃ (d' : ℕ) , d' ∈ l4 :=by
  apply exists_mem_of_ne_nil ; exact l4n0

 rcases l4ex with ⟨d' , d'mem⟩

 have dl4ex : ∃ (d : ℕ) , d ∈ dedup l4:=by
  use d' ; rw [mem_dedup] ; exact d'mem

 rcases dl4ex with ⟨d , dmem⟩

 have dp : Nat.Prime d :=by
  have : d ∈ factors (N (i + 1 ) + 1) :=by { rw [←mem_dedup] ; exact dmem }
  apply prime_of_mem_factors
  exact this

 have countP4 : 1 ≤ countP Nat.Prime (dedup l4) :=by
  rw [←lt_iff_add_one_le , countP_pos] ; use d
  constructor
  exact dmem
  exact decide_eq_true dp

 exact Nat.add_le_add ih countP4
