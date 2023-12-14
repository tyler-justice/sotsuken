import Mathlib

open Nat
open Finset
open List

theorem coprime_consecutive (n : ℕ) : Nat.coprime  (n + 1) n :=by
 rw [coprime_self_add_left]
 apply coprime_one_left


theorem coprime_consecutive' (n : ℕ) : Nat.coprime  n (n + 1) :=by
 rw [coprime_self_add_right]
 apply coprime_one_right

 lemma disjoint_dedup  (l1 l2 : List ℕ) (h : Disjoint l1 l2) :
  dedup (l1++l2) = dedup l1 ++ dedup l2 := by
  induction' l1 with a l1' IH;
  rw [dedup_nil]
  exact rfl
  by_cases Ha : a ∈ l1'
  rw [dedup_cons_of_mem]
  rw [cons_append]
  rw [dedup_cons_of_mem]
  rw [← IH]
  exact disjoint_of_disjoint_cons_left h
  exact mem_append_left l2 Ha
  exact Ha
  rw [dedup_cons_of_not_mem]
  rw [cons_append]
  rw [dedup_cons_of_not_mem]
  rw [cons_append]
  rw [cons_inj]
  apply IH
  exact disjoint_of_disjoint_cons_left h
  have aux : a ∉ l2 := by
    by_contra
    apply h
    exact List.mem_cons_self a l1'
    assumption
  exact not_mem_append Ha aux
  exact Ha

theorem coprime_factors (k : ℕ) :
  dedup (factors (k*(k+1))) ~ dedup (factors k) ++ dedup (factors (k+1)):= by

 set l1 := factors k
 set l2 := factors (k+1)
 set L := factors (k*(k+1))

 have disjoint : List.Disjoint l1 l2 := by
  refine List.Disjoint.symm (coprime_factors_disjoint ?hab)
  apply coprime_consecutive


 have h2 : factors (k*(k+1)) ~ l1 ++ l2 := by
  apply perm_factors_mul_of_coprime
  apply coprime_consecutive' k

 have h3 :  dedup (l1 ++ l2) = dedup l1 ++ dedup l2 := by
  apply disjoint_dedup
  apply disjoint

 rw [← h3]
 apply Perm.dedup
 apply h2
