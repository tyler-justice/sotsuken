import Mathlib

open Nat
open Finset

#reduce (π 5) --π(n)はn以下の素数の個数
#eval (π' 5) --π'(n)はn未満の素数の個数
#eval (totient 6) --n以下でnと互いに素な自然数の個数(オイラーのφ関数)

theorem primeCounting'_add_le {a k : ℕ} (h0 : 0 < a) (h1 : a < k) (n : ℕ) :
    π' (k + n) ≤ π' k + totient a * (n / a + 1) :=by
  calc --Set.Ico は左が閉じた半開区間 interval close open
    π' (k + n) ≤ ((range k).filter Nat.Prime).card + ((Ico k (k + n)).filter Nat.Prime).card := by
      rw [primeCounting', count_eq_card_filter_range, range_eq_Ico,
       ←Ico_union_Ico_eq_Ico (Nat.zero_le k) le_self_add, filter_union]
      apply card_union_le
    _ ≤ π' k + ((Ico k (k + n)).filter Nat.Prime).card := by
      rw [primeCounting', count_eq_card_filter_range]
    _ ≤ π' k + ((Ico k (k + n)).filter (coprime a)).card := by
      refine' add_le_add_left (card_le_of_subset _) k.primeCounting'
      simp only [subset_iff, and_imp, mem_filter, mem_Ico]
      intro p succ_k_le_p p_lt_n p_prime
      constructor
      · exact ⟨succ_k_le_p, p_lt_n⟩
      · rw [coprime_comm]
        exact coprime_of_lt_prime h0 (gt_of_ge_of_gt succ_k_le_p h1) p_prime
    _ ≤ π' k + totient a * (n / a + 1) := by
      rw [add_le_add_iff_left]
      exact Ico_filter_coprime_le k n h0


theorem Ico_filter_coprime_le {a : ℕ} (k n : ℕ) (a_pos : 0 < a) :
    ((Ico k (k + n)).filter (coprime a)).card ≤ totient a * (n / a + 1) := by
  conv_lhs => rw [← Nat.mod_add_div n a]
  induction' n / a with i ih
  · rw [← filter_coprime_Ico_eq_totient a k]
    --rw [Nat.zero_eq,zero_add,mul_one,mul_zero,add_zero]
    simp only [add_zero, mul_one, mul_zero, le_of_lt (mod_lt n a_pos),
      Nat.zero_eq, zero_add]
    --Porting note: below line was `mono`
    refine Finset.card_mono ?_  --この？何
    refine' monotone_filter_left a.coprime _
    simp only [Finset.le_eq_subset]
    exact Ico_subset_Ico rfl.le (add_le_add_left (le_of_lt (mod_lt n a_pos)) k)
  simp only [mul_succ]
  simp_rw [← add_assoc] at * --⊢って何？
  calc
    (filter a.coprime (Ico k (k + n % a + a * i + a))).card = (filter a.coprime
       (Ico k (k + n % a + a * i) ∪ Ico (k + n % a + a * i) (k + n % a + a * i + a))).card := by
      congr
      rw [Ico_union_Ico_eq_Ico]
      rw [add_assoc]
      exact le_self_add
      exact le_self_add
    _ ≤ (filter a.coprime (Ico k (k + n % a + a * i))).card + a.totient := by
      rw [filter_union, ← filter_coprime_Ico_eq_totient a (k + n % a + a * i)]
      apply card_union_le
    _ ≤ a.totient * i + a.totient + a.totient := add_le_add_right ih (totient a)


theorem filter_coprime_Ico_eq_totient (a n : ℕ) :
    ((Ico n (n + a)).filter (Nat.coprime a)).card = totient a := by
  rw [totient, filter_Ico_card_eq_of_periodic, count_eq_card_filter_range]
  exact periodic_coprime a

theorem periodic_coprime (a : ℕ) : Function.Periodic (Nat.coprime a) a := by
  simp only [coprime_add_self_right, forall_const, iff_self_iff, eq_iff_iff, Function.Periodic]

theorem filter_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (pp : Function.Periodic p a) : ((Ico n (n + a)).filter p).card = a.count p :=
  filter_multiset_Ico_card_eq_of_periodic n a p pp
