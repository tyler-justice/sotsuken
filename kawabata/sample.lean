import Mathlib

/- 素数の無限性を tutorial から必要な部分だけ抜き出してコピーして
みてください. sorry の部分は書き直してください

書き込みました
<<<<<<< Updated upstream
 -/
=======
 -/


theorem exists_prime_factor {n : ℕ } (h : 2 ≤ n) :
 ∃ p : ℕ , Nat.Prime p ∧ p ∣ n := by

  by_cases np : Nat.Prime n
  {use n}
  induction' n using Nat.strong_induction_on with n ih
  --何故P(0)出ない？--
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have mne0: m ≠ 0
  { intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith }
  have mgt2 : 2 ≤ m
  {rw [Nat.two_le_iff]
   refine ⟨ mne0 , mne1⟩ } --two_le this mne1--
  by_cases mp : Nat.Prime m
  exists m
  {rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
   exists p
   refine ⟨ pp, pdvd.trans mdvdn⟩}

open Nat --open Natで各タクティクのNat消せる--
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
 intro n

 have h : 2 ≤ factorial (n + 1) + 1
 { apply Nat.succ_le_succ
   exact Nat.succ_le_of_lt (Nat.factorial_pos _)}
 rcases exists_prime_factor h with ⟨p, pp, pdvd⟩
 exists p
  --refine で何故かnogoal--
 constructor
 by_contra ple
 push_neg at ple
 have : p ∣ Nat.factorial (n + 1)
 {apply Nat.dvd_factorial
  apply pp.pos
  linarith}
 have pdvd1 : p ∣ 1
 {convert Nat.dvd_sub' pdvd this
  simp}
 have ple1 : p ≤ 1
 {apply Nat.le_of_dvd
  apply zero_lt_one
  exact pdvd1 }
 linarith [pp.two_le]
 exact pp



theorem e {n : ℕ }  : n ∣ n := by
 apply?

theorem two : ∀ {m : ℕ}, m ≠ 0 → m ≠ 1 → 2 ≤ m := by
 apply?

theorem dt {a b c : ℕ } : a ∣ b → b ∣ c → a ∣ c := by
 exact Nat.dvd_trans
>>>>>>> Stashed changes


def π' : ℕ → ℕ := Nat.count Nat.Prime

theorem primeCounting'_add_le {a k : ℕ} (h0 : 0 < a) (h1 : a < k) (n : ℕ) :
    π' (k + n) ≤ π' k + Nat.totient a * (n / a + 1) :=by
  calc
    π' (k + n) ≤ ((range k).filter Prime).card + ((Ico k (k + n)).filter Prime).card := by
      rw [primeCounting', count_eq_card_filter_range, range_eq_Ico, ←
        Ico_union_Ico_eq_Ico (zero_le k) le_self_add, filter_union]
      apply card_union_le
    _ ≤ π' k + ((Ico k (k + n)).filter Prime).card := by
      rw [primeCounting', count_eq_card_filter_range]
    _ ≤ π' k + ((Ico k (k + n)).filter (Coprime a)).card := by
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
