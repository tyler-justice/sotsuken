import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.RingTheory.Int.Basic
/-2017Q1を解こう
(1)自然数a,n,kに対し、n(n+1)+a=(n+k)^2が成り立つとき、a≥k²+2k-1を示せ
(2)n(n+1)+14が平方数となるような自然数nを全て求めよ
方針
(1)n,kを1以上の整数として定義する（ℕだとできないことが多いので）
  aもℤにしてよいがa≤1の仮定を使わなかったのでℕのまま。
  calcで示す
(2)
  n=1,13だけが条件を満たすことを示したい
  nが(2)の条件を満たすことと、Xor' (n = 1) (n = 13)を満たすことが、同値と示す
  (Imo1962Q4.leanを参考にした)-/
#check(pow_two)
--(1)
theorem kameda2017Q1_1 (n k:ℤ) (a: ℕ)
  (hn : 1 ≤ n) (hk : 1 ≤ k) (h : n*(n+1)+a=(n+k)^2):
  a≥k^2+2*k-1 := by
  have h1 : (2*k-1)*n ≥ 2*k-1 := by
    calc
      (2*k-1)*n ≥ (2*k-1)*1 := by
        apply mul_le_mul (Int.le_refl (2*k-1)) hn Int.one_nonneg _
        have h2 : 2 ≤ 2 * k := by
          calc
            2 = 2 * 1 := by exact rfl
            _ ≤ 2 * k := by exact mul_le_mul (Int.le_refl 2) hk Int.one_nonneg (Int.nonneg_of_normalize_eq_self rfl)
        calc
          0 ≤ 1 := by apply Int.one_nonneg
          _ ≤ 2*k-1 := by exact Iff.mpr Int.le_sub_one_iff h2
      _ = 2*k-1 := by exact Int.mul_one (2*k-1)
  calc
    a = (n+k)^2 - n*(n+1) := by exact eq_sub_of_add_eq' h
    _ = k^2+(2*k-1)*n := by ring
    _ ≥ k^2+(2*k-1) := by exact Int.add_le_add_left h1 (k^2)
    _ = k^2+2*k-1 := by exact add_sub (k^2) (2*k) 1


--(2)の条件を定義
def ProblemQ1_2 (n : ℤ) : Prop :=
  ∃m:ℤ, 1 ≤ n ∧ 1 ≤ m ∧ n * (n + 1) + 14 = m ^ 2

--(2)の厳しい条件を定義
def ProblemQ1_2' (n : ℤ) : Prop :=
  ∃m:ℤ, 1 ≤ n ∧ 4 ≤ m ∧ n < m ∧ n * (n + 1) + 14 = m ^ 2

--次で使う
theorem change2_2'_prep (n: ℤ) (hn : 1 ≤ n):
  1 * (1 + 1) ≤ n * (n + 1) := by
  apply le_mul_of_one_le_of_le_of_nonneg hn _ _
  exact Int.le_add_of_sub_right_le hn
  have : 2 ≤ n + 1 := by exact Int.le_add_of_sub_right_le hn
  calc
    0 ≤ 2 := by linarith
    _ ≤ n + 1 := by exact this

--(2)の条件と(2)の厳しい条件が同値
theorem change2_2' {n : ℤ} : ProblemQ1_2' n ↔ ProblemQ1_2 n := by
  simp only [ProblemQ1_2, ProblemQ1_2']
  constructor
  . rintro ⟨m, hn, hm, _ ,h⟩
    use m
    constructor
    . exact hn
    constructor
    . calc
        1 ≤ 4 := by linarith
        _ ≤ m := by exact hm
    . exact h
  . rintro ⟨m, hn, hm, h⟩
    use m
    have hnonnegm : 0 ≤ m := by
      calc
        0 ≤ 1 := by linarith
        _ ≤ m := by exact hm
    constructor
    . exact hn
    . constructor
      . have hm16lempow : 4*4 ≤ m*m := by
          calc
            4*4 = 1*(1+1)+14 := by ring_nf
            _ ≤ n * (n + 1) + 14 := by
              apply Int.add_le_add_right _ 14
              apply change2_2'_prep n hn
            _ = m^2 := by exact h
            _ = m*m := by exact sq m
        apply nonneg_le_nonneg_of_sq_le_sq hnonnegm hm16lempow
      constructor
      . have hnnlemm : n*n < m*m := by
          calc
            n*n = n*n + 0 := by linarith
            _ < n*n + (n + 14) := by
              apply add_lt_add_left
              calc
                0 < 1 := by linarith
                _ ≤ n := by exact hn
                _ < n + 14 := by exact Int.lt.intro rfl
            _ = n*(n+1) + 14 := by ring
            _ = m^2 := by exact h
            _ = m*m := by exact sq m
        exact lt_of_mul_self_lt_mul_self hnonnegm hnnlemm
      . exact h

--(1)の条件を定義
def ProblemQ1_1 (n: ℤ) : Prop :=
  ∃k:ℤ, (1 ≤ n) ∧ (1 ≤ k) ∧ n*(n+1) + 14 = (n+k) ^ 2

--(2)の厳しい条件と、(1)の条件が同値
theorem change1_2' {n : ℤ} : ProblemQ1_2' n ↔ ProblemQ1_1 n:= by
  simp only [ProblemQ1_2', ProblemQ1_1]
  constructor
  . rintro ⟨m, hn, _, hnm, h⟩--1→2
    set k := m-n ; use k
    constructor
    . exact hn
    constructor
    . have : 0 < m - n := by exact Int.sub_pos_of_lt hnm
      exact this
    . simp ; exact h
  . rintro ⟨k, hn, hm, h⟩
    use n+k
    constructor
    . exact hn
    constructor
    . have hm16lempow : 4*4 ≤ (n+k)*(n+k) := by
        calc
          4*4 = 1*(1+1)+14 := by linarith
          _ ≤ n * (n + 1) + 14 := by
            apply Int.add_le_add_right _ 14
            apply change2_2'_prep n hn
          _ = (n+k)^2 := by exact h
          _ = (n+k)*(n+k) := by exact sq (n+k)
      apply nonneg_le_nonneg_of_sq_le_sq _ hm16lempow
      calc
        0 ≤ 1 := by exact Int.one_nonneg
        _ ≤ n+1 := by exact Int.le_add_one hn
        _ ≤ n+k := by apply add_le_add_left hm
    constructor
    . exact Int.lt_add_of_pos_right n hm
    . exact h

--次で使う
theorem kameda2017Q1_2'_prep (k : ℤ) (hk : 1 ≤ k) (hk' : k ≤ 3):
  Xor' (k = 1) (Xor' (k = 2) (k = 3)) := by
  apply Iff.mpr xor_iff_not_iff'
  constructor
  . intro h1
    push_neg at h1
    apply Iff.mpr xor_iff_not_iff'
    constructor
    . intro h2 ; push_neg at h2
      have : 1 < k := by exact Ne.lt_of_le (id (Ne.symm h1)) hk
      have : 2 ≤ k := by exact this
      have : 2 < k := by exact Ne.lt_of_le (id (Ne.symm h2)) this
      exact Int.le_antisymm hk' this
    . intro h3 ; push_neg
      rw [h3] ; linarith
  . intro h
    push_neg
    have : k = 2 ∨ k = 3 := by exact Xor'.or h
    rcases this with h2 | h3
    . rw [h2] ; linarith
    . rw [h3] ; linarith

--次で使う
theorem my_lemma_Xor_not (a b : Prop) (h : Xor' a b) (hnota : ¬ a):
  b := by
  have : a ∨ b := by exact Xor'.or h
  have : ¬ a → b := by exact Iff.mp or_iff_not_imp_left this
  exact this hnota

--(2)のメイン
theorem kameda2017Q1_2'' {n : ℤ} : ProblemQ1_2 n ↔ Xor' (n = 1) (n = 13) := by
  rw [←change2_2', change1_2']
  simp only [ProblemQ1_1]
  constructor
  . rintro ⟨k, hn, hk, h⟩
    have h14le: 14 ≥ k ^ 2 + 2 * k - 1 := by
      apply kameda2017Q1_1 n k 14 hn hk h
    have hk' : Xor' (k = 1) (Xor' (k = 2) (k = 3)) := by
      apply kameda2017Q1_2'_prep k hk
      have hmulnonpos : (k+5)*(k-3) ≤ 0 := by
        calc
          0 = 14 - 14 := by rfl
          _ ≥ k ^ 2 + 2 * k - 1 - 14 := by exact Int.sub_le_sub_right h14le 14
          _ = k ^ 2 + 2 * k - 15  := by ring
          _ = (k+5)*(k-3) := by ring
      have hk5pos : k + 5 > 0 := by
        calc
          0 < 1 := by linarith
          _ ≤ k := by exact hk
          _ ≤ k + 5 := by exact Int.le.intro 5 rfl
      have : k - 3 ≤ 0 := by apply nonpos_of_mul_nonpos_right hmulnonpos hk5pos
      exact Int.le_of_sub_nonpos this
    apply Iff.mpr xor_iff_not_iff'
    constructor
    . intro hn' ; push_neg at hn'
      replace h : n^2+(n+14) = n^2+(2*n*k+k^2) := by
        calc
          n^2+(n+14) = n*(n+1)+14 := by ring
          _ = (n+k)^2 := by rw [h]
          _ = n^2 + 2*n*k + k^2 := by rw [add_sq]
          _ = n^2+(2*n*k+k^2) := by ring
      replace h : n+14 = (2*n*k+k^2) := by apply Int.add_left_cancel h
      have : k = 1 := by
        rw [xor_comm] at hk'
        apply my_lemma_Xor_not (Xor' (k=2) (k=3)) (k=1) hk'
        by_cases hk'' : k = 2
        . intro _
          have : ¬ 3 ∣ 10 := by exact Iff.mp (Ne.ite_ne_left_iff hn') (Ne.symm hn')
          have : 3 ∣ (10 : ℤ) := by--n:ℤとしたので、揃える
            rw [dvd_def]
            use n
            rw [hk''] at h
            replace h : n+14 = 4*n+4 := by rw [h] ; ring
            have : 14 = 4 * n + 4 - n := by exact eq_sub_of_add_eq' h
            have : 14 = 3 * n + 4 := by rw [this] ; ring
            have : 14 - 4 = 3 * n := by exact sub_eq_of_eq_add this
            have h10eq3muln : 10 = 3 * n := by rw [←this] ; ring
            apply h10eq3muln
          contradiction
        . intro hXork23
          have : k = 3 := by exact my_lemma_Xor_not (k=2) (k=3) hXork23 hk''
          rw [this] at h
          replace h : n+14 = 6*n+9 := by rw [h] ; ring
          have : n = 1 := by
            have : 14 = 6*n+9 - n := by exact eq_sub_of_add_eq' h
            have : 14 = 5*n + 9 := by rw [this] ; ring
            have : 14 - 9 = 5*n := by exact sub_eq_of_eq_add this
            have : 5 = 5*n := by exact this
            apply Int.eq_one_of_mul_eq_self_right _ (Eq.symm this)
            linarith
          contradiction
      rw [this] at h
      replace h : n+14 = 2*n+1 := by rw [h] ; ring
      have : 14 = 2 * n + 1 - n := by exact eq_sub_of_add_eq' h
      have : 14 = n + 1 := by rw [this] ; ring
      have : 14 - 1 = n := by exact sub_eq_of_eq_add this
      exact (Eq.symm this)
    . intro hn'
      rw [hn']
      linarith
  --後半
  . intro h
    have : n = 1 ∨ n = 13 := by exact Xor'.or h
    by_cases h' : n = 1
    . use 3
      rw [h']
      constructor
      . rfl
      . constructor
        . linarith
        . rfl
    . use 1
      have : n = 13 := by
        have : (¬ n = 1) → n = 13 := by
          apply Iff.mp or_iff_not_imp_left this
        apply this ; exact h'
      rw [this]
      constructor
      . linarith
      . constructor
        . rfl
        . rfl
