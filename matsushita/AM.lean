import Mathlib

/-
 このファイルは Atiyah-MacDonald の Introduction to commutative algebra 
 の内容を Lean で記述する試みを記録したものです.
-/

/-
A 環, x nonunit → x を含む極大イデアルが存在

-/
universe u

variable (A : Type u) [CommRing A] [Nontrivial A]

example (x : A) (h : ¬IsUnit x) : ∃m, Ideal.IsMaximal m ∧ x ∈ m := by
  exact exists_max_ideal_of_mem_nonunits h

/-
 A 環, m A のイデアルで ∀x ∈ A \ m は unit → A local ring, m maximal
-/

theorem thm1  (m : Ideal A) (Htop : m ≠ ⊤) (H : ∀(x : A), x ∉  m → IsUnit x) : 
  LocalRing A:= by
  apply_assumption [LocalRing.of_nonunits_add]
  intros a b Ha Hb
  have lema : a ∈  m := by
    contrapose! H
    push_neg 
    use a 
    constructor
    ·assumption
    ·assumption 
  have lemb : b ∈  m := by
    contrapose! H
    use b 
    constructor
    ·assumption
    ·assumption 
  have ha_plus_b : a + b ∈ m := by
    exact Ideal.add_mem m lema lemb
  have hnonunit : (m : Set A) ⊆ nonunits A := by exact coe_subset_nonunits Htop
  exact Set.mem_of_subset_of_mem hnonunit ha_plus_b
  


/-
  m : A のイデアル, 1 + m の元は unit → A は local ring
-/

example (m : Ideal A) (h_proper : m ≠ ⊤) (h_max : Ideal.IsMaximal m) 
  (H : ∀(x : A), x ∈ m → IsUnit (1 + x)) : 
  LocalRing A := by
  apply_assumption [thm1]
  assumption 
  intro x x_not_in_m
  have lem1 :  Ideal.span ({x} ∪ (m : Set A)) = ⊤ := by sorry
  have lem2 : ∃ y : A, ∃ t : m, x*y  = 1 + t:= by sorry
  cases lem2 with
    | intro y Hy =>
  have lem3 : IsUnit (x*y)  := by sorry
  exact isUnit_of_mul_isUnit_left lem3


example (c m : ℕ) : ¬(c ≤ m) ↔ m < c := by exact Nat.not_le

    
/-
 n : A の冪零元からなる集合 → n は素イデアル, A/n に冪零元なし
-/
def mynilradical (R : Type u) [CommSemiring R] : Ideal R where
  carrier := { a | ∃n : ℕ, a^n = 0}
  zero_mem' := by
    simp 
    use 1
    exact pow_one 0
    
    

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
          intros c 
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
          · have BC2 : a^c = 0 := by 
              have nP : c > m := by exact not_le.mp P 
              have HNN : a^m * a^(c-m) = a^c  := by
                rw [← pow_add]              
                rw [← Nat.add_sub_assoc ?nP m]
                rw [add_comm]
                rw [Nat.add_sub_self_right]
                exact Nat.le_of_lt nP
              rw [←HNN]
              rw [Ha]  
              simp
            rw [BC2]
            simp           
    exact Finset.sum_eq_zero Term
  smul_mem' := by
    intros r s 
    dsimp 
    intro H 
    rcases H with ⟨n,H⟩ 
    use n 
    rw [mul_pow]
    rw [H]
    simp
    

lemma lemnil  (x : A) (n : ℕ )(h : x^n ∈ mynilradical A) : x ∈ mynilradical A := by
  have hnm : ∃ m : ℕ, (x^n)^m = 0 := by
    exact h
  cases hnm with
  | intro m H => _
  have H1 : x^(m*n) = 0 := by 
    rw [← H]
    ring 
  have H2 : ∃ N : ℕ, x^N = 0:= by
    exact Exists.intro (m * n) H1
  exact H2

example : mynilradical (A ⧸ mynilradical A) = ⊥ :=  by
  refine Iff.mpr (Submodule.eq_bot_iff (mynilradical (A ⧸ mynilradical A))) ?_
  intro x H
  have hnil : ∃ n : ℕ, x^n = 0 := by exact H
  have hsurjective : ∃ t : A, (Ideal.Quotient.mk (mynilradical A)) t = x := by
    exact Quot.exists_rep x
  cases hnil with
    | intro n Hn => _ 
  cases hsurjective with
    | intro t Ht => _ 
  have kernel : t ∈ mynilradical A := by
       have image_t : (Ideal.Quotient.mk (mynilradical A)) t^n = 0 := by
          rw [← Hn]
          exact congrFun (congrArg HPow.hPow Ht) n
       have kernel2 : t^n ∈ mynilradical A := by
         exact Iff.mp SModEq.zero image_t 
       exact lemnil A t n kernel2
  have Hfinal : (Ideal.Quotient.mk (mynilradical A)) t = 0 := by
    exact Iff.mpr Ideal.Quotient.eq_zero_iff_mem kernel
  rw [← Ht]
  assumption 







/-
  n A の冪零元からなる集合 ∘ n は A の全ての素イデアルの共通集合
-/

/-
  定義 A 環, Jacobson 根基とは A の極大イデアル全部の共通集合
-/

example :  x ∈ sInf {J : Ideal A | J.IsMaximal} ↔ ∀y : A, IsUnit (1 - x*y) := by
  constructor 
  · intro H1
    by_contra H2 
    push_neg at H2  
    cases H2 with 
    | intro y H3 => _
    have H4 : ∃ M : Ideal A, M.IsMaximal ∧ (1 - x*y) ∈ M := by 
      exact exists_max_ideal_of_mem_nonunits H3
    cases H4 with
    | intro M HM => _ 
    cases HM with 
    | intro HM1 HM2 => _ 
    have H6 : x ∈ M := by 
      apply Ideal.mem_sInf.mp H1 
      exact HM1
    have H7 : x*y ∈ M := by exact Ideal.mul_mem_right y M H6
    have H8 : 1 ∈ M := by exact Iff.mp (Submodule.sub_mem_iff_left M H7) HM2 
    have H9 : M = ⊤ := by exact Iff.mpr (Ideal.eq_top_iff_one M) H8
    have H10 : M ≠ ⊤ := by exact Ideal.IsPrime.ne_top'
    exact H10 H9
  · intro H1
    by_contra H2 
    have H3 : ∃ M : Ideal A, M.IsMaximal ∧ x ∉ M  := by
      by_contra H4 
      push_neg at H4
      have H5 : x ∈ sInf {J : Ideal A| J.IsMaximal} := by exact Iff.mpr Ideal.mem_sInf H4
      exact H2 H5 
    cases H3 with
    | intro  M HM => _ 
    cases HM with
    | intro HMax Hnotx => _ 
    have H6 : Ideal.span ({x} ∪ M) = ⊤ := by sorry
    have H7 : ∃(a : A), ∃(t : M), a*x + t = 1 := by sorry
    cases H7 with
    | intro a H8 => _  
    cases H8 with 
    | intro t H9 => _ 
    have H10 : ¬IsUnit (1 - a*x) := by sorry
    sorry

    

    

    
    
    

    
    
      
             
        
      


  


/-
  I A の Jacobson 根基とする. x ∈ I ↔ ∀ y ∈ A, 1 - xy が単元
-/

/-
 A 環, I_1, ... , I_n A のイデアル
 φ : A → ∏ A/I_i に関して
 1. φ が全射 ↔ ∀ i ≠ j, I_i + I_j = (1)
 2. φ が単射 ↔ ⋂ I_i = (0)
-/

