import Mathlib


variable (α : ℝ)

def seqA : Nat → Nat
  | 0  =>  2
  | n+1 => 3 * seqA n

#eval seqA 2



/- 入試問題　-/
-- 等比数列
example (p α: ℝ) (ppos : p > 0) (a : ℕ → ℝ) 
  (h0 : a 0 = α)
  (h1 : ∀n, a n.succ = p*(a n)) 
    : a n = (p^n) *α := by
  induction' n with n ih
  · simp
    exact h0
  · specialize h1 n
    rw [h1]
    rw [ih]
    simp
    rw [add_comm]
    --nth_rewrite 2 [Real.rpow_add ppos 1 n]
    rw [← mul_assoc]
    nth_rewrite 1 [← Real.rpow_one p]
    rw [Real.rpow_add]
    simp 
    assumption
    

#check pow_add
#check Monoid


      
example ( p n :ℝ) (ppos : p > 0) : p^(1 + n) = p^1*p^n := by
  exact Real.rpow_add ppos 1 n 

    
  


/- 素数の無限性 -/

/- 証明駆動開発 -/
sawaguchi
example (a : ℕ → ℝ) (h : ∀ n, a (n+1) = a n + (n+1)^2) (h0 :a 0 = 0):
  a n = (1/6)*n*(n+1)*(2*n + 1) := by
  induction' n with n ih
  · simp [h0]
  simp at *
  rw [Nat.succ_eq_add_one]
  specialize h (n)
  nth_rewrite 1 [ih] at h
  rw [h]
  ring

/-  AM の Lean への翻訳 -/

variable [CommRing R] (I : Ideal R)

#check Ideal.Quotient.mk I
#check R⧸I



example ( J : Ideal R)  : I*J ≤ I ⊓ J := by 
  exact Ideal.mul_le_inf


example ( J : Ideal R) (h : J ≥ I) :
  (Ideal.Quotient.mk I)⁻¹' ((Ideal.Quotient.mk I)'' J) = J := by
  sorry

example (I  : Ideal R)  (I0 : Ideal (R ⧸ I)) :
       (Ideal.Quotient.mk I)''((Ideal.Quotient.mk I)⁻¹' I0 ) = I0 := by
  sorry

/- 有限集合の全単射 -/

universe u

variable (S : Finset u)
#check S
variable (f : S → S)
#check f


example  (H : Function.Injective f) : Function.Surjective f := by 
  exact Finite.surjective_of_injective H

