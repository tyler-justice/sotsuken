import Mathlib

/- 入試問題　-/
-- 等比数列
example (p α: ℝ) (a : ℕ → ℝ) 
  (h1 : a n+1 = p*(a n)) 
  (h0 : a 0 = α)
  : a n = p^(n-1)*α := by
  sorry
    
  


/- 素数の無限性 -/

/- 証明駆動開発 -/
example (a : ℕ → ℝ) (h : a n+1 = a n + n^2) : 
  a n = (1/6)*n*(n+1)*(2*n + 1) := by
  sorry

/-  AM の Lean への翻訳 -/

variable [CommRing R] (I : Ideal R)
#check Ideal.Quotient.mk I
#check R⧸I


example ( J : Ideal R)  : I*J ≤ I ⊓ J := by 
  sorry

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
  sorry 
