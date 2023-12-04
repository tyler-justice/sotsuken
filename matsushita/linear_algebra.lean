import Mathlib

universe u

variable (a b c d : ℝ)

def A : Matrix (Fin 2) (Fin 2) ℤ := !![1,2;3,4]
def B : Matrix (Fin 2) (Fin 2) ℤ := !![2,-1;0,3]
def C : Matrix (Fin 2) (Fin 2) ℝ := !![a, b ; c, d]
def D : Matrix (Fin 2) (Fin 2) ℝ := !![(1:ℝ),(2:ℝ);(3:ℝ),(4:ℝ)]


#eval A 2
#eval B 0

#check C
#check D

#check C


/-
failed to synthesize instance
  Fintype ℝ
-/

#check A*B

#eval A*B


#eval Matrix.det A



#eval !![1,2;3,4] * !![2,-1;0,3]

#eval !![1,2;3,4]*!![1;2]

#check !![1;2;3]

#check Matrix.vecMulLinear !![1,2;3,4]

#eval Matrix.vecMulLinear  !![1,2;3,4] ![1,2]

#eval Matrix.vecMulLinear !![2,1;3,1] ![-1,0]


/- この定義だと v ↦ vM というのが線型写像の定義 -/

example : Matrix.vecMulLinear !![2,1;3,1] ![-1,0]  = ![-2,-1] := by

/- [,] リストを与える. !! を使うと何故行列になるかは理解していない
 Lean でのベクトル等の記述のやり方は Matrix and vector notation に記述がある. -/

/-
 簡単な行列は !![a,b;c,d], ベクトルは ![a,b] で書ける
-/
  exact Iff.mp hammingDist_eq_zero rfl

#eval (-2)•![1,-2]

#check ![a,b]

#check 2•![a,b] = ![2*a,2*b]

example :  a•![(1:ℝ),(2:ℝ)] = ![a,(2:ℝ)*a] := by
  rw [Matrix.smul_vec2]
  simp
  rw [mul_comm]

/- 1,2 などを実数として認識させるためには (1:ℝ) とすれば良い -/
