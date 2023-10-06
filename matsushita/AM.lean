import Mathlib

/-
 このファイルは Atiyah-MacDonald の Introduction to commutative algebra 
 の内容を Lean で記述する試みを記録したものです.
-/

/-
A 環, x nonunit → x を含む極大イデアルが存在

-/
universe u

variable (A : Type u) [CommRing A]

example (x : A) (h : ¬IsUnit x) : ∃m, Ideal.IsMaximal m ∧ x ∈ m := by
  sorry 

/-
 A 環, m A のイデアルで ∀x ∈ A \ m は unit → A local ring, m maximal
-/

example (m : Ideal A) (H : ∀(x : A), x ∉  m → IsUnit x) : 
  LocalRing A:= by
  sorry

/-
  m : A のイデアル, 1 + m の元は unit → A は local ring
-/

example (m : Ideal A) (H : ∀(x : A), x ∈ m → IsUnit (1 + x)) : 
  LocalRing A := by
  sorry 

/-
 n : A の冪零元からなる集合 → n は素イデアル, A/n に冪零元なし
-/

/-
  n A の冪零元からなる集合 ∘ n は A の全ての素イデアルの共通集合
-/