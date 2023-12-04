import Mathlib

/-
  Atiyah-MacDonald の Introduction to Commutative Algebra の
  一部を Lean で記述することを考えています. まず最初は

  (A : ring) (I : ideal) としたとき, J ⊃ I となる A のイデアル J
  の集合と A/I のイデアルの集合が 1:1 になる

  ことを示そうと思います. 最初の作業は上述の主張をちゃんと

  example (A : ring)...

  のように記述することで, 

  https://leanprover-community.github.io/mathlib-overview.html

  からどのように環とそのイデアルを打ち込めば良いか考えてみてください.
  ササキ
-/