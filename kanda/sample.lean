import Mathlib.Data.Finset.Basic
import Mathlib.Init.Function
import Init.Prelude
/-
  S を有限集合とし, f : S → S を自分自身への写像とします. この時
  f が単射 ↔ 全射となりますが, まずこの主張を Lean で記述してみて
  ください. Tutorial の 4 節が参考になります.
-/

open Set
open Function
open Finset

section
variable {α : Type u_1} [Nonempty α]
variable {S : Finset α} 
variable {f: S → S}

--Finset S is meaning "S is a finite set".
theorem rightside (h:Injective f) : Surjective f :=by
  have setS := toSet S
  let ImS := f '' setS
  /-error:
  application type mismatch
  f '' setS
argument
  setS
has type
  Set α : Type u_1
but is expected to have type
  Set { x // x ∈ S } : Type u_1
  -/

theorem leftside (h:Surjective f) : Injective f :=by
  sorry

--That's naturaly.
--But generary, I think binary relation between S and {1,2,...,n}.
--Using that is seen difficult, So To proof needs a new think.

#check toSet
#check Finset.toSet S



end
