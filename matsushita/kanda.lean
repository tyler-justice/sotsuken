import Mathlib

/-
  S を有限集合とし, f : S → S を自分自身への写像とします. この時
  f が単射 ↔ 全射となりますが, まずこの主張を Lean で記述してみて
  ください. Tutorial の 4 節が参考になります.
-/

/- Lean の reduce と eval の違いを確かめるサンプルプログラム-/

def f  (n : Nat) := n

def g  (n : Nat) := 1*n


theorem f_eq_g : f = g := by
  funext
  unfold f
  unfold g
  rw [one_mul]

--  funext fun n => (Nat.zero_add n).symm


def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

#reduce val

#eval val

theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val1 : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

-- does not reduce to 0
#reduce val1

-- evaluates to 0
#eval val1

#eval Real.sin 2
