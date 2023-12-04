import Mathlib



/- 代数閉体にするべきだろうか?-/

open MvPolynomial

variable {k : Type*} [Field k] [IsAlgClosed k]

variable {n : Type*}

def 𝕀 (X : Set (n → k)) : Set (MvPolynomial n k) :=
  {f | ∀ x ∈ X , eval x f = 0}

open Set

lemma mem_𝕀_iff {X : Set (n → k)} {f : MvPolynomial n k} :
    f ∈ 𝕀 X ↔ ∀ x ∈ X, eval x f = 0 := by
    exact Set.mem_def

lemma empty : 𝕀 (∅ : Set (n → k)) = univ := by
  rw [eq_univ_iff_forall]
  intro f
  rw [mem_𝕀_iff]
  intros x hx
  cases hx

lemma eval_eq_zero  {f : MvPolynomial n k}  : (∀ x, MvPolynomial.eval x f = 0) ↔ f = 0
  := by
  sorry


lemma univ :
  𝕀 (univ : Set (n → k)) = {0} := by
  rw [Set.Subset.antisymm_iff]
  constructor
  · intros f hf
    rw [mem_singleton_iff]
    rw [mem_𝕀_iff] at hf
    rw [← eval_eq_zero]
    intros x
    apply hf
    apply mem_univ

  · rw [singleton_subset_iff]
    rw [mem_𝕀_iff]
    simp

lemma 𝕀_antimono (V W : Set (n →k)) : V ⊆ W → 𝕀 W ⊆ 𝕀 V := by
  intros H
  rw [subset_def] at *
  intros f F
  rw [mem_𝕀_iff] at *
  intros g G
  apply F
  apply H
  assumption

noncomputable def 𝕀' (X : Set (n → k)) : Ideal (MvPolynomial n k) :=
{carrier := (𝕀 X)
 zero_mem' := by simp [𝕀]
 add_mem' := by
    intros f g hf hg
    change ∀ (x : n → k), x ∈ X → eval x f = 0 at hf
    change ∀ (x : n → k), x ∈ X → eval x g = 0 at hg
    rw [mem_𝕀_iff]
    intros x hx
    rw [eval_add]
    rw [hf _ hx, hg _ hx]
    rw [add_zero]

 smul_mem' := by
    intros c f hf
    change ∀ (x : n → k), x ∈ X → eval x f = 0 at hf
    intros x hx
    rw [smul_eq_mul, eval_mul]
    rw [hf _ hx]
    rw [mul_zero]
}

#help command
