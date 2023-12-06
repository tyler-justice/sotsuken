import Mathlib
/-
関数f（微分可能（で連続））
区間a,bで導関数が正
このとき、f(a) < f(b)を示す
-/
example (f : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b)
  (hfc : ContinuousOn f (Set.Icc a b)) --[a,b]でfが連続
  (hfd : DifferentiableOn ℝ f (Set.Ioo a b)) --(a,b)でfが微分可能
  (hfdpos : ∀ x ∈ Set.Ioo a b/-[a, b]-/, 0 < deriv f x):
  f a < f b := by
--  #find apply_assumption
  have h1 : ∃ c, c ∈ Set.Ioo a b ∧ deriv f c = (f b - f a) / (b - a) := by
    exact exists_deriv_eq_slope f hab hfc hfd--平均値の定理（Leanにはいくつかこれの派生がある）
  rcases h1 with ⟨c, h1.left, h1.right⟩
  have hfdcpos : 0 < deriv f c := by
    exact hfdpos c h1.left
  have hbapos : 0 < b - a := by apply sub_pos_of_lt hab
  have h3 : (deriv f c) * (b - a) > 0 := by apply mul_pos hfdcpos hbapos
  have h1.right': (deriv f c) * (b - a) = f b - f a := by
    rw [h1.right, div_mul, div_self]
    simp
    exact ne_of_gt hbapos
  have h2 : f b - f a > 0 := by
    rw [←h1.right']
    exact h3
  calc
    f a = f a + 0 := by simp
    _ < f a + (f b - f a) := by apply add_lt_add_left h2
    _ = f b := by simp
/-本来はf全体で連続や微分可能を言って、そこからa,bの範囲について言及した方がいい？
今回は仮定から区間a,bで考えたけど-/
#check(deriv)
#check(exists_deriv_eq_slope)

--importすべきものが何かを出してくれる
#minimize_imports

--#で使えるコマンドの一覧を出してくれる
#help command
