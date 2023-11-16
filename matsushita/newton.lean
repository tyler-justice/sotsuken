import Mathlib

def newton (n : ℕ) : ℚ  := 
  match n with
  | Nat.zero => 1
  | Nat.succ n' => (newton n' + 2/(newton n'))/2

#eval newton 10

lemma lower_estimate : newton n > 1 := by sorry

theorem main : abs (newton n - Int.sqrt 2) < (1/2)^n := by sorry 


