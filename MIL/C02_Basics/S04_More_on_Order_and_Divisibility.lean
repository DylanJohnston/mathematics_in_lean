import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

--max analogs
#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

#check le_min
example : max a b = max b a := by
  have h: ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    · apply le_max_right
    · apply le_max_left
  apply le_antisymm
  · apply h
  · apply h

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · calc
        min (min a b) c ≤ min a b := by apply min_le_left
        _ ≤ a := by apply min_le_left
    · apply le_min
      · calc
          min (min a b) c ≤ min a b := by apply min_le_left
          _ ≤ b := by apply min_le_right
      · apply min_le_right
  · apply le_min
    · apply le_min
      · apply min_le_left
      · calc
           min a (min b c) ≤ min b c := by apply min_le_right
           _ ≤ b := by apply min_le_left
    · calc
        min a (min b c) ≤ min b c := by apply min_le_right
        _ ≤ c := by apply min_le_right


theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have h1: ∀ x y z : ℝ, min x y + z ≤ x+z := by
    intro x y z
    apply add_le_add_right
    apply min_le_left
  have h2: ∀ x y z : ℝ, min x y + z ≤ y+z := by
    intro x y z
    apply add_le_add_right
    apply min_le_right
  apply le_min
  · apply h1
  · apply h2

#check add_neg_cancel_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  show min a b + c ≤ min (a + c) (b + c)
  apply aux
  show min (a + c) (b + c) ≤ min a b + c
  calc
    min (a + c) (b + c) = min (a + c) (b + c) -c +c := by ring
    _ ≤ min a b + c := by
      apply add_le_add_right
      apply le_min
      · nth_rw 2[← add_zero a]
        rw [← add_neg_cancel c, ← add_assoc]
        apply add_le_add_right
        apply min_le_left
      · nth_rw 2[← add_zero b]
        rw [← add_neg_cancel c, ← add_assoc]
        apply add_le_add_right
        apply min_le_right

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

#check sub_add_cancel

example : |a| - |b| ≤ |a - b| := by
  rw [← add_sub_cancel_right |a - b| |b|]
  apply add_le_add_right
  nth_rw 1 [← sub_add_cancel a b]
  apply abs_add
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

#check dvd_add_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h2: x ∣ w ^ 2 := by
    apply dvd_pow h
    exact Ne.symm (Nat.zero_ne_add_one 1) --used apply? to prove 2 ≠ 0...
  apply dvd_add (h₂:=h2)
  apply dvd_add
  · apply dvd_mul_of_dvd_right
    apply dvd_mul_of_dvd_left
    apply dvd_refl
  · apply dvd_pow
    · apply dvd_refl
    · exact Ne.symm (Nat.zero_ne_add_one 1) --used apply? to prove 2 ≠ 0...
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply gcd_comm
end
