import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  show x ≤ |x| -- assuming 0 ≤ x
  rw [abs_of_nonneg h]
  show x ≤ |x| -- asumming x < 0
  rw [abs_of_neg h]
  linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  show -x ≤ |x| -- h : 0 ≤ x
  rw [abs_of_nonneg h]
  linarith
  show -x ≤ |x| -- h : x < 0
  rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x+y) with h | h
  -- CASE: 0 ≤ x+y
  rcases le_or_gt 0 x with hx | hx
  rcases le_or_gt 0 y with hy | hy
  simp [abs_of_nonneg h, abs_of_nonneg hx, abs_of_nonneg hy]
  simp [abs_of_nonneg h, abs_of_nonneg hx, abs_of_neg hy]
  linarith
  rcases le_or_gt 0 y with hy | hy
  simp [abs_of_nonneg h, abs_of_neg hx, abs_of_nonneg hy]
  linarith
  simp [abs_of_nonneg h, abs_of_neg hx, abs_of_neg hy]
  linarith
  -- CASE: x+y < 0
  rcases le_or_gt 0 x with hx | hx
  rcases le_or_gt 0 y with hy | hy
  simp [abs_of_neg h, abs_of_nonneg hx, abs_of_nonneg hy]
  linarith
  simp [abs_of_neg h, abs_of_nonneg hx, abs_of_neg hy]
  linarith
  rcases le_or_gt 0 y with hy | hy
  simp [abs_of_neg h, abs_of_neg hx, abs_of_nonneg hy]
  linarith
  simp [abs_of_neg h, abs_of_neg hx, abs_of_neg hy]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases lt_or_ge 0 y with h | h
  rw [abs_of_pos h]
  constructor
  intro x_le_y
  left
  apply x_le_y
  rintro (h1|h2)
  apply h1
  linarith
  rw [abs_of_nonpos h]
  constructor
  intro x_le_neg_y
  right
  apply x_le_neg_y
  rintro (h1|h2)
  linarith
  apply h2


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  intro abs_x_lt_y
  rcases lt_or_ge 0 x with xpos | xnonpos
  constructor
  rw [abs_of_pos xpos] at abs_x_lt_y
  linarith
  rw [abs_of_pos xpos] at abs_x_lt_y
  linarith
  constructor
  rw [abs_of_nonpos xnonpos] at abs_x_lt_y
  linarith
  rw [abs_of_nonpos xnonpos] at abs_x_lt_y
  linarith
  rintro ⟨h1,h2⟩
  rcases lt_or_ge 0 x with xpos | xnonpos
  rw [abs_of_pos xpos]
  apply h2
  rw [abs_of_nonpos xnonpos]
  linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x,⟨y,hz|hz⟩⟩
  calc
    z = x ^ 2 + y ^ 2 := by apply hz
    _ ≥ 0 + 0 := by
      apply add_le_add
      repeat
      apply pow_two_nonneg
    _ = 0 := by apply zero_add 0
  calc
    z = x ^ 2 + y ^ 2 + 1:= by apply hz
    _ ≥ 0 + 0 + 1:= by
      apply add_le_add
      apply add_le_add
      apply pow_two_nonneg
      apply pow_two_nonneg
      apply le_rfl
    _ = 1 := by
      rw [zero_add 0]
      apply zero_add 1
    _ ≥ 0 := by apply zero_le_one

#check eq_zero_or_eq_zero_of_mul_eq_zero

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h2: (x+1)*(x-1) = 0 := by
    calc
    (x+1)*(x-1) = x^2 - 1 := by ring
    _ = 1 - 1 := by rw [h]
    _ = 0 := by apply sub_self 1
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h2 with x0|y0
  right
  linarith
  left
  linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h2: (x+y)*(x-y) = 0 := by
    calc
    (x+y)*(x-y) = x^2 - y^2 := by ring
    _ = x^2 - x^2 := by rw [h]
    _ = 0 := by apply sub_self (x^2)
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h2 with left_eq_0|right_eq_0
  right
  linarith
  left
  linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h2: (x+1)*(x-1) = 0 := by
    calc
    (x+1)*(x-1) = x^2 - 1 := by ring
    _ = 1 - 1 := by rw [h]
    _ = 0 := by apply sub_self 1
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h2 with x0|y0
  right
  rw [← sub_neg_eq_add] at x0
  rw [sub_eq_zero] at x0
  apply x0
  left
  rw [sub_eq_zero] at y0
  apply y0

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h2: (x+y)*(x-y) = 0 := by
    calc
    (x+y)*(x-y) = x^2 - y^2 := by ring
    _ = x^2 - x^2 := by rw [h]
    _ = 0 := by apply sub_self (x^2)
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h2 with left_eq_0|right_eq_0
  right
  rw [← sub_neg_eq_add] at left_eq_0
  rw [sub_eq_zero] at left_eq_0
  apply left_eq_0
  left
  rw [sub_eq_zero] at right_eq_0
  apply right_eq_0
end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  show (P → Q) → ¬P ∨ Q
  intro P_im_Q
  contrapose! P_im_Q
  apply P_im_Q
  show ¬P ∨ Q → P → Q
  rintro (notP | Q)
  contrapose! notP
  obtain ⟨l,r⟩ := notP
  apply l
  intro P
  apply Q
