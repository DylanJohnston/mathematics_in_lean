import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

-- ¬P is shorthand for "P → False"
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro flb
  obtain ⟨a, flba⟩ := flb
  obtain ⟨x, hx⟩ := h a
  have : f x ≥ a := flba x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  intro fub
  obtain ⟨a, fuba⟩ := fub
  have u : ∀ a : ℝ, ∃ x, x > a := by
    intro a
    use a + 1
    linarith
  obtain ⟨x, x_gt_a⟩ := u a
  have : x ≤ a := fuba x
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro b_le_a
  have : f b ≤ f a := by apply h b_le_a
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro mf
  have : f a ≤ f b := by exact mf h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro x y
    change x ≤ y → 0 ≤ 0
    intro _
    apply le_refl
  have h' : f 1 ≤ f 0 := le_refl _
  have one_eq_zero : (1 : ℝ) ≤ 0 := by apply h monof h'
  have : 0 < (1 : ℝ) := by apply zero_lt_one
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro zero_lt_x
  have x_le_half_x : x < x/2 := by
    apply h (x/2)
    apply half_pos zero_lt_x --if 0 < x then 0 < x/2
  have : x > x/2 := by
    apply div_two_lt_of_pos zero_lt_x
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by --h reads "∃ x, P x → False"
  intro x px
  apply h -- changes "False" to "∃ x, P x"
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro exists_x_st_px
  obtain ⟨x,px⟩ := exists_x_st_px
  apply h x px

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry --harder to prove (haven't seen how to work with ∃ in statement). See two examples from now

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro all_x_Px
  obtain ⟨x,not_Px⟩ := h
  apply not_Px
  apply all_x_Px x

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h h'

example (h : Q) : ¬¬Q := by
  intro notQ
  apply notQ h
end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  by_contra h''
  apply h'
  apply lt_of_not_ge at h''
  use x

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  by_contra h'
  apply h
  push_neg at h'
  exact h'

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith
end

section
variable (a : ℕ)

#check False.elim

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
