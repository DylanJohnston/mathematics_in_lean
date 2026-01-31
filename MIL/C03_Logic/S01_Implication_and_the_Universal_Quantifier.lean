import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry --prove later

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

/-  note that the variables are implicit (in curly brackets). When applying a lemma
    we do not need to pass variables, just the hypotheses (and the variables are inferred)
    from the hypotheses).-/
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry

#check abs_mul --|a * b| = |a| * |b|
#check mul_le_mul -- a * c ≤ b * d w/ reasonable hyp. on a,b,c,d
#check abs_nonneg -- 0 ≤ |a|
#check mul_lt_mul_right -- b*a < c*a ↔ b < c if a > 0
#check one_mul -- 1 * a = a

theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by
      apply mul_le_mul
      show |x| ≤ |x|
      apply le_rfl
      show |y| ≤ ε
      apply le_of_lt ylt
      show 0 ≤ |y|
      apply abs_nonneg
      show 0 ≤ |x|
      apply abs_nonneg
    _ < 1 * ε := by
      calc
      |x| * ε < ε * ε := by
        apply mul_lt_mul xlt le_rfl epos
        show 0 ≤ ε
        apply le_of_lt epos
      _ ≤ 1 * ε := by
        apply mul_le_mul ele1 le_rfl _ _
        show 0 ≤ ε
        apply le_of_lt epos
        show 0 ≤ 1
        apply zero_le_one
    _ = ε := by apply one_mul

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp /-alternative is "change f x + g x ≤ a + b",
        since (fun x ↦ f x + g x) x and f x + g x are definitionally equal-/
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  change a + b ≤ f x + g x
  apply add_le_add
  apply hfa
  apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  change 0 ≤ f x * g x
  apply mul_nonneg
  apply nnf
  apply nng


example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  change f x * g x ≤ a * b
  apply mul_le_mul
  show f x ≤ a
  apply hfa
  show g x ≤ b
  apply hgb
  show 0 ≤ g x
  apply nng
  show 0 ≤ a
  apply nna
end

section
variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  change c * f a ≤ c * f b
  apply mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  change f (g a) ≤ f (g b)
  apply mf
  apply mg aleb

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := by rfl
    _ = -f (-x) * -g (-x) := by rw[of, og]
    _ = f (-x) * g (-x) := by apply neg_mul_neg

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := by rfl
    _ = f (-x) * -g (-x) := by rw[ef, og]
    _ = -f (-x) * g (-x) := by apply Eq.symm (neg_mul_comm (f (-x)) (g (-x)))
    _ = -(f (-x) * g (-x)) := by apply Eq.symm (neg_mul_eq_neg_mul (f (-x)) (g (-x)))

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  calc
  (fun x ↦ f (g x)) x = f (g x) := by rfl
  _ = f (-g (-x)) := by
    apply congrArg-- https://www.leanexplore.com/?pkg=Batteries&pkg=Init&pkg=Lean&pkg=Mathlib&pkg=Std&q=if+a+equals+b+then+f+a+equals+f+b
    apply og
  _ = f (g (-x)) := by
    rw [← ef]
end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  sorry

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  sorry

end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  sorry

end
