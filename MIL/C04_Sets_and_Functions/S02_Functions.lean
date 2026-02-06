import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)


open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  simp --I think simp just unpacked the RHS to f'' s ⊆ v. Done.

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x fx_f''s
  rcases fx_f''s with ⟨u,⟨us,fs_fx⟩⟩
  apply h at fs_fx
  convert us
  apply fs_fx.symm

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x
  rintro ⟨a,⟨fa_u,fa_x⟩⟩
  simp at fa_u
  rw [fa_x] at fa_u
  exact fa_u

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro x xu
  rcases h x with ⟨y,hy⟩
  use y
  constructor
  show f y ∈ u
  rw[hy];exact xu
  exact hy

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x fxs
  rcases fxs with ⟨a,⟨as,fa_x⟩⟩
  have a_in_t : a ∈ t := by apply h as
  use a

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x fx_u
  show f x ∈ v
  exact h fx_u

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  repeat
  rintro (fx_in_u | fx_in_v)
  left; exact fx_in_u
  right; exact fx_in_v

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro x ⟨y,⟨ys,yt⟩,rfl⟩
  /- rfl would be "f x = y", so it replaces x with fy everywhere and doesn't
  bother creating a hypothesis. Just now appreciated why this is handy to do... -/
  constructor
  use y
  use y

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro x ⟨x_fs,x_ft⟩
  rcases x_fs with ⟨y,⟨ys,fy_x⟩⟩
  rcases x_ft with ⟨z,⟨zt,fz_x⟩⟩ --z is actually equal to y since f injective. I'll deal with this later
  use y
  constructor
  constructor
  show y ∈ s
  exact ys
  show y ∈ t
  convert zt
  rw [fz_x.symm] at fy_x
  exact h fy_x
  show f y = x
  exact fy_x

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  simp
  constructor
  rintro ⟨y,⟨⟨i,yai⟩,fy_x⟩⟩
  use i, y
  rintro ⟨i,⟨y,⟨yai,fy_x⟩⟩⟩
  use y
  constructor
  use i
  exact fy_x

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro x
  rintro ⟨y, y_inter, fy_x⟩
  simp; intro i
  use y
  constructor
  simp at y_inter
  apply y_inter i
  exact fy_x

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x
  simp
  rintro h
  rcases h i with ⟨y,⟨yai,fy_x⟩⟩
  use y
  constructor
  intro j
  rcases h j with ⟨z,⟨zaj,rfl⟩⟩
  rw [injf fy_x]
  exact zaj
  exact fy_x

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x x_nonneg y y_nonneg sqrt_eq
  calc
  x = (√x)^2 := by rw [sq_sqrt x_nonneg]
  _ = (√y)^2 := by rw [sqrt_eq]
  _ = y := by rw [sq_sqrt y_nonneg]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x x_nonneg y y_nonneg sq_eq
  simp at sq_eq
  calc
  x = √(x^2) := by rw [sqrt_sq x_nonneg]
  _ = √(y^2) := by rw [sq_eq]
  _ = y := by rw [sqrt_sq y_nonneg]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  simp
  constructor
  rintro ⟨sx, ⟨sx_nonneg, rfl⟩⟩
  apply sqrt_nonneg
  intro x_nonneg
  use x^2
  constructor
  apply sq_nonneg
  apply sqrt_sq x_nonneg


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  simp
  constructor
  rintro ⟨y,rfl⟩
  apply sq_nonneg
  intro x_nonneg
  use √x
  apply sq_sqrt x_nonneg
end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse]
  rw [dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  --mp
  intro injf
  intro x
  rw [inverse]
  have hf : ∃ x_1, f x_1 = f x := by use x
  rw [dif_pos hf]
  apply injf
  exact Classical.choose_spec hf
  --mpr
  intro left_inv
  intro x y fx_fy
  calc
    x = (inverse f (f x)) := by apply (left_inv x).symm
    _ = (inverse f (f y)) := by rw[fx_fy]
    _ = y := by apply left_inv y

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  --mp
  intro surjf
  intro y
  rw [inverse]
  have hf : ∃ x_1, f x_1 = y := by apply surjf
  rw [dif_pos hf]
  exact Classical.choose_spec hf
  --mpr
  intro right_inv
  intro y
  use inverse f y
  apply right_inv

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  apply h₁
  have h₃ : j ∉ S
  rw [h] at h₁; contradiction
  contradiction

-- COMMENTS: TODO: improve this
end
