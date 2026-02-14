import MIL.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext

example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem

instance [Monoid M] : Min (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z
      rintro ⟨t, ht, u, hu, x_equiv_y⟩
      rintro ⟨v, hv, w, hw, y_equiv_z⟩
      use t*v, ?_, w*u, ?_
      calc
        x * (t * v) = y * (u * v) := by simp [← mul_assoc, x_equiv_y]
        _ = y * v * u := by rw [mul_comm u v, mul_assoc]
        _ = z * (w * u) := by rw [y_equiv_z, mul_assoc]
      apply N.mul_mem ht hv
      apply N.mul_mem hw hu
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂ (· * ·) (by
      intro a b a_cong_b c d c_cong_d
      simp
      rcases a_cong_b with ⟨t,tn,u,un,a_equiv_b⟩
      rcases c_cong_d with ⟨v,vn,w,wn,c_equiv_d⟩
      use t*v, ?_, u*w, ?_
      show a * c * (t * v) = b * d * (u * w)
      calc
        a * c * (t * v) = a*t*c*v := by rw [← mul_assoc, mul_assoc a c t, mul_comm c t, ← mul_assoc]
        _ = b*u*d*w := by rw [mul_assoc (a*t) c v, a_equiv_b, c_equiv_d, ← mul_assoc]
        _ = b*d*(u*w) := by rw [mul_assoc b u d, mul_comm u d, ← mul_assoc, mul_assoc]
      apply N.mul_mem tn vn
      apply N.mul_mem un wn
      )
  mul_assoc := by
    rintro a b c
    rcases Quotient.exists_rep a with ⟨x, hx⟩ -- for q in quotient, ∃ a, ⟦a⟧ = q
    rcases Quotient.exists_rep b with ⟨y, hy⟩
    rcases Quotient.exists_rep c with ⟨z, hz⟩
    rw [← hx,← hy,← hz]
    apply Quotient.sound --states x ≃ y → ⟦x⟧ = ⟦y⟧. Use this to lift the goal into M.
    simp [mul_assoc]
  one := QuotientMonoid.mk N 1
  one_mul := by
      intro a
      rcases Quotient.exists_rep a with ⟨x, hx⟩
      rw [← hx]
      apply Quotient.sound; simp
  mul_one := by
      intro a
      rcases Quotient.exists_rep a with ⟨x, hx⟩
      rw [← hx]
      apply Quotient.sound; simp
