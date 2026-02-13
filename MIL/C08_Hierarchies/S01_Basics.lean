import MIL.Common
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Real.Basic

set_option autoImplicit true


class One₁ (α : Type) where
  /-- The element one -/
  one : α


#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

#check One₂.one


example (α : Type) [One₁ α] : α := One₁.one

example (α : Type) [One₁ α] := (One₁.one : α)

@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl

--This is a magma
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia


class Semigroup₀ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)


attribute [instance] Semigroup₀.toDia₁

example {α : Type} [Semigroup₀ α] (a b : α) : α := a ⋄ b


class Semigroup₁ (α : Type) extends toDia₁ : Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b


class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

-- This is a unital magma
class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a



set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙


class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α

/- Below is a bad way to do it as we get two unrelated ⋄ operations
   One from Monoid₂.toSemigroup₁.toDia₁ and one from Monoid₂.toDiaOneClass₁.toDia₁
   -/
class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

/- As seen below, this is not a problem if we use "extends" method as in Monoid₁ -/
example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl


/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk


#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁


class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙


lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]


export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)


example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]


lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b := by
  have : a⁻¹ ⋄ a = 𝟙 := by
    exact (inv_dia a)
  rw [← one_dia b, ← this, dia_assoc, h, dia_one]

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  have h : a⁻¹ ⋄ a = 𝟙 := by apply inv_dia a
  have : a = (a⁻¹)⁻¹ := by apply (inv_eq_of_dia h).symm
  calc
  a ⋄ a⁻¹ = (a⁻¹)⁻¹ ⋄ a⁻¹ := by rw [← this]
  _ = 𝟙 := by apply inv_dia a⁻¹


class AddSemigroup₃ (α : Type) extends Add α where
  /-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
  /-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1


attribute [simp] Group₃.inv_mul AddGroup₃.neg_add



@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  have : a⁻¹ * a = 1 := by
    apply (Group₃.inv_mul a)
  rw [← mul_one a⁻¹, ← h, ← mul_assoc₃, this, one_mul]

@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  have h : a⁻¹ * a = 1 := by apply inv_mul a
  have : a = (a⁻¹)⁻¹ := by apply (inv_eq_of_mul h).symm
  calc
  a * a⁻¹ = (a⁻¹)⁻¹ * a⁻¹ := by rw [← this]
  _ = 1 := by apply inv_mul a⁻¹

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  calc
  b = a⁻¹ * (a * b) := by
    nth_rw 1 [← one_mul b]
    rw [← Group₃.inv_mul a, mul_assoc₃]
  _ = a⁻¹ * (a * c) := by rw [h]
  _ = c := by rw[← mul_assoc₃, Group₃.inv_mul a, one_mul c]

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
  calc
  b = (b * a) * a⁻¹ := by
    nth_rw 1 [← mul_one b]
    rw [← @Group₃.mul_inv _ _ a, mul_assoc₃]
  _ = (c * a) * a⁻¹ := by rw [h]
  _ = c := by rw[mul_assoc₃, Group₃.mul_inv, mul_one c]

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G

class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ add_comm := by
    intro a b
    have h: a+b+a+b = a+a+b+b := by --a+a+b+b = (1+1)(a+b) = a+b+a+b
      calc
      a+b+a+b = 1*(a+b)+1*(a+b) := by simp [right_distrib, add_assoc₃]
      _ = (1+1)*(a+b) := by rw [Ring₃.right_distrib]
      _ = a+a+b+b := by simp [Ring₃.left_distrib, Ring₃.right_distrib, add_assoc₃]
    calc
    a+b = (-a + a)+(a+b)+(b + -b) := by simp [Ring₃]
    _ = -a + (a+a+b+b) + -b := by
      simp [← add_assoc₃]
      rw [add_assoc₃, Ring₃.toAddGroup₃.add_neg]
      simp
    _ = -a + (a+b+a+b) + -b := by rw[← h]
    _ = b + a := by
      simp [add_assoc₃]
      rw [← add_assoc₃, Ring₃.toAddGroup₃.neg_add]
      simp
}

instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type) extends LE₁ α where
  rfl : ∀ a : α, a ≤₁ a
  trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c

class PartialOrder₁ (α : Type) extends Preorder₁ α where
  antisymm : ∀ a b : α, a ≤₁ b → b ≤₁ a → a = b

class OrderedCommMonoid₁ (α : Type) extends CommMonoid α, PartialOrder₁ α where
  mul_le_of_le: ∀ a b c: α, a ≤₁ b → c * a ≤₁ c * b

instance : OrderedCommMonoid₁ ℕ where
  le := (· ≤ .)
  rfl := Nat.le_refl
  trans := @Nat.le_trans
  antisymm := @Nat.le_antisymm
  mul_le_of_le := @Nat.mul_le_mul_left

class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul


class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib

def nsmul₁ {M : Type*} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a

instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry

#synth Module₁ ℤ ℤ -- abGrpModule ℤ


class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
