import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
  apply le_inf
  · apply inf_le_right
  · apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
  apply le_inf
  · calc
    x ⊓ y ⊓ z ≤ x ⊓ y := by apply inf_le_left
    _ ≤ x := by apply inf_le_left
  · apply le_inf
    · calc
        x ⊓ y ⊓ z ≤ x ⊓ y := by apply inf_le_left
        _ ≤ y := by apply inf_le_right
    · apply inf_le_right
  show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
  apply le_inf
  · apply le_inf
    · apply inf_le_left
    · calc
      x ⊓ (y ⊓ z) ≤ y ⊓ z := by apply inf_le_right
      _ ≤ y := by apply inf_le_left
  · calc
    x ⊓ (y ⊓ z) ≤ y ⊓ z := by apply inf_le_right
    _ ≤ z := by apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  show x ⊔ y ≤ y ⊔ x
  apply sup_le
  · apply le_sup_right
  · apply le_sup_left
  show y ⊔ x ≤ x ⊔ y
  apply sup_le
  · apply le_sup_right
  · apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm

  show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z) --case a
  apply sup_le
  show x ⊔ y ≤ x ⊔ (y ⊔ z) --case a.1
  apply sup_le
  show x ≤ x ⊔ (y ⊔ z) --case a.1.1
  apply le_sup_left
  show y ≤ x ⊔ (y ⊔ z) --case a.1.2
  calc
    y ≤ y ⊔ z := by apply le_sup_left
    _ ≤ x ⊔ (y ⊔ z) := by apply le_sup_right
  show z ≤ x ⊔ (y ⊔ z) -- case a.2
  calc
    z ≤ y ⊔ z := by apply le_sup_right
    _ ≤ x ⊔ (y ⊔ z) := by apply le_sup_right

  show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z --case b
  apply sup_le
  show x ≤ x ⊔ y ⊔ z -- case b.1
  calc
    x ≤ x ⊔ y := by apply le_sup_left
    _ ≤ x ⊔ y ⊔ z := by apply le_sup_left
  show y ⊔ z ≤ x ⊔ y ⊔ z -- case b.2
  apply sup_le
  show y ≤ x ⊔ y ⊔ z -- case b.2.1
  calc
    y ≤ x ⊔ y := by apply le_sup_right
    _ ≤ x ⊔ y ⊔ z := by apply le_sup_left
  show z ≤ x ⊔ y ⊔ z -- case b.2.2
  apply le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  show x ⊓ (x ⊔ y) ≤ x -- case a
  apply inf_le_left
  show x ≤ x ⊓ (x ⊔ y) -- case b
  apply le_inf
  show x ≤ x -- case b.1
  apply le_rfl
  show x ≤ x ⊔ y -- case b.2
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  show x ⊔ x ⊓ y ≤ x -- case a
  apply sup_le
  show x ≤ x -- case a.1
  apply le_rfl
  show x ⊓ y ≤ x -- case a.2
  apply inf_le_left
  show x ≤ x ⊔ x ⊓ y -- case b
  apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

--did the other, that was enough...
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

-- following "hand written" proof from https://math.stackexchange.com/a/4757231/580026
example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  have eq_implies_meet_eq: ∀ x y z : α, x = y → (x ⊓ z) = (y ⊓ z) := by
        intro x y z x_eq_y
        apply le_antisymm
        show x ⊓ z ≤ y ⊓ z -- case a
        apply le_inf
        show x ⊓ z ≤ y -- case a.1
        calc
          x ⊓ z ≤ x := by apply inf_le_left
          _ = y := by apply x_eq_y
        show x ⊓ z ≤ z -- case a.2
        apply inf_le_right
        show y ⊓ z ≤ x ⊓ z -- case b
        apply le_inf
        show y ⊓ z ≤ x -- case b.1
        calc
          y ⊓ z ≤ y := by apply inf_le_left
          _ = x := by apply Eq.symm x_eq_y
        show y ⊓ z ≤ z -- case b.2
        apply inf_le_right
  calc
    a ⊓ (b ⊔ c) = (a ⊓ (a ⊔ c)) ⊓ (b ⊔ c) := by
      apply le_antisymm
      show a ⊓ (b ⊔ c) ≤ a ⊓ (a ⊔ c) ⊓ (b ⊔ c) -- case a
      apply le_inf
      show a ⊓ (b ⊔ c) ≤ a ⊓ (a ⊔ c) -- case a.1
      apply le_inf
      show a ⊓ (b ⊔ c) ≤ a -- case a.1.1
      apply inf_le_left
      show a ⊓ (b ⊔ c) ≤ a ⊔ c -- case a.1.2
      calc
        a ⊓ (b ⊔ c) ≤ a := by apply inf_le_left
        _ ≤ a ⊔ c := by apply le_sup_left
      show a ⊓ (b ⊔ c) ≤ b ⊔ c -- case a.2
      apply inf_le_right
      show a ⊓ (a ⊔ c) ⊓ (b ⊔ c) ≤ a ⊓ (b ⊔ c) -- case b
      apply le_inf
      show a ⊓ (a ⊔ c) ⊓ (b ⊔ c) ≤ a -- case b.1
      calc
        a ⊓ (a ⊔ c) ⊓ (b ⊔ c) ≤ a ⊓ (a ⊔ c) := by apply inf_le_left
        _ ≤ a := by apply inf_le_left
      show a ⊓ (a ⊔ c) ⊓ (b ⊔ c) ≤ b ⊔ c -- case b.2
      apply inf_le_right

    _ = a ⊓ ((a ⊔ c) ⊓ (b ⊔ c)) := by apply inf_assoc
    _ = a ⊓ ((a ⊓ b) ⊔ c) := by
      calc
        a ⊓ ((a ⊔ c) ⊓ (b ⊔ c)) = ((a ⊔ c) ⊓ (b ⊔ c)) ⊓ a := by apply inf_comm
        _ = ((a ⊓ b) ⊔ c) ⊓ a := by
          apply eq_implies_meet_eq
          -- annoying rw step because my unions are back-to-front, e.g. (A∩B)∪C instead of C∪(A∩B) etc
          nth_rw 1 [sup_comm]
          nth_rw 2 [sup_comm]
          nth_rw 3 [sup_comm]
          apply Eq.symm (h c a b)
        _ = a ⊓ ((a ⊓ b) ⊔ c) := by apply inf_comm
    _ = ((a ⊓ b) ⊔ a) ⊓ ((a ⊓ b) ⊔ c) := by
      apply eq_implies_meet_eq
      show a = a ⊓ b ⊔ a
      rw[sup_comm]
      apply Eq.symm (absorb2 a b)
    _ = a ⊓ b ⊔ a ⊓ c := by apply Eq.symm (h (a ⊓ b) a c)

end


section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  calc
    0 = a + -a := by apply Eq.symm (add_neg_cancel a)
    _ ≤ b + -a := by apply add_le_add_right h (-a)
    _ = b - a := by apply Eq.symm (sub_eq_add_neg b a)

example (h: 0 ≤ b - a) : a ≤ b := by
  calc
    a = 0 + a := by apply Eq.symm (zero_add a)
    _ ≤ b - a + a := by
      apply add_le_add_right
      exact h
    _ = b := by apply sub_add_cancel

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h2: 0 ≤ b - a := by
    calc
      0 = a + -a := by apply Eq.symm (add_neg_cancel a)
      _ ≤ b + -a := by apply add_le_add_right h (-a)
      _ = b - a := by apply Eq.symm (sub_eq_add_neg b a)
  have h3: 0 ≤ b*c - a*c := by
    calc
      0 ≤ (b-a)*c := by apply mul_nonneg h2 h'
      _ =  b*c - a*c := by apply sub_mul
  calc
    a * c = 0 + a * c := by apply Eq.symm (zero_add (a * c))
    _ ≤ b*c - a*c + a*c := by apply add_le_add_right h3
    _ = b*c := by apply sub_add_cancel
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have zero_lq_2d : 0 ≤ dist x y*2:= by
    calc
      0 = dist x x := by apply Eq.symm (dist_self x)
    _ ≤ dist x y + dist y x := by apply dist_triangle
    _ = dist x y + dist x y := by
      apply add_left_cancel_iff.mpr
      apply dist_comm
    _ = 2*dist x y := by apply Eq.symm (two_mul (dist x y))
    _ = dist x y*2 := by apply mul_comm
  apply nonneg_of_mul_nonneg_left zero_lq_2d
  apply zero_lt_two
end
