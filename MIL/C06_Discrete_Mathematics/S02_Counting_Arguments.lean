import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (s t : Finset α) (f : α → β)

example : #(s ×ˢ t) = #s * #t := by rw [card_product]
example : #(s ×ˢ t) = #s * #t := by simp

example : #(s ∪ t) = #s + #t - #(s ∩ t) := by rw [card_union]

example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by rw [card_union_of_disjoint h]
example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by simp [h]

example (h : Function.Injective f) : #(s.image f) = #s := by rw [card_image_of_injective _ h]

example (h : Set.InjOn f s) : #(s.image f) = #s := by rw [card_image_of_injOn h]

section
open Fintype

variable {α β : Type*} [Fintype α] [Fintype β]

example : card (α × β) = card α * card β := by simp

example : card (α ⊕ β) = card α + card β := by simp

example (n : ℕ) : card (Fin n → α) = (card α)^n := by simp

variable {n : ℕ} {γ : Fin n → Type*} [∀ i, Fintype (γ i)]

example : card ((i : Fin n) → γ i) = ∏ i, card (γ i) := by simp

example : card (Σ i, γ i) = ∑ i, card (γ i) := by simp

end

#check Disjoint

example (m n : ℕ) (h : m ≥ n) :
    card (range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  rw [card_union_of_disjoint, card_range, card_image_of_injective, card_range]; omega
  . apply add_right_injective
  . simp [disjoint_iff_ne]; omega

def triangle (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range (n+1) ×ˢ range (n+1) | p.1 < p.2}

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n = (range (n+1)).biUnion (fun j ↦ (range j).image (., j)) := by
    ext p
    simp only [triangle, mem_filter, mem_product, mem_range, mem_biUnion, mem_image]
    constructor
    . rintro ⟨⟨hp1, hp2⟩, hp3⟩
      use p.2, hp2, p.1, hp3
    . rintro ⟨p1, hp1, p2, hp2, rfl⟩
      omega
  rw [this, card_biUnion]; swap
  · -- take care of disjointness first
    intro x _ y _ xney
    simp [disjoint_iff_ne, xney]
  -- continue the calculation
  transitivity (∑ i ∈ range (n + 1), i)
  · congr; ext i
    rw [card_image_of_injective, card_range]
    intros i1 i2; simp
  rw [sum_range_id]; rfl

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n ≃ Σ i : Fin (n + 1), Fin i.val :=
    { toFun := by
        rintro ⟨⟨i, j⟩, hp⟩
        simp [triangle] at hp
        exact ⟨⟨j, hp.1.2⟩, ⟨i, hp.2⟩⟩
      invFun := by
        rintro ⟨i, j⟩
        use ⟨j, i⟩
        simp [triangle]
        exact j.isLt.trans i.isLt
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [←Fintype.card_coe]
  trans; apply (Fintype.card_congr this)
  rw [Fintype.card_sigma, sum_fin_eq_sum_range]
  convert Finset.sum_range_id (n + 1)
  simp_all

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  apply Nat.eq_div_of_mul_eq_right (by norm_num)
  let turn (p : ℕ × ℕ) : ℕ × ℕ := (n - 1 - p.1, n - p.2)
  calc 2 * #(triangle n)
      = #(triangle n) + #(triangle n) := by omega
    _ = #(triangle n) + #(triangle n |>.image turn) := by
          apply congr; rfl
          symm
          apply card_image_of_injOn
          unfold turn triangle
          intro ⟨x1,x2⟩ x_in_t ⟨y1,y2⟩ y_in_t
          simp_all
          omega
    _ = #(range n ×ˢ range (n + 1)) := by
          rw [← card_union_of_disjoint]
          simp only [triangle, turn]
          sorry
          /- completely stuck on the above so read solutions.
             Idea: start with congr to remove #, ext x, then
             simp [triangle] and rcases and omega it.

             I completely missed the idea to use congr -/
          apply disjoint_iff_ne.mpr
          intro ⟨x1,x2⟩ x_in_t ⟨y1,y2⟩ y_in_t
          simp_all [triangle, turn]
          rcases y_in_t with ⟨a,b,h⟩
          omega
    _ = (n + 1) * n := by
          simp; ring

def triangle' (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range n ×ˢ range n | p.1 ≤ p.2}

example (n : ℕ) : #(triangle' n) = #(triangle n) := by
  have this : (triangle n).image (fun (x,y) ↦ (x,y-1)) = (triangle' n) := by
    sorry
    /- I'll just assume this fact.
       My initial thoughts are to use ext x, simp (with triangle), omega, etc
       Solution confirms this is along the right lines -/
  calc
    #(triangle' n) = #((triangle n).image (fun (x,y) ↦ (x,y-1))) := by
      congr
      apply this.symm
    _ = #(triangle n) := by
      apply card_image_of_injOn
      intro ⟨x1,x2⟩ x_in_t ⟨y1,y2⟩ y_in_t fx_fy
      simp [triangle] at *
      have y2_gt_0 : y2 > 0 := by
        calc
        0 ≤ y1 := by apply Nat.zero_le y1
        _ < y2 := by apply y_in_t.2
      have y2_ge_1 : y2 ≥ 1 := by exact y2_gt_0
      have x2_gt_0 : x2 > 0 := by
        calc
        0 ≤ x1 := by apply Nat.zero_le x1
        _ < x2 := by apply x_in_t.2
      have x2_ge_1 : x2 ≥ 1 := by exact x2_gt_0
      omega

section
open Classical
variable (s t : Finset Nat) (a b : Nat)

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ #{b ∈ t | r a b})
    (h_right : ∀ b ∈ t, #{a ∈ s | r a b} ≤ 1) :
    3 * #(s) ≤ #(t) := by
  calc 3 * #(s)
      = ∑ a ∈ s, 3                               := by simp [sum_const_nat, mul_comm]
    _ ≤ ∑ a ∈ s, #({b ∈ t | r a b})              := sum_le_sum h_left
    _ = ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by simp
    _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := sum_comm
    _ = ∑ b ∈ t, #({a ∈ s | r a b})              := by simp
    _ ≤ ∑ b ∈ t, 1                               := sum_le_sum h_right
    _ ≤ #(t)                                     := by simp

example (m k : ℕ) (h : m ≠ k) (h' : m / 2 = k / 2) : m = k + 1 ∨ k = m + 1 := by omega

example {n : ℕ} (A : Finset ℕ)
    (hA : #(A) = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  have : ∃ t ∈ range n, 1 < #({u ∈ A | u / 2 = t}) := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · intro a a_in_A
      have : a ∈ range (2 * n) := by
        apply hA' a_in_A
      simp at this; simp
      omega
    · simp_all
  rcases this with ⟨t, ht, ht'⟩
  simp only [one_lt_card, mem_filter] at ht'
  rcases ht' with ⟨a, ⟨ha,ja⟩,b,⟨hb,jb⟩,anb⟩
  use a
  constructor; apply ha
  use b
  constructor; apply hb
  have : a = b + 1 ∨ b = a + 1 := by omega
  rcases this with h | h
  <;>
  simp [h, Nat.coprime_comm, Nat.coprime_add_iff_right]
  /- Above three lines came from refactoring below after
    noticing the logic was just repeated-/
  -- rcases this with alb | bla
  -- rw[alb]
  -- rw [Nat.coprime_comm]
  -- rw [Nat.coprime_add_iff_right]
  -- simp
  -- simp
  -- rw[bla]
  -- rw [Nat.coprime_add_iff_right]
  -- simp
  -- simp
