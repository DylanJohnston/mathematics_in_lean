import Mathlib.Tactic

namespace MyListSpace

inductive List (α : Type*) where
  | nil  : List α
  | cons : α → List α → List α

end MyListSpace

namespace MyListSpace2

def append {α : Type*} : List α → List α → List α
  | [],      bs => bs
  | a :: as, bs => a :: (append as bs)

def map {α β : Type*} (f : α → β) : List α → List β
  | []      => []
  | a :: as => f a :: map f as

#eval append [1, 2, 3] [4, 5, 6]
/-  append 1 ::[2,3] [4,5,6] => 1 :: append([2,3] [4,5,6])
    etc  until
    1 :: 2 :: 3 :: [4,5,6]  -/
#eval map (fun n => n^2) [1, 2, 3, 4, 5]

theorem nil_append {α : Type*} (as : List α) : append [] as = as := rfl

theorem cons_append {α : Type*} (a : α) (as : List α) (bs : List α) :
    append (a :: as) bs = a :: (append as bs) := rfl

theorem map_nil {α β : Type*} (f : α → β) : map f [] = [] := rfl

theorem map_cons {α β : Type*} (f : α → β) (a : α) (as : List α) :
    map f (a :: as) = f a :: map f as := rfl

end MyListSpace2

namespace MyListSpace3

variable {α β γ : Type*}
variable (as bs cs : List α)
variable (a b c : α)

open List

theorem append_nil : ∀ as : List α, as ++ [] = as
  | [] => rfl
  | a :: as => by rw [cons_append, append_nil as]

theorem map_map (f : α → β) (g : β → γ) :
    ∀ as : List α, map g (map f as) = map (g ∘ f) as
  | [] => rfl
  | a :: as => by rw [map_cons, map_cons, map_cons, map_map f g as]; rfl

theorem append_nil' : as ++ [] = as := by
  induction' as with a as ih
  . rfl
  . rw [cons_append, ih]

theorem map_map' (f : α → β) (g : β → γ) (as : List α) :
    map g (map f as) = map (g ∘ f) as := by
  induction' as with a as ih
  . rfl
  . simp [map, ih]

def reverse : List α → List α
  | [] => []
  | a :: as => List.append (reverse as) (a::[])

#eval reverse [1, 2, 3, 4, 5]

#check cons_append
#check append_assoc

theorem reverse_append (as bs : List α) : reverse (as ++ bs) = reverse bs ++ reverse as := by
  induction' as with a as ih
  simp [append_nil]; rfl
  simp [cons_append, reverse, ih]

theorem reverse_reverse (as : List α) : reverse (reverse as) = as := by
  induction' as with a as ih
  rfl
  have h (l : List α) (x : α): reverse (l ++ [a]) = [a] ++ reverse l := by
    induction' l with y l induct
    rfl
    simp [reverse]
    rw[induct]; rfl
  simp [reverse]
  rw [h (reverse as) a]
  rw [ih]; rfl

end MyListSpace3

inductive BinTree where
  | empty : BinTree
  | node  : BinTree → BinTree → BinTree

namespace BinTree

def size : BinTree → ℕ
  | empty    => 0
  | node l r => size l + size r + 1

def depth : BinTree → ℕ
  | empty    => 0
  | node l r => max (depth l) (depth r) + 1

theorem size_le : ∀ t : BinTree, size t ≤ 2^depth t - 1
  | empty    => Nat.zero_le _
  | node l r => by
    simp only [depth, size]
    calc l.size + r.size + 1
      ≤ (2^l.depth - 1) + (2^r.depth - 1) + 1 := by
          gcongr <;> apply size_le
    _ ≤ (2 ^ max l.depth r.depth - 1) + (2 ^ max l.depth r.depth - 1) + 1 := by
          gcongr <;> simp
    _ ≤ 2 ^ (max l.depth r.depth + 1) - 1 := by
          have : 0 < 2 ^ max l.depth r.depth := by simp
          omega

theorem depth_le_size : ∀ t : BinTree, depth t ≤ size t := by
  intro t
  induction' t with l r l_dls r_dls
  apply Nat.zero_le
  simp [depth, size]
  constructor
  apply le_add_right l_dls
  apply le_add_left r_dls

def flip : BinTree → BinTree
  | empty => empty
  | node l r => node (flip r) (flip l)

example: flip  (node (node empty (node empty empty)) (node empty empty)) =
    node (node empty empty) (node (node empty empty) empty) := rfl

theorem size_flip : ∀ t, size (flip t) = size t := by
  intro t
  induction' t with l r ihl ihr
  rfl
  simp [flip, size]
  rw[ihl, ihr]; ring

end BinTree

inductive PropForm : Type where
  | var (n : ℕ)           : PropForm
  | fls                   : PropForm
  | conj (A B : PropForm) : PropForm
  | disj (A B : PropForm) : PropForm
  | impl (A B : PropForm) : PropForm
namespace PropForm

def eval : PropForm → (ℕ → Bool) → Bool
  | var n,    v => v n
  | fls,      _ => false
  | conj A B, v => A.eval v && B.eval v
  | disj A B, v => A.eval v || B.eval v
  | impl A B, v => ! A.eval v || B.eval v

def vars : PropForm → Finset ℕ
  | var n    => {n}
  | fls      => ∅
  | conj A B => A.vars ∪ B.vars
  | disj A B => A.vars ∪ B.vars
  | impl A B => A.vars ∪ B.vars

theorem eval_eq_eval : ∀ (A : PropForm) (v1 v2 : ℕ → Bool),
    (∀ n ∈ A.vars, v1 n = v2 n) → A.eval v1 = A.eval v2
  | var n, v1, v2, h    => by simp_all [vars, eval, h]
  | fls, v1, v2, h      => by simp_all [eval]
  | conj A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]
  | disj A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]
  | impl A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]

theorem eval_eq_eval' (A : PropForm) (v1 v2 : ℕ → Bool) (h : ∀ n ∈ A.vars, v1 n = v2 n) :
    A.eval v1 = A.eval v2 := by
  cases A <;> simp_all [eval, vars, fun A => eval_eq_eval' A v1 v2]

def subst : PropForm → ℕ → PropForm → PropForm
  | var n,    m, C => if n = m then C else var n
  | fls,      _, _ => fls
  | conj A B, m, C => conj (A.subst m C) (B.subst m C)
  | disj A B, m, C => disj (A.subst m C) (B.subst m C)
  | impl A B, m, C => impl (A.subst m C) (B.subst m C)

theorem subst_eq_of_not_mem_vars :
    ∀ (A : PropForm) (n : ℕ) (C : PropForm), n ∉ A.vars → A.subst n C = A := by
    intro A n C
    induction' A with x A B Aconjh Bconjh A B Adisjh Bdisjh A B Aimph Bimph
    --case var (I am seeing how induction with ∣s is prehaps more organised since I want to label my cases anyway)
    simp [vars, subst];
    intro p q
    push_neg at p; symm at p; contradiction
    --case fls
    simp [vars, subst]
    --case conj
    simp [vars, subst, Aconjh, Bconjh]
    intro nnA nnB
    exact ⟨(Aconjh nnA),Bconjh nnB⟩
    --case disj
    simp [vars, subst, Adisjh, Bdisjh]
    intro nnA nnB
    exact ⟨(Adisjh nnA),Bdisjh nnB⟩
    --case imp
    simp [vars, subst, Aimph, Bimph]
    intro nnA nnB
    exact ⟨(Aimph nnA),Bimph nnB⟩

theorem subst_eval_eq : ∀ (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool),
  (A.subst n C).eval v = A.eval (fun m => if m = n then C.eval v else v m)
  | var A, n, C, v => by
    simp [subst, eval]
    by_cases h : A = n
    simp [h]
    simp [h]
    rfl
  | fls, n, C, v => by
    simp [subst, eval]
  | (impl A B), n, C, v => by
    simp [subst, eval, subst_eval_eq]
  | (disj A B), n, C, v => by
    simp [subst, eval, subst_eval_eq]
  | (conj A B), n, C, v => by
    simp [subst, eval, subst_eval_eq]

end PropForm
