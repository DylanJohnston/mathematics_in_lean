import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

#check le_of_max_le_left
#check le_of_max_le_right

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n n_ge_max
  calc
    |s n + t n - (a + b)|= |(s n - a) + (t n - b)| := by congr; ring
    _ ≤ |(s n - a)| + |(t n - b)| := by apply abs_add
    _ < ε/2 + ε/2 := by
      apply add_lt_add
      apply hs n
      apply le_of_max_le_left n_ge_max
      apply ht n
      apply le_of_max_le_right n_ge_max
    _ = ε := by norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro e epos
  have e_dvd_c_pos : 0 < e / |c| := by apply div_pos epos acpos
  rcases cs (e/|c|) e_dvd_c_pos with ⟨N, s_conv⟩
  use N
  intro n n_ge_N
  simp
  calc
  |c * s n - c * a| = |c * (s n - a)| := by congr; ring
  _ = |c| * |(s n - a)| := by apply abs_mul
  _ < |c| * (e / |c|) := by apply mul_lt_mul' le_rfl (s_conv n n_ge_N) (abs_nonneg _) acpos
  _ = e := by field_simp

-- for reference
-- def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
--   ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n n_ge_N
  apply lt_add_of_neg_add_lt_left
  rw [add_comm, ← sub_eq_add_neg]
  calc
  |s n| - |a| ≤ |s n - a| := by apply abs_sub_abs_le_abs_sub
  _ < 1 := by apply h n n_ge_N

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n n_ge_max_N0_N1
  have n_ge_N0 : n ≥ N₀ := by apply le_of_max_le_left n_ge_max_N0_N1
  have n_ge_N1 : n ≥ N₁ := by apply le_of_max_le_right n_ge_max_N0_N1
  calc
  |s n * t n - 0| = |s n * t n| := by congr; ring
  _ = |s n| * |t n| := by apply abs_mul (s n) (t n)
  _ = |s n| * |t n - 0| := by ring_nf
  _ < B * (ε/B) := by apply mul_lt_mul_of_nonneg (h₀ n n_ge_N0) (h₁ n n_ge_N1) (abs_nonneg s n) (abs_nonneg (t n - 0))
  _ = ε := by field_simp

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply abs_pos.mpr
    intro a_sub_b
    contrapose! abne
    linarith
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have N_ge_N0 : N ≥ Na := by apply le_max_left Na Nb
  have N_ge_N1 : N ≥ Nb := by apply le_max_right Na Nb
  have absa : |s N - a| < ε := by
    apply hNa N N_ge_N0
  have absb : |s N - b| < ε := by
    apply hNb N N_ge_N1
  have : |a - b| < |a - b| :=
  calc
    |a - b| = |a - b + (s N - s N)| := by congr; ring
    _ = |s N - b + (-(s N - a))| := by
      apply abs_eq_abs.mpr
      left
      ring
    _ ≤ |s N - b| + |-(s N - a)| := by convert abs_add_le (s N - b) (-(s N - a))
    _ = |s N - b| + |s N - a| := by
      apply add_left_cancel_iff.mpr
      apply abs_eq_abs.mpr
      right
      ring
    _ < ε + ε := by apply add_lt_add absb absa
    _ = |a - b| := by ring
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
