import MIL.Common
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X] (a b c : X)

#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

-- Note the next three lines are not quoted, their purpose is to make sure those things don't get renamed while we're looking elsewhere.
#check EMetricSpace
#check PseudoMetricSpace
#check PseudoEMetricSpace

example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd))

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'

#check Continuous.add
#check continuous_pow
#check continuous_id

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
  apply Continuous.comp hf
  apply Continuous.add
  apply continuous_pow 2
  apply continuous_id

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

variable (r : ℝ)

example : Metric.ball a r = { b | dist b a < r } :=
  rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl

example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr

example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (Eventually.of_forall hus)

example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s := by
  rw [mem_closure_iff]
  intro o o_open a_in_o
  have : ∀ᶠ n in atTop, u n ∈ o := by
    apply hu
    apply IsOpen.mem_nhds o_open a_in_o
  have hOS : ∀ᶠ n in atTop, u n ∈ o ∩ s := by apply this.and (Eventually.of_forall hs)
  rcases hOS.exists with ⟨z, hz⟩
  use u z

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff

example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn hs' hfs

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_isMaxOn hs' hfs

example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ

#check IsCompact.isClosed


example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff

#check isClosed_le
#check eq_empty_or_nonempty

example {X : Type*} [MetricSpace X] [CompactSpace X]
      {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro eps eps_pos
  let φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
  let K : Set (X × X) := {p : X × X | eps ≤ φ p}
  rcases eq_empty_or_nonempty K with h|h
  use 1; constructor; apply zero_lt_one
  intro a b dist_lt_1
  by_contra dist_ge_eps
  push_neg at dist_ge_eps
  have : (a,b) ∈ K := by apply dist_ge_eps
  rw [h] at this
  contradiction
  have Kclosed : IsClosed K := by apply isClosed_le; apply continuous_const; continuity
  have Kcompact : IsCompact K := by apply IsClosed.isCompact Kclosed
  let f : X × X → ℝ := fun x ↦ dist x.1 x.2
  have : ContinuousOn f K := by apply Continuous.continuousOn; continuity
  rcases Kcompact.exists_isMinOn h this with ⟨⟨x0,x1⟩,x0x1_in_K, min_dist_on_K⟩
  use dist x0 x1
  constructor
   -- dist x0 x1 > 0 because dist f x0 f x1 ≥ eps > 0. Cannot find a lemma saying dist f x0 f x1 > 0 → dist x0 x1 > 0
  by_contra dist_eq_0; push_neg at dist_eq_0
  have x0_eq_x1 : x0 = x1 := by apply dist_eq_zero.mp; apply le_antisymm dist_eq_0 dist_nonneg
  have : φ (x0,x1) = 0 := by apply dist_eq_zero.mpr; simp; rw[x0_eq_x1]
  have : φ (x0,x1) > 0 := by
    calc
    φ (x0,x1) ≥ eps := by apply x0x1_in_K
    _ > 0 := by apply eps_pos
  linarith
  -- left to show: if dist a b < dist x0 x1, then (a,b) not in K
  intro a b dist_ab_lt_dist_x0_x1
  by_contra dist_fa_fb_ge_eps; push_neg at dist_fa_fb_ge_eps
  have : (a,b) ∈ K := by apply dist_fa_fb_ge_eps
  have : f (x0, x1) ≤ f (a, b) := by apply min_dist_on_K this
  linarith

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

open BigOperators

open Finset

#check tendsto_pow_atTop_nhds_zero_of_lt_one
#check Tendsto.mul
#check dist_le_range_sum_dist

theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by
    have : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n * 2) atTop (𝓝 0) := by
      rw[← zero_mul (2 : ℝ)]
      apply Tendsto.mul
      · apply tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 / (2 : ℝ)); norm_num; norm_num
      apply tendsto_const_nhds
    rcases Metric.tendsto_atTop.mp this ε ε_pos with ⟨N, hN⟩
    specialize hN N le_rfl
    use N
    rw [dist_zero_right] at hN
    rw [← abs_of_nonneg  (a := 1 / 2 ^ N * 2)]
    rw [Real.norm_eq_abs] at hN
    rw [← one_div_pow (2 : ℝ) N]
    apply hN
    apply mul_nonneg; positivity; apply zero_le_two
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by apply dist_comm
    _ ≤ ∑ i  ∈ range k, dist (u (N + i)) (u (N + (i + 1))) := by
      let u_shift_N := fun i ↦ u (N + i)
      apply dist_le_range_sum_dist u_shift_N
    _ ≤ ∑ i  ∈ range k, (1 / 2 : ℝ) ^ (N + i) := by
      gcongr with i i_in_fin_k
      apply hu
    _ = 1 / 2 ^ N * ∑ i  ∈ range k, (1 / 2 : ℝ) ^ i := by
      rw [Finset.mul_sum]
      congr with i
      rw [pow_add]
      rw [← one_div_pow (2 : ℝ) N]
    _ ≤ 1 / 2 ^ N * 2 := by
      rw [geom_sum_eq]
      gcongr; ring_nf; simp; simp
    _ < ε := by apply hN

open Metric

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n
  sorry
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by sorry
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x`
    belonging to all `f n`. For this, we construct inductively a sequence
    `F n = (c n, r n)` such that the closed ball `closedBall (c n) (r n)` is included
    in the previous ball and in `f n`, and such that `r n` is small enough to ensure
    that `c n` is a Cauchy sequence. Then `c n` converges to a limit which belongs
    to all the `f n`. -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by sorry
  have rB : ∀ n, r n ≤ B n := by sorry
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    sorry
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by sorry
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by sorry
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by sorry
  sorry
