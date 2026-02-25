import MIL.Common
import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter Topology

def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := by apply subset_univ
  sets_of_superset := by {
    intro x y hxf x_sub_y
    simp at *
    apply subset_trans (b:=x) hxf x_sub_y
  }
  inter_sets :=  by {
    intro x y hxf hyf
    simp at *
    exact ⟨hxf,hyf⟩
  }

example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by {
      use 1
      intro b _
      trivial
    }
    sets_of_superset := by {
      intro x y hxf x_sub_y
      rcases hxf with ⟨m,hmbx⟩
      simp
      use m
      intro b m_le_b
      have bx : b ∈ x := by apply hmbx b m_le_b
      apply x_sub_y bx
    }
    inter_sets := by {
      intro x y hxf hyf
      simp at *
      rcases hxf with ⟨m,hm⟩
      rcases hyf with ⟨n,hn⟩
      use max m n
      intro b mmn_le_b
      rw [max_le_iff] at mmn_le_b
      constructor
      apply hm b; apply mmn_le_b.1
      apply hn b; apply mmn_le_b.2
    }
  }

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl

#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
    change map (g ∘ f) F ≤ H
    have hf2: map f F ≤ G := by apply hf
    have hg2 : map g G ≤ H := by apply hg
    rw [← Filter.map_map]
    calc
    map g (map f F) ≤ map g G := by
      apply map_mono; apply hf2
    _ ≤ H := by apply hg2

variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end

example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq

#check comap Prod.fst

#check le_inf_iff

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) := by
  simp [Tendsto, nhds_prod_eq]
  show map f atTop ≤ (comap Prod.fst (𝓝 x₀)) ⊓ (comap Prod.snd (𝓝 y₀)) ↔ map (Prod.fst ∘ f) atTop ≤ 𝓝 x₀ ∧ map (Prod.snd ∘ f) atTop ≤ 𝓝 y₀
  simp [Filter.map_le_iff_le_comap, comap_comap]

example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀

example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

#check Eventually.of_forall
#check Eventually.mono
#check Eventually.and

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  apply (hP.and (hQ.and hR)).mono
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h''
  exact h'' ⟨h, h'⟩

#check mem_closure_iff_clusterPt
#check le_principal_iff
#check neBot_of_le

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M := by
  rw [mem_closure_iff_clusterPt]
  change (𝓝 x ⊓ 𝓟 M).NeBot
  rw [Filter.inf_principal_neBot_iff]
  intro U U_nbhd_x
  have ht : ∀ᶠ (n : ℕ) in atTop, u n ∈ U := by apply hux U_nbhd_x
  have hUM : ∀ᶠ (n : ℕ) in atTop, u n ∈ U ∩ M := by apply Eventually.and (hux U_nbhd_x) huM
  rcases hUM.exists with ⟨n,n_in_U_cap_M⟩
  use u n
