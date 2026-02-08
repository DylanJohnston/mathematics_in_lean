import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

#check Nat.factorial_pos
#check Nat.dvd_factorial
#check Nat.dvd_sub'

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial n + 1 := by
    simp
    apply Nat.succ_le_of_lt (Nat.factorial_pos n)
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial n := by
    apply Nat.dvd_factorial (Nat.Prime.pos pp) ple
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this; simp
  show False
  rw [Nat.prime_def_lt] at pp
  rcases pp with ⟨p_ge_2,idc⟩
  rw [Nat.dvd_one] at this
  linarith


open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto

end

#check Finset.dvd_prod_of_mem
#check Nat.Prime.eq_one_or_self_of_dvd

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i ∈ s, i :=
  Finset.dvd_prod_of_mem _ h

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  convert Nat.Prime.eq_one_or_self_of_dvd prime_q p h
  constructor
  intro p_eq_q; right; assumption
  rintro (pe1|a)
  have : p ≠ 1 := by apply Nat.Prime.ne_one prime_p
  contradiction
  exact a

theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n ∈ s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
  rcases h₁ with p_dvd_a | p_prod
  left
  have p_eq_a : p = a := by
    apply _root_.Nat.Prime.eq_of_dvd_of_prime prime_p h₀.1 p_dvd_a
  exact p_eq_a
  right
  exact ih h₀.2 p_prod

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i ∈ s', i) + 1 := by
    simp
    apply Nat.succ_le_of_lt
    apply Finset.prod_pos
    intro i
    rw[mem_s']
    apply Nat.Prime.pos
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i ∈ s', i := by
    apply Finset.dvd_prod_of_mem
    rwa [mem_s']
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this
    simp
  show False
  have : p =1 := by apply Nat.eq_one_of_dvd_one this
  have : p ≠ 1 := by apply Nat.Prime.ne_one pp
  contradiction

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

#check Nat.div_dvd_of_dvd
#check Nat.div_lt_self

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  apply Nat.div_dvd_of_dvd h₀
  have n_pos : 0 < n := by
    calc
    0 < 2 := by apply zero_lt_two
    _ ≤ m := by apply h₁
    _ < n := by apply h₂
  have m_gt_1: 1 < m := by
    calc
    1 < 2 := by apply one_lt_two
    _ ≤ m := by apply h₁
  apply Nat.div_lt_self n_pos m_gt_1

theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  . rcases em (Nat.Prime m) with h|h
    use m
    rcases (ih m mltn h1 h) with ⟨q, ⟨q_prime,q_dvd_m,q_mod_4_eq_3⟩⟩
    use q
    constructor; apply q_prime
    constructor
    apply dvd_trans q_dvd_m mdvdn
    apply q_mod_4_eq_3
  . let aux_hypoth := aux mdvdn mge2 mltn
    rcases em (Nat.Prime (n / m)) with ndmp|ndmnp
    use n/m
    exact ⟨ndmp, aux_hypoth.1, h1⟩
    rcases (ih (n/m) aux_hypoth.2 h1 ndmnp) with ⟨q, ⟨q_prime,q_dvd_ndm,q_mod_4_eq_3⟩⟩
    use q
    constructor
    apply q_prime
    constructor
    apply dvd_trans q_dvd_ndm aux_hypoth.1
    apply q_mod_4_eq_3

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

#check Nat.dvd_add_iff_left
#check Nat.dvd_sub'

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i ∈ erase s 3, i) + 3) % 4 = 3 := by
    simp
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    rw [← hs p]
    exact ⟨pp,p4eq⟩
  have pne3 : p ≠ 3 := by
    intro peq3
    have : p ∣ (4 * ∏ i ∈ erase s 3, i + 3) ∧ p ∣ 3 := by exact ⟨pdvd, dvd_of_eq peq3⟩
    have : p ∣ (4 * ∏ i ∈ erase s 3, i) := by apply Nat.dvd_sub this.1 this.2
    rcases (Nat.Prime.dvd_mul pp).mp this with pd4 | pdprod
    have : 3 ∣ 4 := by
      rw[peq3] at pd4; assumption
    contradiction
    have : p ∈ s.erase 3 := by
      apply mem_of_dvd_prod_primes pp
      simp
      intro n n_neq_3 ns
      rw [← hs] at ns
      apply ns.1
      apply pdprod
    simp at this
    rcases this with ⟨pne3,idc⟩
    contradiction
  have : p ∣ 4 * ∏ i ∈ erase s 3, i := by
    have : p ∈ erase s 3 := by
      simp
      exact ⟨pne3, ps⟩
    apply Nat.dvd_mul_left_of_dvd
    apply Finset.dvd_prod_of_mem
    apply this
  have : p ∣ 3 := by
    convert Nat.dvd_sub pdvd this
    simp
  have : p = 3 := by
    apply Nat.Prime.eq_of_dvd_of_prime
    apply pp
    apply Nat.prime_three
    apply this
  contradiction
