import CGLProofDAG

/-!
# Two plateau bridge for the critical local polynomial

This is the literal integer part of the three piece reduction.  For `N ≥ 32`
we use `N₁ = floor (5N/6)` and `N₂ = ceil (10N/9)`.  The integer plateaus
`[6Nᵢ/5, 9Nᵢ/5]` cover the source block `(N,2N]`.  A point in the overlap is
assigned to the first plateau, so the two coefficient parts are disjoint.
The analytic local estimate is not asserted here; this module only proves the
finite support and exact sum identities needed to feed it.
-/

namespace GuthMaynardTwoPlateauSmoothingBridge

open scoped BigOperators
open CGLProofDAG

noncomputable section

def sourceBlock (N : ℕ) : Finset ℕ := Finset.Ioc N (2 * N)

def localN1 (N : ℕ) : ℕ := 5 * N / 6

def localN2 (N : ℕ) : ℕ := (10 * N + 8) / 9

def plateau (M : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (2 * M)).filter
    (fun n => 6 * M ≤ 5 * n ∧ 5 * n ≤ 9 * M)

def firstPart (a : ℕ → ℂ) (N n : ℕ) : ℂ :=
  if n ∈ sourceBlock N ∧ n ∈ plateau (localN1 N) then a n else 0

def secondPart (a : ℕ → ℂ) (N n : ℕ) : ℂ :=
  if n ∈ sourceBlock N ∧ n ∉ plateau (localN1 N) ∧
      n ∈ plateau (localN2 N) then a n else 0

theorem localN1_scale {N : ℕ} (hN : 32 ≤ N) :
    N / 2 ≤ localN1 N ∧ localN1 N ≤ 2 * N := by
  unfold localN1
  omega

theorem localN2_scale {N : ℕ} (hN : 32 ≤ N) :
    N / 2 ≤ localN2 N ∧ localN2 N ≤ 2 * N := by
  unfold localN2
  omega

theorem plateau_mem_iff {M n : ℕ} :
    n ∈ plateau M ↔ 6 * M ≤ 5 * n ∧ 5 * n ≤ 9 * M := by
  simp only [plateau, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨by omega, h⟩

theorem plateau_subset_localBlock {M : ℕ} (hM : 1 ≤ M) :
    plateau M ⊆ Finset.Ioc M (2 * M) := by
  intro n hn
  rw [plateau_mem_iff] at hn
  simp only [Finset.mem_Ioc]
  omega

theorem source_mem_plateau_union {N n : ℕ} (hN : 32 ≤ N)
    (hn : n ∈ sourceBlock N) :
    n ∈ plateau (localN1 N) ∨ n ∈ plateau (localN2 N) := by
  rw [plateau_mem_iff, plateau_mem_iff]
  simp only [sourceBlock, Finset.mem_Ioc] at hn
  unfold localN1 localN2
  omega

theorem firstPart_mem_localBlock {N n : ℕ} (hN : 32 ≤ N)
    {a : ℕ → ℂ} (hmem : firstPart a N n ≠ 0) :
    n ∈ Finset.Ioc (localN1 N) (2 * localN1 N) := by
  have hc : n ∈ sourceBlock N ∧ n ∈ plateau (localN1 N) := by
    by_contra h
    simp [firstPart, h] at hmem
  have hM : 1 ≤ localN1 N := by
    unfold localN1
    omega
  exact plateau_subset_localBlock hM hc.2

theorem secondPart_mem_localBlock {N n : ℕ} (hN : 32 ≤ N)
    {a : ℕ → ℂ} (hmem : secondPart a N n ≠ 0) :
    n ∈ Finset.Ioc (localN2 N) (2 * localN2 N) := by
  have hc : n ∈ sourceBlock N ∧ n ∉ plateau (localN1 N) ∧
      n ∈ plateau (localN2 N) := by
    by_contra h
    simp [secondPart, h] at hmem
  have hM : 1 ≤ localN2 N := by
    unfold localN2
    omega
  exact plateau_subset_localBlock hM hc.2.2

theorem source_split_pointwise {N n : ℕ} (hN : 32 ≤ N)
    (hn : n ∈ sourceBlock N) (a : ℕ → ℂ) :
    a n = firstPart a N n + secondPart a N n := by
  have hcover := source_mem_plateau_union hN hn
  simp only [firstPart, secondPart]
  by_cases hp1 : n ∈ plateau (localN1 N)
  · simp [hn, hp1]
  · rcases hcover with hp1' | hp2
    · exact (hp1 hp1').elim
    · simp [hn, hp1, hp2]

theorem source_sum_split {N : ℕ} (hN : 32 ≤ N) (a : ℕ → ℂ) :
    (∑ n ∈ sourceBlock N, a n) =
      (∑ n ∈ sourceBlock N, firstPart a N n) +
        (∑ n ∈ sourceBlock N, secondPart a N n) := by
  calc
    (∑ n ∈ sourceBlock N, a n) =
        (∑ n ∈ sourceBlock N, (firstPart a N n + secondPart a N n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact source_split_pointwise hN hn a
    _ = (∑ n ∈ sourceBlock N, firstPart a N n) +
          (∑ n ∈ sourceBlock N, secondPart a N n) := by
      rw [Finset.sum_add_distrib]

theorem first_second_disjoint {N n : ℕ} :
    ∀ {a : ℕ → ℂ}, firstPart a N n ≠ 0 → secondPart a N n = 0 := by
  intro a hfirst
  have hc : n ∈ sourceBlock N ∧ n ∈ plateau (localN1 N) := by
    by_contra h
    simp [firstPart, h] at hfirst
  simp [secondPart, hc.1, hc.2]

theorem largeValue_two_part_split {V : ℝ} {z₁ z₂ : ℂ}
    (hV : 0 < V) (hlarge : V ≤ ‖z₁ + z₂‖) :
    V / 2 ≤ ‖z₁‖ ∨ V / 2 ≤ ‖z₂‖ := by
  by_contra h
  push_neg at h
  have htriangle : ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le _ _
  linarith

theorem localN_lt_twoT {N : ℕ} {T : ℝ} (hN : 32 ≤ N)
    (hNT : (N : ℝ) < T) :
    (localN1 N : ℝ) < 2 * T ∧ (localN2 N : ℝ) < 2 * T := by
  have hN1 := localN1_scale hN
  have hN2 := localN2_scale hN
  have hN1' : (localN1 N : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN1.2
  have hN2' : (localN2 N : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN2.2
  constructor <;> nlinarith

def PlateauWeight (w : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, (6 / 5 : ℝ) ≤ x → x ≤ 9 / 5 → w x = 1

theorem firstPart_weight_eq {N n : ℕ} {a : ℕ → ℂ} {w : ℝ → ℝ}
    (hN : 32 ≤ N) (hw : PlateauWeight w) (hmem : firstPart a N n ≠ 0) :
    ((w ((n : ℝ) / (localN1 N : ℝ)) : ℂ) * firstPart a N n) =
      firstPart a N n := by
  have hc : n ∈ sourceBlock N ∧ n ∈ plateau (localN1 N) := by
    by_contra h
    simp [firstPart, h] at hmem
  have hp := (plateau_mem_iff.mp hc.2)
  have hM : 0 < (localN1 N : ℝ) := by
    have hs := localN1_scale hN
    have hhalf : 1 ≤ N / 2 := by omega
    have : 1 ≤ localN1 N := hhalf.trans hs.1
    exact_mod_cast this
  have hlow : (6 / 5 : ℝ) ≤ (n : ℝ) / (localN1 N : ℝ) := by
    apply (le_div_iff₀ hM).2
    have h := (show (6 : ℝ) * localN1 N ≤ 5 * n by exact_mod_cast hp.1)
    nlinarith
  have hhigh : (n : ℝ) / (localN1 N : ℝ) ≤ 9 / 5 := by
    apply (div_le_iff₀ hM).2
    have h := (show (5 : ℝ) * n ≤ 9 * localN1 N by exact_mod_cast hp.2)
    nlinarith
  rw [hw _ hlow hhigh]
  simp

theorem secondPart_weight_eq {N n : ℕ} {a : ℕ → ℂ} {w : ℝ → ℝ}
    (hN : 32 ≤ N) (hw : PlateauWeight w) (hmem : secondPart a N n ≠ 0) :
    ((w ((n : ℝ) / (localN2 N : ℝ)) : ℂ) * secondPart a N n) =
      secondPart a N n := by
  have hc : n ∈ sourceBlock N ∧ n ∉ plateau (localN1 N) ∧
      n ∈ plateau (localN2 N) := by
    by_contra h
    simp [secondPart, h] at hmem
  have hp := (plateau_mem_iff.mp hc.2.2)
  have hM : 0 < (localN2 N : ℝ) := by
    have hs := localN2_scale hN
    have hhalf : 1 ≤ N / 2 := by omega
    have : 1 ≤ localN2 N := hhalf.trans hs.1
    exact_mod_cast this
  have hlow : (6 / 5 : ℝ) ≤ (n : ℝ) / (localN2 N : ℝ) := by
    apply (le_div_iff₀ hM).2
    have h := (show (6 : ℝ) * localN2 N ≤ 5 * n by exact_mod_cast hp.1)
    nlinarith
  have hhigh : (n : ℝ) / (localN2 N : ℝ) ≤ 9 / 5 := by
    apply (div_le_iff₀ hM).2
    have h := (show (5 : ℝ) * n ≤ 9 * localN2 N by exact_mod_cast hp.2)
    nlinarith
  rw [hw _ hlow hhigh]
  simp

theorem source_weighted_two_part_split {N : ℕ} (hN : 32 ≤ N)
    {a : ℕ → ℂ} {w : ℝ → ℝ} (hw : PlateauWeight w) (t : ℝ) :
    (∑ n ∈ sourceBlock N,
      a n * Complex.exp (Complex.I * (t * Real.log n))) =
      (∑ n ∈ sourceBlock N,
        (w ((n : ℝ) / (localN1 N : ℝ)) : ℂ) * firstPart a N n *
          Complex.exp (Complex.I * (t * Real.log n))) +
      (∑ n ∈ sourceBlock N,
        (w ((n : ℝ) / (localN2 N : ℝ)) : ℂ) * secondPart a N n *
          Complex.exp (Complex.I * (t * Real.log n))) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h1 : firstPart a N n = 0
  · have h2 : secondPart a N n = a n := by
      have hs := source_split_pointwise hN hn a
      rw [h1, zero_add] at hs
      exact hs.symm
    by_cases h2zero : secondPart a N n = 0
    · have ha0 : a n = 0 := h2.symm.trans h2zero
      simp [h1, h2zero, ha0]
    · have hw2 := secondPart_weight_eq hN hw h2zero
      have hw2a :
          (w ((n : ℝ) / (localN2 N : ℝ)) : ℂ) * a n = a n := by
        simpa [h2] using hw2
      simp only [h1, zero_mul, zero_add]
      rw [h2, hw2a]
      ring
  · have h2 : secondPart a N n = 0 := first_second_disjoint h1
    have hw1 := firstPart_weight_eq hN hw h1
    have hs := source_split_pointwise hN hn a
    have ha : a n = firstPart a N n := by simpa [h2] using hs
    simp only [h2, mul_zero, add_zero]
    have he := congrArg
      (fun z : ℂ => z * Complex.exp (Complex.I * (t * Real.log n))) hw1.symm
    simpa [ha] using he

end
end GuthMaynardTwoPlateauSmoothingBridge

#print axioms GuthMaynardTwoPlateauSmoothingBridge.source_mem_plateau_union
#print axioms GuthMaynardTwoPlateauSmoothingBridge.source_split_pointwise
#print axioms GuthMaynardTwoPlateauSmoothingBridge.source_sum_split
