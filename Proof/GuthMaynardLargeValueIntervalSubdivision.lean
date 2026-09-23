import CGLProofDAG

/-!
# Finite interval subdivision for the Guth--Maynard local route

The proof of Theorem 1.1 applies a Proposition 3.1 estimate at the local
scale `L = N^(6/5)`.  When the ambient interval has length `T > L`, its
large-value set is split into finite fibers of the exact floor index
`⌊t / L⌋₊`.  Every fiber is left-closed and right-open at the local scale;
the ambient hypothesis `t ≤ T` supplies the clipped endpoint for the final
fiber.  Thus boundary points are assigned once, including a point at `T`.

After translating a fiber by `jL`, the Dirichlet polynomial is preserved by
the coefficient phase `exp (i jL log n)`.  This file proves the deterministic
finite partition and translation facts.  It assumes a local large-value bound
uniform in the coefficient sequence, and does not assume the global
Guth--Maynard theorem or claim Proposition 3.1 itself.
-/

namespace GuthMaynardLargeValueIntervalSubdivision

open scoped BigOperators
open CGLProofDAG

noncomputable section

set_option maxHeartbeats 600000
set_option linter.unusedVariables false

/-- Index of the left-closed, right-open interval of width `L` containing `t`.
The final endpoint is retained by the ambient `t ≤ T` condition. -/
def subdivisionIndex (L t : ℝ) : ℕ := ⌊t / L⌋₊

/-- The exact fiber of `W` assigned to interval index `j`. -/
def subdivisionFiber (W : Finset ℝ) (L : ℝ) (j : ℕ) : Finset ℝ :=
  W.filter (fun t => subdivisionIndex L t = j)

/-- The translated fiber, with its left endpoint moved to zero. -/
def translatedSubdivisionFiber
    (W : Finset ℝ) (L : ℝ) (j : ℕ) : Finset ℝ :=
  (subdivisionFiber W L j).image (fun t => t - (j : ℝ) * L)

/-- Coefficients after translating the ordinate forward by `c`. -/
def forwardTranslatedCoefficient (b : ℕ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  b n * Complex.exp (((c * Real.log n : ℝ) : ℂ) * Complex.I)

theorem norm_forwardTranslatedCoefficient
    (b : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    ‖forwardTranslatedCoefficient b c n‖ = ‖b n‖ := by
  unfold forwardTranslatedCoefficient
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Exact phase translation: `D_b(c+u) = D_{b_c}(u)`. -/
theorem dirichletPolynomial_forwardTranslatedCoefficient
    (b : ℕ → ℂ) (N : ℕ) (c u : ℝ) :
    dirichletPolynomial (forwardTranslatedCoefficient b c) N u =
      dirichletPolynomial b N (u + c) := by
  unfold dirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  unfold forwardTranslatedCoefficient
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem oneSeparated_translatedSubdivisionFiber
    {W : Finset ℝ} (hsep : OneSeparated W)
    (L : ℝ) (j : ℕ) :
    OneSeparated (translatedSubdivisionFiber W L j) := by
  intro u hu v hv huv
  change u ∈ (subdivisionFiber W L j).image
      (fun t => t - (j : ℝ) * L) at hu
  change v ∈ (subdivisionFiber W L j).image
      (fun t => t - (j : ℝ) * L) at hv
  rw [Finset.mem_image] at hu hv
  obtain ⟨t, ht, rfl⟩ := hu
  obtain ⟨s, hs, rfl⟩ := hv
  have hts : t ≠ s := by
    intro h
    apply huv
    rw [h]
  have htW : t ∈ W := (Finset.mem_filter.mp ht).1
  have hsW : s ∈ W := (Finset.mem_filter.mp hs).1
  have heq : (t - (j : ℝ) * L) - (s - (j : ℝ) * L) = t - s := by
    ring
  rw [heq]
  exact hsep t htW s hsW hts

theorem card_translatedSubdivisionFiber
    (W : Finset ℝ) (L : ℝ) (j : ℕ) :
    (translatedSubdivisionFiber W L j).card =
      (subdivisionFiber W L j).card := by
  unfold translatedSubdivisionFiber
  apply Finset.card_image_iff.mpr
  intro t ht s hs hts
  linarith

theorem subdivisionFiber_mem_interval
    {W : Finset ℝ} {T L : ℝ} (hL : 0 < L) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    {j : ℕ} (hj : j ∈ Finset.range (⌊T / L⌋₊ + 1))
    {t : ℝ} (ht : t ∈ subdivisionFiber W L j) :
    (j : ℝ) * L ≤ t ∧ t < ((j : ℝ) + 1) * L := by
  have htW : t ∈ W := (Finset.mem_filter.mp ht).1
  have hidx : subdivisionIndex L t = j := (Finset.mem_filter.mp ht).2
  have ht0 : 0 ≤ t := (hheight t htW).1
  have htl : 0 ≤ t / L := div_nonneg ht0 hL.le
  have hfloor_le : (j : ℝ) ≤ t / L := by
    rw [← hidx]
    simpa [subdivisionIndex] using (Nat.floor_le htl)
  have hfloor_lt : t / L < (j : ℝ) + 1 := by
    have h : t / L < (subdivisionIndex L t : ℝ) + 1 := by
      simpa [subdivisionIndex] using (Nat.lt_floor_add_one (t / L))
    rw [hidx] at h
    exact h
  constructor
  · exact (le_div_iff₀ hL).mp hfloor_le
  · exact (div_lt_iff₀ hL).mp hfloor_lt

theorem translatedSubdivisionFiber_mem_local_interval
    {W : Finset ℝ} {T L : ℝ} (hL : 0 < L) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    {j : ℕ} (hj : j ∈ Finset.range (⌊T / L⌋₊ + 1))
    {u : ℝ} (hu : u ∈ translatedSubdivisionFiber W L j) :
    0 ≤ u ∧ u ≤ L := by
  change u ∈ (subdivisionFiber W L j).image
      (fun t => t - (j : ℝ) * L) at hu
  rw [Finset.mem_image] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  obtain ⟨hlo, hhi⟩ := subdivisionFiber_mem_interval hL hT hheight hj ht
  constructor <;> linarith

theorem subdivisionIndex_mem_range
    {W : Finset ℝ} {T L : ℝ} (hL : 0 < L) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    {t : ℝ} (ht : t ∈ W) :
    subdivisionIndex L t ∈ Finset.range (⌊T / L⌋₊ + 1) := by
  apply Finset.mem_range.mpr
  have ht0 : 0 ≤ t := (hheight t ht).1
  have hratio : t / L ≤ T / L :=
    div_le_div_of_nonneg_right (hheight t ht).2 hL.le
  have hfloor : subdivisionIndex L t ≤ ⌊T / L⌋₊ := by
    unfold subdivisionIndex
    simpa using (Nat.floor_mono hratio)
  exact Nat.lt_succ_of_le hfloor

/-- Exact finite cardinal partition.  Fibers are disjoint because the floor
index is a function, and no point is lost because all indices lie in range. -/
theorem card_eq_sum_subdivisionFiber
    {W : Finset ℝ} {T L : ℝ} (hL : 0 < L) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    W.card =
      ∑ j ∈ Finset.range (⌊T / L⌋₊ + 1),
        (subdivisionFiber W L j).card := by
  let J := Finset.range (⌊T / L⌋₊ + 1)
  have hmaps : ∀ t ∈ W, subdivisionIndex L t ∈ J := by
    intro t ht
    exact subdivisionIndex_mem_range hL hT hheight ht
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun _ : ℝ => (1 : ℕ))
  have hsum :
      ∑ j ∈ J, (subdivisionFiber W L j).card = W.card := by
    calc
      ∑ j ∈ J, (subdivisionFiber W L j).card =
          ∑ j ∈ J, ∑ t ∈ W with subdivisionIndex L t = j, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.card_eq_sum_ones]
        rfl
      _ = ∑ t ∈ W, (1 : ℕ) := hfiber
      _ = W.card := by simp
  simpa [J] using hsum.symm

/-! ## Local-to-global large-value count -/

/-- Subdivision reduces an ambient large-value count to the finite sum of
translated local fibers.  The local hypothesis is uniform in coefficients and
therefore survives the explicit phase modulation. -/
theorem card_le_floor_intervals_mul_of_local_bound
    (b : ℕ → ℂ) (N : ℕ) (W : Finset ℝ) {T L V K : ℝ}
    (hL : 0 < L) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ 1)
    (hsep : OneSeparated W)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖)
    (hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      (∀ n, ‖a n‖ ≤ 1) →
      OneSeparated U →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ L) →
      (∀ u ∈ U, V ≤ ‖dirichletPolynomial a N u‖) →
      (U.card : ℝ) ≤ K) :
    (W.card : ℝ) ≤ (⌊T / L⌋₊ + 1 : ℕ) * K := by
  let J := Finset.range (⌊T / L⌋₊ + 1)
  have hcard : W.card =
      ∑ j ∈ J, (subdivisionFiber W L j).card := by
    simpa [J] using (card_eq_sum_subdivisionFiber hL hT hheight)
  have hfiber : ∀ j ∈ J,
      ((subdivisionFiber W L j).card : ℝ) ≤ K := by
    intro j hj
    let U := translatedSubdivisionFiber W L j
    let a := forwardTranslatedCoefficient b ((j : ℝ) * L)
    have ha : ∀ n, ‖a n‖ ≤ 1 := by
      intro n
      dsimp [a]
      rw [norm_forwardTranslatedCoefficient]
      exact hb n
    have hUsep : OneSeparated U := by
      dsimp [U]
      exact oneSeparated_translatedSubdivisionFiber hsep L j
    have hUheight : ∀ u ∈ U, 0 ≤ u ∧ u ≤ L := by
      intro u hu
      exact translatedSubdivisionFiber_mem_local_interval hL hT hheight hj hu
    have hUlarge : ∀ u ∈ U, V ≤ ‖dirichletPolynomial a N u‖ := by
      intro u hu
      dsimp [a]
      rw [dirichletPolynomial_forwardTranslatedCoefficient]
      change u ∈ (subdivisionFiber W L j).image
          (fun t => t - (j : ℝ) * L) at hu
      rw [Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      have hut : (t - (j : ℝ) * L) + (j : ℝ) * L = t := by
        ring
      rw [hut]
      exact hlarge t (Finset.mem_filter.mp ht).1
    have hU := hlocal a U ha hUsep hUheight hUlarge
    rw [← card_translatedSubdivisionFiber W L j]
    exact hU
  have hsumle :
      ∑ j ∈ J, ((subdivisionFiber W L j).card : ℝ) ≤
        ∑ _j ∈ J, K := by
    apply Finset.sum_le_sum
    intro j hj
    exact hfiber j hj
  have hsumK : (∑ _j ∈ J, K) = (J.card : ℝ) * K := by
    simp
  have hW : (W.card : ℝ) =
      ∑ j ∈ J, ((subdivisionFiber W L j).card : ℝ) := by
    exact_mod_cast hcard
  rw [hW]
  exact hsumle.trans_eq (by simp [J])

/-- If the ambient interval is at least one local interval, the floor count is
at most `2T/L`; this is the paper's `⌈T/L⌉` loss up to the harmless endpoint
constant forced by the explicit floor convention. -/
theorem card_le_two_ratio_mul_of_local_bound
    (b : ℕ → ℂ) (N : ℕ) (W : Finset ℝ) {T L V K : ℝ}
    (hL : 0 < L) (hLT : L ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ 1)
    (hsep : OneSeparated W)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖)
    (hK : 0 ≤ K)
    (hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      (∀ n, ‖a n‖ ≤ 1) →
      OneSeparated U →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ L) →
      (∀ u ∈ U, V ≤ ‖dirichletPolynomial a N u‖) →
      (U.card : ℝ) ≤ K) :
    (W.card : ℝ) ≤ 2 * (T / L) * K := by
  have hT : 0 ≤ T := le_trans (le_of_lt hL) hLT
  have hfloor : (⌊T / L⌋₊ : ℝ) ≤ T / L := by
    apply Nat.floor_le
    exact div_nonneg hT hL.le
  have hratio : 1 ≤ T / L := (le_div_iff₀ hL).2 (by simpa using hLT)
  have hcount : ((⌊T / L⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * (T / L) := by
    push_cast
    linarith
  have hmain := card_le_floor_intervals_mul_of_local_bound b N W
    hL hT hheight hb hsep hlarge hlocal
  have := mul_le_mul_of_nonneg_right hcount hK
  exact hmain.trans (by
    calc
      ((⌊T / L⌋₊ + 1 : ℕ) : ℝ) * K ≤
          (2 * (T / L)) * K := this
      _ = 2 * (T / L) * K := by ring)

/-! ## The local branch of the same contract -/

theorem card_le_local_of_T_le
    (b : ℕ → ℂ) (N : ℕ) (W : Finset ℝ) {T L V K : ℝ}
    (hTL : T ≤ L)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ 1)
    (hsep : OneSeparated W)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖)
    (hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      (∀ n, ‖a n‖ ≤ 1) →
      OneSeparated U →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ L) →
      (∀ u ∈ U, V ≤ ‖dirichletPolynomial a N u‖) →
      (U.card : ℝ) ≤ K) :
    (W.card : ℝ) ≤ K := by
  apply hlocal b W
  · exact hb
  · exact hsep
  · intro t ht
    exact ⟨(hheight t ht).1, (hheight t ht).2.trans hTL⟩
  · exact hlarge

end
end GuthMaynardLargeValueIntervalSubdivision

#print axioms GuthMaynardLargeValueIntervalSubdivision.norm_forwardTranslatedCoefficient
#print axioms GuthMaynardLargeValueIntervalSubdivision.dirichletPolynomial_forwardTranslatedCoefficient
#print axioms GuthMaynardLargeValueIntervalSubdivision.card_eq_sum_subdivisionFiber
#print axioms GuthMaynardLargeValueIntervalSubdivision.card_le_floor_intervals_mul_of_local_bound
#print axioms GuthMaynardLargeValueIntervalSubdivision.card_le_two_ratio_mul_of_local_bound
