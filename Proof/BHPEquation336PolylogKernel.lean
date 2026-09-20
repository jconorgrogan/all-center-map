import MRTLemma211AllCharacterSource

/-!
# BHP equation (3.36) with the contour-kernel loss retained

The printed definition of `J(t, chi)` after BHP (3.36) drops the `1 / w`
factor present in the Perron integral immediately above it.  The later Holder
argument requires a decaying Perron kernel, so the pointwise source boundary
must retain the fixed logarithmic loss incurred when the singular kernel near
`w = 0` is regularized.

MRT only needs an unspecified power of the ambient logarithm.  This file proves
that any fixed polylogarithmic loss in the pointwise contour term is absorbed
by the already certified Holder and one-spacing descent.  No pointwise Perron
or Rademacher estimate is assumed inside the proof below.
-/

namespace MAPBHPEquation336PolylogKernel

open scoped BigOperators
open MAPMRTLemma210OrthogonalityReduction
open MAPMRTLemma211AllCharacterSource
open MAPMRTCorollary25Minkowski

noncomputable section

/-- Corrected source boundary for BHP (3.36).  The exponent `K₀` records only
the fixed loss from regularizing the Perron kernel at the shifted contour.
All other terms are the three literal errors printed in (3.36). -/
def BHPEquation336PerronRademacherPolylog : Prop :=
  ∃ C₃₆ : ℝ, 0 < C₃₆ ∧ ∃ K₀ : ℕ,
    ∀ (q X : ℕ) [NeZero q] (T x0 : ℝ)
      (S : Finset (DirichletCharacter ℂ q × ℝ)),
      1 ≤ q → 2 ≤ X → 2 ≤ T →
      (q : ℝ) ≤ x0 → (X : ℝ) ≤ x0 → T ≤ x0 →
      (∀ z ∈ S, |z.2| ≤ T) →
      SameCharacterOneSeparated S →
      ∀ z ∈ S,
        ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤ C₃₆ *
          (Real.log x0 ^ K₀ *
              perronConvolution (criticalLineLNorm z.1) T z.2 +
            (Real.sqrt (q : ℝ) / Real.sqrt T +
              Real.log x0 * Real.sqrt (X : ℝ) / T +
              Real.sqrt (X : ℝ) * principalPerronWeight z))

/-- A fixed polylogarithmic pointwise contour loss only increases the free
logarithmic exponent in the BHP/MRT fourth-moment interface. -/
theorem bhpEquation336AndHolderReduction_of_polylogPerronRademacher
    (hsource : BHPEquation336PerronRademacherPolylog) :
    BHPEquation336AndHolderReduction := by
  classical
  obtain ⟨C₀, hC₀, K₀, hsource⟩ := hsource
  let Cκ : ℝ := 256 * (1 / Real.log 2 + 4)
  let C₃₆ : ℝ := C₀ + C₀ ^ 4 * Cκ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCκ : 0 < Cκ := by
    dsimp [Cκ]
    positivity
  have hC₃₆ : 0 < C₃₆ := by
    dsimp [C₃₆]
    positivity
  refine ⟨C₃₆, hC₃₆, 4 * K₀ + 4, ?_⟩
  intro q X _inst T x0 S hq hX hT hqx hXx hTx hheight hsep
  let L : ℝ := Real.log x0
  let J : DirichletCharacter ℂ q × ℝ → ℝ := fun z =>
    C₀ * L ^ K₀ * perronConvolution (criticalLineLNorm z.1) T z.2
  have hx0 : 2 ≤ x0 := by
    have hXreal : (2 : ℝ) ≤ X := by exact_mod_cast hX
    exact hXreal.trans hXx
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by linarith)
  refine ⟨J, ?_, ?_, ?_⟩
  · intro z hz
    dsimp [J]
    exact mul_nonneg
      (mul_nonneg hC₀.le (pow_nonneg hL K₀))
      (perronConvolution_nonneg (fun s => norm_nonneg _) (by linarith))
  · intro z hz
    have hraw := hsource q X T x0 S hq hX hT hqx hXx hTx
      hheight hsep z hz
    let E : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T +
      Real.log x0 * Real.sqrt (X : ℝ) / T +
      Real.sqrt (X : ℝ) * principalPerronWeight z
    have hE : 0 ≤ E := by
      dsimp [E]
      have hlog : 0 ≤ Real.log x0 := Real.log_nonneg (by linarith)
      have hfirst : 0 ≤ Real.sqrt (q : ℝ) / Real.sqrt T := by positivity
      have hsecond : 0 ≤ Real.log x0 * Real.sqrt (X : ℝ) / T := by
        positivity
      have hthird : 0 ≤ Real.sqrt (X : ℝ) * principalPerronWeight z :=
        mul_nonneg (Real.sqrt_nonneg _) (principalPerronWeight_nonneg z)
      exact add_nonneg (add_nonneg hfirst hsecond) hthird
    have hcoeff : C₀ ≤ C₃₆ := by
      dsimp [C₃₆]
      exact le_add_of_nonneg_right
        (mul_nonneg (pow_nonneg hC₀.le 4) hCκ.le)
    calc
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
          C₀ * (L ^ K₀ *
            perronConvolution (criticalLineLNorm z.1) T z.2 + E) := by
        simpa [L, E] using hraw
      _ = J z + C₀ * E := by dsimp [J]; ring
      _ ≤ J z + C₃₆ * E :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcoeff hE)
      _ = J z + C₃₆ *
          (Real.sqrt (q : ℝ) / Real.sqrt T +
            Real.log x0 * Real.sqrt (X : ℝ) / T +
            Real.sqrt (X : ℝ) * principalPerronWeight z) := by
        rfl
  · have hTpos : 0 < T := by linarith
    have hfamily :
        0 ≤ allCharacterCriticalLineFourthIntegral q (2 * T) :=
      allCharacterCriticalLineFourthIntegral_nonneg q (by linarith)
    have hagg := sum_perronConvolution_fourth_le_exactKernel
      hTpos hheight hsep
    have hkernel := perronHolderKernel_le_log_four hT hTx
    have hkernelFamily :
        (∫ u in (-T)..T, perronWeight u) ^ 3 *
            (4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)) *
              allCharacterCriticalLineFourthIntegral q (2 * T) ≤
          Cκ * L ^ 4 *
              allCharacterCriticalLineFourthIntegral q (2 * T) := by
      simpa [L, Cκ] using mul_le_mul_of_nonneg_right hkernel hfamily
    have hconv :
        (∑ z ∈ S,
          perronConvolution (criticalLineLNorm z.1) T z.2 ^ 4) ≤
          Cκ * L ^ 4 *
            allCharacterCriticalLineFourthIntegral q (2 * T) :=
      hagg.trans hkernelFamily
    have hJrewrite :
        (∑ z ∈ S, J z ^ 4) = (C₀ ^ 4 * L ^ (4 * K₀)) *
          ∑ z ∈ S,
            perronConvolution (criticalLineLNorm z.1) T z.2 ^ 4 := by
      dsimp [J]
      simp_rw [mul_pow, ← pow_mul]
      rw [Finset.mul_sum]
      simp [Nat.mul_comm]
    have hnonnegRight : 0 ≤ L ^ (4 * K₀ + 4) *
        allCharacterCriticalLineFourthIntegral q (2 * T) := by
      positivity
    calc
      (∑ z ∈ S, J z ^ 4) = (C₀ ^ 4 * L ^ (4 * K₀)) *
          ∑ z ∈ S,
            perronConvolution (criticalLineLNorm z.1) T z.2 ^ 4 := hJrewrite
      _ ≤ (C₀ ^ 4 * L ^ (4 * K₀)) *
          (Cκ * L ^ 4 *
            allCharacterCriticalLineFourthIntegral q (2 * T)) :=
        mul_le_mul_of_nonneg_left hconv
          (mul_nonneg (pow_nonneg hC₀.le 4) (pow_nonneg hL _))
      _ = (C₀ ^ 4 * Cκ) *
          (L ^ (4 * K₀ + 4) *
            allCharacterCriticalLineFourthIntegral q (2 * T)) := by
        rw [pow_add]
        ring
      _ ≤ C₃₆ * (L ^ (4 * K₀ + 4) *
          allCharacterCriticalLineFourthIntegral q (2 * T)) := by
        apply mul_le_mul_of_nonneg_right _ hnonnegRight
        dsimp [C₃₆]
        linarith [hC₀.le]
      _ = C₃₆ * Real.log x0 ^ (4 * K₀ + 4) *
          allCharacterCriticalLineFourthIntegral q (2 * T) := by
        dsimp [L]
        ring

/-- Fully descended MRT Lemma 2.11 from the corrected pointwise contour source
and the independent Ramachandra mean-value source. -/
theorem mrtLemma211_of_polylogPerronRademacher_and_ramachandraMeanValue
    (hperron : BHPEquation336PerronRademacherPolylog)
    (hmean : BHPLemma7RamachandraAllCharacterMeanValue) :
    MRTLemma211AllCharacterFourthMoment :=
  mrtLemma211_of_bhpEquation336_and_ramachandraMeanValue
    (bhpEquation336AndHolderReduction_of_polylogPerronRademacher hperron) hmean

end
end MAPBHPEquation336PolylogKernel

#print axioms MAPBHPEquation336PolylogKernel.bhpEquation336AndHolderReduction_of_polylogPerronRademacher
#print axioms MAPBHPEquation336PolylogKernel.mrtLemma211_of_polylogPerronRademacher_and_ramachandraMeanValue
