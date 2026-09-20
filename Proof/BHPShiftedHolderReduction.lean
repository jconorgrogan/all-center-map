import BHPCorrectedPerronKernel

/-!
# Holder and one-spacing reduction on the corrected shifted line

This is the deterministic companion to `BHPCorrectedPerronKernel`.  It shows
that the positive-offset Perron convolutions are controlled by the continuous
all-character fourth moment on that same shifted line.  The argument is
identical to the already certified critical-line packing, but the offset is
kept explicit so no critical/shifted-line substitution is hidden.
-/

namespace MAPBHPShiftedHolderReduction

open scoped BigOperators
open MAPBHPCorrectedPerronKernel
open MAPMRTLemma211AllCharacterSource
open MAPMRTCorollary25Minkowski

noncomputable section

def shiftedCriticalLineLFourth {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (delta t : ℝ) : ℝ :=
  shiftedCriticalLineLNorm chi delta t ^ 4

def allCharacterShiftedLineFourthIntegral
    (q : ℕ) [NeZero q] (delta U : ℝ) : ℝ :=
  ∑ chi : DirichletCharacter ℂ q,
    ∫ t in (-U)..U, shiftedCriticalLineLFourth chi delta t

theorem continuous_shiftedCriticalLineLNorm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {delta : ℝ} (hdeltaHalf : delta ≠ 1 / 2) :
    Continuous (shiftedCriticalLineLNorm chi delta) := by
  unfold shiftedCriticalLineLNorm
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  have harg :
      ((((1 / 2 : ℝ) + delta : ℝ) : ℂ) + t * Complex.I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    apply hdeltaHalf
    linarith
  have houter := (DirichletCharacter.differentiableAt_LFunction chi _
    (.inl harg)).continuousAt
  have hinner : ContinuousAt
      (fun x : ℝ => ((((1 / 2 : ℝ) + delta : ℝ) : ℂ) +
        x * Complex.I)) t := by fun_prop
  exact ContinuousAt.comp_of_eq houter hinner rfl

theorem continuous_shiftedCriticalLineLFourth
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {delta : ℝ} (hdeltaHalf : delta ≠ 1 / 2) :
    Continuous (shiftedCriticalLineLFourth chi delta) := by
  unfold shiftedCriticalLineLFourth
  exact (continuous_shiftedCriticalLineLNorm chi hdeltaHalf).pow 4

theorem allCharacterShiftedLineFourthIntegral_nonneg
    (q : ℕ) [NeZero q] {delta U : ℝ} (hU : 0 ≤ U) :
    0 ≤ allCharacterShiftedLineFourthIntegral q delta U := by
  classical
  unfold allCharacterShiftedLineFourthIntegral
  apply Finset.sum_nonneg
  intro chi hchi
  apply intervalIntegral.integral_nonneg
  · linarith
  · intro t ht
    unfold shiftedCriticalLineLFourth
    positivity

/-- One character row on the shifted line.  The spacing estimate itself is
the already certified character-fiber kernel packing. -/
theorem sum_characterFiber_shiftedPerronConvolution_fourth_le
    {q : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {delta T : ℝ} (hdeltaHalf : delta ≠ 1 / 2) (hT : 0 ≤ T)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S)
    (chi : DirichletCharacter ℂ q) :
    (∑ z ∈ characterFiber S chi,
      perronConvolution (shiftedCriticalLineLFourth chi delta) T z.2) ≤
      4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ) *
        (∫ s in (-2 * T)..(2 * T),
          shiftedCriticalLineLFourth chi delta s) := by
  classical
  let H : ℝ := 4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)
  have hG : Continuous (shiftedCriticalLineLFourth chi delta) :=
    continuous_shiftedCriticalLineLFourth chi hdeltaHalf
  have hlocal :
      (∑ z ∈ characterFiber S chi,
        perronConvolution (shiftedCriticalLineLFourth chi delta) T z.2) ≤
      ∑ z ∈ characterFiber S chi,
        ∫ s in (-2 * T)..(2 * T),
          perronWeight (s - z.2) *
            shiftedCriticalLineLFourth chi delta s := by
    apply Finset.sum_le_sum
    intro z hz
    rw [perronConvolution_eq_translatedIntegral]
    have hzS : z ∈ S := (mem_characterFiber.mp hz).1
    have hzt := hheight z hzS
    have hzt' := abs_le.mp hzt
    apply intervalIntegral.integral_mono_interval
    · linarith [hzt'.1]
    · linarith
    · linarith [hzt'.2]
    · exact Filter.Eventually.of_forall fun s =>
        mul_nonneg (perronWeight_pos _).le (by
          unfold shiftedCriticalLineLFourth
          positivity)
    · exact ((continuous_perronWeight.comp
          (continuous_id.sub continuous_const)).mul hG).intervalIntegrable _ _
  have hswap :
      (∑ z ∈ characterFiber S chi,
        ∫ s in (-2 * T)..(2 * T),
          perronWeight (s - z.2) *
            shiftedCriticalLineLFourth chi delta s) =
      ∫ s in (-2 * T)..(2 * T),
        ∑ z ∈ characterFiber S chi,
          perronWeight (s - z.2) *
            shiftedCriticalLineLFourth chi delta s := by
    rw [intervalIntegral.integral_finset_sum]
    intro z hz
    exact ((continuous_perronWeight.comp
      (continuous_id.sub continuous_const)).mul hG).intervalIntegrable _ _
  have hpoint : ∀ s ∈ Set.Icc (-2 * T) (2 * T),
      (∑ z ∈ characterFiber S chi,
        perronWeight (s - z.2) *
          shiftedCriticalLineLFourth chi delta s) ≤
      H * shiftedCriticalLineLFourth chi delta s := by
    intro s hs
    have hsabs : |s| ≤ 2 * T := abs_le.2 ⟨by linarith [hs.1], hs.2⟩
    have hkernel := characterFiber_perronKernel_sum_le_harmonic
      hT hheight hsep chi hsabs
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hkernel (by
      unfold shiftedCriticalLineLFourth
      positivity)
  calc
    (∑ z ∈ characterFiber S chi,
        perronConvolution (shiftedCriticalLineLFourth chi delta) T z.2) ≤
        ∑ z ∈ characterFiber S chi,
          ∫ s in (-2 * T)..(2 * T),
            perronWeight (s - z.2) *
              shiftedCriticalLineLFourth chi delta s := hlocal
    _ = ∫ s in (-2 * T)..(2 * T),
          ∑ z ∈ characterFiber S chi,
            perronWeight (s - z.2) *
              shiftedCriticalLineLFourth chi delta s := hswap
    _ ≤ ∫ s in (-2 * T)..(2 * T),
          H * shiftedCriticalLineLFourth chi delta s := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (continuous_finset_sum _ fun z hz =>
          (continuous_perronWeight.comp
            (continuous_id.sub continuous_const)).mul hG).intervalIntegrable _ _
      · exact (continuous_const.mul hG).intervalIntegrable _ _
      · exact hpoint
    _ = H * (∫ s in (-2 * T)..(2 * T),
          shiftedCriticalLineLFourth chi delta s) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ) *
        (∫ s in (-2 * T)..(2 * T),
          shiftedCriticalLineLFourth chi delta s) := rfl

/-- Holder and one-spacing, summed over all characters, on the corrected
positive-offset line. -/
theorem sum_shiftedPerronConvolution_fourth_le_exactKernel
    {q : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {delta T : ℝ} (hdeltaHalf : delta ≠ 1 / 2) (hT : 0 < T)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S) :
    (∑ z ∈ S,
      perronConvolution (shiftedCriticalLineLNorm z.1 delta) T z.2 ^ 4) ≤
      (∫ u in (-T)..T, perronWeight u) ^ 3 *
        (4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)) *
          allCharacterShiftedLineFourthIntegral q delta (2 * T) := by
  classical
  let W : ℝ := ∫ u in (-T)..T, perronWeight u
  let H : ℝ := 4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)
  let F : DirichletCharacter ℂ q × ℝ → ℝ := fun z =>
    perronConvolution (shiftedCriticalLineLFourth z.1 delta) T z.2
  have hholder :
      (∑ z ∈ S,
        perronConvolution (shiftedCriticalLineLNorm z.1 delta) T z.2 ^ 4) ≤
        W ^ 3 * ∑ z ∈ S, F z := by
    calc
      (∑ z ∈ S,
          perronConvolution (shiftedCriticalLineLNorm z.1 delta) T z.2 ^ 4) ≤
          ∑ z ∈ S, W ^ 3 * F z := by
        apply Finset.sum_le_sum
        intro z hz
        have hh := perronConvolution_fourth_le_cubeWeightMass_mul
          (t := z.2) (continuous_shiftedCriticalLineLNorm z.1 hdeltaHalf) hT
        simpa [W, F, shiftedCriticalLineLFourth] using hh
      _ = W ^ 3 * ∑ z ∈ S, F z := by rw [Finset.mul_sum]
  have hfiber :
      (∑ chi : DirichletCharacter ℂ q,
        ∑ z ∈ characterFiber S chi, F z) = ∑ z ∈ S, F z :=
    sum_characterFiber_fiberwise S F
  have hpack :
      (∑ z ∈ S, F z) ≤
        H * allCharacterShiftedLineFourthIntegral q delta (2 * T) := by
    rw [← hfiber]
    calc
      (∑ chi : DirichletCharacter ℂ q,
          ∑ z ∈ characterFiber S chi, F z) ≤
          ∑ chi : DirichletCharacter ℂ q,
            H * (∫ s in (-2 * T)..(2 * T),
              shiftedCriticalLineLFourth chi delta s) := by
        apply Finset.sum_le_sum
        intro chi hchi
        have hrow := sum_characterFiber_shiftedPerronConvolution_fourth_le
          hdeltaHalf hT.le hheight hsep chi
        have heq : (∑ z ∈ characterFiber S chi, F z) =
            ∑ z ∈ characterFiber S chi,
              perronConvolution
                (shiftedCriticalLineLFourth chi delta) T z.2 := by
          apply Finset.sum_congr rfl
          intro z hz
          have hzchi : z.1 = chi := (mem_characterFiber.mp hz).2
          simp [F, hzchi]
        rw [heq]
        simpa [H] using hrow
      _ = H * allCharacterShiftedLineFourthIntegral q delta (2 * T) := by
        unfold allCharacterShiftedLineFourthIntegral
        rw [← Finset.mul_sum]
        simp only [neg_mul]
  have hW0 : 0 ≤ W := by
    dsimp [W]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun u hu => (perronWeight_pos u).le)
  calc
    (∑ z ∈ S,
        perronConvolution (shiftedCriticalLineLNorm z.1 delta) T z.2 ^ 4) ≤
        W ^ 3 * ∑ z ∈ S, F z := hholder
    _ ≤ W ^ 3 *
        (H * allCharacterShiftedLineFourthIntegral q delta (2 * T)) :=
      mul_le_mul_of_nonneg_left hpack (pow_nonneg hW0 3)
    _ = (∫ u in (-T)..T, perronWeight u) ^ 3 *
        (4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)) *
          allCharacterShiftedLineFourthIntegral q delta (2 * T) := by
      dsimp [W, H]
      ring

end
end MAPBHPShiftedHolderReduction

#print axioms MAPBHPShiftedHolderReduction.sum_characterFiber_shiftedPerronConvolution_fourth_le
#print axioms MAPBHPShiftedHolderReduction.sum_shiftedPerronConvolution_fourth_le_exactKernel
