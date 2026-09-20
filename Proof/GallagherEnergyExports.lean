import SignedGallagherCore
import MajorArcIntegratedPowerWeld

namespace MAPNearCollarGallagher

open AddCircle MeasureTheory Set
open scoped BigOperators ENNReal ArithmeticFunction
noncomputable section
open PrimePairEndpoints MAPMajorArcWeld

/-- Sum of the literal signed sliding energies over any finite family of
rational centers.  This is the precise AP-facing input to Gallagher. -/
def finiteSignedSlidingEnergy
    (X y : ℝ) (pairs : Finset (ℕ × ℕ)) : ℝ :=
  ∑ qa ∈ pairs,
    ∫ x : ℝ, ‖signedSlidingDiscrepancy X qa.1 qa.2 x y‖ ^ 2

/-- Sum of the literal signed Fourier discrepancy energies on Gallagher's
closed band. -/
def finiteSignedFourierEnergy
    (X y : ℝ) (pairs : Finset (ℕ × ℕ)) : ℝ :=
  ∑ qa ∈ pairs,
    ∫ beta in Set.Icc (-(1 / (8 * y))) (1 / (8 * y)),
      ‖signedFourierDiscrepancy X qa.1 qa.2 beta‖ ^ 2

/-- Exact finite-family Gallagher transfer.  There is no union overlap loss:
the rational centers are summed with their literal multiplicity. -/
theorem finiteSignedFourierEnergy_le_slidingEnergy
    {X y : ℝ} {pairs : Finset (ℕ × ℕ)}
    (hX : 0 ≤ X) (hy : 0 < y) :
    finiteSignedFourierEnergy X y pairs ≤
      4 / y ^ 2 * finiteSignedSlidingEnergy X y pairs := by
  unfold finiteSignedFourierEnergy finiteSignedSlidingEnergy
  calc
    (∑ qa ∈ pairs,
      ∫ beta in Set.Icc (-(1 / (8 * y))) (1 / (8 * y)),
        ‖signedFourierDiscrepancy X qa.1 qa.2 beta‖ ^ 2) ≤
      ∑ qa ∈ pairs,
        (4 / y ^ 2) *
          ∫ x : ℝ, ‖signedSlidingDiscrepancy X qa.1 qa.2 x y‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro qa hqa
      exact signedMeasureGallagherInequality_constant_four
        X y qa.1 qa.2 hX hy
    _ = 4 / y ^ 2 *
        ∑ qa ∈ pairs,
          ∫ x : ℝ, ‖signedSlidingDiscrepancy X qa.1 qa.2 x y‖ ^ 2 := by
      rw [Finset.mul_sum]

/-- AP-facing implication with the smallest possible source contract: a bound
on the actual summed signed sliding energy. -/
theorem finiteSignedFourierEnergy_le_of_slidingEnergy_le
    {X y E : ℝ} {pairs : Finset (ℕ × ℕ)}
    (hX : 0 ≤ X) (hy : 0 < y) (hE : 0 ≤ E)
    (hslide : finiteSignedSlidingEnergy X y pairs ≤ E) :
    finiteSignedFourierEnergy X y pairs ≤ 4 / y ^ 2 * E := by
  exact (finiteSignedFourierEnergy_le_slidingEnergy hX hy).trans
    (mul_le_mul_of_nonneg_left hslide (by positivity))

/-- The major-arc Gallagher window whose closed Fourier band is exactly the
paper radius `(log X)^D/X`. -/
def paperGallagherWindow (X : ℝ) (D : ℕ) : ℝ :=
  X / (8 * (Real.log X) ^ D)

theorem paperGallagherWindow_pos
    {X : ℝ} (D : ℕ) (hX : 1 < X) :
    0 < paperGallagherWindow X D := by
  unfold paperGallagherWindow
  have hlog : 0 < Real.log X := Real.log_pos hX
  positivity

/-- Exact normalization requested by the major-arc weld. -/
theorem inv_eight_paperGallagherWindow_eq_paperArcRadius
    {X : ℝ} (D : ℕ) (hX : 1 < X) :
    1 / (8 * paperGallagherWindow X D) = paperArcRadius X D := by
  unfold paperGallagherWindow paperArcRadius
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hpow : 0 < (Real.log X) ^ D := pow_pos hlog D
  have hX0 : X ≠ 0 := ne_of_gt (zero_lt_one.trans hX)
  field_simp

/-- Literal nested paper index set, presented as a finite set of pairs. -/
def paperReducedPairs (X : ℝ) (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 (paperDenominatorCutoff X B)).biUnion fun q =>
    (reducedResidues q).image fun a => (q, a)

/-- Every pair in the literal nested paper family appears in the flattened
finite set; the first coordinate makes distinct denominator fibers disjoint. -/
theorem sum_paperReducedPairs
    {M : Type*} [AddCommMonoid M]
    (X : ℝ) (B : ℕ) (f : ℕ → ℕ → M) :
    ∑ qa ∈ paperReducedPairs X B, f qa.1 qa.2 =
      ∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
        ∑ a ∈ reducedResidues q, f q a := by
  classical
  unfold paperReducedPairs
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_image]
    · intro a₁ ha₁ a₂ ha₂ h
      exact congrArg Prod.snd h
  · intro q₁ hq₁ q₂ hq₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro qa hqa₁ hqa₂
    rcases Finset.mem_image.mp hqa₁ with ⟨a₁, ha₁, rfl⟩
    rcases Finset.mem_image.mp hqa₂ with ⟨a₂, ha₂, hpair⟩
    exact hne (congrArg Prod.fst hpair).symm

/-- Paper-major signed sliding energy at the exact dual window. -/
def paperMajorSignedSlidingEnergy (X : ℝ) (B D : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
    ∑ a ∈ reducedResidues q,
      ∫ x : ℝ,
        ‖signedSlidingDiscrepancy X q a x
          (paperGallagherWindow X D)‖ ^ 2

/-- Paper-major signed Fourier-model error energy, on the literal paper arc. -/
def paperMajorSignedFourierEnergy (X : ℝ) (B D : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
    ∑ a ∈ reducedResidues q,
      ∫ beta in Set.Icc (-(paperArcRadius X D)) (paperArcRadius X D),
        ‖signedFourierDiscrepancy X q a beta‖ ^ 2

/-- Exact AP-sliding-energy to paper-major Fourier-energy transfer. -/
theorem paperMajorSignedFourierEnergy_le_slidingEnergy
    {X : ℝ} (B D : ℕ) (hX : 1 < X) :
    paperMajorSignedFourierEnergy X B D ≤
      4 / paperGallagherWindow X D ^ 2 *
        paperMajorSignedSlidingEnergy X B D := by
  have hX0 : 0 ≤ X := (zero_lt_one.trans hX).le
  have hy := paperGallagherWindow_pos D hX
  have hflat := finiteSignedFourierEnergy_le_slidingEnergy
    (pairs := paperReducedPairs X B) hX0 hy
  unfold finiteSignedFourierEnergy finiteSignedSlidingEnergy at hflat
  rw [sum_paperReducedPairs X B (fun q a =>
    ∫ beta in Set.Icc (-(1 / (8 * paperGallagherWindow X D)))
      (1 / (8 * paperGallagherWindow X D)),
        ‖signedFourierDiscrepancy X q a beta‖ ^ 2)] at hflat
  rw [sum_paperReducedPairs X B (fun q a =>
    ∫ x : ℝ,
      ‖signedSlidingDiscrepancy X q a x
        (paperGallagherWindow X D)‖ ^ 2)] at hflat
  unfold paperMajorSignedFourierEnergy paperMajorSignedSlidingEnergy
  simpa only [inv_eight_paperGallagherWindow_eq_paperArcRadius D hX] using hflat

/-- Same theorem with a source-supplied AP sliding-energy bound. -/
theorem paperMajorSignedFourierEnergy_le_of_slidingEnergy_le
    {X E : ℝ} (B D : ℕ) (hX : 1 < X) (hE : 0 ≤ E)
    (hslide : paperMajorSignedSlidingEnergy X B D ≤ E) :
    paperMajorSignedFourierEnergy X B D ≤
      4 / paperGallagherWindow X D ^ 2 * E := by
  exact (paperMajorSignedFourierEnergy_le_slidingEnergy B D hX).trans
    (mul_le_mul_of_nonneg_left hslide (by positivity))

/-- Near-collar reduced-pair energy at the manuscript Gallagher window. -/
def nearReducedPairSignedFourierEnergy
    (epsilon X : ℝ) (B Cc : ℕ) : ℝ :=
  finiteSignedFourierEnergy X (gallagherWindow epsilon X Cc)
    (reducedRationalPairs X B)

/-- Exact all-reduced-pair near energy consequence. -/
theorem nearReducedPairSignedFourierEnergy_le_slidingEnergy
    {epsilon X : ℝ} (B Cc : ℕ) (hX : 0 ≤ X)
    (hy : 0 < gallagherWindow epsilon X Cc) :
    nearReducedPairSignedFourierEnergy epsilon X B Cc ≤
      4 / gallagherWindow epsilon X Cc ^ 2 *
        finiteSignedSlidingEnergy X (gallagherWindow epsilon X Cc)
          (reducedRationalPairs X B) := by
  exact finiteSignedFourierEnergy_le_slidingEnergy hX hy

end
end MAPNearCollarGallagher
