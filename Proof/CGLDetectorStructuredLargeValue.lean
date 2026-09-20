import CGLCompactStripSplitDensityConstructor
import PostA5TypeICoefficientProvenance

/-!
# A detector-structured compact-density seam

The literal Type-I output is a two-point coefficient family, not an arbitrary
unit-ball coefficient.  This file records the strictly weaker large-value
input obtained by preserving that provenance and proves that it is sufficient
for the fixed-primitive high-strip density conclusion.

This does not assert the structured large-value estimate.  It changes the
remaining analytic target from all bounded coefficients to the exact
normalized mollifier-detector coefficients (with the sole optional global
translation phase).
-/

namespace CGLDetectorStructuredLargeValue

open DirichletZeros ZeroDensityInterface MAPAPZeroDensityCert MAPGuthMaynard
open CGLProofDAG FixedCharacterPoweredBridge
open CGLCompactStripDensityConstructor
open CGLCompactStripSplitDensityConstructor
open PostA5TypeICoefficientProvenance

noncomputable section

/-- The exact GM-sized estimate only for coefficients retained by the literal
Type-I detector.  This is strictly narrower than
`UniformThirtyThirteenLargeValue`: it contains the same numerical range, but
only the two coefficient sequences certified by
`IsNormalizedDetectorCoefficient`. -/
def DetectorStructuredThirtyThirteenLargeValue : Prop :=
  ∀ κ eta : ℝ, 0 < κ → 0 < eta →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T sigma : ℝ) (D : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        Real.rpow T κ ≤ D →
        (D : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 →
        (∀ n, ‖b n‖ ≤ 1) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W,
          Real.rpow D sigma *
              Real.rpow T (-inputLoss κ (eta / 2)) ≤
            ‖dirichletPolynomial b D t‖) →
        ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
            (U Ncut : ℕ) (Y scale : ℝ),
          IsNormalizedDetectorCoefficient
            chi U Ncut Y sigma D scale T b →
          (W.card : ℝ) ≤
            C * Real.rpow T (densityCoeff * (1 - sigma) + eta)

/-- The source-faithful post-A.5 split with coefficient provenance retained.
The numerical fields are identical to `PostA5HighStripSplitReduction`; only
the final existential certificate is new. -/
def PostA5HighStripStructuredSplitReduction : Prop :=
  ∀ K delta loss : ℝ, 0 < K → 0 < delta → 0 < loss →
    ∃ κ A T₀ : ℝ,
      0 < κ ∧ κ ≤ 1 / 2 ∧ 2 * κ ≤ loss ∧ 0 < A ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        ∀ (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r),
          chi.IsPrimitive → chi ≠ 1 → r ≤ Q →
          ∃ (D : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) (ZI ZII : ℕ),
            Real.rpow T κ ≤ D ∧
            (D : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
            (∀ n, ‖b n‖ ≤ 1) ∧
            OneSeparated W ∧
            (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
            (∀ t ∈ W,
              Real.rpow D sigma *
                  Real.rpow T (-inputLoss κ (loss / 2)) ≤
                ‖dirichletPolynomial b D t‖) ∧
            dirichletZeroCount chi sigma T ≤ ZI + ZII ∧
            (ZI : ℝ) ≤ A * Real.rpow T loss * (1 + (W.card : ℝ)) ∧
            (ZII : ℝ) ≤
              A * Real.rpow T
                (2 * (1 - sigma) + 2 * κ + loss) ∧
            ∃ (U Ncut : ℕ) (Y scale : ℝ),
              IsNormalizedDetectorCoefficient
                chi U Ncut Y sigma D scale T b

/-- The published arbitrary-coefficient input implies the detector-structured
one, so the new seam is a conservative weakening. -/
theorem detectorStructuredThirtyThirteen_of_uniform
    (huniform : UniformThirtyThirteenLargeValue) :
    DetectorStructuredThirtyThirteenLargeValue := by
  intro κ eta hκ heta
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := huniform κ eta hκ heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T sigma D b W hT hsigmaLow hsigmaHigh hDlow hDhigh hb hsep
    hheight hlarge q _inst chi U Ncut Y scale hprovenance
  exact hbound T sigma D b W hT hsigmaLow hsigmaHigh hDlow hDhigh hb
    hsep hheight hlarge

/-- The detector-structured GM input already suffices for the same
fixed-primitive high-strip density theorem. -/
theorem fixedPrimitiveHighStripDensity_of_structuredSplitReduction
    (hsplit : PostA5HighStripStructuredSplitReduction)
    (hstructured : DetectorStructuredThirtyThirteenLargeValue) :
    ∀ K delta eta : ℝ, 0 < K → 0 < delta → 0 < eta →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
          (Q : ℝ) ≤ Real.rpow (Real.log T) K →
          7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
          ∀ (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r),
            chi.IsPrimitive → chi ≠ 1 → r ≤ Q →
            (dirichletZeroCount chi sigma T : ℝ) ≤
              C * Real.rpow T (densityCoeff * (1 - sigma) + eta) := by
  intro K delta eta hK hdelta heta
  let loss : ℝ := eta / 8
  have hloss : 0 < loss := by dsimp [loss]; positivity
  obtain ⟨κ, A, Tsplit, hκ, _hκhalf, hκloss, hA, hTsplit, hsplit'⟩ :=
    hsplit K delta loss hK hdelta hloss
  obtain ⟨Cgm, Tgm, hCgm, hTgm, hgm⟩ :=
    hstructured κ loss hκ hloss
  let Cfinal : ℝ := A * (2 + Cgm)
  let T₀ : ℝ := max Tsplit Tgm
  refine ⟨Cfinal, T₀, ?_, ?_, ?_⟩
  · dsimp [Cfinal]
    positivity
  · exact hTsplit.trans (le_max_left _ _)
  · intro T Q sigma hT hQ hsigmaLow hsigmaHigh r _inst chi
      hprimitive hchi hrQ
    have hTsplit' : Tsplit ≤ T := (le_max_left _ _).trans hT
    have hTgm' : Tgm ≤ T := (le_max_right _ _).trans hT
    obtain ⟨D, b, W, ZI, ZII, hDlow, hDhigh, hb, hsep, hheight,
      hpoly, hcount, hZI, hZII, U, Ncut, Y, scale, hprovenance⟩ :=
      hsplit' T Q sigma hTsplit' hQ hsigmaLow hsigmaHigh r chi
        hprimitive hchi hrQ
    have hW := hgm T sigma D b W hTgm' hsigmaLow hsigmaHigh
      hDlow hDhigh hb hsep hheight hpoly r chi U Ncut Y scale hprovenance
    have hTone : 1 ≤ T :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (hTgm.trans hTgm')
    have hTnonneg : 0 ≤ T := zero_le_one.trans hTone
    have hpowOne :
        1 ≤ Real.rpow T (densityCoeff * (1 - sigma) + loss) :=
      Real.one_le_rpow hTone (by
        have : 0 ≤ 1 - sigma := by linarith
        dsimp [densityCoeff]
        positivity)
    have hOneW :
        1 + (W.card : ℝ) ≤
          (1 + Cgm) *
            Real.rpow T (densityCoeff * (1 - sigma) + loss) := by
      calc
        1 + (W.card : ℝ) ≤
            Real.rpow T (densityCoeff * (1 - sigma) + loss) +
              Cgm * Real.rpow T
                (densityCoeff * (1 - sigma) + loss) :=
          add_le_add hpowOne hW
        _ = (1 + Cgm) *
            Real.rpow T (densityCoeff * (1 - sigma) + loss) := by ring
    have hZI' : (ZI : ℝ) ≤
        A * (1 + Cgm) *
          Real.rpow T (densityCoeff * (1 - sigma) + 2 * loss) := by
      calc
        (ZI : ℝ) ≤ A * Real.rpow T loss * (1 + (W.card : ℝ)) := hZI
        _ ≤ A * Real.rpow T loss *
            ((1 + Cgm) *
              Real.rpow T (densityCoeff * (1 - sigma) + loss)) := by
          exact mul_le_mul_of_nonneg_left hOneW
            (mul_nonneg hA.le (Real.rpow_nonneg hTnonneg _))
        _ = A * (1 + Cgm) *
            Real.rpow T (densityCoeff * (1 - sigma) + 2 * loss) := by
          rw [show A * Real.rpow T loss *
                ((1 + Cgm) * Real.rpow T
                  (densityCoeff * (1 - sigma) + loss)) =
              A * (1 + Cgm) *
                (Real.rpow T loss * Real.rpow T
                  (densityCoeff * (1 - sigma) + loss)) by ring]
          congr 1
          calc
            Real.rpow T loss *
                Real.rpow T (densityCoeff * (1 - sigma) + loss) =
              Real.rpow T
                (loss + (densityCoeff * (1 - sigma) + loss)) :=
              (Real.rpow_add (lt_of_lt_of_le zero_lt_one hTone) _ _).symm
            _ = Real.rpow T
                (densityCoeff * (1 - sigma) + 2 * loss) := by
              congr 1
              ring
    have hZIexp :
        densityCoeff * (1 - sigma) + 2 * loss ≤
          densityCoeff * (1 - sigma) + eta := by
      dsimp [loss]
      linarith
    have hZIfinal : (ZI : ℝ) ≤
        A * (1 + Cgm) *
          Real.rpow T (densityCoeff * (1 - sigma) + eta) := by
      exact hZI'.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hTone hZIexp)
        (mul_nonneg hA.le (by positivity)))
    have hIIexp :
        2 * (1 - sigma) + 2 * κ + loss ≤
          densityCoeff * (1 - sigma) + eta := by
      calc
        2 * (1 - sigma) + 2 * κ + loss ≤
            2 * (1 - sigma) + 2 * κ + 2 * loss := by linarith
        _ ≤ densityCoeff * (1 - sigma) + eta :=
          typeII_exponent_with_reserve_le (by linarith) hκloss (by
            dsimp [loss]
            linarith)
    have hZIIfinal : (ZII : ℝ) ≤
        A * Real.rpow T (densityCoeff * (1 - sigma) + eta) := by
      exact hZII.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hTone hIIexp) hA.le)
    have hcountReal :
        (dirichletZeroCount chi sigma T : ℝ) ≤ (ZI : ℝ) + (ZII : ℝ) := by
      exact_mod_cast hcount
    calc
      (dirichletZeroCount chi sigma T : ℝ) ≤
          (ZI : ℝ) + (ZII : ℝ) := hcountReal
      _ ≤ A * (1 + Cgm) *
            Real.rpow T (densityCoeff * (1 - sigma) + eta) +
          A * Real.rpow T (densityCoeff * (1 - sigma) + eta) :=
        add_le_add hZIfinal hZIIfinal
      _ = Cfinal *
          Real.rpow T (densityCoeff * (1 - sigma) + eta) := by
        dsimp [Cfinal]
        ring

end
end CGLDetectorStructuredLargeValue

#print axioms CGLDetectorStructuredLargeValue.detectorStructuredThirtyThirteen_of_uniform
#print axioms CGLDetectorStructuredLargeValue.fixedPrimitiveHighStripDensity_of_structuredSplitReduction
