import CGLCompactStripDensityConstructor
import PostA5TypeIIFourthMoment

/-!
# Source-faithful split compact-strip constructor

`CGLCompactStripDensityConstructor.PostA5HighStripLargeValueReduction` is kept
as an intentionally strong regression interface.  The published argument does
not send Type II through a common polynomial.  This module replaces it in the
canonical proof path by the literal split:

* Type-I weighted zero mass is controlled by one common polynomial witness;
* Type-II weighted zero mass is controlled directly by the exponent from
  Montgomery's separated fourth moment, `2(1-sigma)+2*kappa+loss`.

The theorem below proves all deterministic exponent absorption.  In
particular, no Type-II common polynomial is assumed or manufactured.
-/

namespace CGLCompactStripSplitDensityConstructor

open DirichletZeros ZeroDensityInterface MAPAPZeroDensityCert MAPGuthMaynard
open CGLProofDAG FixedCharacterPoweredBridge
open CGLCompactStripDensityConstructor

noncomputable section

/-- Source-faithful high-strip output after the finite A.4/A.5 partition.
`ZI` and `ZII` retain the two weighted contributions to the analytic zero
count.  Only `ZI` is reduced to the common polynomial set `W`; `ZII` carries
the exact Montgomery fourth-moment exponent.  The condition `2*kappa ≤ loss`
records the reserve chosen before the detector is run. -/
def PostA5HighStripSplitReduction : Prop :=
  ∀ K delta loss : ℝ, 0 < K → 0 < delta → 0 < loss →
    ∃ κ A T₀ : ℝ,
      0 < κ ∧ κ ≤ 1 / 2 ∧ 2 * κ ≤ loss ∧ 0 < A ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        ∀ (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r),
          chi.IsPrimitive → chi ≠ 1 → r ≤ Q →
          ∃ (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) (ZI ZII : ℕ),
            Real.rpow T κ ≤ N ∧
            (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
            (∀ n, ‖b n‖ ≤ 1) ∧
            OneSeparated W ∧
            (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
            (∀ t ∈ W,
              Real.rpow N sigma *
                  Real.rpow T (-inputLoss κ (loss / 2)) ≤
                ‖dirichletPolynomial b N t‖) ∧
            dirichletZeroCount chi sigma T ≤ ZI + ZII ∧
            (ZI : ℝ) ≤
              A * Real.rpow T loss * (1 + (W.card : ℝ)) ∧
            (ZII : ℝ) ≤
              A * Real.rpow T
                (2 * (1 - sigma) + 2 * κ + loss)

/-- The `30/13` target dominates the Type-II coefficient `2` on the whole
high strip. -/
theorem typeII_base_exponent_le_density
    {sigma : ℝ} (hsigma : sigma ≤ 1) :
    2 * (1 - sigma) ≤ densityCoeff * (1 - sigma) := by
  dsimp [densityCoeff]
  have hnonneg : 0 ≤ 1 - sigma := by linarith
  nlinarith

/-- The exact reserve ledger used for the direct Type-II contribution. -/
theorem typeII_exponent_with_reserve_le
    {sigma κ loss eta : ℝ}
    (hsigma : sigma ≤ 1) (hkappa : 2 * κ ≤ loss)
    (hloss : 3 * loss ≤ eta) :
    2 * (1 - sigma) + 2 * κ + 2 * loss ≤
      densityCoeff * (1 - sigma) + eta := by
  have hbase := typeII_base_exponent_le_density hsigma
  linarith

/-- The source-faithful split, followed by Guth--Maynard only on Type I,
proves the canonical fixed-primitive high-strip density estimate. -/
theorem fixedPrimitiveHighStripDensity_of_splitReduction
    (hsplit : PostA5HighStripSplitReduction)
    (huniform : UniformThirtyThirteenLargeValue) :
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
    huniform κ loss hκ hloss
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
    obtain ⟨N, b, W, ZI, ZII, hNlow, hNhigh, hb, hsep, hheight,
      hpoly, hcount, hZI, hZII⟩ :=
      hsplit' T Q sigma hTsplit' hQ hsigmaLow hsigmaHigh r chi
        hprimitive hchi hrQ
    have hW := hgm T sigma N b W hTgm' hsigmaLow hsigmaHigh
      hNlow hNhigh hb hsep hheight hpoly
    have hTone : 1 ≤ T :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (hTgm.trans hTgm')
    have hTnonneg : 0 ≤ T := zero_le_one.trans hTone
    have hbase0 : 0 ≤ densityCoeff * (1 - sigma) := by
      have : 0 ≤ 1 - sigma := by linarith
      dsimp [densityCoeff]
      positivity
    have hpowOne :
        1 ≤ Real.rpow T (densityCoeff * (1 - sigma) + loss) :=
      Real.one_le_rpow hTone (by positivity)
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

/-- Direct Guth--Maynard specialization of the split constructor. -/
theorem fixedPrimitiveHighStripDensity_of_guthMaynard_and_splitReduction
    (hGM : GuthMaynardTheorem11)
    (hsplit : PostA5HighStripSplitReduction) :
    ∀ K delta eta : ℝ, 0 < K → 0 < delta → 0 < eta →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
          (Q : ℝ) ≤ Real.rpow (Real.log T) K →
          7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
          ∀ (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r),
            chi.IsPrimitive → chi ≠ 1 → r ≤ Q →
            (dirichletZeroCount chi sigma T : ℝ) ≤
              C * Real.rpow T (densityCoeff * (1 - sigma) + eta) :=
  fixedPrimitiveHighStripDensity_of_splitReduction hsplit
    (uniformThirtyThirteenLargeValue_of_guthMaynard hGM)

/-- Canonical source-faithful compact-strip analytic surface.  The high field
retains the genuine Type-I/Type-II split; the low/principal field is unchanged
from the already compiled constructor. -/
structure CompactStripSplitAnalyticInput : Prop where
  postA5HighStripSplit : PostA5HighStripSplitReduction
  lowStripOrPrincipal : FixedPrimitiveLowStripOrPrincipalDensity

/-- Shortest fixed-primitive constructor through the source-faithful split. -/
theorem fixedPrimitivePolylogDensity_of_guthMaynard_and_split
    (hanalytic : CompactStripSplitAnalyticInput)
    (hGM : GuthMaynardTheorem11) :
    CGLPolylogBypass.FixedPrimitivePolylogDensity :=
  fixedPrimitivePolylogDensity_of_components
    hanalytic.lowStripOrPrincipal
    (fixedPrimitiveHighStripDensity_of_guthMaynard_and_splitReduction
      hGM hanalytic.postA5HighStripSplit)

/-- Project-facing compact-strip density constructor with no Type-II common
polynomial premise. -/
theorem polylogConductorDensity_of_guthMaynard_and_split
    (hanalytic : CompactStripSplitAnalyticInput)
    (hGM : GuthMaynardTheorem11) :
    PolylogConductorDensity :=
  CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target
    (fixedPrimitivePolylogDensity_of_guthMaynard_and_split hanalytic hGM)

end

end CGLCompactStripSplitDensityConstructor

#print axioms CGLCompactStripSplitDensityConstructor.typeII_exponent_with_reserve_le
#print axioms CGLCompactStripSplitDensityConstructor.fixedPrimitiveHighStripDensity_of_splitReduction
#print axioms CGLCompactStripSplitDensityConstructor.fixedPrimitiveHighStripDensity_of_guthMaynard_and_splitReduction
#print axioms CGLCompactStripSplitDensityConstructor.fixedPrimitivePolylogDensity_of_guthMaynard_and_split
#print axioms CGLCompactStripSplitDensityConstructor.polylogConductorDensity_of_guthMaynard_and_split
