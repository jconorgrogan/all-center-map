import PrincipalZetaCompactCrowding
import MontgomeryLowStripBridge
import CGLDetectorStructuredLargeValue
import CGLv2PolylogConductorDensity
import PrincipalZetaDetectorDichotomy

/-!
# Principal zeta density through the detector-structured large-value seam

The conductor-one branch does not need the full arbitrary-coefficient
Guth--Maynard theorem as a separate input.  Its literal zero detector produces
the same normalized mollifier coefficient (up to the one global translation
phase) already retained in the nonprincipal post-A.5 branch.

This file packages that strictly weaker route.  The remaining zeta-specific
analytic leaf is `PrincipalPoleRemovedStructuredDetectorReduction`: it is the
quantitative output of the pole-removed contour in
`PrincipalZetaDetectorPoleRemoval`, before any large-value theorem is applied.
It counts distinct divisor-supported zeros, exhibits one common polynomial,
and records its exact coefficient provenance.  The multiplicity restoration,
epsilon allocation, and final `30/13` density estimate are proved here.
-/

namespace MAPPrincipalZetaStructuredDensity

open Filter
open CGLProofDAG DirichletZeros MAPGuthMaynard
open MAPPrincipalZetaCompactCrowding
open PostA5TypeICoefficientProvenance
open CGLDetectorStructuredLargeValue

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- The premise-free principal multiplicity envelope is subpower. -/
theorem eventually_principal_crowding_log_le_rpow
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      1683 * Real.log (T + 3) ≤ Real.rpow T (eta / 2) := by
  have hquarter : 0 < eta / 4 := by positivity
  have hpoly := ZeroDensityArithmetic.polylog_absorption 1 (eta / 4) hquarter
  have hconst := (tendsto_rpow_atTop hquarter).eventually
    (eventually_ge_atTop (2 * 1683 : ℝ))
  filter_upwards [hpoly, hconst, eventually_ge_atTop 3]
    with T hpolyT hconstT hT
  have hTpos : 0 < T := by linarith
  have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hshiftPos : 0 < T + 3 := by linarith
  have hshift : T + 3 ≤ 2 * T := by linarith
  have hlogShift : Real.log (T + 3) ≤ 2 * Real.log T := by
    have hmono := Real.log_le_log hshiftPos hshift
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTpos.ne'] at hmono
    have hlog2 : Real.log 2 ≤ Real.log T :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hfirst :
      1683 * Real.log (T + 3) ≤
        Real.rpow T (eta / 4) * Real.rpow T (eta / 4) := by
    calc
      1683 * Real.log (T + 3) ≤
          (2 * 1683) * Real.log T := by nlinarith
      _ = (2 * 1683) * Real.rpow (Real.log T) 1 := by
        exact congrArg (fun x : ℝ => (2 * 1683) * x)
          (Real.rpow_one (Real.log T)).symm
      _ ≤ Real.rpow T (eta / 4) * Real.rpow T (eta / 4) :=
        mul_le_mul hconstT hpolyT
          (Real.rpow_nonneg hlogTpos.le _)
          (Real.rpow_nonneg hTpos.le _)
  calc
    1683 * Real.log (T + 3) ≤
        Real.rpow T (eta / 4) * Real.rpow T (eta / 4) := hfirst
    _ = Real.rpow T (eta / 2) := by
      calc
        Real.rpow T (eta / 4) * Real.rpow T (eta / 4) =
            Real.rpow T (eta / 4 + eta / 4) :=
          (Real.rpow_add hTpos _ _).symm
        _ = Real.rpow T (eta / 2) := by congr 1 <;> ring

/-- Legacy one-polynomial interface.  The certified principal A.4 argument
has a real Type-II branch, so this interface is intentionally retained only
for compatibility: pole removal alone does not inhabit it.  Any future use
must cite an additional theorem collapsing Type II to the same polynomial. -/
def PrincipalPoleRemovedStructuredDetectorReduction : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ kappa A Tdet : ℝ,
      0 < kappa ∧ kappa ≤ 1 / 2 ∧ 0 < A ∧ 2 ≤ Tdet ∧
      ∀ (T sigma : ℝ), Tdet ≤ T →
        7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        ∃ (D : ℕ) (b : ℕ → ℂ) (W : Finset ℝ)
            (U Ncut : ℕ) (Y scale : ℝ),
          Real.rpow T kappa ≤ D ∧
          (D : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
          (∀ n, ‖b n‖ ≤ 1) ∧
          OneSeparated W ∧
          (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
          (∀ t ∈ W,
            Real.rpow D sigma *
                Real.rpow T (-inputLoss kappa (epsilon / 2)) ≤
              ‖dirichletPolynomial b D t‖) ∧
          ((zeroSupport chiOne sigma T).card : ℝ) ≤
            A * Real.rpow T epsilon * (1 + (W.card : ℝ)) ∧
          IsNormalizedDetectorCoefficient
            chiOne U Ncut Y sigma D scale T b

/-- Honest conductor-one post-A.5 interface.  It preserves the one common
Type-I detector polynomial and keeps the critical-line Type-II contribution
as a separate cardinality ledger, exactly as in the nonprincipal A.4
architecture. -/
def PrincipalPostA5StructuredSplitReduction : Prop :=
  ∀ loss : ℝ, 0 < loss →
    ∃ kappa A Tdet : ℝ,
      0 < kappa ∧ kappa ≤ 1 / 2 ∧ 2 * kappa ≤ loss ∧
      0 < A ∧ 2 ≤ Tdet ∧
      ∀ (T sigma : ℝ), Tdet ≤ T →
        7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        ∃ (D : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) (ZI ZII : ℕ)
            (U Ncut : ℕ) (Y scale : ℝ),
          Real.rpow T kappa ≤ D ∧
          (D : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
          (∀ n, ‖b n‖ ≤ 1) ∧
          OneSeparated W ∧
          (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
          (∀ t ∈ W,
            Real.rpow D sigma *
                Real.rpow T (-inputLoss kappa (loss / 2)) ≤
              ‖dirichletPolynomial b D t‖) ∧
          (zeroSupport chiOne sigma T).card ≤ ZI + ZII ∧
          (ZI : ℝ) ≤ A * Real.rpow T loss * (1 + (W.card : ℝ)) ∧
          (ZII : ℝ) ≤ A * Real.rpow T
            (2 * (1 - sigma) + 2 * kappa + loss) ∧
          IsNormalizedDetectorCoefficient
            chiOne U Ncut Y sigma D scale T b

/-- The honest split plus the shared detector-structured large-value theorem
gives the exact principal high-strip density consumed by MAP.  Type II is
bounded on its own ledger; it is never renamed as a Type-I polynomial. -/
theorem principal_zeta_high_strip_density_of_structured_split
    (hSplit : PrincipalPostA5StructuredSplitReduction)
    (hStructured : DetectorStructuredThirtyThirteenLargeValue) :
    ∀ eta : ℝ, 0 < eta →
      ∃ C Tzero : ℝ, 0 < C ∧ 2 ≤ Tzero ∧
        ∀ (T sigma : ℝ), Tzero ≤ T →
          7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
          (dirichletZeroCount chiOne sigma T : ℝ) ≤
            C * Real.rpow T
              (densityCoeff * (1 - sigma) + eta) := by
  intro eta heta
  let loss : ℝ := eta / 16
  have hloss : 0 < loss := by dsimp [loss]; positivity
  obtain ⟨kappa, A, Tsplit, hkappa, _hkappaHalf, hkappaLoss,
      hA, hTsplit, hsplit⟩ := hSplit loss hloss
  obtain ⟨B, Tlarge, hB, hTlarge, hlarge⟩ :=
    hStructured kappa loss hkappa hloss
  obtain ⟨Tcrowd, hcrowd⟩ := Filter.eventually_atTop.1
    (eventually_principal_crowding_log_le_rpow eta heta)
  let C : ℝ := A * (3 + B)
  let Tzero : ℝ := max Tsplit (max Tlarge (max Tcrowd 3))
  refine ⟨C, Tzero, ?_, ?_, ?_⟩
  · dsimp [C]
    positivity
  · exact hTsplit.trans (le_max_left _ _)
  intro T sigma hT hsigmaLow hsigmaHigh
  have hTsplit' : Tsplit ≤ T := (le_max_left _ _).trans hT
  have hTlarge' : Tlarge ≤ T :=
    ((le_max_left Tlarge (max Tcrowd 3)).trans
      (le_max_right Tsplit (max Tlarge (max Tcrowd 3)))).trans hT
  have hTcrowd' : Tcrowd ≤ T :=
    (((le_max_left Tcrowd 3).trans
      (le_max_right Tlarge (max Tcrowd 3))).trans
      (le_max_right Tsplit (max Tlarge (max Tcrowd 3)))).trans hT
  have hTthree : 3 ≤ T :=
    (((le_max_right Tcrowd 3).trans
      (le_max_right Tlarge (max Tcrowd 3))).trans
      (le_max_right Tsplit (max Tlarge (max Tcrowd 3)))).trans hT
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  obtain ⟨D, b, W, ZI, ZII, U, Ncut, Y, scale,
      hDlow, hDhigh, hbcoef, hsep, hheight, hpoly, hsupport,
      hZI, hZII, hprovenance⟩ :=
    hsplit T sigma hTsplit' hsigmaLow hsigmaHigh
  have hW := hlarge T sigma D b W hTlarge' hsigmaLow hsigmaHigh
    hDlow hDhigh hbcoef hsep hheight hpoly 1 chiOne U Ncut Y scale hprovenance
  have hbaseNonneg :
      0 ≤ densityCoeff * (1 - sigma) + loss := by
    have : 0 ≤ 1 - sigma := by linarith
    dsimp [densityCoeff]
    positivity
  have honePow :
      1 ≤ Real.rpow T (densityCoeff * (1 - sigma) + loss) :=
    Real.one_le_rpow hTone hbaseNonneg
  have hOneW :
      1 + (W.card : ℝ) ≤
        (1 + B) * Real.rpow T
          (densityCoeff * (1 - sigma) + loss) := by
    calc
      1 + (W.card : ℝ) ≤
          Real.rpow T (densityCoeff * (1 - sigma) + loss) +
            B * Real.rpow T
              (densityCoeff * (1 - sigma) + loss) :=
        add_le_add honePow hW
      _ = (1 + B) * Real.rpow T
          (densityCoeff * (1 - sigma) + loss) := by ring
  have hZI' : (ZI : ℝ) ≤
      A * (1 + B) * Real.rpow T
        (densityCoeff * (1 - sigma) + 2 * loss) := by
    calc
      (ZI : ℝ) ≤ A * Real.rpow T loss * (1 + (W.card : ℝ)) := hZI
      _ ≤ A * Real.rpow T loss *
          ((1 + B) * Real.rpow T
            (densityCoeff * (1 - sigma) + loss)) := by
        exact mul_le_mul_of_nonneg_left hOneW
          (mul_nonneg hA.le (Real.rpow_nonneg hTpos.le _))
      _ = A * (1 + B) * Real.rpow T
          (densityCoeff * (1 - sigma) + 2 * loss) := by
        rw [show A * Real.rpow T loss *
            ((1 + B) * Real.rpow T
              (densityCoeff * (1 - sigma) + loss)) =
            A * (1 + B) *
              (Real.rpow T loss * Real.rpow T
                (densityCoeff * (1 - sigma) + loss)) by ring]
        congr 1
        calc
          Real.rpow T loss *
              Real.rpow T (densityCoeff * (1 - sigma) + loss) =
            Real.rpow T
              (loss + (densityCoeff * (1 - sigma) + loss)) :=
            (Real.rpow_add hTpos _ _).symm
          _ = Real.rpow T
              (densityCoeff * (1 - sigma) + 2 * loss) := by
            congr 1
            ring
  have hIIexp :
      2 * (1 - sigma) + 2 * kappa + loss ≤
        densityCoeff * (1 - sigma) + 2 * loss := by
    have hgap : 2 * (1 - sigma) ≤ densityCoeff * (1 - sigma) := by
      have hs : 0 ≤ 1 - sigma := by linarith
      dsimp [densityCoeff]
      nlinarith
    linarith
  have hZII' : (ZII : ℝ) ≤
      A * Real.rpow T
        (densityCoeff * (1 - sigma) + 2 * loss) :=
    hZII.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hTone hIIexp) hA.le)
  have hsupportReal : ((zeroSupport chiOne sigma T).card : ℝ) ≤
      (ZI : ℝ) + (ZII : ℝ) := by exact_mod_cast hsupport
  have hsupport' : ((zeroSupport chiOne sigma T).card : ℝ) ≤
      A * (2 + B) * Real.rpow T
        (densityCoeff * (1 - sigma) + 2 * loss) := by
    calc
      ((zeroSupport chiOne sigma T).card : ℝ) ≤
          (ZI : ℝ) + (ZII : ℝ) := hsupportReal
      _ ≤ A * (1 + B) * Real.rpow T
            (densityCoeff * (1 - sigma) + 2 * loss) +
          A * Real.rpow T
            (densityCoeff * (1 - sigma) + 2 * loss) :=
        add_le_add hZI' hZII'
      _ = A * (2 + B) * Real.rpow T
          (densityCoeff * (1 - sigma) + 2 * loss) := by ring
  have hcount := principal_dirichletZeroCount_le_log_mul_supportCard
    (by linarith : 0 ≤ sigma) (by linarith : 0 ≤ T)
  have hcrowdT := hcrowd T hTcrowd'
  have hexp :
      eta / 2 + (densityCoeff * (1 - sigma) + 2 * loss) ≤
        densityCoeff * (1 - sigma) + eta := by
    dsimp [loss]
    linarith
  calc
    (dirichletZeroCount chiOne sigma T : ℝ) ≤
        (1683 * Real.log (T + 3)) *
          (zeroSupport chiOne sigma T).card := hcount
    _ ≤ Real.rpow T (eta / 2) *
          (A * (2 + B) * Real.rpow T
            (densityCoeff * (1 - sigma) + 2 * loss)) := by
      exact mul_le_mul hcrowdT hsupport'
        (Nat.cast_nonneg _) (Real.rpow_nonneg hTpos.le _)
    _ = A * (2 + B) * Real.rpow T
          (eta / 2 + (densityCoeff * (1 - sigma) + 2 * loss)) := by
      rw [show Real.rpow T (eta / 2) *
          (A * (2 + B) * Real.rpow T
            (densityCoeff * (1 - sigma) + 2 * loss)) =
          A * (2 + B) *
            (Real.rpow T (eta / 2) * Real.rpow T
              (densityCoeff * (1 - sigma) + 2 * loss)) by ring]
      congr 1
      exact (Real.rpow_add hTpos _ _).symm
    _ ≤ A * (2 + B) * Real.rpow T
          (densityCoeff * (1 - sigma) + eta) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hTone hexp)
        (mul_nonneg hA.le (by positivity))
    _ ≤ C * Real.rpow T
          (densityCoeff * (1 - sigma) + eta) := by
      dsimp [C]
      have hpow0 := Real.rpow_nonneg hTpos.le
        (densityCoeff * (1 - sigma) + eta)
      have hB0 : 0 ≤ B := hB.le
      nlinarith

/-- The pole-removed structured detector plus the shared structured
large-value estimate gives the complete principal high-strip density theorem.
No arbitrary-coefficient large-value statement and no separate zeta density
theorem occur in the assumptions. -/
theorem principal_zeta_high_strip_density_of_structured_detector
    (hDetector : PrincipalPoleRemovedStructuredDetectorReduction)
    (hStructured : DetectorStructuredThirtyThirteenLargeValue) :
    ∀ eta : ℝ, 0 < eta →
      ∃ C Tzero : ℝ, 0 < C ∧ 2 ≤ Tzero ∧
        ∀ (T sigma : ℝ), Tzero ≤ T →
          7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
          (dirichletZeroCount chiOne sigma T : ℝ) ≤
            C * Real.rpow T
              (densityCoeff * (1 - sigma) + eta) := by
  intro eta heta
  have hetaFour : 0 < eta / 4 := by positivity
  obtain ⟨kappa, A, Tdet, hkappa, _hkappaHalf, hA, hTdet, hdet⟩ :=
    hDetector (eta / 4) hetaFour
  obtain ⟨B, Tlarge, hB, hTlarge, hlarge⟩ :=
    hStructured kappa (eta / 4) hkappa hetaFour
  obtain ⟨Tcrowd, hcrowd⟩ := Filter.eventually_atTop.1
    (eventually_principal_crowding_log_le_rpow eta heta)
  let C : ℝ := A * (1 + B)
  let Tzero : ℝ := max Tdet (max Tlarge (max Tcrowd 3))
  refine ⟨C, Tzero, ?_, ?_, ?_⟩
  · dsimp [C]
    positivity
  · exact hTdet.trans (le_max_left _ _)
  intro T sigma hT hsigmaLow hsigmaHigh
  have hTdet' : Tdet ≤ T := (le_max_left _ _).trans hT
  have hTlarge' : Tlarge ≤ T :=
    ((le_max_left Tlarge (max Tcrowd 3)).trans
      (le_max_right Tdet (max Tlarge (max Tcrowd 3)))).trans hT
  have hTcrowd' : Tcrowd ≤ T :=
    (((le_max_left Tcrowd 3).trans
      (le_max_right Tlarge (max Tcrowd 3))).trans
      (le_max_right Tdet (max Tlarge (max Tcrowd 3)))).trans hT
  have hTthree : 3 ≤ T :=
    (((le_max_right Tcrowd 3).trans
      (le_max_right Tlarge (max Tcrowd 3))).trans
      (le_max_right Tdet (max Tlarge (max Tcrowd 3)))).trans hT
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  obtain ⟨D, b, W, U, Ncut, Y, scale, hDlow, hDhigh, hb, hsep,
      hheight, hpoly, hsupport, hprovenance⟩ :=
    hdet T sigma hTdet' hsigmaLow hsigmaHigh
  have hW := hlarge T sigma D b W hTlarge' hsigmaLow hsigmaHigh
    hDlow hDhigh hb hsep hheight hpoly 1 chiOne U Ncut Y scale hprovenance
  have hbaseExpNonneg :
      0 ≤ densityCoeff * (1 - sigma) + eta / 4 := by
    have : 0 ≤ 1 - sigma := by linarith
    dsimp [densityCoeff]
    positivity
  have honePow :
      1 ≤ Real.rpow T (densityCoeff * (1 - sigma) + eta / 4) :=
    Real.one_le_rpow hTone hbaseExpNonneg
  have honeCard :
      1 + (W.card : ℝ) ≤
        (1 + B) * Real.rpow T
          (densityCoeff * (1 - sigma) + eta / 4) := by
    calc
      1 + (W.card : ℝ) ≤
          Real.rpow T (densityCoeff * (1 - sigma) + eta / 4) +
            B * Real.rpow T
              (densityCoeff * (1 - sigma) + eta / 4) :=
        add_le_add honePow hW
      _ = (1 + B) * Real.rpow T
          (densityCoeff * (1 - sigma) + eta / 4) := by ring
  have hsupportBound :
      ((zeroSupport chiOne sigma T).card : ℝ) ≤
        C * Real.rpow T
          (densityCoeff * (1 - sigma) + eta / 2) := by
    calc
      ((zeroSupport chiOne sigma T).card : ℝ) ≤
          A * Real.rpow T (eta / 4) * (1 + (W.card : ℝ)) := hsupport
      _ ≤ A * Real.rpow T (eta / 4) *
          ((1 + B) * Real.rpow T
            (densityCoeff * (1 - sigma) + eta / 4)) := by
        exact mul_le_mul_of_nonneg_left honeCard
          (mul_nonneg hA.le (Real.rpow_nonneg hTpos.le _))
      _ = A * (1 + B) *
          (Real.rpow T (eta / 4) *
            Real.rpow T (densityCoeff * (1 - sigma) + eta / 4)) := by ring
      _ = A * (1 + B) * Real.rpow T
          (eta / 4 + (densityCoeff * (1 - sigma) + eta / 4)) := by
        exact congrArg (fun x : ℝ => A * (1 + B) * x)
          (Real.rpow_add hTpos (eta / 4)
            (densityCoeff * (1 - sigma) + eta / 4)).symm
      _ = C * Real.rpow T
          (densityCoeff * (1 - sigma) + eta / 2) := by
        dsimp [C]
        congr 2
        ring
  have hsigmaZero : 0 ≤ sigma := by linarith
  have hcount :=
    principal_dirichletZeroCount_le_log_mul_supportCard hsigmaZero
      (by linarith : 0 ≤ T)
  have hcrowdT := hcrowd T hTcrowd'
  calc
    (dirichletZeroCount chiOne sigma T : ℝ) ≤
        (1683 * Real.log (T + 3)) *
          (zeroSupport chiOne sigma T).card := hcount
    _ ≤ Real.rpow T (eta / 2) *
          (C * Real.rpow T
            (densityCoeff * (1 - sigma) + eta / 2)) := by
      exact mul_le_mul hcrowdT hsupportBound
        (Nat.cast_nonneg _) (Real.rpow_nonneg hTpos.le _)
    _ = C * (Real.rpow T (eta / 2) *
          Real.rpow T
            (densityCoeff * (1 - sigma) + eta / 2)) := by ring
    _ = C * Real.rpow T
          (eta / 2 + (densityCoeff * (1 - sigma) + eta / 2)) := by
      exact congrArg (fun x : ℝ => C * x)
        (Real.rpow_add hTpos (eta / 2)
          (densityCoeff * (1 - sigma) + eta / 2)).symm
    _ = C * Real.rpow T
          (densityCoeff * (1 - sigma) + eta) := by
      congr 2
      ring

/-- Canonical low-strip/principal field using the shared structured
large-value input. -/
theorem fixedPrimitiveLowStripOrPrincipalDensity_of_structured_sources
    (hMontgomery : ∃ Czero : ℝ, 0 < Czero ∧
      ∀ (r : ℕ) [NeZero r] (T sigma : ℝ),
        2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 4 / 5 →
          (MAPAPZeroDensityCert.ambientZeroCountAtLevel r sigma T : ℝ) ≤
            Czero * Real.rpow ((r : ℝ) * T)
              (MAPMontgomeryLowStrip.inghamExponent sigma) *
              (Real.log ((r : ℝ) * T)) ^ 9)
    (hDetector : PrincipalPoleRemovedStructuredDetectorReduction)
    (hStructured : DetectorStructuredThirtyThirteenLargeValue) :
    CGLCompactStripDensityConstructor.FixedPrimitiveLowStripOrPrincipalDensity := by
  apply MAPMontgomeryLowStrip.fixedPrimitiveLowStripOrPrincipalDensity_of_montgomery_and_zeta
    hMontgomery
  exact principal_zeta_high_strip_density_of_structured_detector
    hDetector hStructured

/-- Canonical low-strip/principal field through the honest ZI/ZII split. -/
theorem fixedPrimitiveLowStripOrPrincipalDensity_of_honest_structured_sources
    (hMontgomery : ∃ Czero : ℝ, 0 < Czero ∧
      ∀ (r : ℕ) [NeZero r] (T sigma : ℝ),
        2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 4 / 5 →
          (MAPAPZeroDensityCert.ambientZeroCountAtLevel r sigma T : ℝ) ≤
            Czero * Real.rpow ((r : ℝ) * T)
              (MAPMontgomeryLowStrip.inghamExponent sigma) *
              (Real.log ((r : ℝ) * T)) ^ 9)
    (hSplit : PrincipalPostA5StructuredSplitReduction)
    (hStructured : DetectorStructuredThirtyThirteenLargeValue) :
    CGLCompactStripDensityConstructor.FixedPrimitiveLowStripOrPrincipalDensity := by
  apply MAPMontgomeryLowStrip.fixedPrimitiveLowStripOrPrincipalDensity_of_montgomery_and_zeta
    hMontgomery
  exact principal_zeta_high_strip_density_of_structured_split
    hSplit hStructured

/-- Any complete fixed-primitive compact-strip density theorem automatically
fills the weaker low-strip/principal field.  This projection is useful because
the CGL all-cases source already includes `q = 1`; once that source is
certified, a second principal-zeta density proof is unnecessary. -/
theorem fixedPrimitiveLowStripOrPrincipalDensity_of_fixedPrimitive
    (hfixed : CGLPolylogBypass.FixedPrimitivePolylogDensity) :
    CGLCompactStripDensityConstructor.FixedPrimitiveLowStripOrPrincipalDensity := by
  intro K delta eta hK hdelta heta
  obtain ⟨C, Tzero, hC, hTzero, hbound⟩ :=
    hfixed K delta eta hK hdelta heta
  refine ⟨C, Tzero, hC, hTzero, ?_⟩
  intro T Q sigma hT hQ hsigmaLow hsigmaHigh r _inst chi hprimitive hrQ _hcase
  exact hbound T Q sigma hT hQ hsigmaLow hsigmaHigh r chi hprimitive hrQ

/-- Fastest wall-clock route: the literal CGL v2 all-cases theorem, specialized
through its existing fixed-character adapter, already supplies the complete
low-strip/principal field including conductor one. -/
theorem fixedPrimitiveLowStripOrPrincipalDensity_of_cgl_v2
    (hCGL : CGLMeshFormalization.CGLv2Theorem12AllCases) :
    CGLCompactStripDensityConstructor.FixedPrimitiveLowStripOrPrincipalDensity :=
  fixedPrimitiveLowStripOrPrincipalDensity_of_fixedPrimitive
    (CGLMeshFormalization.fixedPrimitivePolylogDensity_of_cgl_v2 hCGL)

end
end MAPPrincipalZetaStructuredDensity

#print axioms MAPPrincipalZetaStructuredDensity.principal_zeta_high_strip_density_of_structured_detector
#print axioms MAPPrincipalZetaStructuredDensity.fixedPrimitiveLowStripOrPrincipalDensity_of_structured_sources
#print axioms MAPPrincipalZetaStructuredDensity.eventually_principal_crowding_log_le_rpow
#print axioms MAPPrincipalZetaStructuredDensity.fixedPrimitiveLowStripOrPrincipalDensity_of_fixedPrimitive
#print axioms MAPPrincipalZetaStructuredDensity.fixedPrimitiveLowStripOrPrincipalDensity_of_cgl_v2
#print axioms MAPPrincipalZetaStructuredDensity.principal_zeta_high_strip_density_of_structured_split
#print axioms MAPPrincipalZetaStructuredDensity.fixedPrimitiveLowStripOrPrincipalDensity_of_honest_structured_sources
