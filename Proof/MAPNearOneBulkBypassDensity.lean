import MAPNearOneBulkBypassPowered
import MAPNearOneBulkBypassInterface
import MAPNearOneBulkBypassDetectorNonprincipal
import MAPNearOneBulkBypassDetectorPrincipal
import PrincipalDiscreteFourthFromContinuous

/-! The literal strengthened detector splits and the new powered window give
multiplicity-aware bulk density. The only analytic argument is the same GM
large-value theorem; both fourth-moment inputs are proved locally. -/
namespace MAPNearOneBulkBypassDensity
open DirichletZeros ZeroDensityInterface MAPAPZeroDensityCert MAPGuthMaynard
open CGLProofDAG FixedCharacterPoweredBridge
open CGLCompactStripDensityConstructor CGLCompactStripSplitDensityConstructor
open PostA5TypeICoefficientProvenance MAPPrincipalZetaCompactCrowding
open MAPPrincipalZetaStructuredDensity MAPNearOneBulkBypassPowered
open MAPNearOneBulkBypassInterface
noncomputable section
local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

def DetectorStructuredBulkLargeValue : Prop :=
  ∀ κ eta : ℝ, 0 < κ → 0 < eta →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T sigma : ℝ) (D : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 4 / 5 ≤ sigma → sigma ≤ 1 →
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

theorem structuredBulkLargeValue (hGM : GuthMaynardTheorem11) :
    DetectorStructuredBulkLargeValue := by
  intro κ eta hκ heta
  obtain ⟨C, T₀, hC, hT₀, hb⟩ := nearOneBulkUniformLargeValue hGM κ (eta / 2) hκ (by positivity)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T sigma D b W hT hsLow hsHigh hDlow hDhigh hcoef hsep hheight hpoly
    q _inst chi U Ncut Y scale hprov
  have hbound := hb T sigma D b W hT hsLow hsHigh hDlow hDhigh hcoef hsep hheight hpoly
  have hTone : 1 ≤ T := by linarith [hT₀.trans hT]
  have hexp : bulkExponent sigma + eta / 2 ≤ densityCoeff * (1 - sigma) + eta := by
    dsimp [bulkExponent, densityCoeff]
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hTone hexp) hC.le)

theorem nonprincipal_bulk_density
    (hsplit : MAPNearOneBulkBypassDetectorNonprincipal.PostA5HighStripStructuredSplitReduction)
    (hstructured : DetectorStructuredBulkLargeValue) :
    ∀ K delta eta : ℝ, 0 < K → 0 < delta → 0 < eta →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
          (Q : ℝ) ≤ Real.rpow (Real.log T) K →
          4 / 5 ≤ sigma → sigma ≤ 1 →
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
      hsplit' T Q sigma hTsplit' hQ (by linarith) hsigmaHigh r chi
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
theorem principal_bulk_density
    (hSplit : MAPNearOneBulkBypassDetectorPrincipal.PrincipalPostA5StructuredSplitReduction)
    (hStructured : DetectorStructuredBulkLargeValue) :
    ∀ eta : ℝ, 0 < eta →
      ∃ C Tzero : ℝ, 0 < C ∧ 2 ≤ Tzero ∧
        ∀ (T sigma : ℝ), Tzero ≤ T →
          4 / 5 ≤ sigma → sigma ≤ 1 →
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
    hsplit T sigma hTsplit' (by linarith) hsigmaHigh
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

/-- The fixed-primitive bulk output, including the conductor-one case. -/
theorem fixedPrimitiveBulkPolylogDensity_of_GM (hGM : GuthMaynardTheorem11) :
    FixedPrimitiveBulkPolylogDensity := by
  have hstructured := structuredBulkLargeValue hGM
  have hfourth := PrincipalDiscreteFourthFromContinuous.directDiscreteFourthMomentPair_proved
  have hnp := nonprincipal_bulk_density
    (MAPNearOneBulkBypassDetectorNonprincipal.postA5HighStripStructuredSplitReduction_of_nonprincipalFourthMoment hfourth.nonprincipal)
    hstructured
  have hp := principal_bulk_density
    (MAPNearOneBulkBypassDetectorPrincipal.principalPostA5StructuredSplitReduction_of_fourthMoment hfourth.principal)
    hstructured
  intro K eta hK heta
  obtain ⟨Cn, Tn, hCn, hTn, hn⟩ := hnp K 1 eta hK (by norm_num) heta
  obtain ⟨Cp, Tp, hCp, hTp, hp⟩ := hp eta heta
  refine ⟨max Cn Cp, max Tn Tp, hCn.trans_le (le_max_left _ _),
    hTn.trans (le_max_left _ _), ?_⟩
  intro T Q sigma hT hQ hsLow hsHigh r _inst chi hprim hrQ
  have hTn' : Tn ≤ T := (le_max_left _ _).trans hT
  have hTp' : Tp ≤ T := (le_max_right _ _).trans hT
  have hsOne : sigma ≤ 1 := by linarith
  have hpow : 0 ≤ Real.rpow T (densityCoeff * (1 - sigma) + eta) :=
    Real.rpow_nonneg (by linarith [hTn.trans hTn']) _
  by_cases hchi : chi = 1
  · have hr : r = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hchi,
        DirichletCharacter.conductor_one] at hprim
      exact hprim.symm
    subst r
    subst chi
    exact (hp T sigma hTp' hsLow hsOne).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · exact (hn T Q sigma hTn' hQ hsLow hsOne r chi hprim hchi hrQ).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)

end
end MAPNearOneBulkBypassDensity
#print axioms MAPNearOneBulkBypassDensity.fixedPrimitiveBulkPolylogDensity_of_GM
