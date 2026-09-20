import PostA5RecenteredTypeIExtractor
import PostA5RecenteredSourceBudget
import PostA5LongSpacingAssembly
import CGLCompactStripSplitDensityConstructor
import McCurleyPrimitiveLowPredicate

/-!
# Repaired high-strip split assembly

Finite assembly of the recentered Type-I common polynomial and the direct
source-normalized Type-II fourth-moment branch.  The Type-II branch is never
replaced by a common polynomial.
-/

namespace PostA5HighStripSplitAssembly

open Filter Set
open scoped BigOperators FourierTransform
open CGLProofDAG DirichletZeros MAPAppendixA4PostA5SetAdapter
open MAPAppendixA4DetectorDichotomy
open MAPAppendixA4RecenteredGammaRepair
open PostA5TypeIFourierAssembly PostA5TypeIOrdinateRecentering
open PostA5TypeIFourierTailAbsorption PostA5RecenteredTypeIExtractor
open PostA5RecenteredSourceSplit PostA5TypeIIFourthMoment
open PostA5LongSpacingAssembly PostA5CrowdingDeterministic
open SchwartzMap

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Choice adapter for the repaired source-normalized Type-II fiber. -/
theorem exists_sourceTypeII_shift_assignment
    (chi : DirichletCharacter ℂ q) {U : ℕ} {Y R V : ℝ}
    {Z S : Finset ℂ}
    (hS : S ⊆ postA5SourceTypeIISet chi U Y R V Z) :
    ∃ shift : ℂ → ℝ, ∀ rho ∈ S,
      shift rho ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R) ∧
      V / (29 * Real.rpow Y (1 / 2 - rho.re) *
          (2 * Real.sqrt U)) ≤
        ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) +
            (rho.im + shift rho) * Complex.I)‖ := by
  classical
  have hwitness : ∀ rho ∈ S,
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R),
        V / (29 * Real.rpow Y (1 / 2 - rho.re) *
            (2 * Real.sqrt U)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)‖ := by
    intro rho hrho
    exact (mem_postA5SourceTypeIISet_iff chi U Y R V Z rho).mp
      (hS hrho) |>.2
  let shift : ℂ → ℝ := fun rho =>
    if hrho : rho ∈ S then Classical.choose (hwitness rho hrho) else 0
  refine ⟨shift, ?_⟩
  intro rho hrho
  dsimp [shift]
  rw [dif_pos hrho]
  exact Classical.choose_spec (hwitness rho hrho)

/-- A set separated by at least `3B`, with `B≥1`, contains at most one point
in each unit floor bin. -/
theorem floorBin_card_le_one_of_threeSeparated
    (S : Finset ℂ) {B : ℝ} (hB : 1 ≤ B)
    (hsep : ∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
      3 * B ≤ |rho.im - rho'.im|) (m : ℤ) :
    (S.filter fun rho => Int.floor rho.im = m).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro rho hrho rho' hrho'
  have hrhoS : rho ∈ S := (Finset.mem_filter.mp hrho).1
  have hrho'S : rho' ∈ S := (Finset.mem_filter.mp hrho').1
  have hfloor : Int.floor rho.im = Int.floor rho'.im :=
    (Finset.mem_filter.mp hrho).2.trans
      (Finset.mem_filter.mp hrho').2.symm
  by_contra hne
  have hgap := hsep rho hrhoS rho' hrho'S hne
  have hlo : ((Int.floor rho.im : ℤ) : ℝ) ≤ rho.im := Int.floor_le _
  have hhi : rho.im < ((Int.floor rho.im : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hlo' : ((Int.floor rho'.im : ℤ) : ℝ) ≤ rho'.im := Int.floor_le _
  have hhi' : rho'.im < ((Int.floor rho'.im : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  rw [hfloor] at hlo hhi
  have habs : |rho.im - rho'.im| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  linarith

def shellNormalizedCoefficient
    (b : ℕ → ℂ) (D : ℕ) (scale : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc D (2 * D) then (scale : ℂ) * b n else 0

theorem norm_shellNormalizedCoefficient_le_one
    (b : ℕ → ℂ) {D : ℕ} {scale L : ℝ}
    (hscale : 0 ≤ scale) (hL : 0 ≤ L)
    (hscaleL : scale * L ≤ 1)
    (hb : ∀ n ∈ Finset.Ioc D (2 * D), ‖b n‖ ≤ L) :
    ∀ n, ‖shellNormalizedCoefficient b D scale n‖ ≤ 1 := by
  intro n
  unfold shellNormalizedCoefficient
  split_ifs with hn
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hscale]
    exact (mul_le_mul_of_nonneg_left (hb n hn) hscale).trans hscaleL
  · simp

theorem dirichletPolynomial_shellNormalizedCoefficient
    (b : ℕ → ℂ) (D : ℕ) {scale : ℝ} (hscale : 0 ≤ scale) (t : ℝ) :
    ‖dirichletPolynomial (shellNormalizedCoefficient b D scale) D t‖ =
      scale * ‖dirichletPolynomial b D t‖ := by
  unfold dirichletPolynomial shellNormalizedCoefficient
  rw [show (∑ n ∈ Finset.Ioc D (2 * D),
      (if n ∈ Finset.Ioc D (2 * D) then
          (scale : ℂ) * b n else 0) *
        Complex.exp (Complex.I * (t * Real.log n))) =
      (scale : ℂ) *
        ∑ n ∈ Finset.Ioc D (2 * D),
          b n * Complex.exp (Complex.I * (t * Real.log n)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos hn]
    ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hscale]

theorem detectorCommonCoefficient_shell_bound
    (chi : DirichletCharacter ℂ q) {U N D : ℕ} {Y sigma e Kd : ℝ}
    (hY : 0 < Y) (hD : 1 ≤ D) (hsigma : 0 ≤ sigma)
    (he : 0 ≤ e) (hKd : 0 ≤ Kd)
    (hdiv : ∀ n : ℕ, 0 < n →
      (orderedDivisorCount 2 n : ℝ) ≤ Kd * Real.rpow n e) :
    ∀ n ∈ Finset.Ioc D (2 * D),
      ‖detectorCommonCoefficient chi U N Y sigma n‖ ≤
        Real.rpow D (-sigma) * (Kd * Real.rpow (2 * D) e) := by
  intro n hn
  have hnD : (D : ℝ) ≤ n := by
    exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
  have hnUpper : (n : ℝ) ≤ 2 * D := by
    exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have htwoD0 : (0 : ℝ) ≤ 2 * D := by positivity
  have hpowNeg : Real.rpow n (-sigma) ≤ Real.rpow D (-sigma) :=
    Real.rpow_le_rpow_of_nonpos hDpos hnD (neg_nonpos.mpr hsigma)
  have hpowPos : Real.rpow n e ≤ Real.rpow (2 * D) e :=
    Real.rpow_le_rpow hn0 hnUpper he
  calc
    ‖detectorCommonCoefficient chi U N Y sigma n‖ ≤
        Real.rpow n (-sigma) * orderedDivisorCount 2 n :=
      norm_detectorCommonCoefficient_le chi U N hY sigma hnpos
    _ ≤ Real.rpow D (-sigma) * (Kd * Real.rpow n e) := by
      calc
        Real.rpow n (-sigma) * orderedDivisorCount 2 n ≤
            Real.rpow D (-sigma) * orderedDivisorCount 2 n :=
          mul_le_mul_of_nonneg_right hpowNeg (Nat.cast_nonneg _)
        _ ≤ Real.rpow D (-sigma) * (Kd * Real.rpow n e) :=
          mul_le_mul_of_nonneg_left (hdiv n hnpos)
            (Real.rpow_nonneg hDpos.le _)
    _ ≤ Real.rpow D (-sigma) *
        (Kd * Real.rpow (2 * D) e) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpowPos hKd)
        (Real.rpow_nonneg hDpos.le _)

/-- Apply the canonical nonprincipal fourth moment to the actual shifted
Type-II image.  The source zero ordinates are `3B`-separated and each shift
has size at most `B`; the resulting image is one-separated and lies in the
literal enlarged interval `[-2T,2T]`. -/
theorem sourceTypeII_shifted_moment_of_nonprincipalFourthMoment
    (hfourth :
      FixedCharacterFourthMomentFromAFE.NonprincipalFixedCharacterDiscreteFourthMoment)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Cfourth Tfourth : ℝ, 0 < Cfourth ∧ 2 ≤ Tfourth ∧
      ∀ (T B : ℝ) (r : ℕ) [NeZero r]
        (chi : DirichletCharacter ℂ r),
        chi.IsPrimitive → chi ≠ 1 →
        ∀ (S : Finset ℂ) (shift : ℂ → ℝ),
        0 ≤ T → 1 ≤ B → B ≤ T → Tfourth ≤ 2 * T →
        (∀ rho ∈ S, |rho.im| ≤ T) →
        (∀ rho ∈ S, |shift rho| ≤ B) →
        (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
          3 * B ≤ |rho.im - rho'.im|) →
        (∑ t ∈ S.image (fun rho => rho.im + shift rho),
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
          Cfourth * Real.rpow ((r : ℝ) * (2 * T)) (1 + epsilon) := by
  obtain ⟨Cfourth, Tfourth, hCfourth, hTfourth, hsource⟩ :=
    hfourth epsilon hepsilon
  refine ⟨Cfourth, Tfourth, hCfourth, hTfourth, ?_⟩
  intro T B r _inst chi hprimitive hchi S shift hT hB hBT hTsource
    hheight hshift hsep
  have hspacing := shifted_image_oneSeparated_and_card S Complex.im shift
    hB hshift hsep
  apply hsource (2 * T) r chi
    (S.image fun rho => rho.im + shift rho) hTsource hprimitive hchi hspacing.1
  intro t ht
  rw [Finset.mem_image] at ht
  obtain ⟨rho, hrho, rfl⟩ := ht
  calc
    |rho.im + shift rho| ≤ |rho.im| + |shift rho| := abs_add_le _ _
    _ ≤ T + B := add_le_add (hheight rho hrho) (hshift rho hrho)
    _ ≤ 2 * T := by linarith

/-- Exact normalization ledger for Type I.  All asymptotic work is reduced
to the single positive cost bound in `hcost`; the `D^sigma` normalization
cancels literally against `D^-sigma`. -/
theorem normalized_typeI_threshold_of_cost
    {T D J Kd e h dDet dOut : ℝ}
    (hT : 0 < T) (hD : 0 < D) (hJ : 0 < J) (hKd : 0 < Kd)
    (hcost : 96 * Real.rpow T h * J * Kd * Real.rpow (2 * D) e ≤
      Real.rpow T (dOut - dDet)) :
    Real.rpow D sigma * Real.rpow T (-dOut) ≤
      (Real.rpow D (-sigma) * (Kd * Real.rpow (2 * D) e))⁻¹ *
        (Real.rpow T (-dDet) / (4 * (24 * Real.rpow T h) * J)) := by
  have htwoD : 0 < 2 * D := mul_pos (by norm_num) hD
  have hLpos : 0 < Real.rpow D (-sigma) *
      (Kd * Real.rpow (2 * D) e) :=
    mul_pos (Real.rpow_pos_of_pos hD _)
      (mul_pos hKd (Real.rpow_pos_of_pos htwoD _))
  have hdenpos : 0 < 4 * (24 * Real.rpow T h) * J :=
    mul_pos (mul_pos (by norm_num)
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos hT _))) hJ
  rw [show (Real.rpow D (-sigma) *
      (Kd * Real.rpow (2 * D) e))⁻¹ *
        (Real.rpow T (-dDet) / (4 * (24 * Real.rpow T h) * J)) =
      (Real.rpow T (-dDet) / (4 * (24 * Real.rpow T h) * J)) /
        (Real.rpow D (-sigma) * (Kd * Real.rpow (2 * D) e)) by ring]
  apply (le_div_iff₀ hLpos).2
  apply (le_div_iff₀ hdenpos).2
  have hpowcost := mul_le_mul_of_nonneg_left hcost
    (Real.rpow_nonneg hT.le (-dOut))
  have hTcombine : Real.rpow T (-dOut) *
      Real.rpow T (dOut - dDet) = Real.rpow T (-dDet) := by
    calc
      Real.rpow T (-dOut) * Real.rpow T (dOut - dDet) =
          Real.rpow T ((-dOut) + (dOut - dDet)) :=
        (Real.rpow_add hT _ _).symm
      _ = Real.rpow T (-dDet) := by congr 1 <;> ring
  have hDcancel : Real.rpow D sigma * Real.rpow D (-sigma) = 1 := by
    calc
      Real.rpow D sigma * Real.rpow D (-sigma) =
          Real.rpow D (sigma + -sigma) := (Real.rpow_add hD _ _).symm
      _ = 1 := by simp
  calc
    Real.rpow D sigma * Real.rpow T (-dOut) *
          (Real.rpow D (-sigma) * (Kd * Real.rpow (2 * D) e)) *
          (4 * (24 * Real.rpow T h) * J) =
        Real.rpow T (-dOut) *
          (96 * Real.rpow T h * J * Kd * Real.rpow (2 * D) e) := by
      rw [show Real.rpow D sigma * Real.rpow T (-dOut) *
          (Real.rpow D (-sigma) * (Kd * Real.rpow (2 * D) e)) *
          (4 * (24 * Real.rpow T h) * J) =
        (Real.rpow D sigma * Real.rpow D (-sigma)) *
          (Real.rpow T (-dOut) *
            (96 * Real.rpow T h * J * Kd * Real.rpow (2 * D) e)) by ring,
        hDcancel, one_mul]
    _ ≤ Real.rpow T (-dOut) * Real.rpow T (dOut - dDet) := hpowcost
    _ = Real.rpow T (-dDet) := hTcombine

/-- The natural Type-I collar expression is bounded by one common scalar
cost times `1+|W|`. -/
theorem typeI_natural_ledger_of_cost
    {P J C : ℕ} {T eta A : ℝ}
    (hcost : ((P * J *
      (4 * shiftedFloorWindowCount C + 2 * (C + 1)) : ℕ) : ℝ) ≤
        A * Real.rpow T eta) (W : Finset ℝ) :
    ((P * J *
      (4 * (shiftedFloorWindowCount C * 1) * W.card +
        2 * (C + 1) * 1) : ℕ) : ℝ) ≤
      A * Real.rpow T eta * (1 + (W.card : ℝ)) := by
  have hnat :
      4 * (shiftedFloorWindowCount C * 1) * W.card +
          2 * (C + 1) * 1 ≤
        (4 * shiftedFloorWindowCount C + 2 * (C + 1)) *
          (1 + W.card) := by
    let s := shiftedFloorWindowCount C
    have hadd :
        4 * s * W.card + 2 * (C + 1) ≤
          (4 * s * W.card + 2 * (C + 1)) +
            (4 * s + 2 * (C + 1) * W.card) :=
      Nat.le_add_right _ _
    dsimp [s] at hadd
    convert hadd using 1 <;> ring
  have hcast :
      ((P * J *
        (4 * (shiftedFloorWindowCount C * 1) * W.card +
          2 * (C + 1) * 1) : ℕ) : ℝ) ≤
        ((P * J * (4 * shiftedFloorWindowCount C +
          2 * (C + 1)) : ℕ) : ℝ) * (1 + (W.card : ℝ)) := by
    have hnatR :
        ((4 * (shiftedFloorWindowCount C * 1) * W.card +
          2 * (C + 1) * 1 : ℕ) : ℝ) ≤
        (((4 * shiftedFloorWindowCount C + 2 * (C + 1)) *
          (1 + W.card) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hnatR ⊢
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hnatR (Nat.cast_nonneg J))
      (Nat.cast_nonneg P)
    simpa only [mul_assoc] using hmul
  exact hcast.trans (mul_le_mul_of_nonneg_right hcost (by positivity))

/-- Exact finite two-branch weld.  All set partition, long-spacing,
multiplicity, collar, coefficient normalization, and cardinal arithmetic is
proved here.  The only branch estimate supplied by the caller is the literal
fourth moment of the actual shifted Type-II ordinate image; the three final
real inequalities are the subsequent power/polylog ledger. -/
theorem finite_highStrip_split_witness
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {kappaDet etaDet kappaOut etaOut e h T sigma Y R V Kd Mfourth AZI AZII : ℝ}
    {U P C : ℕ} (Z0 : Finset ℂ)
    (hT : 4 ≤ T) (hY : 1 ≤ Y) (hR : 0 < R)
    (hU : 1 ≤ U) (hV : 0 < V) (he : 0 < e) (hKd : 0 < Kd)
    (hkappaDet : 0 < kappaDet) (hetaDet : 0 < etaDet)
    (hkappaOut : 0 < kappaOut) (hetaOut : 0 < etaOut) (hh : 0 < h)
    (hzero : ∀ rho ∈ Z0, DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ rho ∈ Z0, sigma ≤ rho.re)
    (hbetaSeven : 7 / 10 ≤ sigma) (hbetaFour : sigma ≤ 4 / 5)
    (hbetaHigh : ∀ rho ∈ Z0, rho.re ≤ 1)
    (hheight : ∀ rho ∈ Z0, |rho.im| ≤ T)
    (hsep : ∀ rho ∈ Z0, ∀ rho' ∈ Z0, rho ≠ rho' →
      3 * detectorVerticalCutoff R ≤ |rho.im - rho'.im|)
    (hcountThin : dirichletZeroCount chi sigma T ≤ P * Z0.card)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : ∀ rho ∈ Z0,
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R + V + V ≤
        Real.exp (-(1 / Y)))
    (hVR : V = Real.rpow R (-inputLoss kappaDet etaDet))
    (hVlower : Real.rpow T (-inputLoss kappaDet etaDet) ≤ V)
    (hDtime : ∀ j : Fin (detectorDyadicCount
      (detectorArithmeticCutoff Y R)), ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ T)
    (hJtime : (detectorDyadicCount
      (detectorArithmeticCutoff Y R) : ℝ) ≤ 2 * T)
    (hC : 2 * Real.pi * Real.rpow T h ≤ C)
    (htail : ∀ (j : Fin (detectorDyadicCount
        (detectorArithmeticCutoff Y R))) (rho : ℂ),
      sigma ≤ rho.re → rho.re ≤ 1 →
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U
            (detectorArithmeticCutoff Y R) Y sigma n‖) *
        (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        (V / (detectorDyadicCount
          (detectorArithmeticCutoff Y R) : ℝ)) / 2)
    (hdiv : ∀ n : ℕ, 0 < n →
      (orderedDivisorCount 2 n : ℝ) ≤ Kd * Real.rpow n e)
    (hUoutLow : Real.rpow T kappaOut ≤ U)
    (hUoutHigh : (U : ℝ) ≤
      Real.rpow T (1 / 2) * (Real.log T) ^ 2)
    (hNlow : ∀ (j : Fin (detectorDyadicCount
        (detectorArithmeticCutoff Y R))) (rho : ℂ),
      rho ∈ Z0 →
      V ≤ (detectorDyadicCount (detectorArithmeticCutoff Y R) : ℝ) *
        ‖arithmeticDetectorDyadicBlock chi U
          (detectorArithmeticCutoff Y R) rho Y j‖ →
      Real.rpow T kappaOut ≤ (2 ^ (j : ℕ) : ℕ))
    (hNhigh : ∀ j : Fin (detectorDyadicCount
      (detectorArithmeticCutoff Y R)),
      ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤
        Real.rpow T (1 / 2) * (Real.log T) ^ 2)
    (hthreshold : ∀ j : Fin (detectorDyadicCount
      (detectorArithmeticCutoff Y R)),
      let D : ℕ := 2 ^ (j : ℕ)
      let L : ℝ := Real.rpow D (-sigma) *
        (Kd * Real.rpow (2 * D) e)
      Real.rpow D sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
        L⁻¹ * (V /
          (4 * (24 * Real.rpow T h) *
            detectorDyadicCount (detectorArithmeticCutoff Y R))))
    (hmoment : ∀ (shift : ℂ → ℝ) (SII : Finset ℂ),
      SII ⊆ postA5SourceTypeIISet chi U Y R V Z0 →
      (∀ rho ∈ SII,
        shift rho ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R)) →
      (∑ t ∈ SII.image (fun rho => rho.im + shift rho),
        ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤ Mfourth)
    (hZIledger : ∀ (j : Fin (detectorDyadicCount
        (detectorArithmeticCutoff Y R))) (W : Finset ℝ),
      ((P * detectorDyadicCount (detectorArithmeticCutoff Y R) *
        (4 * (shiftedFloorWindowCount C * 1) * W.card +
          2 * (C + 1) * 1) : ℕ) : ℝ) ≤
        AZI * Real.rpow T etaOut * (1 + (W.card : ℝ)))
    (hZIIledger : (P : ℝ) *
      (Mfourth /
        (V / (29 * Real.rpow Y (1 / 2 - sigma) *
          (2 * Real.sqrt U))) ^ 4) ≤
      AZII * Real.rpow T
        (2 * (1 - sigma) + 2 * kappaOut + etaOut)) :
    ∃ (Nout : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) (ZI ZII : ℕ),
      Real.rpow T kappaOut ≤ Nout ∧
      (Nout : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
      (∀ n, ‖b n‖ ≤ 1) ∧
      OneSeparated W ∧
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W,
        Real.rpow Nout sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
          ‖dirichletPolynomial b Nout t‖) ∧
      dirichletZeroCount chi sigma T ≤ ZI + ZII ∧
      (ZI : ℝ) ≤ AZI * Real.rpow T etaOut * (1 + (W.card : ℝ)) ∧
      (ZII : ℝ) ≤ AZII * Real.rpow T
        (2 * (1 - sigma) + 2 * kappaOut + etaOut) := by
  classical
  let Ncut := detectorArithmeticCutoff Y R
  let ZIset := postA5TypeISet chi U Y R V Z0
  let ZIIset := postA5SourceTypeIISet chi U Y R V Z0
  have hbudget' : ∀ rho ∈ Z0,
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R +
          Real.rpow R (-inputLoss kappaDet etaDet) +
          Real.rpow R (-inputLoss kappaDet etaDet) ≤
        Real.exp (-(1 / Y)) := by
    intro rho hrho
    rw [← hVR]
    exact hbudget rho hrho
  have hbetaLow' : ∀ rho ∈ Z0, 7 / 10 ≤ rho.re := by
    intro rho hrho
    exact hbetaSeven.trans (hbetaLow rho hrho)
  obtain ⟨j, S1, hS1, hcardI, hblock, hcardSplit⟩ :=
    post_A5_budgeted_zeroSet_common_dyadic_or_sourceTypeII_polynomial_height
      chi hchi hkappaDet hetaDet hU hY hR hzero hbetaLow' hbetaHigh hUN hB hbudget'
  have hS1Z0 : S1 ⊆ Z0 := by
    intro rho hrho
    have hziset : rho ∈ postA5TypeISet chi U Y R
        (Real.rpow R (-inputLoss kappaDet etaDet)) Z0 := hS1 hrho
    exact (Finset.mem_filter.mp hziset).1
  have hS1source : ∀ m : ℤ,
      ∑ rho ∈ S1 with Int.floor rho.im = m, (1 : ℕ) ≤ 1 := by
    intro m
    simp only [Finset.sum_const, Nat.smul_one_eq_cast]
    exact floorBin_card_le_one_of_threeSeparated S1 hB
      (fun rho hrho rho' hrho' hne =>
        hsep rho (hS1Z0 hrho) rho' (hS1Z0 hrho') hne) m
  have hD : 1 ≤ 2 ^ (j : ℕ) := Nat.one_le_two_pow
  have hmass : ∀ rho ∈ endpointInterior S1 T C,
      (∫ xi in Set.Icc (-(Real.rpow T h)) (Real.rpow T h),
        ‖((𝓕 (detectorRealPartCutoff
          (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        24 * Real.rpow T h := by
    intro rho hrho
    have hrhoS : rho ∈ S1 := Finset.filter_subset _ _ hrho
    have hrhoZ : rho ∈ Z0 := hS1Z0 hrhoS
    apply integral_norm_fourier_detectorRealPartCutoff_Icc_le hD
    · exact sub_nonneg.mpr (hbetaLow rho hrhoZ)
    · linarith [hbetaHigh rho hrhoZ]
    · exact Real.rpow_nonneg (by linarith : 0 ≤ T) _
  obtain ⟨braw, W, hbraw, hWsep, hWheight, hWlarge, hS1card⟩ :=
    exists_typeI_commonPolynomial_oneSeparated_recentered_with_collar
      chi hU Y sigma j S1 (fun _ => 1) hC
      (fun rho hrho => hheight rho (hS1Z0 hrho))
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)) hV
      hmass
      (fun rho hrho => htail j rho
        (hbetaLow rho (hS1Z0 (Finset.filter_subset _ _ hrho)))
        (hbetaHigh rho (hS1Z0 (Finset.filter_subset _ _ hrho))))
      (fun rho hrho => by
        rw [hVR]
        exact hblock rho hrho)
      hS1source
  let D : ℕ := 2 ^ (j : ℕ)
  let L : ℝ := Real.rpow D (-sigma) *
    (Kd * Real.rpow (2 * D) e)
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hLpos : 0 < L := by
    dsimp [L]
    exact mul_pos (Real.rpow_pos_of_pos hDpos _)
      (mul_pos hKd (Real.rpow_pos_of_pos (by positivity) _))
  let scale : ℝ := L⁻¹
  have hscale : 0 ≤ scale := inv_nonneg.mpr hLpos.le
  have hscaleL : scale * L ≤ 1 := by
    dsimp [scale]
    rw [inv_mul_cancel₀ hLpos.ne']
  let b : ℕ → ℂ := shellNormalizedCoefficient braw D scale
  have hb : ∀ n, ‖b n‖ ≤ 1 := by
    apply norm_shellNormalizedCoefficient_le_one braw hscale hLpos.le hscaleL
    intro n hn
    rw [hbraw n]
    dsimp [L, D]
    exact detectorCommonCoefficient_shell_bound chi (by linarith) hD
      (by linarith) he.le hKd.le hdiv n hn
  have hWlarge' : ∀ t ∈ W,
      Real.rpow D sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
        ‖dirichletPolynomial b D t‖ := by
    intro t ht
    calc
      Real.rpow D sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
          scale * (V / (4 * (24 * Real.rpow T h) *
            detectorDyadicCount (detectorArithmeticCutoff Y R))) := by
        simpa [D, L, scale] using hthreshold j
      _ ≤ scale * ‖dirichletPolynomial braw D t‖ := by
        exact mul_le_mul_of_nonneg_left (by simpa [D] using hWlarge t ht) hscale
      _ = ‖dirichletPolynomial b D t‖ := by
        symm
        exact dirichletPolynomial_shellNormalizedCoefficient braw D hscale t
  have hZIIsetSub : ZIIset ⊆
      postA5SourceTypeIISet chi U Y R V Z0 := by
    intro rho hrho
    simpa [ZIIset] using hrho
  obtain ⟨shift, hshiftChoice⟩ :=
    exists_sourceTypeII_shift_assignment chi hZIIsetSub
  have hshiftAbs : ∀ rho ∈ ZIIset,
      |shift rho| ≤ detectorVerticalCutoff R := by
    intro rho hrho
    exact abs_le.mpr (hshiftChoice rho hrho).1
  have hZIIbeta : ∀ rho ∈ ZIIset, sigma ≤ rho.re := by
    intro rho hrho
    have hrhoZ : rho ∈ Z0 := by
      have := (mem_postA5SourceTypeIISet_iff chi U Y R V Z0 rho).mp
        (hZIIsetSub hrho)
      exact this.1
    exact hbetaLow rho hrhoZ
  have hZIIsep : ∀ rho ∈ ZIIset, ∀ rho' ∈ ZIIset, rho ≠ rho' →
      3 * detectorVerticalCutoff R ≤ |rho.im - rho'.im| := by
    intro rho hrho rho' hrho' hne
    apply hsep rho
    · exact (mem_postA5SourceTypeIISet_iff chi U Y R V Z0 rho).mp
        (hZIIsetSub hrho) |>.1
    · exact (mem_postA5SourceTypeIISet_iff chi U Y R V Z0 rho').mp
        (hZIIsetSub hrho') |>.1
    · exact hne
  have hmoment' := hmoment shift ZIIset hZIIsetSub
    (fun rho hrho => (hshiftChoice rho hrho).1)
  have hZIIcard : (ZIIset.card : ℝ) ≤
      Mfourth / (V / (29 * Real.rpow Y (1 / 2 - sigma) *
        (2 * Real.sqrt U))) ^ 4 :=
    typeII_card_le_of_shifted_fourthMoment chi ZIIset shift hB hU hY hV
      hshiftAbs hZIIsep hZIIbeta
      (fun rho hrho => (hshiftChoice rho hrho).2) hmoment'
  let typeICost : ℕ :=
    4 * (shiftedFloorWindowCount C * 1) * W.card + 2 * (C + 1) * 1
  let ZIout : ℕ := P * detectorDyadicCount (detectorArithmeticCutoff Y R) * typeICost
  let ZIIout : ℕ := P * ZIIset.card
  have hS1card' : S1.card ≤ typeICost := by
    simpa [typeICost] using hS1card
  have hcardI' : ZIset.card ≤
      detectorDyadicCount (detectorArithmeticCutoff Y R) * S1.card := by
    dsimp [ZIset]
    rw [hVR]
    exact hcardI
  have hcardSplit' : Z0.card ≤ ZIset.card + ZIIset.card := by
    dsimp [ZIset, ZIIset]
    rw [hVR]
    exact hcardSplit
  have hcount : dirichletZeroCount chi sigma T ≤ ZIout + ZIIout := by
    calc
      dirichletZeroCount chi sigma T ≤ P * Z0.card := hcountThin
      _ ≤ P * (ZIset.card + ZIIset.card) :=
        Nat.mul_le_mul_left P hcardSplit'
      _ ≤ P *
          (detectorDyadicCount (detectorArithmeticCutoff Y R) * S1.card +
            ZIIset.card) := by
        exact Nat.mul_le_mul_left P (Nat.add_le_add_right hcardI' _)
      _ ≤ P *
          (detectorDyadicCount (detectorArithmeticCutoff Y R) * typeICost +
            ZIIset.card) := by
        gcongr
      _ = ZIout + ZIIout := by
        dsimp [ZIout, ZIIout]
        ring
  have hZIIoutBound : (ZIIout : ℝ) ≤ AZII * Real.rpow T
      (2 * (1 - sigma) + 2 * kappaOut + etaOut) := by
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    dsimp [ZIIout]
    push_cast
    exact (mul_le_mul_of_nonneg_left hZIIcard hP0).trans hZIIledger
  by_cases hS1ne : S1.Nonempty
  · obtain ⟨rho, hrho⟩ := hS1ne
    refine ⟨D, b, W, ZIout, ZIIout, ?_, ?_, hb, hWsep, hWheight,
      hWlarge', hcount, ?_, hZIIoutBound⟩
    · simpa [D] using hNlow j rho (hS1Z0 hrho) (by
        rw [hVR]
        exact hblock rho hrho)
    · simpa [D] using hNhigh j
    · simpa [ZIout, typeICost] using hZIledger j W
  · have hS1empty : S1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS1ne
    have hZIempty : ZIset.card = 0 := by
      have hcardI'' := hcardI'
      rw [hS1empty] at hcardI''
      simp only [Finset.card_empty, mul_zero] at hcardI''
      omega
    have hZ0toII : Z0.card ≤ ZIIset.card := by
      rw [hZIempty, zero_add] at hcardSplit'
      exact hcardSplit'
    have hcountEmpty : dirichletZeroCount chi sigma T ≤ ZIIout := by
      calc
        dirichletZeroCount chi sigma T ≤ P * Z0.card := hcountThin
        _ ≤ P * ZIIset.card := Nat.mul_le_mul_left P hZ0toII
        _ = ZIIout := rfl
    refine ⟨U, fun _ => 0, ∅, 0, ZIIout, hUoutLow, hUoutHigh,
      ?_, ?_, ?_, ?_, ?_, ?_, hZIIoutBound⟩
    · simp
    · intro t ht
      simp at ht
    · intro t ht
      simp at ht
    · intro t ht
      simp at ht
    · simpa using hcountEmpty
    · have hzeroLedger := hZIledger j (∅ : Finset ℝ)
      norm_num at hzeroLedger ⊢
      have hlhs : (0 : ℝ) ≤
          (P : ℝ) * detectorDyadicCount (detectorArithmeticCutoff Y R) *
            (2 * ((C : ℝ) + 1)) := by positivity
      exact hlhs.trans hzeroLedger

end
end PostA5HighStripSplitAssembly

#print axioms PostA5HighStripSplitAssembly.exists_sourceTypeII_shift_assignment
#print axioms PostA5HighStripSplitAssembly.floorBin_card_le_one_of_threeSeparated
#print axioms PostA5HighStripSplitAssembly.norm_shellNormalizedCoefficient_le_one
#print axioms PostA5HighStripSplitAssembly.dirichletPolynomial_shellNormalizedCoefficient
#print axioms PostA5HighStripSplitAssembly.detectorCommonCoefficient_shell_bound
#print axioms PostA5HighStripSplitAssembly.sourceTypeII_shifted_moment_of_nonprincipalFourthMoment
#print axioms PostA5HighStripSplitAssembly.normalized_typeI_threshold_of_cost
#print axioms PostA5HighStripSplitAssembly.typeI_natural_ledger_of_cost
#print axioms PostA5HighStripSplitAssembly.finite_highStrip_split_witness
