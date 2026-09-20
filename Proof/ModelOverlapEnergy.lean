import ShortIntervalTauFour
import MajorArcFinalAnalyticWeld
import SingularSeriesSquareMean
import AllCenterEndpointPublicWeld

/-!
# Square-energy form of the continuous-kernel/Ramanujan remainder

This file starts after the prime polynomial has been replaced by its
continuous model.  It sums the already-certified continuous-kernel estimate
and the exact Ramanujan tail on the literal translated window.  No
Siegel--Walfisz or prime-polynomial premise occurs here.
-/

namespace MAPModelOverlapEnergy

open scoped BigOperators
open PrimePairEndpoints MAPMajorArcWeld
open MAPRamanujanWindowAbsorption

noncomputable section

def modeledOverlapError (X : ℝ) (B D : ℕ) (h : ℤ) : ℂ :=
  modeledPaperMajorContribution X B D h - primePairMajorModel X h

def modeledOverlapErrorEnergy (X H h₀ : ℝ) (B D : ℕ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀,
    if h = 0 then 0 else ‖modeledOverlapError X B D h‖ ^ 2

/-- Elementary conversion used by both the kernel and Ramanujan components:
enough natural logarithmic powers dominate the requested real exponent. -/
theorem pow_div_pow_le_rpow_neg
    {L A : ℝ} {m n : ℕ}
    (hL : 1 ≤ L) (hmn : m ≤ n) (hA : A ≤ (n - m : ℕ)) :
    L ^ m / L ^ n ≤ Real.rpow L (-A) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  apply (div_le_iff₀ (pow_pos hLpos n)).2
  have hexp : (m : ℝ) ≤ -A + (n : ℝ) := by
    have hcast : A ≤ ((n - m : ℕ) : ℝ) := by exact_mod_cast hA
    have hmncast : (m : ℝ) ≤ n := by exact_mod_cast hmn
    rw [Nat.cast_sub hmn] at hcast
    linarith
  calc
    L ^ m = Real.rpow L (m : ℝ) := (Real.rpow_natCast L m).symm
    _ ≤ Real.rpow L (-A + (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL hexp
    _ = Real.rpow L (-A) * Real.rpow L (n : ℝ) :=
      Real.rpow_add hLpos (-A) (n : ℝ)
    _ = Real.rpow L (-A) * L ^ n := by
      congr 1
      exact Real.rpow_natCast L n

/-- Literal finite-energy consequence of the certified continuous kernel and
Ramanujan tail.  The only geometric premises are positivity of the arc radius
and the fact that all nonzero shifts in the window satisfy `|h| ≤ X`. -/
theorem modeledOverlapErrorEnergy_le_components
    {X H h₀ : ℝ} {B D : ℕ}
    (hX : 0 ≤ X)
    (hR : 0 < paperArcRadius X D)
    (hshift : ∀ h ∈ translatedWindow H h₀, h ≠ 0 → |(h : ℝ)| ≤ X) :
    modeledOverlapErrorEnergy X H h₀ B D ≤
      4 * (2 / (Real.pi ^ 2 * paperArcRadius X D)) ^ 2 *
          singularSquareMain H h₀ +
        (4 * (2 / (Real.pi ^ 2 * paperArcRadius X D)) ^ 2 +
            2 * X ^ 2) *
          ramanujanTailEnergy H h₀ (paperDenominatorCutoff X B) := by
  classical
  let K : ℝ := 2 / (Real.pi ^ 2 * paperArcRadius X D)
  let Q : ℕ := paperDenominatorCutoff X B
  unfold modeledOverlapErrorEnergy singularSquareMain ramanujanTailEnergy
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hhwin
  by_cases hh0 : h = 0
  · subst h
    simp [modeledOverlapError, singularSeriesTotal]
  · simp only [if_neg hh0]
    let T : ℝ :=
      ‖truncatedSingularCoefficient Q h -
        ((singularSeriesTotal h : ℝ) : ℂ)‖
    have hT : 0 ≤ T := norm_nonneg _
    have hmodel :=
      MAPMajorArcFinalAnalyticWeld.norm_modeledPaperMajorContribution_sub_overlapSingular_le
        hX (hshift h hhwin hh0) hR hT (le_rfl : T ≤ T)
    have hSsq :
        ‖((singularSeriesTotal h : ℝ) : ℂ)‖ ^ 2 =
          (singularSeriesTotal h) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hTsq :
        T ^ 2 =
          ‖truncatedSingularCoefficient Q h -
            ((singularSeriesTotal h : ℝ) : ℂ)‖ ^ 2 := rfl
    have hK0 : 0 ≤ K := by
      dsimp [K]
      positivity
    have hnorm0 : 0 ≤ ‖modeledOverlapError X B D h‖ := norm_nonneg _
    have hS0 : 0 ≤ ‖((singularSeriesTotal h : ℝ) : ℂ)‖ := norm_nonneg _
    have hA0 : 0 ≤
        K * (‖((singularSeriesTotal h : ℝ) : ℂ)‖ + T) + T * X := by
      positivity
    have hmodel' :
        ‖modeledOverlapError X B D h‖ ≤
          K * (‖((singularSeriesTotal h : ℝ) : ℂ)‖ + T) + T * X := by
      simpa [K, modeledOverlapError, primePairMajorModel, mul_comm] using hmodel
    have hsq1 :
        ‖modeledOverlapError X B D h‖ ^ 2 ≤
          (K * (‖((singularSeriesTotal h : ℝ) : ℂ)‖ + T) + T * X) ^ 2 :=
      (sq_le_sq₀ hnorm0 hA0).2 hmodel'
    have hsum :
        (‖((singularSeriesTotal h : ℝ) : ℂ)‖ + T) ^ 2 ≤
          2 * ‖((singularSeriesTotal h : ℝ) : ℂ)‖ ^ 2 + 2 * T ^ 2 := by
      nlinarith [sq_nonneg (‖((singularSeriesTotal h : ℝ) : ℂ)‖ - T)]
    have hsq2 :
        (K * (‖((singularSeriesTotal h : ℝ) : ℂ)‖ + T) + T * X) ^ 2 ≤
          2 * (K * (‖((singularSeriesTotal h : ℝ) : ℂ)‖ + T)) ^ 2 +
            2 * (T * X) ^ 2 := by
      nlinarith [sq_nonneg
        (K * (‖((singularSeriesTotal h : ℝ) : ℂ)‖ + T) - T * X)]
    have hpoint :
        ‖modeledOverlapError X B D h‖ ^ 2 ≤
          4 * K ^ 2 * ‖((singularSeriesTotal h : ℝ) : ℂ)‖ ^ 2 +
            (4 * K ^ 2 + 2 * X ^ 2) * T ^ 2 := by
      calc
        ‖modeledOverlapError X B D h‖ ^ 2 ≤
            (K * (‖((singularSeriesTotal h : ℝ) : ℂ)‖ + T) + T * X) ^ 2 := hsq1
        _ ≤ 2 * (K * (‖((singularSeriesTotal h : ℝ) : ℂ)‖ + T)) ^ 2 +
              2 * (T * X) ^ 2 := hsq2
        _ ≤ 4 * K ^ 2 * ‖((singularSeriesTotal h : ℝ) : ℂ)‖ ^ 2 +
              (4 * K ^ 2 + 2 * X ^ 2) * T ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg K)]
    simpa [K, Q, modeledOverlapError, hSsq, hTsq] using hpoint

/-- The continuous-kernel tail has the exact `X / log(X)^D` scale. -/
theorem kernelTailFactor_sq_le
    {X : ℝ} {D : ℕ} (hX : Real.exp 1 ≤ X) :
    (2 / (Real.pi ^ 2 * paperArcRadius X D)) ^ 2 ≤
      4 * X ^ 2 / (Real.log X) ^ (2 * D) := by
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hX
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog1
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hpowpos : 0 < (Real.log X) ^ D := pow_pos hlogpos D
  have heq :
      2 / (Real.pi ^ 2 * paperArcRadius X D) =
        (2 * X) / (Real.pi ^ 2 * (Real.log X) ^ D) := by
    unfold paperArcRadius
    field_simp
  have hden : (Real.log X) ^ D ≤
      Real.pi ^ 2 * (Real.log X) ^ D := by
    simpa using mul_le_mul_of_nonneg_right hpi hpowpos.le
  have hK :
      2 / (Real.pi ^ 2 * paperArcRadius X D) ≤
        (2 * X) / (Real.log X) ^ D := by
    rw [heq]
    exact div_le_div_of_nonneg_left (by positivity)
      hpowpos (by simpa [mul_comm] using hden)
  have hK0 : 0 ≤ 2 / (Real.pi ^ 2 * paperArcRadius X D) := by
    unfold paperArcRadius
    positivity
  have hright0 : 0 ≤ (2 * X) / (Real.log X) ^ D := by positivity
  calc
    (2 / (Real.pi ^ 2 * paperArcRadius X D)) ^ 2 ≤
        ((2 * X) / (Real.log X) ^ D) ^ 2 :=
      (sq_le_sq₀ hK0 hright0).2 hK
    _ = 4 * X ^ 2 / (Real.log X) ^ (2 * D) := by
      rw [div_pow, ← pow_mul]
      ring

/-- Quantitative summation of the modeled continuous-kernel and exact
Ramanujan tails.  The hypotheses `A ≤ 2D-6` and `A ≤ B-16` display the two
losses rather than hiding them in asymptotic notation. -/
theorem modeledOverlapErrorEnergy_logSaving_of_exponents
    {A ε X H h₀ : ℝ} {B D : ℕ} {Cs Ct : ℝ}
    (hA : 0 < A) (hε : 0 < ε)
    (hX : Real.exp 1 ≤ X)
    (hlegal : LegalParameters ε X H h₀)
    (hB16 : 16 ≤ B) (hAB : A ≤ (B - 16 : ℕ))
    (hD6 : 6 ≤ 2 * D) (hAD : A ≤ (2 * D - 6 : ℕ))
    (hCs : 0 ≤ Cs) (hCt : 0 ≤ Ct)
    (hsingular : singularSquareMain H h₀ ≤
      Cs * H * (Real.log X) ^ 6)
    (htail : ramanujanTailEnergy H h₀ (paperDenominatorCutoff X B) ≤
      Ct * H * (Real.log X) ^ 16 /
        (paperDenominatorCutoff X B + 1 : ℕ))
    (hshift : ∀ h ∈ translatedWindow H h₀, h ≠ 0 → |(h : ℝ)| ≤ X) :
    modeledOverlapErrorEnergy X H h₀ B D ≤
      (16 * Cs + 18 * Ct) * H * X ^ 2 *
        Real.rpow (Real.log X) (-A) := by
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hX
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog1
  have hR : 0 < paperArcRadius X D := by
    unfold paperArcRadius
    positivity
  let K : ℝ := 2 / (Real.pi ^ 2 * paperArcRadius X D)
  let Q : ℕ := paperDenominatorCutoff X B
  have hH0 : 0 ≤ H :=
    (Real.rpow_nonneg hXpos.le (2 / 15 + ε)).trans hlegal.1
  have hsing0 : 0 ≤ singularSquareMain H h₀ := by
    unfold singularSquareMain
    positivity
  have htail0 : 0 ≤ ramanujanTailEnergy H h₀ Q := by
    unfold ramanujanTailEnergy
    positivity
  have hcomponent := modeledOverlapErrorEnergy_le_components
    (B := B) (D := D) hXpos.le hR hshift
  have hKsq : K ^ 2 ≤ 4 * X ^ 2 / (Real.log X) ^ (2 * D) := by
    simpa [K] using kernelTailFactor_sq_le (X := X) (D := D) hX
  have hkernelRatio :
      (Real.log X) ^ 6 / (Real.log X) ^ (2 * D) ≤
        Real.rpow (Real.log X) (-A) :=
    pow_div_pow_le_rpow_neg hlog1 hD6 hAD
  have hKterm :
      4 * K ^ 2 * singularSquareMain H h₀ ≤
        16 * Cs * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
    calc
      4 * K ^ 2 * singularSquareMain H h₀ ≤
          4 * (4 * X ^ 2 / (Real.log X) ^ (2 * D)) *
            (Cs * H * (Real.log X) ^ 6) := by gcongr
      _ = 16 * Cs * H * X ^ 2 *
            ((Real.log X) ^ 6 / (Real.log X) ^ (2 * D)) := by ring
      _ ≤ 16 * Cs * H * X ^ 2 *
            Real.rpow (Real.log X) (-A) := by
        exact mul_le_mul_of_nonneg_left hkernelRatio (by positivity)
  have hpowD : 1 ≤ (Real.log X) ^ (2 * D) := one_le_pow₀ hlog1
  have hKcoarse : K ^ 2 ≤ 4 * X ^ 2 := by
    calc
      K ^ 2 ≤ 4 * X ^ 2 / (Real.log X) ^ (2 * D) := hKsq
      _ ≤ 4 * X ^ 2 := by
        exact (div_le_iff₀ (pow_pos hlogpos (2 * D))).2
          (le_mul_of_one_le_right (by positivity) hpowD)
  have hcoef : 4 * K ^ 2 + 2 * X ^ 2 ≤ 18 * X ^ 2 := by
    nlinarith [sq_nonneg X]
  have hQlower : (Real.log X) ^ B < (Q + 1 : ℕ) := by
    simpa [Q, paperDenominatorCutoff] using
      (Nat.lt_floor_add_one ((Real.log X) ^ B))
  have htailRatio :
      (Real.log X) ^ 16 / (Q + 1 : ℕ) ≤
        Real.rpow (Real.log X) (-A) := by
    calc
      (Real.log X) ^ 16 / (Q + 1 : ℕ) ≤
          (Real.log X) ^ 16 / (Real.log X) ^ B := by
        exact div_le_div_of_nonneg_left (by positivity)
          (pow_pos hlogpos B) hQlower.le
      _ ≤ Real.rpow (Real.log X) (-A) :=
        pow_div_pow_le_rpow_neg hlog1 hB16 hAB
  have htailTerm :
      (4 * K ^ 2 + 2 * X ^ 2) *
          ramanujanTailEnergy H h₀ Q ≤
        18 * Ct * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
    calc
      (4 * K ^ 2 + 2 * X ^ 2) * ramanujanTailEnergy H h₀ Q ≤
          (18 * X ^ 2) *
            (Ct * H * (Real.log X) ^ 16 / (Q + 1 : ℕ)) := by
        exact mul_le_mul hcoef (by simpa [Q] using htail)
          htail0 (by positivity)
      _ = 18 * Ct * H * X ^ 2 *
            ((Real.log X) ^ 16 / (Q + 1 : ℕ)) := by ring
      _ ≤ 18 * Ct * H * X ^ 2 *
            Real.rpow (Real.log X) (-A) := by
        exact mul_le_mul_of_nonneg_left htailRatio (by positivity)
  calc
    modeledOverlapErrorEnergy X H h₀ B D ≤
        4 * K ^ 2 * singularSquareMain H h₀ +
          (4 * K ^ 2 + 2 * X ^ 2) * ramanujanTailEnergy H h₀ Q := by
      simpa [K, Q] using hcomponent
    _ ≤ 16 * Cs * H * X ^ 2 * Real.rpow (Real.log X) (-A) +
          18 * Ct * H * X ^ 2 * Real.rpow (Real.log X) (-A) :=
      add_le_add hKterm htailTerm
    _ = (16 * Cs + 18 * Ct) * H * X ^ 2 *
          Real.rpow (Real.log X) (-A) := by ring

/-- Public all-center family for the post-prime-polynomial modeled remainder,
at any denominator/radius exponents satisfying the two displayed losses. -/
theorem modeledOverlapErrorEnergy_family_of_exponents
    {A ε : ℝ} {B D : ℕ}
    (hA : 0 < A) (hε : 0 < ε)
    (hB16 : 16 ≤ B) (hAB : A ≤ (B - 16 : ℕ))
    (hD6 : 6 ≤ 2 * D) (hAD : A ≤ (2 * D - 6 : ℕ)) :
    ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X H h₀ : ℝ, X₀ ≤ X →
        LegalParameters ε X H h₀ →
        modeledOverlapErrorEnergy X H h₀ B D ≤
          C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
  obtain ⟨Cs, Xs, hCs, hXs, hsing⟩ :=
    SingularSeriesSquareMean.translated_singularSquareMain_le ε hε
  obtain ⟨Ct, Xt, hCt, hXt, htail⟩ :=
    MAPShortIntervalTauFour.certified_legalRamanujanTailEnergy ε hε
  have hshiftEvent := SupportBoundaryQuantitative.eventually_two_rpow_one_sub_lt hε
  rw [Filter.eventually_atTop] at hshiftEvent
  obtain ⟨Xshift, hshiftEvent⟩ := hshiftEvent
  let C : ℝ := 16 * Cs + 18 * Ct
  let X₀ : ℝ := max (max Xs Xt) (max (Real.exp 1) Xshift)
  have hC : 0 < C := by dsimp [C]; positivity
  have hX₀ : 3 ≤ X₀ := by
    dsimp [X₀]
    exact hXt.trans (le_max_right Xs Xt) |>.trans
      (le_max_left (max Xs Xt) (max (Real.exp 1) Xshift))
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hXXs : Xs ≤ X :=
    (le_max_left Xs Xt).trans
      ((le_max_left (max Xs Xt) (max (Real.exp 1) Xshift)).trans hXX₀)
  have hXXt : Xt ≤ X :=
    (le_max_right Xs Xt).trans
      ((le_max_left (max Xs Xt) (max (Real.exp 1) Xshift)).trans hXX₀)
  have hXexp : Real.exp 1 ≤ X :=
    (le_max_left (Real.exp 1) Xshift).trans
      ((le_max_right (max Xs Xt) (max (Real.exp 1) Xshift)).trans hXX₀)
  have hXXshift : Xshift ≤ X :=
    (le_max_right (Real.exp 1) Xshift).trans
      ((le_max_right (max Xs Xt) (max (Real.exp 1) Xshift)).trans hXX₀)
  have hshiftX : 2 * Real.rpow X (1 - ε) < X := hshiftEvent X hXXshift
  have hshift : ∀ h ∈ translatedWindow H h₀, h ≠ 0 → |(h : ℝ)| ≤ X := by
    intro h hh hh0
    have hnat := SupportBoundaryQuantitative.natAbs_shift_le_two_rpow hlegal hh
    have hcast : (h.natAbs : ℝ) = |(h : ℝ)| := by
      rw [← Int.cast_abs]
      norm_num
    rw [← hcast]
    exact hnat.trans hshiftX.le
  have hs := hsing X H h₀ hXXs hlegal
  have ht := htail X H h₀ (paperDenominatorCutoff X B) hXXt hlegal
  simpa [C] using modeledOverlapErrorEnergy_logSaving_of_exponents
    hA hε hXexp hlegal hB16 hAB hD6 hAD hCs.le hCt.le hs ht hshift

/-! ## The exact surviving prime-polynomial component -/

/-- The portion of the major coefficient error before the continuous-kernel
and Ramanujan replacements.  This is the exact output of the integrated
Siegel--Walfisz/Abel estimate, not a restatement of the final overlap error. -/
def primePolynomialModelError (X : ℝ) (B D : ℕ) (h : ℤ) : ℂ :=
  MAPHarmonicEndpoint.majorCoefficient X B D h -
    modeledPaperMajorContribution X B D h

def primePolynomialModelErrorEnergy (X H h₀ : ℝ) (B D : ℕ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀,
    if h = 0 then 0 else ‖primePolynomialModelError X B D h‖ ^ 2

/-- Explicit analytic contract left by the deterministic major-arc weld.  It
contains only the actual-prime-polynomial to continuous-model energy.  In the
manuscript this is the quantitative consequence of uniform Siegel--Walfisz
and Abel summation. -/
def SelectablePrimePolynomialModelErrorEnergyFamily : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∀ B₀ D₀ : ℕ,
      ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
        ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
          ∀ X H h₀ : ℝ, X₀ ≤ X →
            LegalParameters ε X H h₀ →
            primePolynomialModelErrorEnergy X H h₀ B D ≤
              C * H * X ^ 2 * Real.rpow (Real.log X) (-A)

def majorOverlapError (X : ℝ) (B D : ℕ) (h : ℤ) : ℂ :=
  MAPHarmonicEndpoint.majorCoefficient X B D h - primePairMajorModel X h

def majorOverlapErrorEnergy (X H h₀ : ℝ) (B D : ℕ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀,
    if h = 0 then 0 else ‖majorOverlapError X B D h‖ ^ 2

theorem majorOverlapError_eq_prime_add_modeled
    (X : ℝ) (B D : ℕ) (h : ℤ) :
    majorOverlapError X B D h =
      primePolynomialModelError X B D h + modeledOverlapError X B D h := by
  unfold majorOverlapError primePolynomialModelError modeledOverlapError
  ring

theorem majorOverlapErrorEnergy_le_prime_add_modeled
    (X H h₀ : ℝ) (B D : ℕ) :
    majorOverlapErrorEnergy X H h₀ B D ≤
      2 * primePolynomialModelErrorEnergy X H h₀ B D +
        2 * modeledOverlapErrorEnergy X H h₀ B D := by
  classical
  unfold majorOverlapErrorEnergy primePolynomialModelErrorEnergy
    modeledOverlapErrorEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  by_cases hh0 : h = 0
  · simp [hh0]
  · simp only [if_neg hh0]
    rw [majorOverlapError_eq_prime_add_modeled]
    exact MAPVarianceTransferWeld.norm_add_sq_le_two_mul _ _

/-- The prime-polynomial contract plus the certified kernel and Ramanujan
tails yields the exact selectable overlap-major energy expected by the final
support/boundary connector. -/
theorem selectableMajorOverlapEnergy_of_primePolynomialModel
    (hPrime : SelectablePrimePolynomialModelErrorEnergyFamily) :
    ∀ A ε : ℝ, 0 < A → 0 < ε →
      ∀ B₀ D₀ : ℕ,
        ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
          ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
            ∀ X H h₀ : ℝ, X₀ ≤ X →
              LegalParameters ε X H h₀ →
              majorOverlapErrorEnergy X H h₀ B D ≤
                C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
  intro A ε hA hε B₀ D₀
  let n : ℕ := ⌈A⌉₊
  let Bmin : ℕ := max B₀ (n + 16)
  let Dmin : ℕ := max D₀ (n + 3)
  obtain ⟨B, D, hBmin, hDmin, Cp, Xp, hCp, hXp, hp⟩ :=
    hPrime A ε hA hε Bmin Dmin
  have hB₀ : B₀ ≤ B := (le_max_left B₀ (n + 16)).trans hBmin
  have hD₀ : D₀ ≤ D := (le_max_left D₀ (n + 3)).trans hDmin
  have hnB : n + 16 ≤ B := (le_max_right B₀ (n + 16)).trans hBmin
  have hnD : n + 3 ≤ D := (le_max_right D₀ (n + 3)).trans hDmin
  have hB16 : 16 ≤ B := by omega
  have hAB : A ≤ (B - 16 : ℕ) := by
    have hceil : A ≤ (n : ℝ) := by simpa [n] using Nat.le_ceil A
    have hn : n ≤ B - 16 := by omega
    exact hceil.trans (by exact_mod_cast hn)
  have hD6 : 6 ≤ 2 * D := by omega
  have hAD : A ≤ (2 * D - 6 : ℕ) := by
    have hceil : A ≤ (n : ℝ) := by simpa [n] using Nat.le_ceil A
    have hn : n ≤ 2 * D - 6 := by omega
    exact hceil.trans (by exact_mod_cast hn)
  obtain ⟨Cm, Xm, hCm, hXm, hm⟩ :=
    modeledOverlapErrorEnergy_family_of_exponents hA hε hB16 hAB hD6 hAD
  let C : ℝ := 2 * Cp + 2 * Cm
  let X₀ : ℝ := max Xp Xm
  refine ⟨B, D, hB₀, hD₀, C, X₀, by dsimp [C]; positivity,
    hXp.trans (le_max_left _ _), ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hXXp : Xp ≤ X := (le_max_left Xp Xm).trans hXX₀
  have hXXm : Xm ≤ X := (le_max_right Xp Xm).trans hXX₀
  have hsplit := majorOverlapErrorEnergy_le_prime_add_modeled X H h₀ B D
  have hpX := hp X H h₀ hXXp hlegal
  have hmX := hm X H h₀ hXXm hlegal
  calc
    majorOverlapErrorEnergy X H h₀ B D ≤
        2 * primePolynomialModelErrorEnergy X H h₀ B D +
          2 * modeledOverlapErrorEnergy X H h₀ B D := hsplit
    _ ≤ 2 * (Cp * H * X ^ 2 * Real.rpow (Real.log X) (-A)) +
          2 * (Cm * H * X ^ 2 * Real.rpow (Real.log X) (-A)) := by
      gcongr
    _ = C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      dsimp [C]
      ring

end
end MAPModelOverlapEnergy

#print axioms MAPModelOverlapEnergy.modeledOverlapErrorEnergy_le_components
#print axioms MAPModelOverlapEnergy.kernelTailFactor_sq_le
#print axioms MAPModelOverlapEnergy.modeledOverlapErrorEnergy_logSaving_of_exponents
#print axioms MAPModelOverlapEnergy.modeledOverlapErrorEnergy_family_of_exponents
#print axioms MAPModelOverlapEnergy.selectableMajorOverlapEnergy_of_primePolynomialModel
