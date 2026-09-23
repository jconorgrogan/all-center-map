import JutilaPrincipalEpsilonShiftedContour
import JutilaPrincipalZeroStrictBoundary
import JutilaPrincipalSourceConvexity
import JutilaLemma6ErrorBound
import JutilaLemma6DirectTail
import JutilaCollarSourceParameters
import JutilaLemma6GenericDeltaLedger
import JutilaPrincipalDetectorPole
import JutilaPseudocharacterMollifierBound
import JutilaGappedGrahamBypass
import PostA5HighStripSplitReductionFromFourthMoment

/-!
# Square-root remainder on the epsilon-shifted principal left line

The left factor `ζ(ρ+z)` now sits at `Re = ε = 1/500`, inside the certified
square-root strip.  The extra Mellin cost `X^ε` is a fixed power of `D` and
is strictly smaller than the Lemma 6 saving `2δ-12δ²` at `δ = 1/280`.

The resulting remainder is eventually smaller than `1/2` at source
parameters; together with the high-ordinate pole bound this yields
`‖directSeries‖ < 1` on `|Im ρ| ≥ 12 log D`.
-/

namespace MAPJutilaPrincipalEpsilonRemainder

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators
open MAPJutilaPrincipalEpsilonShiftedContour
open MAPJutilaPrincipalSourceConvexity
open MAPJutilaPrincipalDetectorVerticalIntegrability
open MAPJutilaPrincipalDetectorFinitePole
open MAPJutilaPrincipalDetectorPole
open MAPJutilaLemma6FiniteContour
open MAPJutilaLemma6SieveCoefficientBridge
open MAPJutilaLemma6ErrorBound
open MAPJutilaMEntire
open MAPJutilaPseudocharacterMExact
open MAPJutilaPseudocharacterMollifierSum
open MAPJutilaPseudocharacterMollifierBound
open MAPJutilaPseudocharacterHarmonicLower
open MAPJutilaGappedGrahamBypass
open MAPJutilaLemma6DirectTail
open MAPJutilaCollarSourceParameters
open MAPJutilaLemma6GenericTailAbsorption
open MAPJutilaLemma6GenericDeltaLedger
open MAPPrincipalZetaFixedStrip
open JutilaPolynomialExponentialIntegral

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

theorem norm_jutilaLocalEulerFactorComplex_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖jutilaLocalEulerFactorComplex chi p s‖ ≤ (p : ℝ) + 1 := by
  have hpow : ‖jutilaNatPower p s‖ ≤ 1 :=
    MAPJutilaMNonnegativeHalfPlaneBound.norm_jutilaNatPower_le_one hp.pos hs
  have hchi : ‖chi p‖ ≤ 1 := DirichletCharacter.norm_le_one chi p
  rw [jutilaLocalEulerFactorComplex, selbergPseudoCoeff_prime_sub_one hp]
  calc
    ‖1 + -(p : ℂ) * chi p * jutilaNatPower p s‖ ≤
        ‖(1 : ℂ)‖ + ‖-(p : ℂ) * chi p * jutilaNatPower p s‖ :=
      norm_add_le _ _
    _ = 1 + (p : ℝ) * ‖chi p‖ * ‖jutilaNatPower p s‖ := by
      simp only [norm_one, norm_mul, norm_neg, Complex.norm_natCast]
    _ ≤ 1 + (p : ℝ) * 1 * 1 := by gcongr
    _ = (p : ℝ) + 1 := by ring

theorem norm_jutilaLocalEulerProductComplex_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (r d : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖jutilaLocalEulerProductComplex chi r d s‖ ≤
      pseudocharacterEulerProduct (r / r.gcd d) := by
  let n := r / r.gcd d
  have hprodNorm :
      ‖∏ p ∈ n.primeFactors, jutilaLocalEulerFactorComplex chi p s‖ ≤
        ∏ p ∈ n.primeFactors, ‖jutilaLocalEulerFactorComplex chi p s‖ :=
    Finset.norm_prod_le _ _
  calc
    ‖jutilaLocalEulerProductComplex chi r d s‖ ≤
        ∏ p ∈ n.primeFactors, ‖jutilaLocalEulerFactorComplex chi p s‖ := by
      simpa [jutilaLocalEulerProductComplex, n] using hprodNorm
    _ ≤ ∏ p ∈ n.primeFactors, ((p : ℝ) + 1) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        exact norm_jutilaLocalEulerFactorComplex_le chi
          (Nat.prime_of_mem_primeFactors hp) hs
    _ = pseudocharacterEulerProduct (r / r.gcd d) := rfl

theorem norm_jutilaMTermComplex_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {r d : ℕ} (hd : 0 < d) (hxi : ‖xi d‖ ≤ 1)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖jutilaMTermComplex chi xi r d s‖ ≤
      pseudocharacterLocalEnvelope r d := by
  have hchi : ‖chi d‖ ≤ 1 := DirichletCharacter.norm_le_one chi d
  have hf := norm_selbergPseudoAt_le r d
  have hpower :=
    MAPJutilaMNonnegativeHalfPlaneBound.norm_jutilaNatPower_le_one hd hs
  have hEuler := norm_jutilaLocalEulerProductComplex_le chi r d hs
  unfold jutilaMTermComplex
  simp only [norm_mul]
  calc
    ‖xi d‖ * ‖chi d‖ * ‖selbergPseudoAt r d‖ *
        ‖jutilaNatPower d s‖ * ‖jutilaLocalEulerProductComplex chi r d s‖ ≤
      1 * 1 * (Nat.totient (r.gcd d) : ℝ) * 1 *
        pseudocharacterEulerProduct (r / r.gcd d) := by
      gcongr
    _ = pseudocharacterLocalEnvelope r d := by
      unfold pseudocharacterLocalEnvelope
      ring

theorem norm_jutilaMWeightedSumComplex_le_harmonic4
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {Ds S : Finset ℕ} {z2 R : ℕ}
    (hDcard : Ds.card ≤ z2) (hDpos : ∀ d ∈ Ds, 0 < d)
    (hxi : ∀ d ∈ Ds, ‖xi d‖ ≤ 1)
    (hS : S ⊆ Finset.Icc 1 R)
    (hrsq : ∀ r ∈ S, Squarefree r)
    (hrcop : ∀ r ∈ S, r.Coprime q)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖jutilaMWeightedSumComplex chi xi Ds S s‖ ≤
      (z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4 := by
  have hterm : ∀ r ∈ S, ∀ d ∈ Ds,
      ‖jutilaMTermComplex chi xi r d s‖ ≤
        pseudocharacterLocalEnvelope r d :=
    fun r hr d hd =>
      norm_jutilaMTermComplex_le chi xi (hDpos d hd) (hxi d hd) hs
  have hsum :=
    sum_inv_mul_norm_finitePseudocharacterMollifier_selected_le
      hDcard hS hrsq hrcop hterm
  calc
    ‖jutilaMWeightedSumComplex chi xi Ds S s‖ ≤
        ∑ r ∈ S, ‖(r : ℂ)⁻¹ * jutilaMFiniteComplex chi xi Ds r s‖ := by
      unfold jutilaMWeightedSumComplex
      exact norm_sum_le _ _
    _ = ∑ r ∈ S, (r : ℝ)⁻¹ * ‖jutilaMFiniteComplex chi xi Ds r s‖ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [norm_mul, norm_inv]
      simp
    _ = ∑ r ∈ S,
          (r : ℝ)⁻¹ *
            ‖finitePseudocharacterMollifier Ds
              (fun r d => jutilaMTermComplex chi xi r d s) r‖ := by
      apply Finset.sum_congr rfl
      intro r hr
      rfl
    _ ≤ _ := hsum

theorem norm_canonical_M_halfPlane_le
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2) (R : ℕ)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖jutilaMWeightedSumComplex chiOne (jutilaLambdaComplex z1 z2)
        (jutilaLambdaSupport z2) (jutilaPrimedRSet 1 R) s‖ ≤
      (Nat.floor z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4 := by
  have hDcard : (jutilaLambdaSupport z2).card ≤ Nat.floor z2 := by
    simp [jutilaLambdaSupport]
  have hDpos : ∀ d ∈ jutilaLambdaSupport z2, 0 < d :=
    fun d hd => (Finset.mem_Icc.mp hd).1
  have hxi : ∀ d ∈ jutilaLambdaSupport z2,
      ‖jutilaLambdaComplex z1 z2 d‖ ≤ 1 := by
    intro d hd
    simpa [jutilaLambdaComplex, Complex.norm_real, Real.norm_eq_abs]
      using abs_jutilaLambda_le_one hz1 hz12 d
  exact norm_jutilaMWeightedSumComplex_le_harmonic4 chiOne
    (jutilaLambdaComplex z1 z2) hDcard hDpos hxi
    (jutilaPrimedRSet_subset_Icc 1 R)
    (fun r hr => squarefree_of_mem_jutilaPrimedRSet hr)
    (fun r hr => coprime_of_mem_jutilaPrimedRSet hr) hs

private theorem sqrt_one_add_le (t u : ℝ) :
    Real.sqrt (1 + |t + u|) ≤ Real.sqrt (1 + |t|) * (1 + |u|) := by
  have h1 : 0 ≤ 1 + |t| := by positivity
  have h2 : 0 ≤ 1 + |u| := by positivity
  have harg : 1 + |t + u| ≤ (1 + |t|) * (1 + |u|) := by
    calc
      1 + |t + u| ≤ 1 + (|t| + |u|) := by linarith [abs_add_le t u]
      _ ≤ (1 + |t|) * (1 + |u|) := by nlinarith [abs_nonneg t, abs_nonneg u]
  have hsq := Real.sqrt_le_sqrt harg
  have hmul : Real.sqrt ((1 + |t|) * (1 + |u|)) =
      Real.sqrt (1 + |t|) * Real.sqrt (1 + |u|) :=
    Real.sqrt_mul h1 _
  have hsu : Real.sqrt (1 + |u|) ≤ 1 + |u| := by
    have : Real.sqrt (1 + |u|) ≤ Real.sqrt ((1 + |u|) ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [abs_nonneg u]
    simpa [Real.sqrt_sq h2] using this
  calc
    Real.sqrt (1 + |t + u|) ≤ Real.sqrt ((1 + |t|) * (1 + |u|)) := hsq
    _ = Real.sqrt (1 + |t|) * Real.sqrt (1 + |u|) := hmul
    _ ≤ Real.sqrt (1 + |t|) * (1 + |u|) :=
      mul_le_mul_of_nonneg_left hsu (Real.sqrt_nonneg _)

/-- Pointwise square-root envelope on the epsilon-shifted left line. -/
theorem norm_principal_detector_epsilonLeft_sqrt_le
    {beta t : ℝ} {Cζ C : ℝ}
    (hCζ : 0 ≤ Cζ) (hC : 0 ≤ C)
    (hζ : ∀ sigma u : ℝ, principalSqrtShift ≤ sigma →
      sigma ≤ 3 * principalSqrtShift →
      ‖riemannZeta ((sigma : ℂ) + u * I)‖ ≤
        Cζ * Real.sqrt (1 + |u|))
    (xi : ℕ → ℂ) {Ds : Finset ℕ}
    (hDpos : ∀ d ∈ Ds, 0 < d) (S : Finset ℕ)
    {X u : ℝ} (hX : 1 ≤ X)
    (hM : ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chiOne xi Ds S s‖ ≤ C)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    ‖jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi Ds S X (principalEpsilonLeft beta u)‖ ≤
      (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
        Cζ * Real.sqrt (1 + |t|) * Real.rpow X (-beta + principalSqrtShift) * C *
        ((1 + |u|) ^ 2 * Real.exp (-|u|)) := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  let z : ℂ := principalEpsilonLeft beta u
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hz : z ≠ 0 := principalEpsilonLeft_ne_zero hbetaLo u
  have hLrho :
      DirichletCharacter.LFunction chiOne rho = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  rw [jutilaDetectorExtension_eq_raw chiOne xi Ds S X hLrho hz]
  have hG := norm_Gamma_principal_epsilonLeft_le (u := u) hbetaLo hbetaHi
  have hPow : ‖(X : ℂ) ^ z‖ = Real.rpow X (-beta + principalSqrtShift) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    simp [z, principalEpsilonLeft]
  let s : ℂ := rho + z
  have hsRe : s.re = principalSqrtShift := by
    simp [s, rho, z, lemmaSixZeroPoint, principalEpsilonLeft]
  have hsIm : s.im = t + u := by
    simp [s, rho, z, lemmaSixZeroPoint, principalEpsilonLeft]
  have hL : ‖DirichletCharacter.LFunction chiOne s‖ ≤
      Cζ * Real.sqrt (1 + |t|) * (1 + |u|) := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    have hspt : s = ((principalSqrtShift : ℂ) + (t + u : ℝ) * I) := by
      apply Complex.ext
      · simp [s, rho, z, lemmaSixZeroPoint, principalEpsilonLeft]
      · simp [s, rho, z, lemmaSixZeroPoint, principalEpsilonLeft]
    have hbound := hζ principalSqrtShift (t + u) le_rfl
      (by linarith [principalSqrtShift_pos])
    have hsqrt := sqrt_one_add_le t u
    calc
      ‖riemannZeta s‖ = ‖riemannZeta
          ((principalSqrtShift : ℂ) + (t + u : ℝ) * I)‖ := by rw [hspt]
      _ ≤ Cζ * Real.sqrt (1 + |t + u|) := hbound
      _ ≤ Cζ * (Real.sqrt (1 + |t|) * (1 + |u|)) :=
        mul_le_mul_of_nonneg_left hsqrt hCζ
      _ = Cζ * Real.sqrt (1 + |t|) * (1 + |u|) := by ring
  have hs0 : 0 ≤ s.re := by rw [hsRe]; exact principalSqrtShift_pos.le
  have hm := hM s hs0
  have hgamma0 : 0 ≤
      12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift) :=
    by
      apply div_nonneg (by norm_num)
      apply mul_nonneg
      · linarith [principalSqrtShift_lt_four_fifths]
      · exact principalSqrtShift_pos.le
  have hu0 : 0 ≤ 1 + |u| := by positivity
  have hexpu0 : 0 ≤ Real.exp (-(Real.pi / 2) * |u|) := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt (1 + |t|) := Real.sqrt_nonneg _
  have hxp0 : 0 ≤ Real.rpow X (-beta + principalSqrtShift) :=
    Real.rpow_nonneg hXpos.le _
  have hmid0 : 0 ≤ Cζ * Real.sqrt (1 + |t|) * (1 + |u|) := by
    positivity
  have hright0 : 0 ≤
      ((12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
        (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) *
        (Cζ * Real.sqrt (1 + |t|) * (1 + |u|)) *
        Real.rpow X (-beta + principalSqrtShift) * C := by
    positivity
  have hexp :
      Real.exp (-(Real.pi / 2) * |u|) ≤ Real.exp (-|u|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_gt_three, abs_nonneg u]
  simp only [norm_mul, hPow]
  calc
    _ ≤ ((12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
          (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) *
        (Cζ * Real.sqrt (1 + |t|) * (1 + |u|)) *
        Real.rpow X (-beta + principalSqrtShift) * C := by
          gcongr
          all_goals try exact hright0
          all_goals try exact hmid0
          all_goals try exact hxp0
          all_goals try exact hgamma0
          all_goals positivity
    _ ≤ ((12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
          (1 + |u|) * Real.exp (-|u|)) *
        (Cζ * Real.sqrt (1 + |t|) * (1 + |u|)) *
        Real.rpow X (-beta + principalSqrtShift) * C := by
          gcongr
          all_goals try exact hright0
          all_goals try exact hmid0
          all_goals try exact hxp0
          all_goals try exact hgamma0
          all_goals positivity
    _ = (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
          Cζ * Real.sqrt (1 + |t|) *
          Real.rpow X (-beta + principalSqrtShift) * C *
          ((1 + |u|) ^ 2 * Real.exp (-|u|)) := by ring

def principalEpsilonVerticalMass : ℝ :=
  ∫ u : ℝ, (1 + |u|) ^ 2 * Real.exp (-|u|)

theorem integrable_principalEpsilonVerticalMass :
    Integrable (fun u : ℝ => (1 + |u|) ^ 2 * Real.exp (-|u|)) := by
  have h := integrable_shiftedAbsPowExp
    (A := 1) (k := 2) (c := 1) (by norm_num) (by norm_num)
  convert h using 1
  ext u
  simp [shiftedAbsPowExp]

theorem principalEpsilonVerticalMass_nonneg :
    0 ≤ principalEpsilonVerticalMass :=
  integral_nonneg fun _ => by positivity

theorem principalEpsilonVerticalMass_le :
    principalEpsilonVerticalMass ≤
      (2 : ℝ) ^ 2 *
        ((1 : ℝ) ^ 2 * (2 / 1) +
          2 * (1 / 1 : ℝ) ^ ((2 : ℝ) + 1) * (Nat.factorial 2 : ℝ)) := by
  have h := integral_shiftedAbsPowExp_le
    (A := 1) (k := 2) (c := 1) (by norm_num) (by norm_num)
  have hmass : principalEpsilonVerticalMass =
      ∫ u : ℝ, shiftedAbsPowExp 1 2 1 u := by
    unfold principalEpsilonVerticalMass shiftedAbsPowExp
    simp
  rw [hmass]
  exact h

theorem GammaConst_nonneg :
    0 ≤ 12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift) := by
  apply div_nonneg (by norm_num)
  apply mul_nonneg
  · linarith [principalSqrtShift_lt_four_fifths]
  · exact principalSqrtShift_pos.le

theorem norm_integral_principal_detector_epsilonLeft_le
    {beta t : ℝ} {Cζ C : ℝ}
    (hCζ : 0 ≤ Cζ) (hC : 0 ≤ C)
    (hζ : ∀ sigma u : ℝ, principalSqrtShift ≤ sigma →
      sigma ≤ 3 * principalSqrtShift →
      ‖riemannZeta ((sigma : ℂ) + u * I)‖ ≤
        Cζ * Real.sqrt (1 + |u|))
    (xi : ℕ → ℂ) {Ds : Finset ℕ}
    (hDpos : ∀ d ∈ Ds, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 1 ≤ X)
    (hM : ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chiOne xi Ds S s‖ ≤ C)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    ‖∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi Ds S X (principalEpsilonLeft beta u)‖ ≤
      (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
        Cζ * Real.sqrt (1 + |t|) * Real.rpow X (-beta + principalSqrtShift) * C *
        principalEpsilonVerticalMass := by
  let K : ℝ :=
    (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
      Cζ * Real.sqrt (1 + |t|) * Real.rpow X (-beta + principalSqrtShift) * C
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg GammaConst_nonneg hCζ)
      (Real.sqrt_nonneg _)) (Real.rpow_nonneg (zero_le_one.trans hX) _)) hC
  let F : ℝ → ℂ := fun u =>
    jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
      xi Ds S X (principalEpsilonLeft beta u)
  let E : ℝ → ℝ := fun u => K * ((1 + |u|) ^ 2 * Real.exp (-|u|))
  have hE : Integrable E :=
    integrable_principalEpsilonVerticalMass.const_mul K
  have hpoint : ∀ u : ℝ, ‖F u‖ ≤ E u := fun u => by
    simpa [F, E, K] using
      norm_principal_detector_epsilonLeft_sqrt_le hCζ hC hζ
        xi hDpos S hX hM hbetaLo hbetaHi hrho (u := u)
  have hFint : Integrable F :=
    integrable_principal_detector_epsilonLeft xi hDpos S hX
      hbetaLo hbetaHi hrho
  calc
    ‖∫ u : ℝ, F u‖ ≤ ∫ u : ℝ, E u :=
      MeasureTheory.norm_integral_le_of_norm_le hE
        (Filter.Eventually.of_forall hpoint)
    _ = K * principalEpsilonVerticalMass := by
      simp [E, principalEpsilonVerticalMass, integral_const_mul]

theorem norm_principal_canonical_epsilonError_le
    {beta t z1 z2 : ℝ} {R : ℕ} {X Cζ C : ℝ}
    (hz1 : 1 < z1) (hz12 : z1 < z2)
    (hX : 1 ≤ X) (hCζ : 0 ≤ Cζ) (hC : 0 ≤ C)
    (hζ : ∀ sigma u : ℝ, principalSqrtShift ≤ sigma →
      sigma ≤ 3 * principalSqrtShift →
      ‖riemannZeta ((sigma : ℂ) + u * I)‖ ≤
        Cζ * Real.sqrt (1 + |u|))
    (hM : ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chiOne (jutilaLambdaComplex z1 z2)
        (jutilaLambdaSupport z2) (jutilaPrimedRSet 1 R) s‖ ≤ C)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    ‖(∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne z1 z2
        (jutilaPrimedRSet 1 R) (lemmaSixZeroPoint beta t) X n) -
      principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R‖ ≤
      (1 / (2 * Real.pi)) *
        ((12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
          Cζ * Real.sqrt (1 + |t|) *
          Real.rpow X (-beta + principalSqrtShift) * C *
          principalEpsilonVerticalMass) := by
  have hid := principal_canonical_directSeries_sub_pole_eq_epsilonLeft
    (R := R) hz1 hz12 hX hbetaLo hbetaHi hrho
  have hleft := norm_integral_principal_detector_epsilonLeft_le
    hCζ hC hζ (jutilaLambdaComplex z1 z2)
    (fun d hd => (Finset.mem_Icc.mp hd).1)
    (jutilaPrimedRSet 1 R) hX hM hbetaLo hbetaHi hrho
  have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpi]
  exact mul_le_mul_of_nonneg_left hleft hpi

/-- Exact remaining exponent at `δ = 1/280` after the `X^ε` cost and the
square-root height `1/2` (no p.48 extra `1/560`). -/
theorem principal_epsilon_error_exponent_280
    {beta : ℝ} (hbeta : (279 / 280 : ℝ) ≤ beta) :
    -(1 + 12 * (1 / 280 : ℝ)) * beta
      + (1 + 12 * (1 / 280 : ℝ)) * principalSqrtShift
      + (1 / 2 + 8 * (1 / 280 : ℝ)) + (1 / 280 : ℝ) + (1 / 2 : ℝ)
      ≤ - (1 / 250 : ℝ) := by
  have hcoeff : (0 : ℝ) ≤ 1 + 12 * (1 / 280 : ℝ) := by norm_num
  have hmono :
      -(1 + 12 * (1 / 280 : ℝ)) * beta ≤
        -(1 + 12 * (1 / 280 : ℝ)) * (279 / 280 : ℝ) := by nlinarith
  have hnum :
      -(1 + 12 * (1 / 280 : ℝ)) * (279 / 280 : ℝ)
        + (1 + 12 * (1 / 280 : ℝ)) * (1 / 500 : ℝ)
        + (1 / 2 + 8 * (1 / 280 : ℝ)) + (1 / 280 : ℝ) + (1 / 2 : ℝ)
        ≤ - (1 / 250 : ℝ) := by norm_num
  unfold principalSqrtShift
  linarith

theorem principal_epsilon_error_power_280
    {D beta : ℝ} (hD : 1 ≤ D) (hbeta : (279 / 280 : ℝ) ≤ beta) :
    Real.rpow D (-(1 + 12 * (1 / 280 : ℝ)) * beta
        + (1 + 12 * (1 / 280 : ℝ)) * principalSqrtShift
        + (1 / 2 + 8 * (1 / 280 : ℝ)) + (1 / 280 : ℝ) + (1 / 2 : ℝ))
      ≤ Real.rpow D (-(1 / 250 : ℝ)) := by
  exact Real.rpow_le_rpow_of_exponent_le hD
    (principal_epsilon_error_exponent_280 hbeta)

private theorem sqrt_one_add_t_le_two_sqrt_D
    {D t : ℝ} (hD : 1 ≤ D) (ht : |t| ≤ D) :
    Real.sqrt (1 + |t|) ≤ 2 * Real.sqrt D := by
  have h1 : 1 + |t| ≤ 2 * D := by linarith [abs_nonneg t]
  have hsq := Real.sqrt_le_sqrt h1
  have hmul : Real.sqrt (2 * D) = Real.sqrt 2 * Real.sqrt D :=
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
  have h2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  calc
    Real.sqrt (1 + |t|) ≤ Real.sqrt (2 * D) := hsq
    _ = Real.sqrt 2 * Real.sqrt D := hmul
    _ ≤ 2 * Real.sqrt D :=
      mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)


/-- High-ordinate pole strictly below 1/2, using the same envelope as
`eventually_source_principalDetectorPole_lt_one`. -/
theorem eventually_source_principalDetectorPole_lt_half :
    ∀ᶠ D : ℝ in atTop, ∀ rho : ℂ,
      (279 / 280 : ℝ) ≤ rho.re → rho.re ≤ 1 →
      12 * Real.log D ≤ |rho.im| →
      ‖principalDetectorPole rho (lemmaSixSmoothScale (1 / 280) D)
        (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
        (sourceR (1 / 280) D)‖ < 1 / 2 := by
  have hδlo : (1 / 560 : ℝ) ≤ 1 / 280 := by norm_num
  have hδhi : (1 / 280 : ℝ) ≤ 1 / 280 := le_rfl
  filter_upwards [eventually_sourceGeometry hδlo hδhi,
    eventually_ge_atTop (25 : ℝ), eventually_ge_atTop (Real.exp 1)] with
    D hgeo hD hDe
  intro rho hbeta hbeta1 ht
  have hDp : 0 < D := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hbound := principalDetectorPole_norm_le
    (X := lemmaSixSmoothScale (1 / 280) D)
    (z1 := sourceZ1 (1 / 280) D) (z2 := sourceZ2 (1 / 280) D)
    (sourceR (1 / 280) D)
    (by linarith : 0 ≤ rho.re) hbeta1
    (by
      have hlogD : 1 ≤ Real.log D := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) hDe
      linarith)
    (by linarith [hgeo.X_two]) hgeo.z1_one hgeo.z12
  have hExp : Real.exp (-|rho.im| / 2) ≤ Real.rpow D (-6) := by
    have h := Real.exp_le_exp.mpr
      (show -|rho.im| / 2 ≤ (-6) * Real.log D by linarith only [ht])
    simpa [Real.rpow_def_of_pos hDp, mul_comm] using h
  have hXup : lemmaSixSmoothScale (1 / 280) D ≤ D ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hD1
      (show 1 + 12 * (1 / 280 : ℝ) ≤ (2 : ℝ) by norm_num)
    simpa [lemmaSixSmoothScale] using h
  have hRup : (sourceR (1 / 280) D : ℝ) ≤ D :=
    hgeo.R_upper.trans (Real.rpow_le_self_of_one_le hD1 (by norm_num))
  have hz2up : sourceZ2 (1 / 280) D ≤ D :=
    Real.rpow_le_self_of_one_le hD1 (by linarith)
  have hpow0 : 0 ≤ Real.rpow D (-6) := Real.rpow_nonneg hDp.le _
  have hX0 : 0 ≤ lemmaSixSmoothScale (1 / 280) D :=
    (lemmaSixSmoothScale_pos hDp).le
  have hz20 : 0 ≤ sourceZ2 (1 / 280) D :=
    (hgeo.z1_one.trans hgeo.z12).le.trans' zero_le_one
  calc
    _ ≤ 24 * Real.exp (-|rho.im| / 2) * lemmaSixSmoothScale (1 / 280) D *
          (sourceR (1 / 280) D : ℝ) * sourceZ2 (1 / 280) D := hbound
    _ ≤ 24 * Real.rpow D (-6) * D ^ 2 * D * D := by gcongr
    _ = 24 / D ^ 2 := by
      have hDpow : Real.rpow D (-6) * D ^ 2 * D * D = (D ^ 2)⁻¹ := by
        have hneg : Real.rpow D (-6) = (Real.rpow D 6)⁻¹ :=
          Real.rpow_neg hDp.le _
        rw [hneg]
        norm_num [Real.rpow_eq_pow]
        field_simp
      rw [show 24 * Real.rpow D (-6) * D ^ 2 * D * D =
          24 * (Real.rpow D (-6) * D ^ 2 * D * D) by ring, hDpow]
      simp [div_eq_mul_inv]
    _ < 1 / 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hDp)).2 (by
        nlinarith [sq_nonneg (D - 25)])

/-- Source-parameter smallness of the canonical detector series. -/
theorem eventually_principal_canonical_directSeries_lt_one :
    ∀ᶠ D : ℝ in atTop, ∀ (T omega : ℝ) (rho : ℂ),
      1 ≤ T → T = D → 0 ≤ omega →
      (279 / 280 : ℝ) ≤ rho.re → rho.re ≤ 1 - omega →
      |rho.im| ≤ T → 12 * Real.log D ≤ |rho.im| →
      principalF rho = 0 →
      ‖∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne
        (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
        (jutilaPrimedRSet 1 (sourceR (1 / 280) D)) rho
        (lemmaSixSmoothScale (1 / 280) D) n‖ < 1 := by
  obtain ⟨Cζ, hCζpos, hζ⟩ :=
    exists_riemannZeta_sqrt_bound principalSqrtShift_pos
      principalSqrtShift_le_one_eight
  have hCζ : 0 ≤ Cζ := hCζpos.le
  let K : ℝ :=
    (1 / (2 * Real.pi)) *
      (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
      Cζ * 2 * principalEpsilonVerticalMass
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) GammaConst_nonneg) hCζ)
        (by norm_num))
      principalEpsilonVerticalMass_nonneg
  have hpoly :=
    PostA5HighStripSplitReductionFromFourthMoment.eventually_const_mul_polylog_le_rpow
      (2 * K * 16) 4 (1 / 500)
      (by exact mul_nonneg (mul_nonneg (by norm_num) hK) (by norm_num))
      (by norm_num)
  have hδlo : (1 / 560 : ℝ) ≤ 1 / 280 := by norm_num
  have hδhi : (1 / 280 : ℝ) ≤ 1 / 280 := le_rfl
  have htwo :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 500)).eventually
      (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hpoly, eventually_source_principalDetectorPole_lt_half,
    eventually_sourceGeometry hδlo hδhi, eventually_ge_atTop (Real.exp 1),
    eventually_gt_atTop (1 : ℝ), htwo] with D hpoly hpole hgeo hDe hDone htwo
  intro T omega rho hT hDT _homega hrlo hrhi ht htHi hF
  have hDp : 0 < D := zero_lt_one.trans hDone
  have hD1 : 1 ≤ D := hDone.le
  have hbetaHi : rho.re < 1 :=
    MAPPrincipalZetaFixedStrip.principalRegularized_zero_re_lt_one hF
  have hbetaLo : (4 / 5 : ℝ) ≤ rho.re := by linarith
  have hz1 : 1 < sourceZ1 (1 / 280) D := hgeo.z1_one
  have hz12 : sourceZ1 (1 / 280) D < sourceZ2 (1 / 280) D := hgeo.z12
  have hX : 1 ≤ lemmaSixSmoothScale (1 / 280) D :=
    (by linarith : (1 : ℝ) ≤ 2).trans hgeo.X_two
  have hrpoint : lemmaSixZeroPoint rho.re rho.im = rho := by
    apply Complex.ext <;> simp [lemmaSixZeroPoint]
  let C : ℝ :=
    (Nat.floor (sourceZ2 (1 / 280) D) : ℝ) *
      (sourceR (1 / 280) D : ℝ) *
      (harmonic (sourceR (1 / 280) D) : ℝ) ^ 4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hM : ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chiOne
        (jutilaLambdaComplex (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D))
        (jutilaLambdaSupport (sourceZ2 (1 / 280) D))
        (jutilaPrimedRSet 1 (sourceR (1 / 280) D)) s‖ ≤ C :=
    fun s hs => by simpa [C] using
      norm_canonical_M_halfPlane_le hz1 hz12 (sourceR (1 / 280) D) hs
  have herr := norm_principal_canonical_epsilonError_le
    (beta := rho.re) (t := rho.im) hz1 hz12 hX hCζ hC hζ hM hbetaLo hbetaHi
    (by simpa [hrpoint] using hF)
  rw [hrpoint] at herr
  have htD : |rho.im| ≤ D := by rw [← hDT]; exact ht
  have hsqrt := sqrt_one_add_t_le_two_sqrt_D hD1 htD
  have hlog : 1 ≤ Real.log D := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hDe
  have hfloorZ : (Nat.floor (sourceZ2 (1 / 280) D) : ℝ) ≤
      sourceZ2 (1 / 280) D :=
    Nat.floor_le (Real.rpow_nonneg hDp.le _)
  have hCsrc : C ≤ Real.rpow D (1 / 2 + 8 * (1 / 280 : ℝ)) *
      Real.rpow D (1 / 280 : ℝ) * (1 + Real.log D) ^ 4 := by
    dsimp [C]
    have hz20 : 0 ≤ sourceZ2 (1 / 280) D :=
      (hz1.trans hz12).le.trans' zero_le_one
    have hR0 : 0 ≤ (sourceR (1 / 280) D : ℝ) := Nat.cast_nonneg _
    have hh0 : 0 ≤ (harmonic (sourceR (1 / 280) D) : ℝ) := by
      unfold harmonic
      positivity
    have hh : (harmonic (sourceR (1 / 280) D) : ℝ) ≤ 1 + Real.log D :=
      hgeo.harmonic_upper
    have hz2eq : sourceZ2 (1 / 280) D =
        Real.rpow D (1 / 2 + 8 * (1 / 280 : ℝ)) := rfl
    calc
      (Nat.floor (sourceZ2 (1 / 280) D) : ℝ) *
            (sourceR (1 / 280) D : ℝ) *
            (harmonic (sourceR (1 / 280) D) : ℝ) ^ 4 ≤
          sourceZ2 (1 / 280) D * (sourceR (1 / 280) D : ℝ) *
            (1 + Real.log D) ^ 4 := by
        apply mul_le_mul
        · exact mul_le_mul hfloorZ le_rfl hR0 hz20
        · exact pow_le_pow_left₀ hh0 hh 4
        · exact pow_nonneg hh0 4
        · exact mul_nonneg hz20 hR0
      _ ≤ Real.rpow D (1 / 2 + 8 * (1 / 280 : ℝ)) *
            Real.rpow D (1 / 280 : ℝ) * (1 + Real.log D) ^ 4 := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul
          · exact le_of_eq hz2eq
          · exact hgeo.R_upper
          · exact hR0
          · exact Real.rpow_nonneg hDp.le _
        · exact pow_nonneg (by linarith) 4
  have hxpow :
      Real.rpow (lemmaSixSmoothScale (1 / 280) D)
          (-rho.re + principalSqrtShift) =
        Real.rpow D ((1 + 12 * (1 / 280 : ℝ)) *
          (-rho.re + principalSqrtShift)) := by
    unfold lemmaSixSmoothScale
    exact (Real.rpow_mul hDp.le _ _).symm
  have hprod :
      Real.rpow D ((1 + 12 * (1 / 280 : ℝ)) *
          (-rho.re + principalSqrtShift)) *
        Real.rpow D (1 / 2 + 8 * (1 / 280 : ℝ)) *
        Real.rpow D (1 / 280 : ℝ) * Real.rpow D (1 / 2) =
      Real.rpow D
        (-(1 + 12 * (1 / 280 : ℝ)) * rho.re
          + (1 + 12 * (1 / 280 : ℝ)) * principalSqrtShift
          + (1 / 2 + 8 * (1 / 280 : ℝ)) + (1 / 280 : ℝ) + (1 / 2 : ℝ)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hDp, ← Real.rpow_add hDp, ← Real.rpow_add hDp]
    congr 1
    ring
  have hrem :
      (1 / (2 * Real.pi)) *
        ((12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
          Cζ * Real.sqrt (1 + |rho.im|) *
          Real.rpow (lemmaSixSmoothScale (1 / 280) D)
            (-rho.re + principalSqrtShift) * C *
          principalEpsilonVerticalMass) ≤
      K * (1 + Real.log D) ^ 4 *
        Real.rpow D
          (-(1 + 12 * (1 / 280 : ℝ)) * rho.re
            + (1 + 12 * (1 / 280 : ℝ)) * principalSqrtShift
            + (1 / 2 + 8 * (1 / 280 : ℝ)) + (1 / 280 : ℝ) + (1 / 2 : ℝ)) := by
    have hsqrtPow : Real.sqrt D = Real.rpow D (1 / 2) := Real.sqrt_eq_rpow _
    have hscale0 : 0 ≤ lemmaSixSmoothScale (1 / 280) D := by linarith
    have hpowscale0 : 0 ≤ Real.rpow (lemmaSixSmoothScale (1 / 280) D)
        (-rho.re + principalSqrtShift) := Real.rpow_nonneg hscale0 _
    have hprefix0 : 0 ≤
        (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) * Cζ *
          (2 * Real.sqrt D) *
          Real.rpow (lemmaSixSmoothScale (1 / 280) D)
            (-rho.re + principalSqrtShift) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg GammaConst_nonneg hCζ) (by positivity))
        hpowscale0
    have hprefixShort : 0 ≤
        (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) * Cζ *
          (2 * Real.sqrt D) :=
      mul_nonneg (mul_nonneg GammaConst_nonneg hCζ) (by positivity)
    dsimp [K]
    calc
      _ ≤ (1 / (2 * Real.pi)) *
            ((12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
              Cζ * (2 * Real.sqrt D) *
              Real.rpow (lemmaSixSmoothScale (1 / 280) D)
                (-rho.re + principalSqrtShift) *
              (Real.rpow D (1 / 2 + 8 * (1 / 280 : ℝ)) *
                Real.rpow D (1 / 280 : ℝ) * (1 + Real.log D) ^ 4) *
              principalEpsilonVerticalMass) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        gcongr
        · exact principalEpsilonVerticalMass_nonneg
        · exact mul_nonneg GammaConst_nonneg hCζ
        · rfl
      _ = ((1 / (2 * Real.pi)) *
            (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
            Cζ * 2 * principalEpsilonVerticalMass) *
          (1 + Real.log D) ^ 4 *
          (Real.rpow (lemmaSixSmoothScale (1 / 280) D)
              (-rho.re + principalSqrtShift) *
            Real.rpow D (1 / 2 + 8 * (1 / 280 : ℝ)) *
            Real.rpow D (1 / 280 : ℝ) * Real.sqrt D) := by ring
      _ = ((1 / (2 * Real.pi)) *
            (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
            Cζ * 2 * principalEpsilonVerticalMass) *
          (1 + Real.log D) ^ 4 *
          (Real.rpow D ((1 + 12 * (1 / 280 : ℝ)) *
              (-rho.re + principalSqrtShift)) *
            Real.rpow D (1 / 2 + 8 * (1 / 280 : ℝ)) *
            Real.rpow D (1 / 280 : ℝ) * Real.rpow D (1 / 2)) := by
        rw [hxpow, hsqrtPow]
      _ = _ := by
        rw [hprod]
        rfl
  have hpowLe := principal_epsilon_error_power_280 hD1 hrlo
  have hlog4 : (1 + Real.log D) ^ 4 ≤ 16 * (Real.log D) ^ 4 := by
    calc
      _ ≤ (2 * Real.log D) ^ 4 := by gcongr; linarith
      _ = _ := by ring
  have habsorb : K * (1 + Real.log D) ^ 4 ≤
      Real.rpow D (1 / 500) := by
    have hlogp : (Real.log D) ^ (4 : ℕ) = Real.rpow (Real.log D) 4 :=
      (Real.rpow_natCast _ 4).symm
    have hmain : (2 * K * 16) * Real.rpow (Real.log D) 4 ≤
        Real.rpow D (1 / 500) := hpoly
    have hposD : 0 ≤ Real.rpow D (1 / 500) := Real.rpow_nonneg hDp.le _
    calc
      K * (1 + Real.log D) ^ 4 ≤ K * (16 * (Real.log D) ^ 4) :=
        mul_le_mul_of_nonneg_left hlog4 hK
      _ = ((2 * K * 16) * Real.rpow (Real.log D) 4) / 2 := by
        rw [hlogp]; ring
      _ ≤ Real.rpow D (1 / 500) / 2 :=
        div_le_div_of_nonneg_right hmain (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ Real.rpow D (1 / 500) := by linarith [hposD]
  have hconst :
      K * (1 + Real.log D) ^ 4 * Real.rpow D (-(1 / 250 : ℝ)) < 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right habsorb
      (Real.rpow_nonneg hDp.le (-(1 / 250 : ℝ)))
    have heq : Real.rpow D (1 / 500) * Real.rpow D (-(1 / 250 : ℝ)) =
        Real.rpow D (-(1 / 500 : ℝ)) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hDp]
      congr 1
      norm_num
    have hlt : Real.rpow D (-(1 / 500 : ℝ)) ≤ 1 / 4 := by
      have hpos : 0 < Real.rpow D (1 / 500) := Real.rpow_pos_of_pos hDp _
      have hneg : Real.rpow D (-(1 / 500 : ℝ)) =
          (Real.rpow D (1 / 500))⁻¹ :=
        Real.rpow_neg hDp.le _
      rw [hneg]
      have htwo' : 4 ≤ Real.rpow D (1 / 500) := by
        simpa only [Real.rpow_eq_pow] using htwo
      exact (inv_le_iff_one_le_mul₀ hpos).mpr (by nlinarith [htwo'])
    have hmul' : K * (1 + Real.log D) ^ 4 *
        Real.rpow D (-(1 / 250 : ℝ)) ≤
        Real.rpow D (1 / 500) * Real.rpow D (-(1 / 250 : ℝ)) := by
      simpa only [Real.rpow_eq_pow] using hmul
    exact (hmul'.trans_eq heq).trans_lt
      (lt_of_le_of_lt hlt (by norm_num : (1 / 4 : ℝ) < 1 / 2))
  have htri :
      ‖∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne
        (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
        (jutilaPrimedRSet 1 (sourceR (1 / 280) D)) rho
        (lemmaSixSmoothScale (1 / 280) D) n‖ ≤
      ‖(∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne
          (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
          (jutilaPrimedRSet 1 (sourceR (1 / 280) D)) rho
          (lemmaSixSmoothScale (1 / 280) D) n) -
        principalDetectorPole rho (lemmaSixSmoothScale (1 / 280) D)
          (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
          (sourceR (1 / 280) D)‖ +
      ‖principalDetectorPole rho (lemmaSixSmoothScale (1 / 280) D)
        (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
        (sourceR (1 / 280) D)‖ :=
    norm_le_norm_sub_add _ _
  have hremSmall :
      ‖(∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne
          (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
          (jutilaPrimedRSet 1 (sourceR (1 / 280) D)) rho
          (lemmaSixSmoothScale (1 / 280) D) n) -
        principalDetectorPole rho (lemmaSixSmoothScale (1 / 280) D)
          (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
          (sourceR (1 / 280) D)‖ < 1 / 2 :=
    lt_of_le_of_lt herr <|
      lt_of_le_of_lt hrem <|
        lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left hpowLe
            (mul_nonneg hK (pow_nonneg (by linarith) _)))
          hconst
  have hpoleSmall := hpole rho hrlo (le_trans hrhi (by linarith)) htHi
  calc
    _ ≤ _ := htri
    _ < (1 / 2 : ℝ) + (1 / 2 : ℝ) := add_lt_add hremSmall hpoleSmall
    _ = 1 := by norm_num

end

end MAPJutilaPrincipalEpsilonRemainder

#print axioms MAPJutilaPrincipalEpsilonRemainder.norm_principal_canonical_epsilonError_le
#print axioms MAPJutilaPrincipalEpsilonRemainder.principal_epsilon_error_exponent_280
#print axioms MAPJutilaPrincipalEpsilonRemainder.eventually_principal_canonical_directSeries_lt_one
