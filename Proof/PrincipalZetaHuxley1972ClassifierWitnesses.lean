import AppendixA4DetectorDichotomy
import PrincipalZetaHuxley1972Equation314GammaNormalizer
import PrincipalZetaHuxley1972Equation315ClassifierArithmetic

/-!
# Huxley 1972, (3.12)--(3.15): literal classifier witnesses

This file attaches the two published alternatives to the two sides of the
contour identity.  In particular, it does not take a Type-I/Type-II cover as
an input.

There is one harmless source-normalization repair.  The shifted contour has
Gamma factor `Gamma (1/2-beta+iu)`, whereas the displayed normalizer (3.14)
is written with `Gamma (1/2+iu)`.  Since `c₂` is chosen after all absolute
constants, we use the certified compact-strip Gamma bound directly and choose
a (possibly smaller) explicit `c₂`.  This changes no class estimate later in
the paper: those estimates only use that `c₂` is a fixed positive constant.
-/

namespace MAPPrincipalZetaHuxley1972ClassifierWitnesses

open Set MeasureTheory Complex Filter
open scoped Topology ArithmeticFunction LSeries.notation BigOperators
open MAPMollifierCoefficientIdentity MAPAppendixA4GammaEndpoint
open MAPAppendixA4FullContourLimit MAPAppendixA4DetectorDichotomy
open MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic
open MAPGammaCompactStripSharp

noncomputable section

set_option maxHeartbeats 2400000

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-! ## The literal dyadic regions on the shifted contour -/

/-- The central region `|u| <= 2` used with class `(ii,1)`. -/
def huxleyCentralRegion : Set ℝ := {u | |u| ≤ 2}

/-- The `n`th exterior dyadic region.  Its radii are
`2^(n+1) < |u| <= 2^(n+2)`, so class `(ii,n+2)` controls the critical-line
factor throughout it. -/
def huxleyDyadicRegion (n : ℕ) : Set ℝ :=
  {u | (2 : ℝ) ^ (n + 1) < |u| ∧ |u| ≤ (2 : ℝ) ^ (n + 2)}

/-- The central region together with all exterior dyadic regions. -/
def huxleyContourRegion : Option ℕ → Set ℝ
  | none => huxleyCentralRegion
  | some n => huxleyDyadicRegion n

theorem measurableSet_huxleyCentralRegion :
    MeasurableSet huxleyCentralRegion := by
  exact measurableSet_le continuous_abs.measurable measurable_const

theorem measurableSet_huxleyDyadicRegion (n : ℕ) :
    MeasurableSet (huxleyDyadicRegion n) := by
  exact (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

theorem measurableSet_huxleyContourRegion (i : Option ℕ) :
    MeasurableSet (huxleyContourRegion i) := by
  cases i with
  | none => exact measurableSet_huxleyCentralRegion
  | some n => exact measurableSet_huxleyDyadicRegion n

private theorem two_pow_strictMono : StrictMono (fun n : ℕ => (2 : ℝ) ^ n) :=
  strictMono_nat_of_lt_succ fun n => by
    rw [pow_succ]
    have hpos : 0 < (2 : ℝ) ^ n := by positivity
    nlinarith

private theorem huxleyDyadicRegion_disjoint_of_lt
    {m n : ℕ} (hmn : m < n) :
    Disjoint (huxleyDyadicRegion m) (huxleyDyadicRegion n) := by
  rw [Set.disjoint_left]
  intro u hum hun
  have hmUpper : |u| ≤ (2 : ℝ) ^ (m + 2) := hum.2
  have hnLower : (2 : ℝ) ^ (n + 1) < |u| := hun.1
  have hindex : m + 2 ≤ n + 1 := by omega
  have hpowers : (2 : ℝ) ^ (m + 2) ≤ (2 : ℝ) ^ (n + 1) :=
    two_pow_strictMono.monotone hindex
  linarith

theorem pairwiseDisjoint_huxleyContourRegion :
    Pairwise (Function.onFun Disjoint huxleyContourRegion) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some n =>
          unfold Function.onFun
          rw [Set.disjoint_left]
          intro u huC huD
          have hlow : (2 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
            have : (1 : ℕ) ≤ n + 1 := by omega
            simpa using two_pow_strictMono.monotone this
          exact (not_lt_of_ge (huC.trans hlow)) huD.1
  | some m =>
      cases j with
      | none =>
          unfold Function.onFun
          rw [Set.disjoint_left]
          intro u huD huC
          have hlow : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
            have : (1 : ℕ) ≤ m + 1 := by omega
            simpa using two_pow_strictMono.monotone this
          exact (not_lt_of_ge (huC.trans hlow)) huD.1
      | some n =>
          unfold Function.onFun
          have hmn : m < n ∨ n < m := Nat.lt_or_gt_of_ne (by
            intro h
            apply hij
            simpa using congrArg some h)
          rcases hmn with hmn | hnm
          · exact huxleyDyadicRegion_disjoint_of_lt hmn
          · exact (huxleyDyadicRegion_disjoint_of_lt hnm).symm

private theorem exists_two_pow_ge (x : ℝ) :
    ∃ n : ℕ, x ≤ (2 : ℝ) ^ n := by
  have h := (tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 2)).eventually (eventually_ge_atTop x)
  exact h.exists

theorem iUnion_huxleyContourRegion :
    (⋃ i : Option ℕ, huxleyContourRegion i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro u
  by_cases hcentral : |u| ≤ 2
  · rw [Set.mem_iUnion]
    exact ⟨none, hcentral⟩
  · have hlarge : (2 : ℝ) < |u| := lt_of_not_ge hcentral
    obtain ⟨N, hN⟩ := exists_two_pow_ge |u|
    have hex : ∃ n : ℕ, |u| ≤ (2 : ℝ) ^ (n + 2) := by
      exact ⟨N, hN.trans (two_pow_strictMono.monotone (by omega))⟩
    let n := Nat.find hex
    have hnUpper : |u| ≤ (2 : ℝ) ^ (n + 2) := Nat.find_spec hex
    have hnLower : (2 : ℝ) ^ (n + 1) < |u| := by
      by_cases hn0 : n = 0
      · rw [hn0]
        norm_num
        exact hlarge
      · have hpred : n - 1 < n := Nat.pred_lt hn0
        have hnot := Nat.find_min hex hpred
        have hshape : n - 1 + 2 = n + 1 := by omega
        rw [hshape] at hnot
        exact lt_of_not_ge hnot
    rw [Set.mem_iUnion]
    exact ⟨some n, hnLower, hnUpper⟩

/-! ## Literal class predicates -/

/-- Huxley's class `(ii,n)`, equation (3.13), written at the actual
critical-line ordinate `t`. -/
def HuxleyClassIIAt
    (rho : ℂ) (U : ℕ) (Y alpha c₂ : ℝ) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ t : ℝ,
    |rho.im - t| ≤ (2 : ℝ) ^ n ∧
      c₂ * (2 : ℝ) ^ n * Real.rpow Y (alpha - 1 / 2) <
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I) *
          mollifier chiOne U (((1 / 2 : ℝ) : ℂ) + t * I)‖

def HuxleyClassII
    (rho : ℂ) (U : ℕ) (Y alpha c₂ : ℝ) : Prop :=
  ∃ n : ℕ, HuxleyClassIIAt rho U Y alpha c₂ n

theorem criticalLineProductNorm_le_of_not_classII
    {rho : ℂ} {U : ℕ} {Y alpha c₂ : ℝ}
    (hnot : ¬ HuxleyClassII rho U Y alpha c₂)
    {n : ℕ} (hn : 1 ≤ n) {u : ℝ}
    (hu : |u| ≤ (2 : ℝ) ^ n) :
    MAPAppendixA4DetectorDichotomy.criticalLineProductNorm
        chiOne U rho u ≤
      c₂ * (2 : ℝ) ^ n * Real.rpow Y (alpha - 1 / 2) := by
  rw [MAPAppendixA4DetectorDichotomy.criticalLineProductNorm_eq]
  rw [DirichletCharacter.LFunction_modOne_eq]
  have hnear : |rho.im - (rho.im + u)| ≤ (2 : ℝ) ^ n := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hu
  by_contra hle
  apply hnot
  refine ⟨n, hn, rho.im + u, hnear, ?_⟩
  simpa [Complex.ofReal_add, add_mul] using (lt_of_not_ge hle)

/-! ## A shifted-strip replacement for the implicit constant in (3.14) -/

/-- A safe upper budget for the `n`th exterior region.  The four factors are
the compact-strip Gamma constant, the class `(ii,n+2)` threshold, the
largest polynomial Gamma factor, and the length of the containing interval.
-/
def shiftedEquation314TailMajorant (n : ℕ) : ℝ :=
  12 * (2 : ℝ) ^ (n + 2) * (1 + (2 : ℝ) ^ (n + 2)) *
    Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1)) *
      (2 : ℝ) ^ (n + 3)

private theorem two_mul_nat_le_two_pow
    {m : ℕ} (hm : 1 ≤ m) : 2 * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [pow_succ]
      have hpow : 2 ≤ 2 ^ m := by
        exact (show 2 = 2 ^ 1 by norm_num) ▸
          Nat.pow_le_pow_right (by norm_num) hm
      omega

private theorem eight_mul_exp_neg_pi_lt_one :
    8 * Real.exp (-Real.pi) < 1 := by
  have hexp3 : (8 : ℝ) < Real.exp 3 := by
    have h := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hexppi : (8 : ℝ) < Real.exp Real.pi :=
    hexp3.trans (Real.exp_lt_exp.mpr Real.pi_gt_three)
  have hpos : 0 < Real.exp Real.pi := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_lt_one hpos).2 hexppi

theorem summable_shiftedEquation314TailMajorant :
    Summable shiftedEquation314TailMajorant := by
  let r : ℝ := 8 * Real.exp (-Real.pi)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by simpa [r] using eight_mul_exp_neg_pi_lt_one
  have hgeom : Summable (fun n : ℕ =>
      (3072 * Real.exp (-Real.pi)) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left
      (3072 * Real.exp (-Real.pi))
  apply Summable.of_nonneg_of_le
    (fun n => by unfold shiftedEquation314TailMajorant; positivity) _ hgeom
  intro n
  have hpowOne : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 2) := by
    exact one_le_pow₀ (by norm_num)
  have hadd : 1 + (2 : ℝ) ^ (n + 2) ≤
      (2 : ℝ) ^ (n + 3) := by
    calc
      1 + (2 : ℝ) ^ (n + 2) ≤
          (2 : ℝ) ^ (n + 2) + (2 : ℝ) ^ (n + 2) := by
        linarith
      _ = (2 : ℝ) ^ (n + 3) := by
        rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
        ring
  have hnat : 2 * (n + 1) ≤ 2 ^ (n + 1) :=
    two_mul_nat_le_two_pow (by omega)
  have hnatReal : (2 : ℝ) * (n + 1) ≤
      (2 : ℝ) ^ (n + 1) := by exact_mod_cast hnat
  have hexp :
      Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1)) ≤
        Real.exp (-Real.pi * (n + 1)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hpowers :
      (2 : ℝ) ^ (n + 2) * (2 : ℝ) ^ (n + 3) *
          (2 : ℝ) ^ (n + 3) =
        256 * (8 : ℝ) ^ n := by
    rw [← pow_add, ← pow_add]
    rw [show n + 2 + (n + 3) + (n + 3) = 3 * n + 8 by omega,
      pow_add, pow_mul]
    norm_num
    ring
  have hexpSplit :
      Real.exp (-Real.pi * (n + 1)) =
        Real.exp (-Real.pi) * (Real.exp (-Real.pi)) ^ n := by
    rw [show -Real.pi * (n + 1) = -Real.pi + n * (-Real.pi) by ring,
      Real.exp_add, Real.exp_nat_mul]
  calc
    shiftedEquation314TailMajorant n ≤
        12 * (2 : ℝ) ^ (n + 2) * (2 : ℝ) ^ (n + 3) *
          Real.exp (-Real.pi * (n + 1)) * (2 : ℝ) ^ (n + 3) := by
      unfold shiftedEquation314TailMajorant
      gcongr
    _ = (3072 * Real.exp (-Real.pi)) * r ^ n := by
      rw [show 12 * (2 : ℝ) ^ (n + 2) * (2 : ℝ) ^ (n + 3) *
            Real.exp (-Real.pi * (n + 1)) * (2 : ℝ) ^ (n + 3) =
          12 * ((2 : ℝ) ^ (n + 2) * (2 : ℝ) ^ (n + 3) *
            (2 : ℝ) ^ (n + 3)) * Real.exp (-Real.pi * (n + 1)) by ring,
        hpowers, hexpSplit]
      dsimp [r]
      rw [mul_pow]
      ring

/-- `464 = 4 * 2 * 58` is the central-region cost: length four, class
`(ii,1)` threshold two, and the certified full shifted-kernel constant 58. -/
def shiftedEquation314Normalizer : ℝ :=
  Real.pi /
    (3 * (464 + ∑' n : ℕ, shiftedEquation314TailMajorant n))

theorem shiftedEquation314Normalizer_pos :
    0 < shiftedEquation314Normalizer := by
  unfold shiftedEquation314Normalizer
  apply div_pos Real.pi_pos
  have hsum : 0 ≤ ∑' n : ℕ, shiftedEquation314TailMajorant n :=
    tsum_nonneg fun n => by unfold shiftedEquation314TailMajorant; positivity
  positivity

theorem shiftedEquation314Normalizer_normalized_budget :
    shiftedEquation314Normalizer *
          (464 + ∑' n : ℕ, shiftedEquation314TailMajorant n) /
        (2 * Real.pi) < 1 / 3 := by
  have hsum : 0 ≤ ∑' n : ℕ, shiftedEquation314TailMajorant n :=
    tsum_nonneg fun n => by unfold shiftedEquation314TailMajorant; positivity
  have hK : 0 < 464 + ∑' n : ℕ, shiftedEquation314TailMajorant n := by
    positivity
  unfold shiftedEquation314Normalizer
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hK.ne', hpi]
  nlinarith [Real.pi_pos]

/-! ## Failure of (3.13) bounds each literal integral piece -/

theorem norm_gammaLeftIntegrand_central_le_of_not_classII
    {rho : ℂ} {U : ℕ} {Y alpha c₂ u : ℝ}
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hY : 1 ≤ Y) (hc₂ : 0 ≤ c₂)
    (hnot : ¬ HuxleyClassII rho U Y alpha c₂)
    (hu : u ∈ huxleyCentralRegion) :
    ‖gammaLeftIntegrand chiOne U rho Y u‖ ≤
      116 * c₂ * Real.rpow Y (alpha - rho.re) := by
  have hprod := criticalLineProductNorm_le_of_not_classII hnot
    (n := 1) (by omega) (u := u) (by simpa [huxleyCentralRegion] using hu)
  have hkernel := gammaLeftKernelNorm_le_uniform
    hbetaLow hbetaHigh hY u
  have hinv : (1 + u ^ 2)⁻¹ ≤ (1 : ℝ) := by
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg u])
  have hkernel' : gammaLeftKernelNorm rho Y u ≤
      58 * Real.rpow Y (1 / 2 - rho.re) := by
    calc
      gammaLeftKernelNorm rho Y u ≤
          58 * Real.rpow Y (1 / 2 - rho.re) * (1 + u ^ 2)⁻¹ := hkernel
      _ ≤ 58 * Real.rpow Y (1 / 2 - rho.re) * 1 := by
        exact mul_le_mul_of_nonneg_left hinv
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (zero_le_one.trans hY) _))
      _ = 58 * Real.rpow Y (1 / 2 - rho.re) := by ring
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hk0 : 0 ≤ gammaLeftKernelNorm rho Y u := norm_nonneg _
  have hp0 : 0 ≤ criticalLineProductNorm chiOne U rho u := norm_nonneg _
  have hkernelR0 : 0 ≤ 58 * Real.rpow Y (1 / 2 - rho.re) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hYpos.le _)
  have hrpow : Real.rpow Y (1 / 2 - rho.re) *
      Real.rpow Y (alpha - 1 / 2) = Real.rpow Y (alpha - rho.re) := by
    calc
      Real.rpow Y (1 / 2 - rho.re) * Real.rpow Y (alpha - 1 / 2) =
          Real.rpow Y ((1 / 2 - rho.re) + (alpha - 1 / 2)) :=
        (Real.rpow_add hYpos _ _).symm
      _ = Real.rpow Y (alpha - rho.re) := by congr 1; ring
  rw [norm_gammaLeftIntegrand_eq_kernel_mul_criticalLineProductNorm]
  calc
    gammaLeftKernelNorm rho Y u * criticalLineProductNorm chiOne U rho u ≤
        (58 * Real.rpow Y (1 / 2 - rho.re)) *
          (c₂ * (2 : ℝ) ^ (1 : ℕ) *
            Real.rpow Y (alpha - 1 / 2)) :=
      mul_le_mul hkernel' hprod hp0
        hkernelR0
    _ = 116 * c₂ *
          (Real.rpow Y (1 / 2 - rho.re) *
            Real.rpow Y (alpha - 1 / 2)) := by norm_num; ring
    _ = 116 * c₂ * Real.rpow Y (alpha - rho.re) := by
      rw [hrpow]

private theorem gammaLeftKernelNorm_le_sharp_on_dyadic
    {rho : ℂ} {Y u : ℝ} {n : ℕ}
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hY : 1 ≤ Y) (hu : u ∈ huxleyDyadicRegion n) :
    gammaLeftKernelNorm rho Y u ≤
      12 * (1 + (2 : ℝ) ^ (n + 2)) *
        Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1)) *
          Real.rpow Y (1 / 2 - rho.re) := by
  let a : ℝ := 1 / 2 - rho.re
  have haLow : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have haHigh : a ≤ 1 / 2 := by dsimp [a]; linarith
  have huOne : 1 ≤ |u| := by
    have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      simpa using two_pow_strictMono.monotone (show 1 ≤ n + 1 by omega)
    linarith [hu.1]
  have hgamma := norm_Gamma_compactStrip_le_exp_pi_half
    haLow haHigh huOne
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hYpow :
      ‖(Y : ℂ) ^ ((a : ℂ) + u * I)‖ = Real.rpow Y a := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp
  have hpoly : 1 + |u| ≤ 1 + (2 : ℝ) ^ (n + 2) := by linarith [hu.2]
  have hexp : Real.exp (-(Real.pi / 2) * |u|) ≤
      Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, hu.1]
  unfold gammaLeftKernelNorm
  dsimp only [a]
  rw [norm_mul, hYpow]
  calc
    ‖Complex.Gamma ((a : ℂ) + u * I)‖ * Real.rpow Y a ≤
        (12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) *
          Real.rpow Y a :=
      mul_le_mul_of_nonneg_right hgamma (Real.rpow_nonneg hYpos.le _)
    _ ≤ (12 * (1 + (2 : ℝ) ^ (n + 2)) *
          Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1))) *
            Real.rpow Y a := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hYpos.le _)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hpoly (by norm_num)) hexp
        (Real.exp_nonneg _)
        (mul_nonneg (by norm_num) (by positivity))
    _ = 12 * (1 + (2 : ℝ) ^ (n + 2)) *
        Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1)) *
          Real.rpow Y (1 / 2 - rho.re) := by rfl

theorem norm_gammaLeftIntegrand_dyadic_le_of_not_classII
    {rho : ℂ} {U n : ℕ} {Y alpha c₂ u : ℝ}
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hY : 1 ≤ Y) (hc₂ : 0 ≤ c₂)
    (hnot : ¬ HuxleyClassII rho U Y alpha c₂)
    (hu : u ∈ huxleyDyadicRegion n) :
    ‖gammaLeftIntegrand chiOne U rho Y u‖ ≤
      (12 * (2 : ℝ) ^ (n + 2) *
        (1 + (2 : ℝ) ^ (n + 2)) *
          Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1))) *
            c₂ * Real.rpow Y (alpha - rho.re) := by
  have hprod := criticalLineProductNorm_le_of_not_classII hnot
    (n := n + 2) (by omega) (u := u) hu.2
  have hkernel := gammaLeftKernelNorm_le_sharp_on_dyadic
    hbetaLow hbetaHigh hY hu
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hp0 : 0 ≤ criticalLineProductNorm chiOne U rho u := norm_nonneg _
  have hright0 : 0 ≤ c₂ * (2 : ℝ) ^ (n + 2) *
      Real.rpow Y (alpha - 1 / 2) :=
    mul_nonneg (mul_nonneg hc₂ (by positivity))
      (Real.rpow_nonneg hYpos.le _)
  have hkernelR0 : 0 ≤
      12 * (1 + (2 : ℝ) ^ (n + 2)) *
        Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1)) *
          Real.rpow Y (1 / 2 - rho.re) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (by positivity))
        (Real.exp_nonneg _))
      (Real.rpow_nonneg hYpos.le _)
  have hrpow : Real.rpow Y (1 / 2 - rho.re) *
      Real.rpow Y (alpha - 1 / 2) = Real.rpow Y (alpha - rho.re) := by
    calc
      Real.rpow Y (1 / 2 - rho.re) * Real.rpow Y (alpha - 1 / 2) =
          Real.rpow Y ((1 / 2 - rho.re) + (alpha - 1 / 2)) :=
        (Real.rpow_add hYpos _ _).symm
      _ = Real.rpow Y (alpha - rho.re) := by congr 1; ring
  rw [norm_gammaLeftIntegrand_eq_kernel_mul_criticalLineProductNorm]
  calc
    gammaLeftKernelNorm rho Y u * criticalLineProductNorm chiOne U rho u ≤
        (12 * (1 + (2 : ℝ) ^ (n + 2)) *
          Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1)) *
            Real.rpow Y (1 / 2 - rho.re)) *
          (c₂ * (2 : ℝ) ^ (n + 2) *
            Real.rpow Y (alpha - 1 / 2)) :=
      mul_le_mul hkernel hprod hp0 hkernelR0
    _ = (12 * (2 : ℝ) ^ (n + 2) *
        (1 + (2 : ℝ) ^ (n + 2)) *
          Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1))) *
            c₂ * (Real.rpow Y (1 / 2 - rho.re) *
              Real.rpow Y (alpha - 1 / 2)) := by ring
    _ = (12 * (2 : ℝ) ^ (n + 2) *
        (1 + (2 : ℝ) ^ (n + 2)) *
          Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1))) *
            c₂ * Real.rpow Y (alpha - rho.re) := by
      rw [hrpow]

theorem volumeReal_huxleyCentralRegion_le_four :
    volume.real huxleyCentralRegion ≤ 4 := by
  have hsubset : huxleyCentralRegion ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro u hu
    rw [huxleyCentralRegion, Set.mem_setOf_eq] at hu
    exact (abs_le.mp hu)
  calc
    volume.real huxleyCentralRegion ≤ volume.real (Set.Icc (-2 : ℝ) 2) :=
      measureReal_mono hsubset measure_Icc_lt_top.ne
    _ = 4 := by
      rw [measureReal_def, Real.volume_Icc]
      norm_num

theorem volumeReal_huxleyDyadicRegion_le (n : ℕ) :
    volume.real (huxleyDyadicRegion n) ≤ (2 : ℝ) ^ (n + 3) := by
  let D : ℝ := (2 : ℝ) ^ (n + 2)
  have hsubset : huxleyDyadicRegion n ⊆ Set.Icc (-D) D := by
    intro u hu
    exact (abs_le.mp hu.2)
  calc
    volume.real (huxleyDyadicRegion n) ≤ volume.real (Set.Icc (-D) D) :=
      measureReal_mono hsubset measure_Icc_lt_top.ne
    _ = 2 * D := by
      have hD0 : 0 ≤ D := by dsimp [D]; positivity
      rw [measureReal_def, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith)]
      ring
    _ = (2 : ℝ) ^ (n + 3) := by
      dsimp [D]
      rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
      ring

theorem norm_setIntegral_central_le_of_not_classII
    {rho : ℂ} {U : ℕ} {Y alpha c₂ : ℝ}
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hY : 1 ≤ Y) (hc₂ : 0 ≤ c₂)
    (hnot : ¬ HuxleyClassII rho U Y alpha c₂) :
    ‖∫ u : ℝ in huxleyCentralRegion,
        gammaLeftIntegrand chiOne U rho Y u‖ ≤
      464 * c₂ * Real.rpow Y (alpha - rho.re) := by
  have hpoint : ∀ u : ℝ, u ∈ huxleyCentralRegion →
      ‖gammaLeftIntegrand chiOne U rho Y u‖ ≤
        116 * c₂ * Real.rpow Y (alpha - rho.re) := fun u hu =>
    norm_gammaLeftIntegrand_central_le_of_not_classII
      hbetaLow hbetaHigh hY hc₂ hnot hu
  have hsubset : huxleyCentralRegion ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro u hu
    exact abs_le.mp hu
  have hfinite : volume huxleyCentralRegion < ⊤ :=
    (measure_mono hsubset).trans_lt measure_Icc_lt_top
  have hraw := norm_setIntegral_le_of_norm_le_const
    hfinite hpoint
  have hC0 : 0 ≤ 116 * c₂ * Real.rpow Y (alpha - rho.re) :=
    mul_nonneg (mul_nonneg (by norm_num) hc₂)
      (Real.rpow_nonneg (zero_le_one.trans hY) _)
  calc
    ‖∫ u : ℝ in huxleyCentralRegion,
        gammaLeftIntegrand chiOne U rho Y u‖ ≤
        (116 * c₂ * Real.rpow Y (alpha - rho.re)) *
          volume.real huxleyCentralRegion := hraw
    _ ≤ (116 * c₂ * Real.rpow Y (alpha - rho.re)) * 4 :=
      mul_le_mul_of_nonneg_left volumeReal_huxleyCentralRegion_le_four hC0
    _ = 464 * c₂ * Real.rpow Y (alpha - rho.re) := by ring

theorem norm_setIntegral_dyadic_le_of_not_classII
    {rho : ℂ} {U n : ℕ} {Y alpha c₂ : ℝ}
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hY : 1 ≤ Y) (hc₂ : 0 ≤ c₂)
    (hnot : ¬ HuxleyClassII rho U Y alpha c₂) :
    ‖∫ u : ℝ in huxleyDyadicRegion n,
        gammaLeftIntegrand chiOne U rho Y u‖ ≤
      c₂ * Real.rpow Y (alpha - rho.re) *
        shiftedEquation314TailMajorant n := by
  let C : ℝ :=
    (12 * (2 : ℝ) ^ (n + 2) *
      (1 + (2 : ℝ) ^ (n + 2)) *
        Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (n + 1))) *
          c₂ * Real.rpow Y (alpha - rho.re)
  have hpoint : ∀ u ∈ huxleyDyadicRegion n,
      ‖gammaLeftIntegrand chiOne U rho Y u‖ ≤ C := by
    intro u hu
    simpa [C] using norm_gammaLeftIntegrand_dyadic_le_of_not_classII
      hbetaLow hbetaHigh hY hc₂ hnot hu
  have hfinite : volume (huxleyDyadicRegion n) < ⊤ :=
    (measure_mono (show huxleyDyadicRegion n ⊆
        Set.Icc (-((2 : ℝ) ^ (n + 2))) ((2 : ℝ) ^ (n + 2)) by
          intro u hu
          exact abs_le.mp hu.2)).trans_lt
      (measure_Icc_lt_top (μ := volume))
  have hraw := norm_setIntegral_le_of_norm_le_const hfinite hpoint
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (by positivity)) (by positivity))
          (Real.exp_nonneg _)) hc₂)
      (Real.rpow_nonneg (zero_le_one.trans hY) _)
  calc
    ‖∫ u : ℝ in huxleyDyadicRegion n,
        gammaLeftIntegrand chiOne U rho Y u‖ ≤
        C * volume.real (huxleyDyadicRegion n) := hraw
    _ ≤ C * (2 : ℝ) ^ (n + 3) :=
      mul_le_mul_of_nonneg_left (volumeReal_huxleyDyadicRegion_le n) hC0
    _ = c₂ * Real.rpow Y (alpha - rho.re) *
        shiftedEquation314TailMajorant n := by
      unfold C shiftedEquation314TailMajorant
      ring

/-- Failure of every literal class-II inequality (3.13) makes the complete
shifted contour integral small.  This is the missing analytic attachment
between (3.13), the dyadic Gamma budget, and the sentence immediately after
(3.14). -/
theorem huxleyEquation314_full_shifted_integral_lt_oneThird_of_not_classII
    {rho : ℂ} {U : ℕ} {Y alpha : ℝ}
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hY : 1 ≤ Y) (halpha : alpha ≤ rho.re)
    (hintegrable : Integrable (gammaLeftIntegrand chiOne U rho Y))
    (hnot : ¬ HuxleyClassII rho U Y alpha shiftedEquation314Normalizer) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ u : ℝ, gammaLeftIntegrand chiOne U rho Y u)‖ < 1 / 3 := by
  let f : ℝ → ℂ := gammaLeftIntegrand chiOne U rho Y
  let B : Option ℕ → ℝ
    | none => 464 * shiftedEquation314Normalizer *
        Real.rpow Y (alpha - rho.re)
    | some n => shiftedEquation314Normalizer *
        Real.rpow Y (alpha - rho.re) * shiftedEquation314TailMajorant n
  have hfi : IntegrableOn f (⋃ i : Option ℕ, huxleyContourRegion i) volume := by
    rw [iUnion_huxleyContourRegion]
    simpa [f] using hintegrable
  have hregions := hasSum_integral_iUnion (f := f) (μ := volume)
    measurableSet_huxleyContourRegion
    pairwiseDisjoint_huxleyContourRegion
    hfi
  have hregions' : HasSum
      (fun i : Option ℕ => ∫ u : ℝ in huxleyContourRegion i, f u)
      (∫ u : ℝ, f u) := by
    simpa [iUnion_huxleyContourRegion] using hregions
  have hscale0 : 0 ≤ Real.rpow Y (alpha - rho.re) :=
    Real.rpow_nonneg (zero_le_one.trans hY) _
  have hfactor0 : 0 ≤ shiftedEquation314Normalizer *
      Real.rpow Y (alpha - rho.re) :=
    mul_nonneg shiftedEquation314Normalizer_pos.le hscale0
  have htailSum : HasSum
      (fun n : ℕ => shiftedEquation314Normalizer *
        Real.rpow Y (alpha - rho.re) * shiftedEquation314TailMajorant n)
      (shiftedEquation314Normalizer * Real.rpow Y (alpha - rho.re) *
        ∑' n : ℕ, shiftedEquation314TailMajorant n) :=
    summable_shiftedEquation314TailMajorant.hasSum.mul_left
      (shiftedEquation314Normalizer * Real.rpow Y (alpha - rho.re))
  have hcentralSum : HasSum
      (fun _u : PUnit.{1} => 464 * shiftedEquation314Normalizer *
        Real.rpow Y (alpha - rho.re))
      (464 * shiftedEquation314Normalizer *
        Real.rpow Y (alpha - rho.re)) := by
    simpa using hasSum_fintype
      (fun _u : PUnit.{1} => 464 * shiftedEquation314Normalizer *
        Real.rpow Y (alpha - rho.re))
  let BSum : ℕ ⊕ PUnit.{1} → ℝ
    | Sum.inl n => shiftedEquation314Normalizer *
        Real.rpow Y (alpha - rho.re) * shiftedEquation314TailMajorant n
    | Sum.inr _ => 464 * shiftedEquation314Normalizer *
        Real.rpow Y (alpha - rho.re)
  have hbudgetSum : HasSum B
      (shiftedEquation314Normalizer * Real.rpow Y (alpha - rho.re) *
          ∑' n : ℕ, shiftedEquation314TailMajorant n +
        464 * shiftedEquation314Normalizer *
          Real.rpow Y (alpha - rho.re)) := by
    have hsumOnSum : HasSum BSum
        (shiftedEquation314Normalizer * Real.rpow Y (alpha - rho.re) *
            ∑' n : ℕ, shiftedEquation314TailMajorant n +
          464 * shiftedEquation314Normalizer *
            Real.rpow Y (alpha - rho.re)) := by
      simpa [BSum, Function.comp_def] using htailSum.sum hcentralSum
    let e := Equiv.optionEquivSumPUnit.{0, 0} ℕ
    have htransport : HasSum (BSum ∘ e)
        (shiftedEquation314Normalizer * Real.rpow Y (alpha - rho.re) *
            ∑' n : ℕ, shiftedEquation314TailMajorant n +
          464 * shiftedEquation314Normalizer *
            Real.rpow Y (alpha - rho.re)) :=
      (e.hasSum_iff).2 hsumOnSum
    have hfun : BSum ∘ e = B := by
      funext i
      cases i <;> rfl
    rwa [hfun] at htransport
  have hpiece : ∀ i : Option ℕ,
      ‖∫ u : ℝ in huxleyContourRegion i, f u‖ ≤ B i := by
    intro i
    cases i with
    | none =>
        simpa [B, f, huxleyContourRegion] using
          norm_setIntegral_central_le_of_not_classII
            hbetaLow hbetaHigh hY shiftedEquation314Normalizer_pos.le hnot
    | some n =>
        simpa [B, f, huxleyContourRegion] using
          norm_setIntegral_dyadic_le_of_not_classII
            (n := n) hbetaLow hbetaHigh hY
              shiftedEquation314Normalizer_pos.le hnot
  have hfull : ‖∫ u : ℝ, f u‖ ≤
      shiftedEquation314Normalizer * Real.rpow Y (alpha - rho.re) *
          ∑' n : ℕ, shiftedEquation314TailMajorant n +
        464 * shiftedEquation314Normalizer *
          Real.rpow Y (alpha - rho.re) :=
    hregions'.norm_le_of_bounded hbudgetSum hpiece
  have hscale1 : Real.rpow Y (alpha - rho.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hY (by linarith)
  have hK0 : 0 ≤ 464 + ∑' n : ℕ, shiftedEquation314TailMajorant n := by
    have htail0 : 0 ≤ ∑' n : ℕ, shiftedEquation314TailMajorant n :=
      tsum_nonneg fun n : ℕ => by
      unfold shiftedEquation314TailMajorant
      positivity
    positivity
  have hfull' : ‖∫ u : ℝ, f u‖ ≤
      shiftedEquation314Normalizer *
        (464 + ∑' n : ℕ, shiftedEquation314TailMajorant n) := by
    calc
      ‖∫ u : ℝ, f u‖ ≤
          shiftedEquation314Normalizer * Real.rpow Y (alpha - rho.re) *
              ∑' n : ℕ, shiftedEquation314TailMajorant n +
            464 * shiftedEquation314Normalizer *
              Real.rpow Y (alpha - rho.re) := hfull
      _ = (shiftedEquation314Normalizer *
            (464 + ∑' n : ℕ, shiftedEquation314TailMajorant n)) *
          Real.rpow Y (alpha - rho.re) := by ring
      _ ≤ (shiftedEquation314Normalizer *
            (464 + ∑' n : ℕ, shiftedEquation314TailMajorant n)) * 1 := by
        exact mul_le_mul_of_nonneg_left hscale1
          (mul_nonneg shiftedEquation314Normalizer_pos.le hK0)
      _ = shiftedEquation314Normalizer *
          (464 + ∑' n : ℕ, shiftedEquation314TailMajorant n) := by ring
  have hpi2 : 0 < 2 * Real.pi := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hscaled : (1 / (2 * Real.pi)) * ‖∫ u : ℝ, f u‖ ≤
      shiftedEquation314Normalizer *
          (464 + ∑' n : ℕ, shiftedEquation314TailMajorant n) /
        (2 * Real.pi) := by
    have hmul := mul_le_mul_of_nonneg_left hfull'
      (show 0 ≤ (2 * Real.pi)⁻¹ by positivity)
    simpa [div_eq_mul_inv, mul_comm] using hmul
  exact hscaled.trans_lt shiftedEquation314Normalizer_normalized_budget

end
end MAPPrincipalZetaHuxley1972ClassifierWitnesses

#print axioms MAPPrincipalZetaHuxley1972ClassifierWitnesses.iUnion_huxleyContourRegion
#print axioms MAPPrincipalZetaHuxley1972ClassifierWitnesses.pairwiseDisjoint_huxleyContourRegion
#print axioms MAPPrincipalZetaHuxley1972ClassifierWitnesses.criticalLineProductNorm_le_of_not_classII
#print axioms MAPPrincipalZetaHuxley1972ClassifierWitnesses.summable_shiftedEquation314TailMajorant
#print axioms MAPPrincipalZetaHuxley1972ClassifierWitnesses.shiftedEquation314Normalizer_normalized_budget
#print axioms MAPPrincipalZetaHuxley1972ClassifierWitnesses.norm_setIntegral_central_le_of_not_classII
#print axioms MAPPrincipalZetaHuxley1972ClassifierWitnesses.norm_setIntegral_dyadic_le_of_not_classII
#print axioms MAPPrincipalZetaHuxley1972ClassifierWitnesses.huxleyEquation314_full_shifted_integral_lt_oneThird_of_not_classII
