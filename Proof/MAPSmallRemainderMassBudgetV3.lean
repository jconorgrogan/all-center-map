import MAPHBPerronSourceData
import MRTOrdinarySlidingMassBudget
import MRTProposition61TypeIIDivisorNormalizationV3
import MRTProposition61TypeIIEndpointWidthV3
import MRTProposition61TypeIIPolylogBudgetV3
import Mathlib.Algebra.IsPrimePow

/-!
# Genuine small-remainder mass under MAP packet geometry

`smallRemainderMass` is the literal `q₀>1` sum of Corollary-5.3
component integrals.  This module does **not** replace it by ordinary
error or by a sliding-mass proxy.

The von Mangoldt coefficient vanishes unless `q₀ n` is a prime power.
Consequently every first factor with `q₀>1` that is not itself a prime
power contributes zero, and the remaining Dirichlet polynomials are
supported on a single geometric progression of length `O(log X)`.

The MRT `H⁻²` factor is applied once, as the literal V3 normalization
`(d(q)⁴)/(q U²)` with `U = |β| H`.  This is definitionally
`MAPDynamicHBTermwiseBudgetConstructorV3.dynamicV3Normalization`.
The bound holds on the Corollary-5.3 range `1 ≤ H ≤ X`, hence on the
MAP aperture range `H ≤ X/2`.
-/

namespace MAPSmallRemainderMassBudgetV3

open scoped BigOperators
open Filter MeasureTheory Set
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPMRTProposition51Source
open MAPMRTOrdinarySlidingMassBudget
open MRTProposition61TypeIIEndpointWidthV3
open MRTProposition61TypeIIDivisorNormalizationV3
open MRTProposition61TypeIIPolylogBudgetV3
open MixedMeanFrontend

noncomputable section

set_option maxHeartbeats 1600000

/-- The packet-indexed V3 normalization, written as the explicit formula so
this module does not import the full termwise constructor.  Unfolding
`MAPDynamicHBTermwiseBudgetConstructorV3.dynamicV3Normalization` yields
the same expression. -/
def dynamicV3Normalization (p : Corollary53Input) : ℝ :=
  (divisorCount p.q : ℝ) ^ 4 /
    (p.q * stationaryWidth p.beta p.H ^ 2)

/-! ## Prime-power restriction on the `q₀>1` factorizations -/

/-- First factors that actually contribute to the Mangoldt small remainder:
positive prime powers dividing `q`. -/
def primePowerModulusFactorizations (q : ℕ) : Finset (ℕ × ℕ) :=
  (modulusFactorizations q).filter (fun z ↦ 1 < z.1 ∧ IsPrimePow z.1)

theorem primePowerModulusFactorizations_subset (q : ℕ) :
    primePowerModulusFactorizations q ⊆
      (modulusFactorizations q).filter (fun z ↦ 1 < z.1) := by
  intro z hz
  simp only [primePowerModulusFactorizations, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hz.2.1⟩

/-- If `q₀>1` is not a prime power, then `q₀ n` is never a prime power. -/
theorem not_isPrimePow_mul_of_not_isPrimePow
    {q₀ n : ℕ} (hq₀ : 1 < q₀) (h : ¬IsPrimePow q₀) :
    ¬IsPrimePow (q₀ * n) := by
  intro hpn
  exact h (IsPrimePow.dvd hpn ⟨n, rfl⟩ (ne_of_gt hq₀))

/-- The Mangoldt coefficient on `q₀ n` vanishes when `q₀>1` is not a prime
power. -/
theorem mapMangoldtCoeff_eq_zero_of_not_prime_pow
    (X : ℝ) {q₀ n : ℕ} (hq₀ : 1 < q₀) (h : ¬IsPrimePow q₀) :
    mapMangoldtCoeff X (q₀ * n) = 0 := by
  unfold mapMangoldtCoeff
  split_ifs with hmem
  · have hΛ : ArithmeticFunction.vonMangoldt (q₀ * n) = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
        (not_isPrimePow_mul_of_not_isPrimePow hq₀ h)
    simpa [hΛ]
  · rfl

theorem criticalDirichletPolynomial_eq_zero_of_not_prime_pow
    (X : ℝ) (q₀ q₁ : ℕ) (chi : DirichletCharacter ℂ q₁) (t : ℝ)
    (hq₀ : 1 < q₀) (h : ¬IsPrimePow q₀) :
    criticalDirichletPolynomial X q₀ q₁ (mapMangoldtCoeff X) chi t = 0 := by
  unfold criticalDirichletPolynomial
  refine Finset.sum_eq_zero ?_
  intro n hn
  simp [mapMangoldtCoeff_eq_zero_of_not_prime_pow X hq₀ h]

theorem characterWindow_eq_zero_of_not_prime_pow
    (X H beta t : ℝ) (q₀ q₁ : ℕ) [NeZero q₁]
    (hq₀ : 1 < q₀) (h : ¬IsPrimePow q₀) :
    characterWindow X q₀ q₁ (mapMangoldtCoeff X) beta H t = 0 := by
  unfold characterWindow
  refine Finset.sum_eq_zero ?_
  intro chi hchi
  simp [criticalDirichletPolynomial_eq_zero_of_not_prime_pow
    X q₀ q₁ chi _ hq₀ h]

theorem componentIntegral_eq_zero_of_not_prime_pow
    {X H beta eta : ℝ} {q₀ q₁ : ℕ} [NeZero q₁]
    (hX : 0 ≤ X) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hq₀ : 1 < q₀) (h : ¬IsPrimePow q₀)
    (component : OuterComponent) :
    componentIntegral X H q₀ q₁ (mapMangoldtCoeff X) beta eta component = 0 := by
  unfold componentIntegral
  simp [characterWindow_eq_zero_of_not_prime_pow _ H beta _ q₀ q₁ hq₀ h]

/-- The literal small remainder retains only prime-power first factors. -/
theorem smallRemainderMass_eq_primePower
    {p : Corollary53Input}
    (hf : p.f = mapMangoldtCoeff p.X)
    (hX : 0 ≤ p.X) (heta : 0 < p.eta) (hetaOne : p.eta ≤ 1)
    (component : OuterComponent) :
    smallRemainderMass p component =
      ∑ z ∈ primePowerModulusFactorizations p.q,
        componentIntegral p.X p.H z.1 z.2 p.f p.beta p.eta component := by
  unfold smallRemainderMass
  refine (Finset.sum_subset_zero_on_sdiff
      (primePowerModulusFactorizations_subset p.q) ?_ (fun _ _ ↦ rfl)).symm
  intro z hz
  have hz' := Finset.mem_sdiff.mp hz
  have hmod := (Finset.mem_filter.mp hz'.1).1
  have hq₀ : 1 < z.1 := (Finset.mem_filter.mp hz'.1).2
  have hq₁ : 1 ≤ z.2 :=
    (Finset.mem_Icc.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hmod).1).2).1
  haveI : NeZero z.2 := ⟨Nat.ne_of_gt (Nat.succ_le_iff.mp hq₁)⟩
  have hnot : ¬IsPrimePow z.1 := by
    intro hpp
    refine hz'.2 ?_
    simp only [primePowerModulusFactorizations, Finset.mem_filter]
    exact ⟨hmod, hq₀, hpp⟩
  rw [hf]
  exact componentIntegral_eq_zero_of_not_prime_pow
    hX heta hetaOne hq₀ hnot component

/-! ## Length of the remaining prime-power support -/

/-- A factor `n` making `p^k n` a prime power is itself a power of `p`. -/
theorem exists_pow_of_prime_pow_mul_isPrimePow
    {p k n : ℕ} (hp : p.Prime) (hk : 0 < k)
    (h : IsPrimePow (p ^ k * n)) :
    ∃ j : ℕ, n = p ^ j := by
  obtain ⟨r, a, hr, ha, heq⟩ := (isPrimePow_nat_iff _).mp h
  have hp_dvd_pow : p ∣ r ^ a := by
    have : p ∣ p ^ k * n :=
      dvd_mul_of_dvd_left (dvd_pow_self p (Nat.ne_of_gt hk)) n
    rwa [← heq] at this
  have hp_dvd : p ∣ r := hp.dvd_of_dvd_pow hp_dvd_pow
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hp_dvd
  subst r
  have hn_dvd : n ∣ p ^ a := by
    have : n ∣ p ^ k * n := dvd_mul_left _ _
    rwa [← heq] at this
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hn_dvd
  exact ⟨j, rfl⟩

theorem card_isPrimePow_mul_le_log
    {q₀ N : ℕ} (hq₀ : 1 < q₀) :
    (((Finset.Icc 1 N).filter (fun n ↦ IsPrimePow (q₀ * n))).card : ℝ) ≤
      (Nat.log 2 N : ℝ) + 1 := by
  classical
  by_cases hpp : IsPrimePow q₀
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q₀).mp hpp
    have hp1 : 1 < p := hp.one_lt
    let s := (Finset.Icc 1 N).filter (fun n ↦ IsPrimePow (p ^ k * n))
    let t := (Finset.range (Nat.log 2 N + 1)).image (fun j ↦ p ^ j)
    have hsubset : s ⊆ t := by
      intro n hn
      have hnI := (Finset.mem_filter.mp hn).1
      have hnpp := (Finset.mem_filter.mp hn).2
      obtain ⟨j, rfl⟩ :=
        exists_pow_of_prime_pow_mul_isPrimePow hp hk hnpp
      have hn1 : 1 ≤ p ^ j := (Finset.mem_Icc.mp hnI).1
      have hnN : p ^ j ≤ N := (Finset.mem_Icc.mp hnI).2
      have hN0 : N ≠ 0 := by
        have : 0 < p ^ j := lt_of_lt_of_le (by exact Nat.succ_pos 0) hn1
        exact Nat.ne_of_gt (lt_of_lt_of_le this hnN)
      have hj : j ≤ Nat.log p N :=
        (Nat.le_log_iff_pow_le hp1 hN0).2 hnN
      have hj2 : j ≤ Nat.log 2 N :=
        hj.trans (Nat.log_anti_left (by norm_num : 1 < 2)
          (Nat.Prime.two_le hp))
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr
        (Nat.lt_succ_of_le hj2), rfl⟩
    have hle : s.card ≤ t.card := Finset.card_le_card hsubset
    have ht : t.card ≤ Nat.log 2 N + 1 := by
      simpa [t, Finset.card_range] using
        (Finset.card_image_le :
          ((Finset.range (Nat.log 2 N + 1)).image (fun j ↦ p ^ j)).card ≤
            (Finset.range (Nat.log 2 N + 1)).card)
    have hnat : s.card ≤ Nat.log 2 N + 1 := hle.trans ht
    exact_mod_cast hnat
  · have hempty :
        (Finset.Icc 1 N).filter (fun n ↦ IsPrimePow (q₀ * n)) = ∅ := by
      ext n
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hn
      exact not_isPrimePow_mul_of_not_isPrimePow hq₀ hpp
    simp [hempty]
    positivity

theorem natLog_two_le_real_log {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hpowR : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast hpow
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_le_log (pow_pos h2 _) hpowR
  have hlogpow : Real.log ((2 : ℝ) ^ Nat.log 2 n) =
      (Nat.log 2 n : ℝ) * Real.log 2 :=
    Real.log_pow (2 : ℝ) (Nat.log 2 n)
  rw [hlogpow] at hlog
  exact (le_div_iff₀ hlog2).2 hlog

/-- Explicit polynomial majorant of one remaining Dirichlet polynomial. -/
def smallRemainderPolyBound (X : ℝ) : ℝ :=
  (Real.log (2 * X) / Real.log 2 + 1) * Real.log (2 * X)

theorem smallRemainderPolyBound_nonneg {X : ℝ} (hX : 2 ≤ X) :
    0 ≤ smallRemainderPolyBound X := by
  unfold smallRemainderPolyBound
  have hlog : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem smallRemainderPolyBound_le_log_sq
    {X : ℝ} (hX : 2 ≤ X) (hlog : 1 ≤ Real.log X) :
    smallRemainderPolyBound X ≤
      (4 / Real.log 2 + 2) * Real.log X ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hlog0 : 0 ≤ Real.log X := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2X : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : Real.log 2 ≤ Real.log X :=
      Real.log_le_log (by norm_num) hX
    linarith
  have hlogX2 : Real.log X ≤ Real.log X ^ 2 := by
    have := mul_le_mul_of_nonneg_right hlog hlog0
    simpa [pow_two] using this
  unfold smallRemainderPolyBound
  have hsum : Real.log (2 * X) / Real.log 2 + 1 ≤
      2 * Real.log X / Real.log 2 + 1 := by gcongr
  have hprod := mul_le_mul hsum h2X
    (Real.log_nonneg (by linarith)) (by positivity)
  have hexp : (2 * Real.log X / Real.log 2 + 1) * (2 * Real.log X) =
      4 * Real.log X ^ 2 / Real.log 2 + 2 * Real.log X := by ring
  have hfinal :
      4 * Real.log X ^ 2 / Real.log 2 + 2 * Real.log X ≤
        (4 / Real.log 2 + 2) * Real.log X ^ 2 := by
    have hsq : 2 * Real.log X ≤ 2 * Real.log X ^ 2 := by nlinarith
    have hdiv : 4 * Real.log X ^ 2 / Real.log 2 =
        (4 / Real.log 2) * Real.log X ^ 2 := by field_simp
    nlinarith
  calc
    _ ≤ (2 * Real.log X / Real.log 2 + 1) * (2 * Real.log X) := hprod
    _ = 4 * Real.log X ^ 2 / Real.log 2 + 2 * Real.log X := hexp
    _ ≤ _ := hfinal

/-! ## Pointwise bound on the remaining Dirichlet polynomial -/

theorem norm_mellinPhase_eq_one (n : ℕ) (t : ℝ) :
    ‖mellinPhase n t‖ = 1 := by
  unfold mellinPhase
  rw [show -(((t * Real.log n : ℝ) : ℂ)) * Complex.I =
      ((-(t * Real.log n) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem mapMangoldtCoeff_norm_le_log_all {X : ℝ} (hX : 2 ≤ X) (n : ℕ) :
    ‖mapMangoldtCoeff X n‖ ≤ Real.log (2 * X) := by
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · exact mapMangoldtCoeff_norm_le_log hX hn
  · simp [mapMangoldtCoeff, hn]
    exact Real.log_nonneg (by linarith)

theorem norm_criticalDirichletPolynomial_map_le
    {X : ℝ} (hX : 2 ≤ X) {q₀ q₁ : ℕ}
    (hq₀ : 1 < q₀) (chi : DirichletCharacter ℂ q₁) (t : ℝ) :
    ‖criticalDirichletPolynomial X q₀ q₁ (mapMangoldtCoeff X) chi t‖ ≤
      smallRemainderPolyBound X := by
  unfold criticalDirichletPolynomial
  let s := Finset.Icc 1 ⌊2 * X⌋₊
  let supp := s.filter (fun n ↦ IsPrimePow (q₀ * n))
  have hN : 0 < ⌊2 * X⌋₊ := by
    have : (1 : ℝ) < 2 * X := by linarith
    exact Nat.floor_pos.mpr (le_of_lt this)
  have hlog2X : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hterm (n : ℕ) (hn : n ∈ s) :
      ‖mapMangoldtCoeff X (q₀ * n) * chi n *
          (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t‖ ≤
        if IsPrimePow (q₀ * n) then Real.log (2 * X) else 0 := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : 0 < n := Nat.succ_le_iff.mp hn1
    have hinv : ‖(Real.sqrt n : ℂ)⁻¹‖ ≤ 1 := by
      have hne : (Real.sqrt n : ℂ) ≠ 0 := by
        have : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn0)
        exact_mod_cast this.ne'
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hsqrt1 : 1 ≤ Real.sqrt n := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        exact_mod_cast hn1
      exact inv_le_one_of_one_le₀ hsqrt1
    have hchi : ‖chi n‖ ≤ 1 := DirichletCharacter.norm_le_one chi n
    have hphase : ‖mellinPhase n t‖ = 1 := norm_mellinPhase_eq_one n t
    have hf : ‖mapMangoldtCoeff X (q₀ * n)‖ ≤ Real.log (2 * X) :=
      mapMangoldtCoeff_norm_le_log_all hX _
    by_cases hpp : IsPrimePow (q₀ * n)
    · rw [if_pos hpp]
      have hmul :
          ‖mapMangoldtCoeff X (q₀ * n) * chi n *
              (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t‖ =
            ‖mapMangoldtCoeff X (q₀ * n)‖ * ‖chi n‖ *
              ‖(Real.sqrt n : ℂ)⁻¹‖ * ‖mellinPhase n t‖ := by
        simp only [norm_mul]
      rw [hmul, hphase, mul_one]
      calc
        ‖mapMangoldtCoeff X (q₀ * n)‖ * ‖chi n‖ *
            ‖(Real.sqrt n : ℂ)⁻¹‖ ≤
          ‖mapMangoldtCoeff X (q₀ * n)‖ * 1 * 1 := by gcongr
        _ = ‖mapMangoldtCoeff X (q₀ * n)‖ := by ring
        _ ≤ Real.log (2 * X) := hf
    · rw [if_neg hpp]
      have hf0 : mapMangoldtCoeff X (q₀ * n) = 0 := by
        unfold mapMangoldtCoeff
        split_ifs with hmem
        · have hΛ : ArithmeticFunction.vonMangoldt (q₀ * n) = 0 :=
            ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
          simpa [hΛ]
        · rfl
      simp [hf0]
  have hsum :
      (∑ n ∈ s,
          ‖mapMangoldtCoeff X (q₀ * n) * chi n *
            (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t‖) ≤
        ∑ n ∈ supp, Real.log (2 * X) := by
    have hyes :
        ∑ n ∈ supp,
          ‖mapMangoldtCoeff X (q₀ * n) * chi n *
            (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t‖ ≤
          ∑ n ∈ supp, Real.log (2 * X) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnS : n ∈ s := (Finset.mem_filter.mp hn).1
      have hpp : IsPrimePow (q₀ * n) := (Finset.mem_filter.mp hn).2
      simpa [hpp] using hterm n hnS
    have hnot :
        ∑ n ∈ s.filter (fun n ↦ ¬IsPrimePow (q₀ * n)),
          ‖mapMangoldtCoeff X (q₀ * n) * chi n *
            (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t‖ = 0 := by
      refine Finset.sum_eq_zero ?_
      intro n hn
      have hnS : n ∈ s := (Finset.mem_filter.mp hn).1
      have hnp : ¬IsPrimePow (q₀ * n) := (Finset.mem_filter.mp hn).2
      have hle := hterm n hnS
      have hnn := norm_nonneg
        (mapMangoldtCoeff X (q₀ * n) * chi n *
          (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t)
      simpa [hnp] using le_antisymm (by simpa [hnp] using hle) hnn
    have hsplit :=
      (Finset.sum_filter_add_sum_filter_not s
        (fun n ↦ IsPrimePow (q₀ * n))
        (fun n ↦ ‖mapMangoldtCoeff X (q₀ * n) * chi n *
          (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t‖)).symm
    calc
      _ = ∑ n ∈ supp, ‖mapMangoldtCoeff X (q₀ * n) * chi n *
              (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t‖ +
          ∑ n ∈ s.filter (fun n ↦ ¬IsPrimePow (q₀ * n)),
            ‖mapMangoldtCoeff X (q₀ * n) * chi n *
              (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t‖ := by
        simpa [supp] using hsplit
      _ = ∑ n ∈ supp, ‖mapMangoldtCoeff X (q₀ * n) * chi n *
              (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t‖ := by
        rw [hnot, add_zero]
      _ ≤ _ := hyes
  have hcard : (supp.card : ℝ) ≤ (Nat.log 2 ⌊2 * X⌋₊ : ℝ) + 1 :=
    card_isPrimePow_mul_le_log hq₀
  have hlogN : (Nat.log 2 ⌊2 * X⌋₊ : ℝ) ≤
      Real.log (⌊2 * X⌋₊ : ℝ) / Real.log 2 :=
    natLog_two_le_real_log hN
  have hfloorR : (⌊2 * X⌋₊ : ℝ) ≤ 2 * X :=
    Nat.floor_le (by linarith : 0 ≤ 2 * X)
  have hlogFloor : Real.log (⌊2 * X⌋₊ : ℝ) ≤ Real.log (2 * X) :=
    Real.log_le_log (by exact_mod_cast hN) hfloorR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmaj : (Nat.log 2 ⌊2 * X⌋₊ : ℝ) + 1 ≤
      Real.log (2 * X) / Real.log 2 + 1 := by
    have := hlogN.trans (div_le_div_of_nonneg_right hlogFloor hlog2.le)
    linarith
  calc
    _ ≤ ∑ n ∈ s,
        ‖mapMangoldtCoeff X (q₀ * n) * chi n *
          (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ supp, Real.log (2 * X) := hsum
    _ = (supp.card : ℝ) * Real.log (2 * X) := by simp
    _ ≤ ((Nat.log 2 ⌊2 * X⌋₊ : ℝ) + 1) * Real.log (2 * X) := by
      gcongr
    _ ≤ (Real.log (2 * X) / Real.log 2 + 1) * Real.log (2 * X) := by
      gcongr
    _ = smallRemainderPolyBound X := rfl

/-! ## Character window, component integral, and mass -/

theorem interval_integral_le_mul_const
    {a b C : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hC : ∀ x ∈ Icc a b, f x ≤ C) :
    ∫ x in a..b, f x ≤ (b - a) * C := by
  have hc : IntervalIntegrable (fun _ : ℝ ↦ C) volume a b :=
    intervalIntegral.intervalIntegrable_const (μ := volume)
  have hmono :
      (∫ x in a..b, f x) ≤ ∫ x in a..b, C :=
    intervalIntegral.integral_mono_on (μ := volume) hab hf hc hC
  have hconst : (∫ _ in a..b, C) = (b - a) * C := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
  exact hmono.trans_eq hconst

theorem characterWindow_map_le
    {X H beta t : ℝ} {q₀ q₁ : ℕ} [NeZero q₁]
    (hX : 2 ≤ X) (hH : 0 ≤ H) (hq₀ : 1 < q₀) :
    characterWindow X q₀ q₁ (mapMangoldtCoeff X) beta H t ≤
      (q₁ : ℝ) * (2 * |beta| * H) * smallRemainderPolyBound X := by
  unfold characterWindow
  have hU : t - |beta| * H ≤ t + |beta| * H := by
    have : 0 ≤ |beta| * H := mul_nonneg (abs_nonneg _) hH
    linarith
  have hB := smallRemainderPolyBound_nonneg hX
  have hterm (chi : DirichletCharacter ℂ q₁) :
      (∫ t' in (t - |beta| * H)..(t + |beta| * H),
        ‖criticalDirichletPolynomial X q₀ q₁
          (mapMangoldtCoeff X) chi t'‖) ≤
        (2 * |beta| * H) * smallRemainderPolyBound X := by
    have hf :=
      (continuous_norm_criticalDirichletPolynomial X q₀ q₁
        (mapMangoldtCoeff X) chi).intervalIntegrable (μ := volume)
        (t - |beta| * H) (t + |beta| * H)
    have hpt : ∀ t' ∈ Icc (t - |beta| * H) (t + |beta| * H),
        ‖criticalDirichletPolynomial X q₀ q₁
          (mapMangoldtCoeff X) chi t'‖ ≤ smallRemainderPolyBound X :=
      fun t' _ ↦ norm_criticalDirichletPolynomial_map_le hX hq₀ chi t'
    have hc : IntervalIntegrable
        (fun _ : ℝ ↦ smallRemainderPolyBound X) volume
        (t - |beta| * H) (t + |beta| * H) :=
      intervalIntegral.intervalIntegrable_const (μ := volume)
    have hint :
        (∫ t' in (t - |beta| * H)..(t + |beta| * H),
          ‖criticalDirichletPolynomial X q₀ q₁
            (mapMangoldtCoeff X) chi t'‖) ≤
          ∫ _ in (t - |beta| * H)..(t + |beta| * H),
            smallRemainderPolyBound X :=
      intervalIntegral.integral_mono_on (μ := volume) hU hf hc hpt
    have hconst :
        (∫ _ in (t - |beta| * H)..(t + |beta| * H),
          smallRemainderPolyBound X) =
          ((t + |beta| * H) - (t - |beta| * H)) *
            smallRemainderPolyBound X := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
    have hint' := hint.trans_eq hconst
    have hlen : (t + |beta| * H) - (t - |beta| * H) = 2 * |beta| * H := by
      ring
    simpa [hlen] using hint'
  have hsum :
      (∑ chi : DirichletCharacter ℂ q₁,
          ∫ t' in (t - |beta| * H)..(t + |beta| * H),
            ‖criticalDirichletPolynomial X q₀ q₁
              (mapMangoldtCoeff X) chi t'‖) ≤
        ∑ _chi : DirichletCharacter ℂ q₁,
          (2 * |beta| * H) * smallRemainderPolyBound X :=
    Finset.sum_le_sum fun chi _ ↦ hterm chi
  have hcard : (Fintype.card (DirichletCharacter ℂ q₁) : ℝ) ≤ q₁ :=
    mod_cast card_dirichletCharacters_le_modulus q₁
  calc
    _ ≤ ∑ _chi : DirichletCharacter ℂ q₁,
        (2 * |beta| * H) * smallRemainderPolyBound X := hsum
    _ = (Fintype.card (DirichletCharacter ℂ q₁) : ℝ) *
        ((2 * |beta| * H) * smallRemainderPolyBound X) := by
      simp
    _ ≤ (q₁ : ℝ) * ((2 * |beta| * H) * smallRemainderPolyBound X) := by
      gcongr
    _ = _ := by ring

theorem componentIntegral_map_le
    {X H beta eta : ℝ} {q₀ q₁ q : ℕ} [NeZero q₁]
    (hX : 2 ≤ X) (hH : 0 ≤ H)
    (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hq₀ : 1 < q₀) (hq₁q : q₁ ≤ q)
    (component : OuterComponent) :
    componentIntegral X H q₀ q₁ (mapMangoldtCoeff X) beta eta component ≤
      (|beta| * X / eta) *
        ((q : ℝ) * (2 * |beta| * H) * smallRemainderPolyBound X) ^ 2 := by
  let e := componentEndpoints X beta eta component
  have he : e.1 ≤ e.2 := componentEndpoints_mono
    (by linarith : 0 ≤ X) heta hetaOne component
  have hB := smallRemainderPolyBound_nonneg hX
  have hU : 0 ≤ |beta| * H := mul_nonneg (abs_nonneg _) hH
  have hq1 : (q₁ : ℝ) ≤ q := by exact_mod_cast hq₁q
  have hW (t : ℝ) :
      characterWindow X q₀ q₁ (mapMangoldtCoeff X) beta H t ≤
        (q : ℝ) * (2 * |beta| * H) * smallRemainderPolyBound X := by
    have hw :=
      characterWindow_map_le (X := X) (H := H) (beta := beta) (t := t)
        (q₀ := q₀) (q₁ := q₁) hX hH hq₀
    have : (q₁ : ℝ) * (2 * |beta| * H) * smallRemainderPolyBound X ≤
        (q : ℝ) * (2 * |beta| * H) * smallRemainderPolyBound X := by
      gcongr
    exact hw.trans this
  have hW2 (t : ℝ) :
      characterWindow X q₀ q₁ (mapMangoldtCoeff X) beta H t ^ 2 ≤
        ((q : ℝ) * (2 * |beta| * H) * smallRemainderPolyBound X) ^ 2 := by
    have hW0 : 0 ≤ characterWindow X q₀ q₁ (mapMangoldtCoeff X) beta H t :=
      characterWindow_nonneg hU
    exact pow_le_pow_left₀ hW0 (hW t) 2
  have hf :
      IntervalIntegrable
        (fun t : ℝ ↦
          characterWindow X q₀ q₁ (mapMangoldtCoeff X) beta H t ^ 2)
        volume e.1 e.2 :=
    ((continuous_characterWindow X H q₀ q₁
      (mapMangoldtCoeff X) beta).pow 2).intervalIntegrable (μ := volume)
      e.1 e.2
  have hint := interval_integral_le_mul_const he hf
    (fun t _ ↦ hW2 t)
  have hlen : e.2 - e.1 ≤ |beta| * X / eta :=
    componentEndpoints_sub_le_abs_mul_div
      (by linarith : 0 ≤ X) heta.le component
  have hsq :
      0 ≤ ((q : ℝ) * (2 * |beta| * H) * smallRemainderPolyBound X) ^ 2 := by
    positivity
  unfold componentIntegral
  calc
    _ ≤ (e.2 - e.1) *
        ((q : ℝ) * (2 * |beta| * H) * smallRemainderPolyBound X) ^ 2 := hint
    _ ≤ (|beta| * X / eta) *
        ((q : ℝ) * (2 * |beta| * H) * smallRemainderPolyBound X) ^ 2 := by
      gcongr

theorem one_le_divisorCount {q : ℕ} (hq : 1 ≤ q) : 1 ≤ divisorCount q := by
  unfold divisorCount
  have h1 : 1 ∈ q.divisors := by
    rw [Nat.mem_divisors]
    exact ⟨one_dvd q, Nat.ne_of_gt (Nat.succ_le_iff.mp hq)⟩
  exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨1, h1⟩)

private theorem factorization_q₁_pos {q : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ modulusFactorizations q) : 1 ≤ z.2 :=
  (Finset.mem_Icc.mp
    (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2).1

private theorem factorization_q₁_le {q : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ modulusFactorizations q) : z.2 ≤ q :=
  (Finset.mem_Icc.mp
    (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2).2

/-- One outer component of the actual `q₀>1` mass, after prime-power
restriction. -/
theorem smallRemainderMass_map_le
    {p : Corollary53Input} [NeZero p.q]
    (hf : p.f = mapMangoldtCoeff p.X)
    (hX : 2 ≤ p.X) (hH : 0 ≤ p.H)
    (heta : 0 < p.eta) (hetaOne : p.eta ≤ 1)
    (component : OuterComponent) :
    smallRemainderMass p component ≤
      (divisorCount p.q : ℝ) * (|p.beta| * p.X / p.eta) *
        ((p.q : ℝ) * (2 * |p.beta| * p.H) *
          smallRemainderPolyBound p.X) ^ 2 := by
  classical
  have hq : 1 ≤ p.q := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (NeZero.ne p.q))
  have hX0 : 0 ≤ p.X := by linarith
  rw [smallRemainderMass_eq_primePower hf hX0 heta hetaOne]
  have hterm : ∀ z ∈ primePowerModulusFactorizations p.q,
      componentIntegral p.X p.H z.1 z.2 p.f p.beta p.eta component ≤
        (|p.beta| * p.X / p.eta) *
          ((p.q : ℝ) * (2 * |p.beta| * p.H) *
            smallRemainderPolyBound p.X) ^ 2 := by
    intro z hz
    have hmod : z ∈ modulusFactorizations p.q :=
      (Finset.mem_filter.mp hz).1
    have hq₀ : 1 < z.1 := (Finset.mem_filter.mp hz).2.1
    have hq₁ : 1 ≤ z.2 := factorization_q₁_pos hmod
    have hq₁q : z.2 ≤ p.q := factorization_q₁_le hmod
    haveI : NeZero z.2 := ⟨Nat.ne_of_gt (Nat.succ_le_iff.mp hq₁)⟩
    rw [hf]
    exact componentIntegral_map_le hX hH heta hetaOne hq₀ hq₁q component
  have hsum := Finset.sum_le_sum hterm
  have hBsq : 0 ≤ (|p.beta| * p.X / p.eta) *
      ((p.q : ℝ) * (2 * |p.beta| * p.H) *
        smallRemainderPolyBound p.X) ^ 2 := by
    have hB := smallRemainderPolyBound_nonneg hX
    positivity
  have hcard :
      ((primePowerModulusFactorizations p.q).card : ℝ) ≤
        (divisorCount p.q : ℝ) := by
    have hle :
        (primePowerModulusFactorizations p.q).card ≤
          ((modulusFactorizations p.q).filter (fun z ↦ 1 < z.1)).card :=
      Finset.card_le_card (primePowerModulusFactorizations_subset p.q)
    have hle' :
        ((modulusFactorizations p.q).filter (fun z ↦ 1 < z.1)).card ≤
          (modulusFactorizations p.q).card :=
      Finset.card_filter_le _ _
    have hdiv := card_modulusFactorizations_le_divisorCount hq
    exact_mod_cast hle.trans (hle'.trans hdiv)
  calc
    _ ≤ ∑ _z ∈ primePowerModulusFactorizations p.q,
        (|p.beta| * p.X / p.eta) *
          ((p.q : ℝ) * (2 * |p.beta| * p.H) *
            smallRemainderPolyBound p.X) ^ 2 := hsum
    _ = ((primePowerModulusFactorizations p.q).card : ℝ) *
        ((|p.beta| * p.X / p.eta) *
          ((p.q : ℝ) * (2 * |p.beta| * p.H) *
            smallRemainderPolyBound p.X) ^ 2) := by
      simp
    _ ≤ (divisorCount p.q : ℝ) *
        ((|p.beta| * p.X / p.eta) *
          ((p.q : ℝ) * (2 * |p.beta| * p.H) *
            smallRemainderPolyBound p.X) ^ 2) := by
      gcongr
    _ = _ := by ring

theorem sum_smallRemainderMass_map_le
    {p : Corollary53Input} [NeZero p.q]
    (hf : p.f = mapMangoldtCoeff p.X)
    (hX : 2 ≤ p.X) (hH : 0 ≤ p.H)
    (heta : 0 < p.eta) (hetaOne : p.eta ≤ 1) :
    (∑ component : OuterComponent, smallRemainderMass p component) ≤
      2 * (divisorCount p.q : ℝ) * (|p.beta| * p.X / p.eta) *
        ((p.q : ℝ) * (2 * |p.beta| * p.H) *
          smallRemainderPolyBound p.X) ^ 2 := by
  have hone := fun component : OuterComponent ↦
    smallRemainderMass_map_le hf hX hH heta hetaOne component
  have hsum :=
    Finset.sum_le_sum (s := (Finset.univ : Finset OuterComponent))
      fun c _ ↦ hone c
  have hcard : (Fintype.card OuterComponent : ℝ) = 2 := by
    have huniv : (Finset.univ : Finset OuterComponent) =
        {OuterComponent.negative, OuterComponent.positive} := by
      ext c
      cases c <;> simp
    have hcard' : ({OuterComponent.negative, OuterComponent.positive} :
        Finset OuterComponent).card = 2 := by
      decide
    exact_mod_cast huniv ▸ hcard'
  calc
    _ ≤ ∑ _c : OuterComponent,
        (divisorCount p.q : ℝ) * (|p.beta| * p.X / p.eta) *
          ((p.q : ℝ) * (2 * |p.beta| * p.H) *
            smallRemainderPolyBound p.X) ^ 2 := hsum
    _ = (Fintype.card OuterComponent : ℝ) *
        ((divisorCount p.q : ℝ) * (|p.beta| * p.X / p.eta) *
          ((p.q : ℝ) * (2 * |p.beta| * p.H) *
            smallRemainderPolyBound p.X) ^ 2) := by
      simp
    _ = 2 * (divisorCount p.q : ℝ) * (|p.beta| * p.X / p.eta) *
        ((p.q : ℝ) * (2 * |p.beta| * p.H) *
          smallRemainderPolyBound p.X) ^ 2 := by
      rw [hcard]
      ring

/-- Normalized small remainder after the single MRT `H⁻²` factor.
The `U²` in `dynamicV3Normalization` cancels the `U²` from the length-`2U`
character window; the remaining `|β|` is the packet bound `1/(qQ)`. -/
theorem dynamicV3Normalization_mul_sum_smallRemainder_le
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    (hf : p.f = mapMangoldtCoeff p.X)
    (hX : 2 ≤ p.X) {Q : ℝ}
    (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
    (heta : p.eta = 1 / Real.sqrt Q)
    (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * Q)) :
    dynamicV3Normalization p *
      (∑ component : OuterComponent, smallRemainderMass p component) ≤
      8 * (divisorCount p.q : ℝ) ^ 5 *
        smallRemainderPolyBound p.X ^ 2 * p.X / Real.sqrt Q := by
  have hH : 0 ≤ p.H := le_trans (by norm_num : (0 : ℝ) ≤ 1) hp.1
  have hetaPos : 0 < p.eta := hp.2.2.2.2.1
  have hetaOne : p.eta ≤ 1 := hp.2.2.2.2.2.1
  have hmass := sum_smallRemainderMass_map_le hf hX hH hetaPos hetaOne
  have hq0 : (0 : ℝ) < p.q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.q)
  have hbne : p.beta ≠ 0 := hp.2.2.2.2.2.2.2.2.1
  have hHpos : 0 < p.H := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp.1
  have hbpos : 0 < |p.beta| := abs_pos.mpr hbne
  have hB := smallRemainderPolyBound_nonneg hX
  have hnorm0 : 0 ≤ dynamicV3Normalization p := by
    unfold dynamicV3Normalization
    positivity
  have hbound := mul_le_mul_of_nonneg_left hmass hnorm0
  have hQ0 : 0 < Q := by linarith
  have hsqrtQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ0
  have hexpand :
      dynamicV3Normalization p *
          (2 * (divisorCount p.q : ℝ) * (|p.beta| * p.X / p.eta) *
            ((p.q : ℝ) * (2 * |p.beta| * p.H) *
              smallRemainderPolyBound p.X) ^ 2) =
        8 * (divisorCount p.q : ℝ) ^ 5 * (p.q : ℝ) * |p.beta| * p.X *
          smallRemainderPolyBound p.X ^ 2 / p.eta := by
    unfold dynamicV3Normalization stationaryWidth
    field_simp
    ring
  have hcancel :
      8 * (divisorCount p.q : ℝ) ^ 5 * (p.q : ℝ) * |p.beta| * p.X *
          smallRemainderPolyBound p.X ^ 2 / p.eta ≤
        8 * (divisorCount p.q : ℝ) ^ 5 *
          smallRemainderPolyBound p.X ^ 2 * p.X / Real.sqrt Q := by
    have hη : p.eta = 1 / Real.sqrt Q := heta
    have hthis :
        8 * (divisorCount p.q : ℝ) ^ 5 * (p.q : ℝ) * |p.beta| * p.X *
            smallRemainderPolyBound p.X ^ 2 / p.eta =
          8 * (divisorCount p.q : ℝ) ^ 5 *
            smallRemainderPolyBound p.X ^ 2 * p.X *
              ((p.q : ℝ) * |p.beta| / p.eta) := by
      ring
    have hβ :
        (p.q : ℝ) * |p.beta| / p.eta ≤ 1 / Real.sqrt Q := by
      rw [hη]
      have : (p.q : ℝ) * |p.beta| ≤ 1 / Q := by
        calc
          (p.q : ℝ) * |p.beta| ≤
              (p.q : ℝ) * (1 / ((p.q : ℝ) * Q)) :=
            mul_le_mul_of_nonneg_left hbeta hq0.le
          _ = 1 / Q := by field_simp
      have hQη : 0 < 1 / Real.sqrt Q := by positivity
      calc
        (p.q : ℝ) * |p.beta| / (1 / Real.sqrt Q) =
            (p.q : ℝ) * |p.beta| * Real.sqrt Q := by field_simp
        _ ≤ (1 / Q) * Real.sqrt Q :=
          mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
        _ = 1 / Real.sqrt Q := by
          field_simp
          rw [Real.sq_sqrt (le_of_lt hQ0)]
    have hmul := mul_le_mul_of_nonneg_left hβ
      (by positivity :
        0 ≤ 8 * (divisorCount p.q : ℝ) ^ 5 *
          smallRemainderPolyBound p.X ^ 2 * p.X)
    calc
      _ = 8 * (divisorCount p.q : ℝ) ^ 5 *
            smallRemainderPolyBound p.X ^ 2 * p.X *
              ((p.q : ℝ) * |p.beta| / p.eta) := hthis
      _ ≤ 8 * (divisorCount p.q : ℝ) ^ 5 *
            smallRemainderPolyBound p.X ^ 2 * p.X * (1 / Real.sqrt Q) :=
        hmul
      _ = _ := by ring
  calc
    _ ≤ dynamicV3Normalization p *
        (2 * (divisorCount p.q : ℝ) * (|p.beta| * p.X / p.eta) *
          ((p.q : ℝ) * (2 * |p.beta| * p.H) *
            smallRemainderPolyBound p.X) ^ 2) := hbound
    _ = 8 * (divisorCount p.q : ℝ) ^ 5 * (p.q : ℝ) * |p.beta| * p.X *
          smallRemainderPolyBound p.X ^ 2 / p.eta := hexpand
    _ ≤ _ := hcancel

/-- The leftover `1/q ≤ 1` above is wasteful but polylog-safe: `d(q)^5`
is still a subpower of `Q`, and `Q^{-1/4}` remains after replacing
`d(q)^5 ≤ d(q)^8`. -/
theorem dynamicV3Normalization_mul_sum_smallRemainder_le_scalar
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    (hf : p.f = mapMangoldtCoeff p.X)
    (hX : 2 ≤ p.X) (hlog : 1 ≤ Real.log p.X) {Q : ℝ}
    (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
    (heta : p.eta = 1 / Real.sqrt Q)
    (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * Q))
    {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hdiv : (divisorCount p.q : ℝ) ^ 4 ≤ Cd * Real.rpow Q (1 / 8 : ℝ)) :
    dynamicV3Normalization p *
      (∑ component : OuterComponent, smallRemainderMass p component) ≤
      (8 * Cd ^ 2 * (4 / Real.log 2 + 2) ^ 2) * p.X *
        Real.log p.X ^ 4 * Real.rpow Q (-(1 / 4 : ℝ)) := by
  have hmain := dynamicV3Normalization_mul_sum_smallRemainder_le
    hp hf hX hQ hqQ heta hbeta
  have hq : 1 ≤ p.q := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (NeZero.ne p.q))
  have hd1 : (1 : ℝ) ≤ divisorCount p.q := by exact_mod_cast one_le_divisorCount hq
  have hd5 : (divisorCount p.q : ℝ) ^ 5 ≤ (divisorCount p.q : ℝ) ^ 8 :=
    pow_le_pow_right₀ hd1 (by norm_num : (5 : ℕ) ≤ 8)
  have hd8 : (divisorCount p.q : ℝ) ^ 8 = ((divisorCount p.q : ℝ) ^ 4) ^ 2 := by
    ring
  have hdiv2 : ((divisorCount p.q : ℝ) ^ 4) ^ 2 ≤
      (Cd * Real.rpow Q (1 / 8 : ℝ)) ^ 2 := by
    have h4 : 0 ≤ (divisorCount p.q : ℝ) ^ 4 := by positivity
    exact pow_le_pow_left₀ h4 hdiv 2
  have hB := smallRemainderPolyBound_le_log_sq hX hlog
  have hB0 := smallRemainderPolyBound_nonneg hX
  have hB2 : smallRemainderPolyBound p.X ^ 2 ≤
      ((4 / Real.log 2 + 2) * Real.log p.X ^ 2) ^ 2 :=
    pow_le_pow_left₀ hB0 hB 2
  have hQ0 : 0 < Q := by linarith
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ0
  have hinvsqrt : 1 / Real.sqrt Q = Real.rpow Q (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, one_div]
    exact (Real.rpow_neg (le_of_lt hQ0) (1 / 2 : ℝ)).symm
  have hpow : (Real.rpow Q (1 / 8 : ℝ)) ^ 2 / Real.sqrt Q =
      Real.rpow Q (-(1 / 4 : ℝ)) := by
    have h2 : (Real.rpow Q (1 / 8 : ℝ)) ^ 2 = Real.rpow Q (1 / 4 : ℝ) := by
      calc
        _ = Real.rpow (Real.rpow Q (1 / 8 : ℝ)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Real.rpow Q ((1 / 8 : ℝ) * 2) :=
          (Real.rpow_mul (le_of_lt hQ0) _ _).symm
        _ = Real.rpow Q (1 / 4 : ℝ) := by congr 1; ring
    calc
      (Real.rpow Q (1 / 8 : ℝ)) ^ 2 / Real.sqrt Q =
          Real.rpow Q (1 / 4 : ℝ) / Real.sqrt Q := by rw [h2]
      _ = Real.rpow Q (1 / 4 : ℝ) * (1 / Real.sqrt Q) := by field_simp
      _ = Real.rpow Q (1 / 4 : ℝ) * Real.rpow Q (-(1 / 2 : ℝ)) := by
        rw [hinvsqrt]
      _ = Real.rpow Q (1 / 4 + -(1 / 2 : ℝ)) :=
        (Real.rpow_add hQ0 _ _).symm
      _ = Real.rpow Q (-(1 / 4 : ℝ)) := by congr 1; ring
  have hCpoly : 0 ≤ 4 / Real.log 2 + 2 := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hX0 : 0 ≤ p.X := by linarith
  have hlog0 : 0 ≤ Real.log p.X := by linarith
  calc
    _ ≤ 8 * (divisorCount p.q : ℝ) ^ 5 *
        smallRemainderPolyBound p.X ^ 2 * p.X / Real.sqrt Q := hmain
    _ ≤ 8 * (divisorCount p.q : ℝ) ^ 8 *
        smallRemainderPolyBound p.X ^ 2 * p.X / Real.sqrt Q := by
      gcongr
    _ = 8 * ((divisorCount p.q : ℝ) ^ 4) ^ 2 *
        smallRemainderPolyBound p.X ^ 2 * p.X / Real.sqrt Q := by
      rw [hd8]
    _ ≤ 8 * (Cd * Real.rpow Q (1 / 8 : ℝ)) ^ 2 *
        smallRemainderPolyBound p.X ^ 2 * p.X / Real.sqrt Q := by
      gcongr
    _ ≤ 8 * (Cd * Real.rpow Q (1 / 8 : ℝ)) ^ 2 *
        (((4 / Real.log 2 + 2) * Real.log p.X ^ 2) ^ 2) * p.X /
          Real.sqrt Q := by
      gcongr
    _ = (8 * Cd ^ 2 * (4 / Real.log 2 + 2) ^ 2) * p.X *
        Real.log p.X ^ 4 *
          ((Real.rpow Q (1 / 8 : ℝ)) ^ 2 / Real.sqrt Q) := by
      ring
    _ = (8 * Cd ^ 2 * (4 / Real.log 2 + 2) ^ 2) * p.X *
        Real.log p.X ^ 4 * Real.rpow Q (-(1 / 4 : ℝ)) := by
      rw [hpow]

/-- Uniform `/30` producer for the literal small-remainder field.
Both logarithmic parameter exponents may subsequently be increased. -/
theorem exists_small_remainder_budget_thirtieth (A : ℝ) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (hf : p.f = mapMangoldtCoeff p.X)
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (_hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H),
            dynamicV3Normalization p *
              (∑ component : OuterComponent,
                smallRemainderMass p component) ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 30 := by
  obtain ⟨Cd, hCd, hdiv⟩ :=
    exists_divisorCount_four_le_range_subpower (1 / 8) (by norm_num)
  let C : ℝ := 8 * Cd ^ 2 * (4 / Real.log 2 + 2) ^ 2
  have hC : 0 ≤ C := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  obtain ⟨B₀, hBgt⟩ := exists_nat_gt (4 * (A + 4))
  refine ⟨B₀, ?_⟩
  intro B hB
  refine ⟨0, ?_⟩
  intro Cc _hCc
  have hBexp : (4 : ℝ) - (B : ℝ) / 4 < -A := by
    have hB₀ : (4 : ℝ) * (A + 4) < B₀ := hBgt
    have hB' : (B₀ : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hdecay := eventually_const_log_power_le_decay
    (30 * C) (4 - (B : ℝ) / 4) A hBexp
  have hlogs : ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hall : ∀ᶠ X : ℝ in atTop,
      3 ≤ X ∧ 1 ≤ Real.log X ∧
        C * Real.rpow (Real.log X) (4 - (B : ℝ) / 4) ≤
          Real.rpow (Real.log X) (-A) / 30 := by
    filter_upwards [hdecay, hlogs, eventually_ge_atTop (3 : ℝ)] with X hd hl hx
    refine ⟨hx, hl, ?_⟩
    have : 30 * C * Real.rpow (Real.log X) (4 - (B : ℝ) / 4) ≤
        Real.rpow (Real.log X) (-A) := hd
    have h30 : 0 < (30 : ℝ) := by norm_num
    have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
    have hr : 0 ≤ Real.rpow (Real.log X) (4 - (B : ℝ) / 4) :=
      Real.rpow_nonneg hlogpos.le _
    nlinarith
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp hall
  refine ⟨max 3 X₁, le_max_left _ _, ?_⟩
  intro X hX p _inst hp hpX hf heta hqQ hbeta _hfar
  obtain ⟨hX3, hlog, hs⟩ := hX₁ X ((le_max_right 3 X₁).trans hX)
  subst X
  have hQ : 1 ≤ (Real.log p.X) ^ B := one_le_pow₀ hlog
  have hdivp := hdiv p.q ((Real.log p.X) ^ B)
    (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (NeZero.ne p.q))) hqQ
  have hmain := dynamicV3Normalization_mul_sum_smallRemainder_le_scalar
    hp hf (by linarith : 2 ≤ p.X) hlog hQ hqQ heta hbeta hCd.le hdivp
  have hX0 : 0 ≤ p.X := by linarith
  have hQpow : Real.rpow ((Real.log p.X) ^ B) (-(1 / 4 : ℝ)) =
      Real.rpow (Real.log p.X) (-(B : ℝ) / 4) := by
    have hlogp : 0 < Real.log p.X := by linarith
    have : (Real.log p.X) ^ B = Real.rpow (Real.log p.X) (B : ℝ) :=
      (Real.rpow_natCast _ B).symm
    calc
      Real.rpow ((Real.log p.X) ^ B) (-(1 / 4 : ℝ)) =
          Real.rpow (Real.rpow (Real.log p.X) (B : ℝ)) (-(1 / 4 : ℝ)) := by
        rw [this]
      _ = Real.rpow (Real.log p.X) ((B : ℝ) * (-(1 / 4 : ℝ))) := by
        simpa [Real.rpow_eq_pow] using
          (Real.rpow_mul hlogp.le (B : ℝ) (-(1 / 4 : ℝ))).symm
      _ = Real.rpow (Real.log p.X) (-(B : ℝ) / 4) := by congr 1; ring
  have hexp : (4 : ℝ) + (-(B : ℝ) / 4) = 4 - (B : ℝ) / 4 := by ring
  have hcomb :
      C * p.X * Real.log p.X ^ 4 *
          Real.rpow ((Real.log p.X) ^ B) (-(1 / 4 : ℝ)) =
        C * p.X * Real.rpow (Real.log p.X) (4 - (B : ℝ) / 4) := by
    have hlogp : 0 < Real.log p.X := by linarith
    have h4 : Real.log p.X ^ 4 = Real.rpow (Real.log p.X) 4 :=
      (Real.rpow_natCast _ 4).symm
    calc
      C * p.X * Real.log p.X ^ 4 *
          Real.rpow ((Real.log p.X) ^ B) (-(1 / 4 : ℝ)) =
        C * p.X * Real.rpow (Real.log p.X) 4 *
          Real.rpow (Real.log p.X) (-(B : ℝ) / 4) := by
        rw [h4, hQpow]
      _ = C * p.X * Real.rpow (Real.log p.X)
            (4 + (-(B : ℝ) / 4)) := by
        rw [mul_assoc, mul_assoc]
        have hadd :=
          (Real.rpow_add hlogp (4 : ℝ) (-(B : ℝ) / 4)).symm
        simpa [Real.rpow_eq_pow, mul_assoc] using
          congrArg (fun z => C * p.X * z) hadd
      _ = C * p.X * Real.rpow (Real.log p.X) (4 - (B : ℝ) / 4) := by
        rw [hexp]
  have hscalar : C * Real.rpow (Real.log p.X) (4 - (B : ℝ) / 4) ≤
      Real.rpow (Real.log p.X) (-A) / 30 := hs
  calc
    _ ≤ C * p.X * Real.log p.X ^ 4 *
        Real.rpow ((Real.log p.X) ^ B) (-(1 / 4 : ℝ)) := by
      simpa [C] using hmain
    _ = C * p.X * Real.rpow (Real.log p.X) (4 - (B : ℝ) / 4) := hcomb
    _ ≤ p.X * (Real.rpow (Real.log p.X) (-A) / 30) := by
      have := mul_le_mul_of_nonneg_left hscalar hX0
      nlinarith
    _ = p.X * Real.rpow (Real.log p.X) (-A) / 30 := by ring

end
end MAPSmallRemainderMassBudgetV3

#print axioms MAPSmallRemainderMassBudgetV3.smallRemainderMass_eq_primePower
#print axioms MAPSmallRemainderMassBudgetV3.norm_criticalDirichletPolynomial_map_le
#print axioms MAPSmallRemainderMassBudgetV3.dynamicV3Normalization_mul_sum_smallRemainder_le
#print axioms MAPSmallRemainderMassBudgetV3.exists_small_remainder_budget_thirtieth

