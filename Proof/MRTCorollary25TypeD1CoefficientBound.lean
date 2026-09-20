import MRTCorollary25TypeD1LiteralWeld
import FixedCharacterPoweredBridge

/-!
# Source-faithful Type-d1 coefficient bound

This file isolates the exact pointwise coefficient bookkeeping used before
MRT Corollary 2.5.  It proves the finite Dirichlet-convolution majorant; no
mean-value or far-annulus conclusion occurs here.
-/

namespace MAPMRTCorollary25TypeD1CoefficientBound

open scoped BigOperators
open ArithmeticFunction CGLProofDAG FixedCharacterPoweredBridge
open MAPMRTCorollary25TypeD1LiteralWeld

noncomputable section

/-- Quantitative form of the source's divisor-bounded condition.  The source
uses `r = k^2`, `ell = k`, with the constant hidden in `≪_k`. -/
def DivisorLogMajorized (r ell : ℕ) (A : ℝ) (f : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, ‖f n‖ ≤
    A * (orderedDivisorCount r n : ℝ) * Real.log (2 + (n : ℝ)) ^ ell

/-- Exact convolution law for ordered divisor counts. -/
theorem sum_orderedDivisorCount_mul_eq
    (r s n : ℕ) :
    (∑ z ∈ n.divisorsAntidiagonal,
        orderedDivisorCount r z.1 * orderedDivisorCount s z.2) =
      orderedDivisorCount (r + s) n := by
  change ((orderedDivisorCount r * orderedDivisorCount s) n) = _
  unfold orderedDivisorCount
  rw [← pow_add]

/-- The first permitted Type-d1 long factor, with the source interval `(M,2M]`. -/
def dyadicOneCoefficient (M : ℝ) (n : ℕ) : ℂ :=
  if M < (n : ℝ) ∧ (n : ℝ) ≤ 2 * M then 1 else 0

/-- The second permitted Type-d1 long factor `L 1_(M,2M]`, where
`L(n)=log n`. -/
def dyadicLogCoefficient (M : ℝ) (n : ℕ) : ℂ :=
  if M < (n : ℝ) ∧ (n : ℝ) ≤ 2 * M then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0

/-- Either source interval is contained in the closed support convention used
by the literal cutoff-removal weld. -/
theorem supportedDyadic_dyadicOneCoefficient
    {M : ℝ} :
    SupportedDyadic M (dyadicOneCoefficient M) := by
  intro n hn
  unfold dyadicOneCoefficient
  split_ifs with h
  · exact (hn ⟨h.1.le, h.2⟩).elim
  · rfl

theorem supportedDyadic_dyadicLogCoefficient
    {M : ℝ} :
    SupportedDyadic M (dyadicLogCoefficient M) := by
  intro n hn
  unfold dyadicLogCoefficient
  split_ifs with h
  · exact (hn ⟨h.1.le, h.2⟩).elim
  · rfl

/-- The indicator long factor is quantitatively 1-divisor-bounded. -/
theorem divisorLogMajorized_dyadicOneCoefficient
    {M : ℝ} (hM : 0 < M) :
    DivisorLogMajorized 1 0 1 (dyadicOneCoefficient M) := by
  intro n
  unfold dyadicOneCoefficient
  split_ifs with h
  · have hnposReal : (0 : ℝ) < n := hM.trans h.1
    have hn0 : n ≠ 0 := by exact_mod_cast hnposReal.ne'
    simp [orderedDivisorCount, ArithmeticFunction.zeta_apply, hn0]
  · simp

/-- The logarithmic long factor is quantitatively 1-divisor-bounded. -/
theorem divisorLogMajorized_dyadicLogCoefficient
    {M : ℝ} (hM : 0 < M) :
    DivisorLogMajorized 1 1 1 (dyadicLogCoefficient M) := by
  intro n
  unfold dyadicLogCoefficient
  split_ifs with h
  · have hnposReal : (0 : ℝ) < n := hM.trans h.1
    have hn0 : n ≠ 0 := by exact_mod_cast hnposReal.ne'
    have hnone : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnone
    have hlogle : Real.log n ≤ Real.log (2 + (n : ℝ)) := by
      apply Real.log_le_log hnposReal
      linarith
    change ‖((Real.log (n : ℝ) : ℝ) : ℂ)‖ ≤
      1 * (orderedDivisorCount 1 n : ℝ) *
        Real.log (2 + (n : ℝ)) ^ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    simpa [orderedDivisorCount, ArithmeticFunction.zeta_apply, hn0] using hlogle
  · simp only [norm_zero, one_mul, pow_one]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by
      have hnnonneg : (0 : ℝ) ≤ n := by positivity
      linarith))

/-- The shifted logarithmic factor in MRT's definition of divisor-boundedness
is globally subpolynomial on positive integers.  The constant absorbs the
finite range below the asymptotic threshold. -/
theorem log_two_add_pow_subpolynomial (ell : ℕ) :
    ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 0 < n →
        Real.log (2 + (n : ℝ)) ^ ell ≤ D * Real.rpow n eta := by
  intro eta heta
  have hevent :=
    (isLittleO_log_rpow_rpow_atTop (ell : ℝ) heta).eventuallyLE
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨A, hA⟩ := hevent
  let R : ℝ := max A 3
  let D : ℝ := Real.rpow 3 eta + Real.log R ^ ell + 1
  have hR3 : 3 ≤ R := le_max_right _ _
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR3
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hDpos : 0 < D := by
    dsimp [D]
    have hpowpos : 0 < Real.rpow 3 eta :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hlogpow0 : 0 ≤ Real.log R ^ ell := pow_nonneg hlogR0 _
    positivity
  refine ⟨D, hDpos, ?_⟩
  intro n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := hn1.trans' (by norm_num)
  have hnpow1 : 1 ≤ Real.rpow n eta := Real.one_le_rpow hn1 heta.le
  by_cases hlarge : A ≤ 2 + (n : ℝ)
  · have hx3 : 3 ≤ 2 + (n : ℝ) := by linarith
    have hx0 : 0 ≤ 2 + (n : ℝ) := by linarith
    have hlogx0 : 0 ≤ Real.log (2 + (n : ℝ)) :=
      Real.log_nonneg (by linarith)
    have hraw := hA (2 + (n : ℝ)) hlarge
    have hlogpow : Real.log (2 + (n : ℝ)) ^ ell ≤
        Real.rpow (2 + (n : ℝ)) eta := by
      simpa [Real.rpow_natCast,
        Real.norm_of_nonneg (pow_nonneg hlogx0 ell),
        Real.norm_of_nonneg (Real.rpow_nonneg hx0 eta)] using hraw
    have htwoadd : 2 + (n : ℝ) ≤ 3 * n := by linarith
    have hrpowmono : Real.rpow (2 + (n : ℝ)) eta ≤
        Real.rpow (3 * n) eta :=
      Real.rpow_le_rpow hx0 htwoadd heta.le
    have hmul : Real.rpow (3 * n) eta =
        Real.rpow 3 eta * Real.rpow n eta := by
      exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hn0
    have hcoeff : Real.rpow 3 eta ≤ D := by
      dsimp [D]
      have hlogpow0 : 0 ≤ Real.log R ^ ell := pow_nonneg hlogR0 _
      exact (le_add_of_nonneg_right hlogpow0).trans
        (le_add_of_nonneg_right (by norm_num))
    calc
      Real.log (2 + (n : ℝ)) ^ ell ≤
          Real.rpow (2 + (n : ℝ)) eta := hlogpow
      _ ≤ Real.rpow (3 * n) eta := hrpowmono
      _ = Real.rpow 3 eta * Real.rpow n eta := hmul
      _ ≤ D * Real.rpow n eta :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hn0 eta)
  · have hxR : 2 + (n : ℝ) ≤ R := by
      have : 2 + (n : ℝ) < A := lt_of_not_ge hlarge
      exact this.le.trans (le_max_left _ _)
    have hlogmono : Real.log (2 + (n : ℝ)) ≤ Real.log R := by
      exact Real.log_le_log (by positivity) hxR
    have hlogx0 : 0 ≤ Real.log (2 + (n : ℝ)) :=
      Real.log_nonneg (by linarith)
    have hpowmono : Real.log (2 + (n : ℝ)) ^ ell ≤
        Real.log R ^ ell := pow_le_pow_left₀ hlogx0 hlogmono ell
    have hcoeff : Real.log R ^ ell ≤ D := by
      dsimp [D]
      have hpow0 : 0 ≤ Real.rpow 3 eta := Real.rpow_nonneg (by norm_num) _
      calc
        Real.log R ^ ell ≤ Real.rpow 3 eta + Real.log R ^ ell :=
          le_add_of_nonneg_left hpow0
        _ ≤ Real.rpow 3 eta + Real.log R ^ ell + 1 :=
          le_add_of_nonneg_right (by norm_num)
    calc
      Real.log (2 + (n : ℝ)) ^ ell ≤ Real.log R ^ ell := hpowmono
      _ ≤ D := hcoeff
      _ ≤ D * Real.rpow n eta := by
        nlinarith

/-- Equation (24), in the precise divisor-log shape needed here: a fixed
ordered-divisor count times a fixed logarithmic power is subpolynomial. -/
theorem orderedDivisorCount_mul_log_pow_subpolynomial
    (r ell : ℕ) (hr : 1 ≤ r) :
    ∀ eta : ℝ, 0 < eta →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
        (orderedDivisorCount r n : ℝ) *
            Real.log (2 + (n : ℝ)) ^ ell ≤
          C * Real.rpow n eta := by
  intro eta heta
  have hhalf : 0 < eta / 2 := by linarith
  obtain ⟨Ctau, hCtau, htau⟩ :=
    orderedDivisorCount_subpolynomial r hr (eta / 2) hhalf
  obtain ⟨Clog, hClog, hlog⟩ :=
    log_two_add_pow_subpolynomial ell (eta / 2) hhalf
  refine ⟨Ctau * Clog, mul_pos hCtau hClog, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  calc
    (orderedDivisorCount r n : ℝ) *
        Real.log (2 + (n : ℝ)) ^ ell ≤
      (Ctau * Real.rpow n (eta / 2)) *
        (Clog * Real.rpow n (eta / 2)) := by
      apply mul_le_mul (htau n hn) (hlog n hn)
      · exact pow_nonneg (Real.log_nonneg (by
          have : (0 : ℝ) ≤ n := by positivity
          linarith)) _
      · exact mul_nonneg hCtau.le (Real.rpow_nonneg hn0 _)
    _ = (Ctau * Clog) *
        (Real.rpow n (eta / 2) * Real.rpow n (eta / 2)) := by ring
    _ = (Ctau * Clog) * Real.rpow n eta := by
      have hpow : Real.rpow n (eta / 2) * Real.rpow n (eta / 2) =
          Real.rpow n eta := by
        calc
          Real.rpow n (eta / 2) * Real.rpow n (eta / 2) =
              Real.rpow n (eta / 2 + eta / 2) :=
            (Real.rpow_add (by positivity : (0 : ℝ) < n) _ _).symm
          _ = Real.rpow n eta := by congr 1; ring
      rw [hpow]

/-- Every factor occurring in a positive antidiagonal factorization is at most
its product. -/
theorem antidiagonal_left_le
    {n : ℕ} {z : ℕ × ℕ} (hz : z ∈ n.divisorsAntidiagonal) : z.1 ≤ n := by
  have hmul : z.1 * z.2 = n := (Nat.mem_divisorsAntidiagonal.mp hz).1
  have hz2 : 0 < z.2 := Nat.pos_of_ne_zero
    (Nat.ne_zero_of_mem_divisorsAntidiagonal hz).2
  rw [← hmul]
  exact Nat.le_mul_of_pos_right z.1 hz2

/-- Right-factor companion to `antidiagonal_left_le`. -/
theorem antidiagonal_right_le
    {n : ℕ} {z : ℕ × ℕ} (hz : z ∈ n.divisorsAntidiagonal) : z.2 ≤ n := by
  have hmul : z.1 * z.2 = n := (Nat.mem_divisorsAntidiagonal.mp hz).1
  have hz1 : 0 < z.1 := Nat.pos_of_ne_zero
    (Nat.ne_zero_of_mem_divisorsAntidiagonal hz).1
  rw [← hmul]
  exact Nat.le_mul_of_pos_left z.2 hz1

/-- The quantitative divisor-log class is closed under literal two-factor
Dirichlet convolution, with the exact additive divisor and logarithmic
indices.  This is the source-faithful finite content of MRT Lemma 2.6 needed
for the Type-d1 cutoff-removal coefficient. -/
theorem literalDirichletConvolution_norm_le_divisorLog
    {r s ell j : ℕ} {A D : ℝ} {alpha beta : ℕ → ℂ}
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (halpha : DivisorLogMajorized r ell A alpha)
    (hbeta : DivisorLogMajorized s j D beta)
    (n : ℕ) :
    ‖literalDirichletConvolution alpha beta n‖ ≤
      (A * D) * (orderedDivisorCount (r + s) n : ℝ) *
        Real.log (2 + (n : ℝ)) ^ (ell + j) := by
  unfold literalDirichletConvolution
  calc
    ‖∑ z ∈ n.divisorsAntidiagonal, alpha z.1 * beta z.2‖ ≤
        ∑ z ∈ n.divisorsAntidiagonal, ‖alpha z.1 * beta z.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ z ∈ n.divisorsAntidiagonal,
        (A * D) *
          ((orderedDivisorCount r z.1 : ℝ) *
            (orderedDivisorCount s z.2 : ℝ)) *
          Real.log (2 + (n : ℝ)) ^ (ell + j) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [norm_mul]
      have hz1le : z.1 ≤ n := antidiagonal_left_le hz
      have hz2le : z.2 ≤ n := antidiagonal_right_le hz
      have hlog1 : Real.log (2 + (z.1 : ℝ)) ≤ Real.log (2 + (n : ℝ)) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.add_le_add_left hz1le 2
      have hlog2 : Real.log (2 + (z.2 : ℝ)) ≤ Real.log (2 + (n : ℝ)) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.add_le_add_left hz2le 2
      have hlog1nonneg : 0 ≤ Real.log (2 + (z.1 : ℝ)) := by
        apply Real.log_nonneg
        have hz1nonneg : (0 : ℝ) ≤ (z.1 : ℝ) := by positivity
        linarith
      have hlog2nonneg : 0 ≤ Real.log (2 + (z.2 : ℝ)) := by
        apply Real.log_nonneg
        have hz2nonneg : (0 : ℝ) ≤ (z.2 : ℝ) := by positivity
        linarith
      have hlognnonneg : 0 ≤ Real.log (2 + (n : ℝ)) := by
        apply Real.log_nonneg
        have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith
      have hpow1 := pow_le_pow_left₀ hlog1nonneg hlog1 ell
      have hpow2 := pow_le_pow_left₀ hlog2nonneg hlog2 j
      have ha := halpha z.1
      have hb := hbeta z.2
      have hcount1 : 0 ≤ (orderedDivisorCount r z.1 : ℝ) := by positivity
      have hcount2 : 0 ≤ (orderedDivisorCount s z.2 : ℝ) := by positivity
      calc
        ‖alpha z.1‖ * ‖beta z.2‖ ≤
            (A * (orderedDivisorCount r z.1 : ℝ) *
                Real.log (2 + (z.1 : ℝ)) ^ ell) *
              (D * (orderedDivisorCount s z.2 : ℝ) *
                Real.log (2 + (z.2 : ℝ)) ^ j) := by
          gcongr
        _ ≤ (A * (orderedDivisorCount r z.1 : ℝ) *
                Real.log (2 + (n : ℝ)) ^ ell) *
              (D * (orderedDivisorCount s z.2 : ℝ) *
                Real.log (2 + (n : ℝ)) ^ j) := by
          gcongr
        _ = (A * D) *
              ((orderedDivisorCount r z.1 : ℝ) *
                (orderedDivisorCount s z.2 : ℝ)) *
              Real.log (2 + (n : ℝ)) ^ (ell + j) := by
          rw [pow_add]
          ring
    _ = (A * D) * (orderedDivisorCount (r + s) n : ℝ) *
        Real.log (2 + (n : ℝ)) ^ (ell + j) := by
      have hsumR :
          (∑ z ∈ n.divisorsAntidiagonal,
            ((orderedDivisorCount r z.1 : ℕ) : ℝ) *
              ((orderedDivisorCount s z.2 : ℕ) : ℝ)) =
            ((orderedDivisorCount (r + s) n : ℕ) : ℝ) := by
        norm_cast
        exact sum_orderedDivisorCount_mul_eq r s n
      rw [← Finset.sum_mul]
      rw [← Finset.mul_sum]
      rw [hsumR]


/-- Subpower form of the literal Type-d1 coefficient estimate.  This is the
exact equation-(24) input used when Corollary 2.5 removes the outer interval. -/
theorem literalDirichletConvolution_subpolynomial
    {r s ell j : ℕ} (hrs : 1 ≤ r + s)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D)
    {alpha beta : ℕ → ℂ}
    (halpha : DivisorLogMajorized r ell A alpha)
    (hbeta : DivisorLogMajorized s j D beta) :
    ∀ eta : ℝ, 0 < eta →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
        ‖literalDirichletConvolution alpha beta n‖ ≤
          C * Real.rpow n eta := by
  intro eta heta
  obtain ⟨C0, hC0, hmajor⟩ :=
    orderedDivisorCount_mul_log_pow_subpolynomial
      (r + s) (ell + j) hrs eta heta
  refine ⟨(A * D) * C0, mul_pos (mul_pos hA hD) hC0, ?_⟩
  intro n hn
  calc
    ‖literalDirichletConvolution alpha beta n‖ ≤
        (A * D) * (orderedDivisorCount (r + s) n : ℝ) *
          Real.log (2 + (n : ℝ)) ^ (ell + j) :=
      literalDirichletConvolution_norm_le_divisorLog hA.le hD.le halpha hbeta n
    _ = (A * D) *
        ((orderedDivisorCount (r + s) n : ℝ) *
          Real.log (2 + (n : ℝ)) ^ (ell + j)) := by ring
    _ ≤ (A * D) * (C0 * Real.rpow n eta) := by
      exact mul_le_mul_of_nonneg_left (hmajor n hn) (mul_nonneg hA.le hD.le)
    _ = ((A * D) * C0) * Real.rpow n eta := by ring


/-- Uniform coefficient bound on the actual Type-d1 product block.  The
subpower constant is fixed independently of `N`, `M`, and `n`; only the
literal scale `(4*N*M)^eta` remains. -/
theorem literalDirichletConvolution_norm_le_productScale
    {r s ell j : ℕ} (hrs : 1 ≤ r + s)
    {eta A D N M : ℝ} (heta : 0 < eta) (hA : 0 < A) (hD : 0 < D)
    (hN : 0 < N) (hM : 0 < M)
    {alpha beta : ℕ → ℂ}
    (halphaSupport : SupportedDyadic N alpha)
    (hbetaSupport : SupportedDyadic M beta)
    (halpha : DivisorLogMajorized r ell A alpha)
    (hbeta : DivisorLogMajorized s j D beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖literalDirichletConvolution alpha beta n‖ ≤
        C * Real.rpow (4 * N * M) eta := by
  obtain ⟨C, hC, hsub⟩ := literalDirichletConvolution_subpolynomial
    hrs hA hD halpha hbeta eta heta
  refine ⟨C, hC, ?_⟩
  intro n
  have hscale0 : 0 ≤ 4 * N * M := by positivity
  by_cases hblock : N * M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 4 * N * M
  · have hnposReal : (0 : ℝ) < n := (mul_pos hN hM).trans_le hblock.1
    have hnpos : 0 < n := by exact_mod_cast hnposReal
    have hn0 : (0 : ℝ) ≤ n := hnposReal.le
    have hrpow : Real.rpow n eta ≤ Real.rpow (4 * N * M) eta :=
      Real.rpow_le_rpow hn0 hblock.2 heta.le
    exact (hsub n hnpos).trans
      (mul_le_mul_of_nonneg_left hrpow hC.le)
  · rw [literalDirichletConvolution_eq_zero_off_productBlock
      hN.le hM.le halphaSupport hbetaSupport hblock]
    simpa using mul_nonneg hC.le (Real.rpow_nonneg hscale0 eta)

/-- Corollary 2.5 on the literal Type-d1 branch with its coefficient premise
fully discharged by the source's divisor-bounded equation (24). -/
theorem cutoffRemoval_literalTypeD1_divisorLog_certified
    {r s ell j : ℕ} (hrs : 1 ≤ r + s)
    {eta A D N M T X1 X2 : ℝ}
    {alpha beta phase : ℕ → ℂ}
    (heta : 0 < eta) (hA : 0 < A) (hD : 0 < D)
    (hN : 0 < N) (hM : 0 < M) (hNM : 1 ≤ N * M)
    (hT : 1 ≤ T)
    (halphaSupport : SupportedDyadic N alpha)
    (hbetaSupport : SupportedDyadic M beta)
    (halpha : DivisorLogMajorized r ell A alpha)
    (hbeta : DivisorLogMajorized s j D beta)
    (hphase : ∀ n, ‖phase n‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      ‖MAPMRTCorollary25.halfLineDirichletPolynomial (N * M) 4
          (MAPMRTCorollary25.intervalCutoff X1 X2
            (MAPMRTCorollary25Instantiation.characterTwist phase
              (literalDirichletConvolution alpha beta))) t‖ ≤
        K * ((∫ u in (-T)..T,
            ‖MAPMRTCorollary25.halfLineDirichletPolynomial (N * M) 4
              (MAPMRTCorollary25Instantiation.characterTwist phase
                (literalDirichletConvolution alpha beta)) (t + u)‖ /
                (1 + |u|)) +
          (C * Real.rpow (4 * N * M) eta) *
            Real.sqrt (N * M) * Real.log (2 + T) / T) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    literalDirichletConvolution_norm_le_productScale hrs heta hA hD hN hM
      halphaSupport hbetaSupport halpha hbeta
  have hscale0 : 0 ≤ 4 * N * M := by positivity
  have hB : 0 ≤ C * Real.rpow (4 * N * M) eta :=
    mul_nonneg hC.le (Real.rpow_nonneg hscale0 eta)
  obtain ⟨K, hK, hcut⟩ :=
    cutoffRemoval_literalTypeD1_certified
      (N := N) (M := M) (T := T) (X1 := X1) (X2 := X2)
      (B := C * Real.rpow (4 * N * M) eta)
      hN hM hNM hT hB halphaSupport hbetaSupport hphase hcoeff
  exact ⟨C, hC, K, hK, hcut⟩

end
end MAPMRTCorollary25TypeD1CoefficientBound

#print axioms MAPMRTCorollary25TypeD1CoefficientBound.log_two_add_pow_subpolynomial
#print axioms MAPMRTCorollary25TypeD1CoefficientBound.orderedDivisorCount_mul_log_pow_subpolynomial
#print axioms MAPMRTCorollary25TypeD1CoefficientBound.sum_orderedDivisorCount_mul_eq
#print axioms MAPMRTCorollary25TypeD1CoefficientBound.literalDirichletConvolution_norm_le_divisorLog
#print axioms MAPMRTCorollary25TypeD1CoefficientBound.literalDirichletConvolution_subpolynomial
#print axioms MAPMRTCorollary25TypeD1CoefficientBound.literalDirichletConvolution_norm_le_productScale
#print axioms MAPMRTCorollary25TypeD1CoefficientBound.cutoffRemoval_literalTypeD1_divisorLog_certified
#print axioms MAPMRTCorollary25TypeD1CoefficientBound.divisorLogMajorized_dyadicOneCoefficient
#print axioms MAPMRTCorollary25TypeD1CoefficientBound.divisorLogMajorized_dyadicLogCoefficient
