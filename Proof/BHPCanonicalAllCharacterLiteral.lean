import BHPCanonicalAllCharacterFromPrincipal

/-!
# Uniform source-faithful all-character BHP fourth moment

This file removes the artificial `T ≤ X` restriction from the selected-prefix
fourth moment.  It retains the literal `1 / sqrt X` Perron error, hence the
summed fourth-moment error `card S / X^2`.  Both analytic constants quantify
before every conductor, cutoff, height, and selected family, which is the
uniformity required by the MAP hard-range consumer.
-/

namespace MAPBHPCanonicalAllCharacterLiteral

set_option maxHeartbeats 8000000

open scoped BigOperators
open MAPMRTLemma211AllCharacterSource
open MAPMRTCorollary25Minkowski
open MAPBHPCorrectedPerronKernel
open MAPBHPShiftedHolderReduction
open MAPBHPShiftedRamachandraWeld
open MAPBHPCanonicalNonprincipalPointwise
open MAPBHPCanonicalAllCharacterFromPrincipal
open RamachandraTheorem6ShiftedStripSource

noncomputable section

private theorem harmonic_nonneg_real_literal (n : ℕ) :
    (0 : ℝ) ≤ (harmonic n : ℝ) := by
  norm_cast
  unfold harmonic
  positivity

/-- Five-term fourth-power convexity.  The exact constant `5^3 = 125` is the
finite-cardinality constant in the standard power-sum inequality. -/
theorem fourth_power_sum_five_le
    {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    (a + b + c + d + e) ^ 4 ≤
      125 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + e ^ 4) := by
  let f : Fin 5 → ℝ := fun i => match i with
    | 0 => a
    | 1 => b
    | 2 => c
    | 3 => d
    | 4 => e
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 5)), 0 ≤ f i := by
    intro i hi
    fin_cases i <;> simp [f, ha, hb, hc, hd, he]
  have h := pow_sum_le_card_mul_sum_pow hf 3
  simp [f, Fin.sum_univ_succ] at h
  convert h using 1 <;> ring

/-- Fixed-constant form of the robust Ramachandra `4T` specialization.
Unlike the existential convenience adapter, this theorem preserves the same
global source constant `C₆` for every later MAP input. -/
theorem canonicalFourfoldHeightShiftedFourthIntegral_polylog_le_fixed
    {C₆ : ℝ} (hC₆ : 0 < C₆)
    (hsource :
      ∀ (q : ℕ) [NeZero q] (U sigma : ℝ),
        3 ≤ U →
        |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * U))⁻¹ →
        allCharacterShiftedStripFourthIntegral q U sigma ≤
          C₆ * ramachandraTheorem6K2Scale q U)
    {q : ℕ} [NeZero q] {T x0 K : ℝ}
    (hT : 1 ≤ T) (hx0 : 2 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hTx : T ≤ x0)
    (hK : 0 ≤ K) (hthreshold : K ≤ Real.log (Real.log x0))
    (hqpoly : (q : ℝ) ≤ (Real.log x0) ^ K) :
    allCharacterShiftedStripFourthIntegral q (4 * T)
        ((1 / 2 : ℝ) + canonicalRamachandraOffset x0) ≤
      (4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
        Real.log x0 ^ 401 := by
  have hraw := hsource q (4 * T)
    ((1 / 2 : ℝ) + canonicalRamachandraOffset x0)
    (by linarith)
    (canonicalShift_mem_theorem6Strip_fourfoldHeight hT hx0 hqx hTx)
  refine hraw.trans ?_
  have hx0one : 1 < x0 := lt_of_lt_of_le (by norm_num) hx0
  have hx0pos : 0 < x0 := zero_lt_one.trans hx0one
  have hlogx : 0 < Real.log x0 := Real.log_pos hx0one
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hexp := exp_sqrt_log_conductor_le_log hK hx0one hthreshold hqpoly
  have hqt : (q : ℝ) * T ≤ x0 ^ 2 := by
    nlinarith [mul_le_mul hqx hTx hTpos.le hx0pos.le]
  have hfour : (4 : ℝ) ≤ x0 ^ 2 := by nlinarith
  have hprodLe : (q : ℝ) * (4 * T) ≤ x0 ^ 4 := by
    calc
      (q : ℝ) * (4 * T) = 4 * ((q : ℝ) * T) := by ring
      _ ≤ 4 * x0 ^ 2 := mul_le_mul_of_nonneg_left hqt (by norm_num)
      _ ≤ x0 ^ 2 * x0 ^ 2 :=
        mul_le_mul_of_nonneg_right hfour (sq_nonneg x0)
      _ = x0 ^ 4 := by ring
  have hlogprod0 : 0 ≤ Real.log ((q : ℝ) * (4 * T)) := by
    apply Real.log_nonneg
    nlinarith [mul_le_mul hqone hT (by norm_num : (0 : ℝ) ≤ 1) hqpos.le]
  have hlogLe : Real.log ((q : ℝ) * (4 * T)) ≤
      4 * Real.log x0 := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (mul_pos hqpos (mul_pos (by norm_num) hTpos))
      (pow_pos hx0pos 4) hprodLe
    rw [Real.log_pow] at hmono
    simpa using hmono
  have hlogpow : Real.log ((q : ℝ) * (4 * T)) ^ 400 ≤
      (4 * Real.log x0) ^ 400 :=
    pow_le_pow_left₀ hlogprod0 hlogLe 400
  unfold ramachandraTheorem6K2Scale
  calc
    C₆ * ((q : ℝ) * (4 * T) *
          Real.log ((q : ℝ) * (4 * T)) ^ 400 *
          Real.exp (Real.sqrt (Real.log (q : ℝ)))) ≤
        C₆ * ((q : ℝ) * (4 * T) *
          (4 * Real.log x0) ^ 400 * Real.log x0) := by
      gcongr
    _ = (4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
          Real.log x0 ^ 401 := by
      rw [mul_pow, pow_succ]
      ring

/-- Fixed-constant Holder weld.  This is the same positive-offset convolution
estimate as the convenience theorem in `BHPShiftedRamachandraWeld`, but its
source constant is explicit and therefore uniform across all inputs. -/
theorem canonicalShiftedPerronConvolutionFourth_le_exactKernel_fixed
    {C₆ : ℝ} (hC₆ : 0 < C₆)
    (hsource :
      ∀ (q : ℕ) [NeZero q] (U sigma : ℝ),
        3 ≤ U →
        |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * U))⁻¹ →
        allCharacterShiftedStripFourthIntegral q U sigma ≤
          C₆ * ramachandraTheorem6K2Scale q U)
    {q : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T x0 K : ℝ}
    (hT : 1 ≤ T) (hx0 : 2 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hTx : T ≤ x0)
    (hK : 0 ≤ K) (hthreshold : K ≤ Real.log (Real.log x0))
    (hqpoly : (q : ℝ) ≤ (Real.log x0) ^ K)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S) :
    (∑ z ∈ S,
      perronConvolution
        (shiftedCriticalLineLNorm z.1
          (canonicalRamachandraOffset x0)) (2 * T) z.2 ^ 4) ≤
      ((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
        (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
      ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
        Real.log x0 ^ 401) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hheightTwo : ∀ z ∈ S, |z.2| ≤ 2 * T := by
    intro z hz
    exact (hheight z hz).trans (by linarith)
  have hholder := sum_shiftedPerronConvolution_fourth_le_exactKernel
    (q := q) (S := S) (delta := canonicalRamachandraOffset x0)
    (T := 2 * T) (canonicalRamachandraOffset_ne_half hx0)
    (by positivity) hheightTwo hsep
  have hmean :=
    canonicalFourfoldHeightShiftedFourthIntegral_polylog_le_fixed
      hC₆ hsource hT hx0 hqx hTx hK hthreshold hqpoly
  have hmean' :
      allCharacterShiftedLineFourthIntegral q
          (canonicalRamachandraOffset x0) (2 * (2 * T)) ≤
        (4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
          Real.log x0 ^ 401 := by
    have hfour : 2 * (2 * T) = 4 * T := by ring
    rw [hfour]
    rw [allCharacterShiftedLineFourthIntegral_eq_source]
    exact hmean
  have hkernel0 :
      0 ≤ (∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
        (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ)) := by
    have hint : 0 ≤ ∫ u in (-(2 * T))..(2 * T), perronWeight u :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun u hu => (perronWeight_pos u).le)
    exact mul_nonneg (pow_nonneg hint 3)
      (mul_nonneg (by norm_num) (harmonic_nonneg_real_literal _))
  exact hholder.trans (mul_le_mul_of_nonneg_left hmean' hkernel0)

/-- Uniform no-`T ≤ X` all-character selected-prefix fourth moment. -/
def CanonicalAllCharacterSelectedFourthMomentLiteral : Prop :=
  ∃ C C₆ : ℝ, 0 < C ∧ 0 < C₆ ∧
    ∀ {q X : ℕ} [NeZero q]
      {S : Finset (DirichletCharacter ℂ q × ℝ)}
      {T x0 K : ℝ},
      2 ≤ X → 1 ≤ T → 8 ≤ x0 →
      (q : ℝ) ≤ x0 → (X : ℝ) ≤ x0 →
      T ≤ x0 → 2 * T ≤ x0 →
      0 ≤ K → K ≤ Real.log (Real.log x0) →
      (q : ℝ) ≤ (Real.log x0) ^ K →
      (∀ z ∈ S, |z.2| ≤ T) →
      SameCharacterOneSeparated S →
      selectedPrefixFourthMass X S ≤
        125 * (C * (1 + Real.log x0) ^ 2) ^ 4 *
          (((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
              (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
              ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
                Real.log x0 ^ 401) +
            (S.card : ℝ) *
              ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4 +
                1 / (X : ℝ) ^ 2) +
            (X : ℝ) ^ 2 * selectedPrincipalDecayMass S)

/-- The two honest global source propositions imply the uniform literal
all-character fourth moment.  There is no hidden `T ≤ X` hypothesis and no
input-dependent choice of constants. -/
theorem canonicalAllCharacterSelectedFourthMomentLiteral_of_sources
    (hPrincipal : CanonicalPrincipalPointwiseSourceLiteral)
    (hRamachandra : RamachandraTheorem6K2Source) :
    CanonicalAllCharacterSelectedFourthMomentLiteral := by
  classical
  obtain ⟨Cₚ, hCₚ, hprincipal⟩ := hPrincipal
  obtain ⟨C₆, hC₆, hsource⟩ := hRamachandra
  let C₀ : ℝ := canonicalNonprincipalPointwiseConstant
  let C : ℝ := C₀ + Cₚ
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    exact canonicalNonprincipalPointwiseConstant_pos
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, C₆, hC, hC₆, ?_⟩
  intro q X _inst S T x0 K hX hT hx0 hqx hXx hTx0 hTwoTx
    hK hthreshold hqpoly hheight hsep
  let L : ℝ := 1 + Real.log x0
  let a : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T
  let b : ℝ := Real.sqrt (X : ℝ) / T
  let d : ℝ := 1 / Real.sqrt (X : ℝ)
  let r : DirichletCharacter ℂ q × ℝ → ℝ := fun z =>
    Real.sqrt (X : ℝ) * principalPerronWeight z
  let V : DirichletCharacter ℂ q × ℝ → ℝ := fun z =>
    perronConvolution
      (shiftedCriticalLineLNorm z.1 (canonicalRamachandraOffset x0))
      (2 * T) z.2
  have hVsum :=
    canonicalShiftedPerronConvolutionFourth_le_exactKernel_fixed
      hC₆ hsource hT (by linarith : 2 ≤ x0) hqx hTx0 hK hthreshold
      hqpoly hheight hsep
  have hL : 0 ≤ L := by
    dsimp [L]
    have := Real.log_nonneg (show (1 : ℝ) ≤ x0 by linarith)
    linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hr (z : DirichletCharacter ℂ q × ℝ) : 0 ≤ r z := by
    dsimp [r]
    exact mul_nonneg (Real.sqrt_nonneg _) (principalPerronWeight_nonneg z)
  have hV (z : DirichletCharacter ℂ q × ℝ) : 0 ≤ V z := by
    dsimp [V]
    exact perronConvolution_nonneg (fun _ => norm_nonneg _) (by linarith)
  have hpoint (z : DirichletCharacter ℂ q × ℝ) (hz : z ∈ S) :
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
        C * L ^ 2 * (V z + a + b + d + r z) := by
    by_cases hzprincipal : z.1 = 1
    · have hp := hprincipal q X z.1 z.2 T x0 hzprincipal hX hT hx0
          hqx hXx hTx0 hTwoTx (hheight z hz)
      have hinner : 0 ≤ V z + a + b + d + r z :=
        add_nonneg (add_nonneg (add_nonneg (add_nonneg (hV z) ha) hb) hd)
          (hr z)
      have hCpC : Cₚ ≤ C := by dsimp [C]; linarith [hC₀.le]
      calc
        ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
            Cₚ * L ^ 2 * (V z + a + b + d + r z) := by
          simpa [L, V, a, b, d, r] using hp
        _ ≤ C * L ^ 2 * (V z + a + b + d + r z) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCpC (sq_nonneg L)) hinner
    · have hp := norm_criticalPrefixPolynomial_le_globalPolylog_literal
          z.1 hzprincipal hX hT hx0 hqx hXx hTx0 hTwoTx
          (hheight z hz)
      have hinner0 : 0 ≤ V z + a + b + d :=
        add_nonneg (add_nonneg (add_nonneg (hV z) ha) hb) hd
      have hinner : V z + a + b + d ≤ V z + a + b + d + r z :=
        le_add_of_nonneg_right (hr z)
      have hC₀C : C₀ ≤ C := by dsimp [C]; linarith [hCₚ.le]
      calc
        ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
            C₀ * L ^ 2 * (V z + a + b + d) := by
          simpa [C₀, L, V, a, b, d] using hp
        _ ≤ C * L ^ 2 * (V z + a + b + d) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC₀C (sq_nonneg L)) hinner0
        _ ≤ C * L ^ 2 * (V z + a + b + d + r z) :=
          mul_le_mul_of_nonneg_left hinner
            (mul_nonneg hC.le (sq_nonneg L))
  have hpoint4 (z : DirichletCharacter ℂ q × ℝ) (hz : z ∈ S) :
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4 ≤
        125 * (C * L ^ 2) ^ 4 *
          (V z ^ 4 + a ^ 4 + b ^ 4 + d ^ 4 + r z ^ 4) := by
    have hp := pow_le_pow_left₀
      (norm_nonneg (criticalPrefixPolynomial q X z.1 z.2)) (hpoint z hz) 4
    have hsum := fourth_power_sum_five_le (hV z) ha hb hd (hr z)
    calc
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4 ≤
          (C * L ^ 2 * (V z + a + b + d + r z)) ^ 4 := hp
      _ = (C * L ^ 2) ^ 4 * (V z + a + b + d + r z) ^ 4 := by
        exact mul_pow (C * L ^ 2) (V z + a + b + d + r z) 4
      _ ≤ (C * L ^ 2) ^ 4 *
          (125 * (V z ^ 4 + a ^ 4 + b ^ 4 + d ^ 4 + r z ^ 4)) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg (by positivity) 4)
      _ = 125 * (C * L ^ 2) ^ 4 *
          (V z ^ 4 + a ^ 4 + b ^ 4 + d ^ 4 + r z ^ 4) := by ac_rfl
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  have hTpos : 0 < T := by linarith
  have ha4 : a ^ 4 = (q : ℝ) ^ 2 / T ^ 2 := by
    dsimp [a]
    exact sqrt_ratio_fourth hq0 hTpos
  have hb4 : b ^ 4 = (X : ℝ) ^ 2 / T ^ 4 := by
    dsimp [b]
    rw [div_pow]
    rw [show Real.sqrt (X : ℝ) ^ 4 =
      (Real.sqrt (X : ℝ) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hX0]
  have hd4 : d ^ 4 = 1 / (X : ℝ) ^ 2 := by
    dsimp [d]
    rw [div_pow]
    norm_num
    rw [show Real.sqrt (X : ℝ) ^ 4 =
      (Real.sqrt (X : ℝ) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hX0]
  have hrsum : (∑ z ∈ S, r z ^ 4) =
      (X : ℝ) ^ 2 * selectedPrincipalDecayMass S := by
    dsimp [r]
    simp_rw [mul_pow]
    rw [show Real.sqrt (X : ℝ) ^ 4 =
      (Real.sqrt (X : ℝ) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hX0]
    rw [← Finset.mul_sum, sum_principalPerronWeight_fourth]
  unfold selectedPrefixFourthMass
  calc
    (∑ z ∈ S, ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4) ≤
        ∑ z ∈ S, 125 * (C * L ^ 2) ^ 4 *
          (V z ^ 4 + a ^ 4 + b ^ 4 + d ^ 4 + r z ^ 4) :=
      Finset.sum_le_sum fun z hz => hpoint4 z hz
    _ = 125 * (C * L ^ 2) ^ 4 *
        ((∑ z ∈ S, V z ^ 4) +
          (S.card : ℝ) * (a ^ 4 + b ^ 4 + d ^ 4) +
          ∑ z ∈ S, r z ^ 4) := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 125 * (C * L ^ 2) ^ 4 *
        (((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
            (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
            ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
              Real.log x0 ^ 401) +
          (S.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4 +
              1 / (X : ℝ) ^ 2) +
          (X : ℝ) ^ 2 * selectedPrincipalDecayMass S) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [ha4, hb4, hd4, hrsum]
      exact add_le_add (add_le_add hVsum (le_refl _)) (le_refl _)
    _ = _ := by rfl

end
end MAPBHPCanonicalAllCharacterLiteral

#print axioms MAPBHPCanonicalAllCharacterLiteral.fourth_power_sum_five_le
#print axioms MAPBHPCanonicalAllCharacterLiteral.canonicalFourfoldHeightShiftedFourthIntegral_polylog_le_fixed
#print axioms MAPBHPCanonicalAllCharacterLiteral.canonicalShiftedPerronConvolutionFourth_le_exactKernel_fixed
#print axioms MAPBHPCanonicalAllCharacterLiteral.canonicalAllCharacterSelectedFourthMomentLiteral_of_sources
