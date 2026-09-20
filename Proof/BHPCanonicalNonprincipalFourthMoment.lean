import BHPCanonicalNonprincipalPointwise
import BHPShiftedRamachandraWeld

/-!
# Source-faithful nonprincipal BHP fourth moment

This file sums the uniform positive-offset pointwise contour estimate over an
arbitrary one-separated finite family.  It keeps the exact Holder/kernel
factor and the shifted Ramachandra moment visible.  The only analytic premise
is the literal shifted Theorem 6 source; no principal-character estimate is
smuggled into this theorem.
-/

namespace MAPBHPCanonicalNonprincipalFourthMoment

open scoped BigOperators
open MAPMRTLemma211AllCharacterSource
open MAPMRTCorollary25Minkowski
open MAPBHPCorrectedPerronKernel
open MAPBHPShiftedHolderReduction
open MAPBHPShiftedRamachandraWeld
open MAPBHPCanonicalNonprincipalPointwise
open RamachandraTheorem6ShiftedStripSource

noncomputable section

def nonprincipalSubfamily {q : ℕ}
    (S : Finset (DirichletCharacter ℂ q × ℝ)) :
    Finset (DirichletCharacter ℂ q × ℝ) := by
  classical
  exact S.filter (fun z => z.1 ≠ 1)

theorem mem_nonprincipalSubfamily_iff
    {q : ℕ} {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {z : DirichletCharacter ℂ q × ℝ} :
    z ∈ nonprincipalSubfamily S ↔ z ∈ S ∧ z.1 ≠ 1 := by
  classical
  simp [nonprincipalSubfamily]

/-- The complete nonprincipal BHP reduction at the corrected positive
offset.  The exact kernel is deliberately retained, so this statement
introduces no hidden logarithmic estimate. -/
theorem nonprincipal_selectedPrefixFourthMass_le_exactKernel
    (hRamachandra : RamachandraTheorem6K2Source)
    {q X : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T x0 K : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hx0 : 8 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0)
    (hTx0 : T ≤ x0) (hTwoTx : 2 * T ≤ x0)
    (hTX : T ≤ (X : ℝ))
    (hK : 0 ≤ K) (hthreshold : K ≤ Real.log (Real.log x0))
    (hqpoly : (q : ℝ) ≤ (Real.log x0) ^ K)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S) :
    ∃ C₆ : ℝ, 0 < C₆ ∧
      (∑ z ∈ nonprincipalSubfamily S,
        ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4) ≤
      64 *
        (canonicalNonprincipalPointwiseConstant *
          (1 + Real.log x0) ^ 2) ^ 4 *
        (((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
            (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
            ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
              Real.log x0 ^ 401) +
          ((nonprincipalSubfamily S).card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4)) := by
  classical
  let S₀ := nonprincipalSubfamily S
  let C₀ : ℝ := canonicalNonprincipalPointwiseConstant
  let L : ℝ := 1 + Real.log x0
  let a : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T
  let b : ℝ := Real.sqrt (X : ℝ) / T
  let V : DirichletCharacter ℂ q × ℝ → ℝ := fun z =>
    perronConvolution
      (shiftedCriticalLineLNorm z.1 (canonicalRamachandraOffset x0))
      (2 * T) z.2
  have hheight₀ : ∀ z ∈ S₀, |z.2| ≤ T := by
    intro z hz
    exact hheight z (mem_nonprincipalSubfamily_iff.mp hz).1
  have hsep₀ : SameCharacterOneSeparated S₀ := by
    intro z hz w hw hzw hchi
    exact hsep z (mem_nonprincipalSubfamily_iff.mp hz).1
      w (mem_nonprincipalSubfamily_iff.mp hw).1 hzw hchi
  obtain ⟨C₆, hC₆, hVsum⟩ :=
    canonicalShiftedPerronConvolutionFourth_le_exactKernel
      hRamachandra hT (by linarith : 2 ≤ x0) hqx hTx0 hK hthreshold
      hqpoly hheight₀ hsep₀
  refine ⟨C₆, hC₆, ?_⟩
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact canonicalNonprincipalPointwiseConstant_pos.le
  have hlog0 : 0 ≤ Real.log x0 :=
    Real.log_nonneg (by linarith)
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hTpos : 0 < T := by linarith
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  have ha4 : a ^ 4 = (q : ℝ) ^ 2 / T ^ 2 := by
    dsimp [a]
    exact sqrt_ratio_fourth hq0 hTpos
  have hb4 : b ^ 4 = (X : ℝ) ^ 2 / T ^ 4 := by
    dsimp [b]
    rw [div_pow]
    rw [show Real.sqrt (X : ℝ) ^ 4 =
      (Real.sqrt (X : ℝ) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hX0]
  have hpoint (z : DirichletCharacter ℂ q × ℝ) (hz : z ∈ S₀) :
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
        C₀ * L ^ 2 * (V z + a + b) := by
    have hzS := (mem_nonprincipalSubfamily_iff.mp hz).1
    have hznp := (mem_nonprincipalSubfamily_iff.mp hz).2
    simpa [C₀, L, V, a, b] using
      (norm_criticalPrefixPolynomial_le_globalPolylog z.1 hznp
        hX hT hx0 hqx hXx hTx0 hTwoTx hTX (hheight z hzS))
  have hVnonneg (z : DirichletCharacter ℂ q × ℝ) : 0 ≤ V z := by
    dsimp [V]
    exact perronConvolution_nonneg (fun _ => norm_nonneg _) (by linarith)
  have hpoint4 (z : DirichletCharacter ℂ q × ℝ) (hz : z ∈ S₀) :
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4 ≤
        64 * (C₀ * L ^ 2) ^ 4 * (V z ^ 4 + a ^ 4 + b ^ 4) := by
    have hscale : 0 ≤ C₀ * L ^ 2 :=
      mul_nonneg hC₀ (sq_nonneg _)
    have hupper := hpoint z hz
    have hp := pow_le_pow_left₀
      (norm_nonneg (criticalPrefixPolynomial q X z.1 z.2)) hupper 4
    have hsum := fourth_power_sum_four_le
      (hVnonneg z) ha hb (show (0 : ℝ) ≤ 0 by norm_num)
    calc
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4 ≤
          (C₀ * L ^ 2 * (V z + a + b)) ^ 4 := hp
      _ = (C₀ * L ^ 2) ^ 4 * (V z + a + b + 0) ^ 4 := by ring
      _ ≤ (C₀ * L ^ 2) ^ 4 *
          (64 * (V z ^ 4 + a ^ 4 + b ^ 4 + 0 ^ 4)) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg hscale 4)
      _ = 64 * (C₀ * L ^ 2) ^ 4 *
          (V z ^ 4 + a ^ 4 + b ^ 4) := by ring
  have hsumPoint :
      (∑ z ∈ S₀, ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4) ≤
        64 * (C₀ * L ^ 2) ^ 4 *
          ((∑ z ∈ S₀, V z ^ 4) +
            (S₀.card : ℝ) * (a ^ 4 + b ^ 4)) := by
    calc
      (∑ z ∈ S₀, ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4) ≤
          ∑ z ∈ S₀,
            64 * (C₀ * L ^ 2) ^ 4 *
              (V z ^ 4 + a ^ 4 + b ^ 4) :=
        Finset.sum_le_sum fun z hz => hpoint4 z hz
      _ = 64 * (C₀ * L ^ 2) ^ 4 *
          ((∑ z ∈ S₀, V z ^ 4) +
            (S₀.card : ℝ) * (a ^ 4 + b ^ 4)) := by
        rw [← Finset.mul_sum]
        congr 1
        simp_rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hinside :
      (∑ z ∈ S₀, V z ^ 4) +
          (S₀.card : ℝ) * (a ^ 4 + b ^ 4) ≤
        (((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
            (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
            ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
              Real.log x0 ^ 401)) +
          (S₀.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4) := by
    rw [ha4, hb4]
    exact add_le_add hVsum (le_refl _)
  exact hsumPoint.trans
    (mul_le_mul_of_nonneg_left hinside
      (mul_nonneg (by norm_num) (pow_nonneg (by positivity) 4)))

/-- Source-faithful no-`T <= X` fourth moment.  The literal Perron truncation
error contributes the additional `(card S)/X^2` term.  This is the version
whose hypotheses match MRT Corollary 2.12, where the prefix cutoff can be at
most the height. -/
theorem nonprincipal_selectedPrefixFourthMass_le_exactKernel_literal
    (hRamachandra : RamachandraTheorem6K2Source)
    {q X : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T x0 K : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hx0 : 8 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0)
    (hTx0 : T ≤ x0) (hTwoTx : 2 * T ≤ x0)
    (hK : 0 ≤ K) (hthreshold : K ≤ Real.log (Real.log x0))
    (hqpoly : (q : ℝ) ≤ (Real.log x0) ^ K)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S) :
    ∃ C₆ : ℝ, 0 < C₆ ∧
      (∑ z ∈ nonprincipalSubfamily S,
        ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4) ≤
      64 *
        (canonicalNonprincipalPointwiseConstant *
          (1 + Real.log x0) ^ 2) ^ 4 *
        (((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
            (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
            ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
              Real.log x0 ^ 401) +
          ((nonprincipalSubfamily S).card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4 +
              1 / (X : ℝ) ^ 2)) := by
  classical
  let S₀ := nonprincipalSubfamily S
  let C₀ : ℝ := canonicalNonprincipalPointwiseConstant
  let L : ℝ := 1 + Real.log x0
  let a : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T
  let b : ℝ := Real.sqrt (X : ℝ) / T
  let d : ℝ := 1 / Real.sqrt (X : ℝ)
  let V : DirichletCharacter ℂ q × ℝ → ℝ := fun z =>
    perronConvolution
      (shiftedCriticalLineLNorm z.1 (canonicalRamachandraOffset x0))
      (2 * T) z.2
  have hheight₀ : ∀ z ∈ S₀, |z.2| ≤ T := by
    intro z hz
    exact hheight z (mem_nonprincipalSubfamily_iff.mp hz).1
  have hsep₀ : SameCharacterOneSeparated S₀ := by
    intro z hz w hw hzw hchi
    exact hsep z (mem_nonprincipalSubfamily_iff.mp hz).1
      w (mem_nonprincipalSubfamily_iff.mp hw).1 hzw hchi
  obtain ⟨C₆, hC₆, hVsum⟩ :=
    canonicalShiftedPerronConvolutionFourth_le_exactKernel
      hRamachandra hT (by linarith : 2 ≤ x0) hqx hTx0 hK hthreshold
      hqpoly hheight₀ hsep₀
  refine ⟨C₆, hC₆, ?_⟩
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact canonicalNonprincipalPointwiseConstant_pos.le
  have hL : 0 ≤ L := by
    dsimp [L]
    have := Real.log_nonneg (show (1 : ℝ) ≤ x0 by linarith)
    linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hTpos : 0 < T := by linarith
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hX0 : 0 ≤ (X : ℝ) := by positivity
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
  have hpoint (z : DirichletCharacter ℂ q × ℝ) (hz : z ∈ S₀) :
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
        C₀ * L ^ 2 * (V z + a + b + d) := by
    have hzS := (mem_nonprincipalSubfamily_iff.mp hz).1
    have hznp := (mem_nonprincipalSubfamily_iff.mp hz).2
    simpa [C₀, L, V, a, b, d] using
      (norm_criticalPrefixPolynomial_le_globalPolylog_literal z.1 hznp
        hX hT hx0 hqx hXx hTx0 hTwoTx (hheight z hzS))
  have hVnonneg (z : DirichletCharacter ℂ q × ℝ) : 0 ≤ V z := by
    dsimp [V]
    exact perronConvolution_nonneg (fun _ => norm_nonneg _) (by linarith)
  have hpoint4 (z : DirichletCharacter ℂ q × ℝ) (hz : z ∈ S₀) :
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4 ≤
        64 * (C₀ * L ^ 2) ^ 4 *
          (V z ^ 4 + a ^ 4 + b ^ 4 + d ^ 4) := by
    have hscale : 0 ≤ C₀ * L ^ 2 :=
      mul_nonneg hC₀ (sq_nonneg _)
    have hp := pow_le_pow_left₀
      (norm_nonneg (criticalPrefixPolynomial q X z.1 z.2))
      (hpoint z hz) 4
    have hsum := fourth_power_sum_four_le (hVnonneg z) ha hb hd
    calc
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4 ≤
          (C₀ * L ^ 2 * (V z + a + b + d)) ^ 4 := hp
      _ = (C₀ * L ^ 2) ^ 4 * (V z + a + b + d) ^ 4 := by ring
      _ ≤ (C₀ * L ^ 2) ^ 4 *
          (64 * (V z ^ 4 + a ^ 4 + b ^ 4 + d ^ 4)) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg hscale 4)
      _ = 64 * (C₀ * L ^ 2) ^ 4 *
          (V z ^ 4 + a ^ 4 + b ^ 4 + d ^ 4) := by ring
  have hsumPoint :
      (∑ z ∈ S₀, ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4) ≤
        64 * (C₀ * L ^ 2) ^ 4 *
          ((∑ z ∈ S₀, V z ^ 4) +
            (S₀.card : ℝ) * (a ^ 4 + b ^ 4 + d ^ 4)) := by
    calc
      (∑ z ∈ S₀, ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4) ≤
          ∑ z ∈ S₀, 64 * (C₀ * L ^ 2) ^ 4 *
            (V z ^ 4 + a ^ 4 + b ^ 4 + d ^ 4) :=
        Finset.sum_le_sum fun z hz => hpoint4 z hz
      _ = 64 * (C₀ * L ^ 2) ^ 4 *
          ((∑ z ∈ S₀, V z ^ 4) +
            (S₀.card : ℝ) * (a ^ 4 + b ^ 4 + d ^ 4)) := by
        rw [← Finset.mul_sum]
        congr 1
        simp_rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hinside :
      (∑ z ∈ S₀, V z ^ 4) +
          (S₀.card : ℝ) * (a ^ 4 + b ^ 4 + d ^ 4) ≤
        (((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
            (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
            ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
              Real.log x0 ^ 401)) +
          (S₀.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4 +
              1 / (X : ℝ) ^ 2) := by
    rw [ha4, hb4, hd4]
    exact add_le_add hVsum (le_refl _)
  exact hsumPoint.trans
    (mul_le_mul_of_nonneg_left hinside
      (mul_nonneg (by norm_num) (pow_nonneg (by positivity) 4)))

/-- The same theorem after the already-certified Holder/kernel logarithmic
collapse.  This is the form directly useful in the MAP hard range. -/
theorem nonprincipal_selectedPrefixFourthMass_le_polylogKernel
    (hRamachandra : RamachandraTheorem6K2Source)
    {q X : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T x0 K : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hx0 : 8 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0)
    (hTx0 : T ≤ x0) (hTwoTx : 2 * T ≤ x0)
    (hTX : T ≤ (X : ℝ))
    (hK : 0 ≤ K) (hthreshold : K ≤ Real.log (Real.log x0))
    (hqpoly : (q : ℝ) ≤ (Real.log x0) ^ K)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S) :
    ∃ C₆ : ℝ, 0 < C₆ ∧
      (∑ z ∈ nonprincipalSubfamily S,
        ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4) ≤
      64 *
        (canonicalNonprincipalPointwiseConstant *
          (1 + Real.log x0) ^ 2) ^ 4 *
        (((256 * (1 / Real.log 2 + 4)) * Real.log x0 ^ 4) *
            ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
              Real.log x0 ^ 401) +
          ((nonprincipalSubfamily S).card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4)) := by
  obtain ⟨C₆, hC₆, hexact⟩ :=
    nonprincipal_selectedPrefixFourthMass_le_exactKernel hRamachandra
      hX hT hx0 hqx hXx hTx0 hTwoTx hTX hK hthreshold hqpoly
      hheight hsep
  refine ⟨C₆, hC₆, hexact.trans ?_⟩
  let W : ℝ :=
    (∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
      (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))
  let W₀ : ℝ :=
    (256 * (1 / Real.log 2 + 4)) * Real.log x0 ^ 4
  let M : ℝ :=
    (4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
      Real.log x0 ^ 401
  let E : ℝ :=
    ((nonprincipalSubfamily S).card : ℝ) *
      ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4)
  have hkernel : W ≤ W₀ := by
    dsimp [W, W₀]
    exact perronHolderKernel_le_log_four
      (show 2 ≤ 2 * T by linarith) hTwoTx
  have hM : 0 ≤ M := by
    dsimp [M]
    have hlog : 0 ≤ Real.log x0 := Real.log_nonneg (by linarith)
    positivity
  have hinside : W * M + E ≤ W₀ * M + E :=
    add_le_add_left (mul_le_mul_of_nonneg_right hkernel hM) E
  exact mul_le_mul_of_nonneg_left hinside (by positivity)

end
end MAPBHPCanonicalNonprincipalFourthMoment

#print axioms MAPBHPCanonicalNonprincipalFourthMoment.mem_nonprincipalSubfamily_iff
#print axioms MAPBHPCanonicalNonprincipalFourthMoment.nonprincipal_selectedPrefixFourthMass_le_exactKernel
#print axioms MAPBHPCanonicalNonprincipalFourthMoment.nonprincipal_selectedPrefixFourthMass_le_exactKernel_literal
#print axioms MAPBHPCanonicalNonprincipalFourthMoment.nonprincipal_selectedPrefixFourthMass_le_polylogKernel
