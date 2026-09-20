import JutilaTwoScaleHorizontalDecay

/-!
# The principal residue in Jutila's Lemma 1 is smaller than one

Jutila, Acta Arith. 32 (1977), Lemma 1, p. 58, moves the initial contour
past `w = 1-s` and states that the residue is `< 1` for the principal
character.  This file proves that numerical assertion in the literal source
regime `h = log^2(qT)`, `|t| > h^2`, `N < qT` (with the harmless explicit
meaning of "qT sufficiently large": `10 ≤ log(qT)`).
-/

namespace JutilaPrincipalResidueBound

open Complex Real Filter Topology
open JutilaTwoScaleSmoothing
open JutilaTwoScaleHorizontalDecay
open MAPGammaCompactStripSharp

noncomputable section

def principalResidueCoefficient (N h sigma t : ℝ) : ℂ :=
  Complex.Gamma
      (1 + ((1 : ℂ) - ((sigma : ℂ) + t * I)) / (h : ℂ)) *
    twoScaleRemovableQuotient N
      ((1 : ℂ) - ((sigma : ℂ) + t * I))

/-- The two-scale quotient at the principal pole retains the useful
`1/|t|` denominator. -/
theorem norm_twoScaleRemovableQuotient_one_sub_le
    {N Q sigma t : ℝ} (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1) (ht : 0 < |t|) :
    ‖twoScaleRemovableQuotient N
        ((1 : ℂ) - ((sigma : ℂ) + t * I))‖ ≤ 4 * Q / |t| := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have h2N0 : 0 < 2 * N := mul_pos (by norm_num) hN0
  let w : ℂ := (1 : ℂ) - ((sigma : ℂ) + t * I)
  have hwIm : w.im = -t := by simp [w]
  have hwRe : w.re = 1 - sigma := by simp [w]
  have hw : w ≠ 0 := by
    intro hw
    have him := congrArg Complex.im hw
    rw [hwIm] at him
    simp at him
    subst t
    norm_num at ht
  have hden : |t| ≤ ‖w‖ := by
    rw [← abs_neg t, ← hwIm]
    exact Complex.abs_im_le_norm w
  have hexp0 : 0 ≤ 1 - sigma := by linarith
  have hexp1 : 1 - sigma ≤ 1 := by linarith
  have h2pow : (2 * N) ^ (1 - sigma) ≤ 2 * N := by
    calc
      (2 * N) ^ (1 - sigma) ≤ (2 * N) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith) hexp1
      _ = 2 * N := Real.rpow_one _
  have hNpow : N ^ (1 - sigma) ≤ N := by
    calc
      N ^ (1 - sigma) ≤ N ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN hexp1
      _ = N := Real.rpow_one _
  have hnum : ‖twoScaleSpectralFactor N w‖ ≤ 4 * Q := by
    calc
      ‖twoScaleSpectralFactor N w‖ ≤
          ‖((2 * N : ℝ) : ℂ) ^ w‖ + ‖(N : ℂ) ^ w‖ := norm_sub_le _ _
      _ = (2 * N) ^ (1 - sigma) + N ^ (1 - sigma) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos h2N0,
          Complex.norm_cpow_eq_rpow_re_of_pos hN0, hwRe]
      _ ≤ 2 * N + N := add_le_add h2pow hNpow
      _ ≤ 4 * Q := by nlinarith
  change ‖twoScaleRemovableQuotient N w‖ ≤ _
  rw [twoScaleRemovableQuotient, Function.update_of_ne hw, norm_div]
  exact (div_le_div_of_nonneg_left (norm_nonneg _) ht hden).trans
    (div_le_div_of_nonneg_right hnum ht.le)

/-- Exact Gamma estimate at `w=1-s`. -/
theorem norm_Gamma_principalResidue_le
    {h sigma t : ℝ} (hh : 2 ≤ h)
    (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1) :
    ‖Complex.Gamma
        (1 + ((1 : ℂ) - ((sigma : ℂ) + t * I)) / (h : ℂ))‖ ≤
      12 * (1 + |t| / h) *
        Real.exp (-(Real.pi / 2) * (|t| / h)) := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hlo : (1 / 2 : ℝ) ≤ 1 + (1 - sigma) / h := by
    have : 0 ≤ (1 - sigma) / h := div_nonneg (by linarith) hh0.le
    linarith
  have hhi : 1 + (1 - sigma) / h ≤ (3 / 2 : ℝ) := by
    have hdiv : (1 - sigma) / h ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hh0).2
      nlinarith
    linarith
  have hpoint :
      1 + ((1 : ℂ) - ((sigma : ℂ) + t * I)) / (h : ℂ) =
        GammaCompactStripScratch.stripPoint
          (1 + (1 - sigma) / h) (-t / h) := by
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]
  have hG := norm_Gamma_positive_strip_le_exp_pi_half
    hlo hhi (t := -t / h)
  rw [← hpoint] at hG
  have habs : |-t / h| = |t| / h := by
    rw [abs_div, abs_neg, abs_of_pos hh0]
  simpa [habs] using hG

/-- A source-faithful explicit residue envelope before the final logarithmic
absorption. -/
theorem norm_principalResidueCoefficient_le
    {N Q h sigma t : ℝ} (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (hh : 2 ≤ h) (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1)
    (ht : 0 < |t|) :
    ‖principalResidueCoefficient N h sigma t‖ ≤
      48 * Q * ((1 + |t| / h) / |t|) *
        Real.exp (-(Real.pi / 2) * (|t| / h)) := by
  have hG := norm_Gamma_principalResidue_le hh hsigma0 hsigma1 (t := t)
  have hQ := norm_twoScaleRemovableQuotient_one_sub_le
    hN hNQ hsigma0 hsigma1 ht
  unfold principalResidueCoefficient
  rw [norm_mul]
  calc
    ‖Complex.Gamma
          (1 + ((1 : ℂ) - ((sigma : ℂ) + t * I)) / (h : ℂ))‖ *
        ‖twoScaleRemovableQuotient N
          ((1 : ℂ) - ((sigma : ℂ) + t * I))‖ ≤
      (12 * (1 + |t| / h) *
          Real.exp (-(Real.pi / 2) * (|t| / h))) * (4 * Q / |t|) := by
        gcongr
    _ = 48 * Q * ((1 + |t| / h) / |t|) *
        Real.exp (-(Real.pi / 2) * (|t| / h)) := by ring

/-- Under `|t| ≥ h²`, the pole residue is bounded by the simple source-scale
quantity `96(Q/h)e^{-h}`. -/
theorem norm_principalResidueCoefficient_le_sourceEnvelope
    {N Q h sigma t : ℝ} (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (hh : 2 ≤ h) (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1)
    (ht : h ^ 2 ≤ |t|) :
    ‖principalResidueCoefficient N h sigma t‖ ≤
      96 * (Q / h) * Real.exp (-h) := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have ht0 : 0 < |t| := lt_of_lt_of_le (sq_pos_of_pos hh0) ht
  have hu : h ≤ |t| / h := by
    apply (le_div_iff₀ hh0).2
    simpa [pow_two] using ht
  have hu1 : 1 ≤ |t| / h := by linarith
  have hratio : (1 + |t| / h) / |t| ≤ 2 / h := by
    apply (div_le_div_iff₀ ht0 hh0).2
    have hrecover : h * (|t| / h) = |t| := by field_simp
    rw [add_mul, one_mul, mul_comm (|t| / h) h, hrecover]
    nlinarith
  have hc : 1 ≤ Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  have hu0 : 0 ≤ |t| / h := div_nonneg (abs_nonneg _) hh0.le
  have hcu : |t| / h ≤ (Real.pi / 2) * (|t| / h) := by
    have hmul := mul_le_mul_of_nonneg_right hc hu0
    norm_num at hmul ⊢
    exact hmul
  have hexponent : h ≤ (Real.pi / 2) * (|t| / h) := hu.trans hcu
  have hexp : Real.exp (-(Real.pi / 2) * (|t| / h)) ≤ Real.exp (-h) := by
    exact Real.exp_monotone (by linarith)
  have hraw := norm_principalResidueCoefficient_le
    hN hNQ hh hsigma0 hsigma1 ht0
  have hQ0 : 0 ≤ Q := by linarith
  calc
    ‖principalResidueCoefficient N h sigma t‖ ≤
        48 * Q * ((1 + |t| / h) / |t|) *
          Real.exp (-(Real.pi / 2) * (|t| / h)) := hraw
    _ ≤ 48 * Q * (2 / h) * Real.exp (-h) := by
      gcongr
    _ = 96 * (Q / h) * Real.exp (-h) := by ring

/-- Jutila's p.58 assertion: the principal residue is strictly smaller than
one once `qT` is in the explicit sufficiently-large range. -/
theorem norm_principalResidueCoefficient_lt_one
    {N Q L h sigma t : ℝ}
    (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (hQ : Q = Real.exp L) (hh : h = L ^ 2) (hL : 10 ≤ L)
    (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1)
    (ht : h ^ 2 ≤ |t|) :
    ‖principalResidueCoefficient N h sigma t‖ < 1 := by
  have hh100 : 100 ≤ h := by rw [hh]; nlinarith
  have hh2 : 2 ≤ h := by linarith
  have henv := norm_principalResidueCoefficient_le_sourceEnvelope
    hN hNQ hh2 hsigma0 hsigma1 ht
  have hQexp : Q * Real.exp (-h) = Real.exp (L - L ^ 2) := by
    rw [hQ, hh, ← Real.exp_add]
    congr 1
  have hnegative : L - L ^ 2 < 0 := by nlinarith
  have hsmall : Q * Real.exp (-h) < 1 := by
    rw [hQexp]
    exact Real.exp_lt_one_iff.mpr hnegative
  have hfactor : 96 / h ≤ 96 / 100 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hh100
  calc
    ‖principalResidueCoefficient N h sigma t‖ ≤
        96 * (Q / h) * Real.exp (-h) := henv
    _ = (96 / h) * (Q * Real.exp (-h)) := by ring
    _ < (96 / h) * 1 :=
      mul_lt_mul_of_pos_left hsmall (div_pos (by norm_num) (by linarith))
    _ ≤ (96 / 100) * 1 := mul_le_mul_of_nonneg_right hfactor (by norm_num)
    _ < 1 := by norm_num

end

end JutilaPrincipalResidueBound

#print axioms JutilaPrincipalResidueBound.norm_twoScaleRemovableQuotient_one_sub_le
#print axioms JutilaPrincipalResidueBound.norm_Gamma_principalResidue_le
#print axioms JutilaPrincipalResidueBound.norm_principalResidueCoefficient_le_sourceEnvelope
#print axioms JutilaPrincipalResidueBound.norm_principalResidueCoefficient_lt_one
