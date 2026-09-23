import MontgomeryDetectorEnergy
import MontgomeryHybridCharacterSampling

/-! # Direct Type-I at a full-scale mollifier

Unlike the short-mollifier route, every occupied shell above U≈qT has
length at least U/2. The ordinary hybrid sampler therefore gives the
terminal count without absorption of a pairwise kernel or integer powers.
-/
namespace MAPMontgomeryFullScaleTypeI
open scoped BigOperators
open CGLProofDAG MontgomeryVaughanFiniteReduction
open MAPMRTLemma210DyadicMeanSquare MAPMontgomeryHybridCharacterSampling
open MAPMontgomeryDetectorCharacterFactorization MAPMontgomeryDetectorEnergy
open MAPAppendixA4PostA5SetAdapter
noncomputable section

theorem detectorShell_direct_hybrid_count
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    {Y sigma T V kappa : ℝ} (hY : 0 < Y) (hsigma : 1/2 ≤ sigma)
    (hT : 0 ≤ T) (hV : 0 < V)
    (hscale : (q : ℝ)*(2*T+1) ≤ kappa*(D : ℝ))
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial (detectorCommonCoefficient chi U N Y sigma) D t‖) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V^2 ≤
      3*(kappa+8*Real.pi) * Real.rpow D (2*(1-sigma)) *
        (harmonic (2*D) : ℝ)^4 := by
  have hlarge' : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport D)
        (untwistedDetectorCommonCoefficient U N Y sigma) chi t‖ := by
    intro chi t ht
    simpa [dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket] using hlarge chi t ht
  have h := sum_character_card_le_of_large_values_symmetric hD
    (untwistedDetectorCommonCoefficient U N Y sigma) hT hV W hsep hheight hlarge'
  have he := detectorCommonCoefficientEnergy_le U N D hY hD hsigma
  have hp : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0<D)
  have hcoeff : 0 ≤ 3*((q : ℝ)*(2*T+1)+8*Real.pi*(D : ℝ)) := by positivity
  have henergy : 0 ≤ Real.rpow D (1-2*sigma)*(harmonic (2*D) : ℝ)^4 :=
    mul_nonneg (Real.rpow_nonneg hp.le _) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_right
    (show 3*((q : ℝ)*(2*T+1)+8*Real.pi*(D : ℝ)) ≤
      3*(kappa+8*Real.pi)*(D : ℝ) by nlinarith only [hscale]) henergy
  have hrpow : (D : ℝ)*Real.rpow D (1-2*sigma) = Real.rpow D (2*(1-sigma)) := by
    calc
      _ = Real.rpow D (1+(1-2*sigma)) := by
        simpa only [Real.rpow_one] using! (Real.rpow_add hp 1 (1-2*sigma)).symm
      _ = _ := by congr 1; ring
  apply h.trans ((mul_le_mul_of_nonneg_left he hcoeff).trans (hscaled.trans_eq ?_))
  calc
    _ = 3*(kappa+8*Real.pi)*((D : ℝ)*Real.rpow D (1-2*sigma))*
        (harmonic (2*D) : ℝ)^4 := by ring
    _ = _ := by rw [hrpow]
/-- The scale condition is automatic for every occupied shell once the
mollifier reaches the full hybrid scale. Empty shells contribute zero. -/
theorem detectorShell_direct_hybrid_count_of_fullMollifier
    {q U N D : ℕ} [NeZero q] (hD : 1 ≤ D)
    {Y sigma T V : ℝ} (hY : 0 < Y) (hsigma : 1/2 ≤ sigma)
    (hT : 0 ≤ T) (hV : 0 < V)
    (hfull : (q : ℝ)*(2*T+1) ≤ (U : ℝ))
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial (detectorCommonCoefficient chi U N Y sigma) D t‖) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V^2 ≤
      3*(2+8*Real.pi) * Real.rpow D (2*(1-sigma)) * (harmonic (2*D) : ℝ)^4 := by
  classical
  by_cases hcut : U < 2*D
  · apply detectorShell_direct_hybrid_count hD hY hsigma hT hV _ W hsep hheight hlarge
    exact hfull.trans (by exact_mod_cast hcut.le)
  · have hcut' : 2*D ≤ U := Nat.le_of_not_gt hcut
    have hzero : ∀ (chi : DirichletCharacter ℂ q) (t : ℝ),
        dirichletPolynomial (detectorCommonCoefficient chi U N Y sigma) D t = 0 := by
      intro chi t
      rw [dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket]
      unfold characterPacketPolynomial
      apply Finset.sum_eq_zero
      intro n hn
      have hnle : n ≤ 2*D := (Finset.mem_Ioc.mp hn).2
      have hnot : n ∉ Finset.Ico (U+1) (N+1) := by
        simp only [Finset.mem_Ico]
        omega
      simp [untwistedDetectorCommonCoefficient, hnot]
    have hempty : ∀ chi, W chi = ∅ := by
      intro chi
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have h := hlarge chi t ht
      rw [hzero, norm_zero] at h
      linarith
    simp only [hempty, Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero, zero_mul]
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)) (by positivity)

end
end MAPMontgomeryFullScaleTypeI
#print axioms MAPMontgomeryFullScaleTypeI.detectorShell_direct_hybrid_count

#print axioms MAPMontgomeryFullScaleTypeI.detectorShell_direct_hybrid_count_of_fullMollifier
