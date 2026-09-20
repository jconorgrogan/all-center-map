import MontgomeryFullScaleTypeI
import MontgomeryFullStripFourier
import MontgomeryLowStripNonprincipalSelection
namespace MAPMontgomeryFullScaleTypeISelection
open scoped BigOperators FourierTransform SchwartzMap
open Set Complex MeasureTheory CGLProofDAG
open MontgomeryVaughanFiniteReduction MAPAppendixA4PostA5SetAdapter
open PostA5TypeIFourierAssembly MAPMontgomeryLowStripNonprincipalSelection
open MAPMontgomeryFullScaleTypeI
noncomputable section

theorem detector_dyadic_length_le {N : ℕ} (hN : 1 ≤ N)
    (j : Fin (detectorDyadicCount N)) : 2^(j : ℕ) ≤ N := by
  have hj : (j : ℕ) ≤ (N-1).log2 := by
    have := j.isLt
    unfold detectorDyadicCount at this
    omega
  by_cases hn : N=1
  · subst N
    have hj0 : (j : ℕ)=0 := by
      have hjlt := j.isLt
      change (j : ℕ)<1 at hjlt
      omega
    simp [hj0]
  · have hp : 2^(j : ℕ) ≤ 2^((N-1).log2) :=
      Nat.pow_le_pow_right (by norm_num) hj
    have hbound := Nat.log2_self_le (by omega : N-1 ≠ 0)
    omega

/-- A deliberately crude polynomial coefficient mass, used only in a tail
that has arbitrary decay order. The counting bound still uses sharp energy. -/
theorem detector_shell_coefficient_mass_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (U N : ℕ)
    {Y sigma : ℝ} (hY : 0 < Y) (hsigma : 0 ≤ sigma)
    {D : ℕ} (hD : 1 ≤ D) (hDN : D ≤ N) :
    (∑ n ∈ Finset.Ioc D (2*D), ‖detectorCommonCoefficient chi U N Y sigma n‖) ≤
      2*(N : ℝ)^2 := by
  have hpoint : ∀ n ∈ Finset.Ioc D (2*D),
      ‖detectorCommonCoefficient chi U N Y sigma n‖ ≤ 2*(D : ℝ) := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hnp : 0 < n := by omega
    have hp := norm_detectorCommonCoefficient_le chi U N hY sigma hnp
    have hpow : Real.rpow n (-sigma) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hnp) (by linarith)
    have htau : (orderedDivisorCount 2 n : ℝ) ≤ n := by
      exact_mod_cast RamachandraShiftedCoefficientEnergy.orderedDivisorCount_two_le_self hnp
    calc
      _ ≤ Real.rpow n (-sigma) * orderedDivisorCount 2 n := hp
      _ ≤ 1*(n : ℝ) := mul_le_mul hpow htau (by positivity) (by norm_num)
      _ ≤ 2*(D : ℝ) := by simpa only [one_mul] using (show (n : ℝ) ≤ 2*(D : ℝ) by exact_mod_cast hn'.2)
  have hsum := Finset.sum_le_sum hpoint
  have hcard : (Finset.Ioc D (2*D)).card = D := by simp; omega
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  have hcast : (D : ℝ) ≤ N := by exact_mod_cast hDN
  nlinarith [sq_nonneg ((N : ℝ)-(D : ℝ)), (by positivity : (0:ℝ)≤D)]

/-- Instantiates all analytic Fourier mass/tail premises on a selected
source shell. The sole tail premise is now a literal numerical inequality. -/
theorem exists_fullStrip_typeI_fourier_family
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (hUN : U ≤ N)
    {Y sigma H V C : ℝ} (hY : 0 < Y) (hsigma : 1/2 ≤ sigma)
    (hH : 0 < H) (hV : 0 < V) (hHC : 2*Real.pi*H ≤ C)
    (k : ℕ) (j : Fin (detectorDyadicCount N)) (S : Finset ℂ)
    (hsep : ∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' → 2*C+1 ≤ |rho.im-rho'.im|)
    (hbetaLow : ∀ rho ∈ S, sigma ≤ rho.re)
    (hbetaHigh : ∀ rho ∈ S, rho.re ≤ 1)
    (htailBudget : 2*(N : ℝ)^2 * ((H^k)⁻¹ *
      MAPMontgomeryFullStripFourier.detectorFourierMomentConstant k) ≤
      (V/(detectorDyadicCount N : ℝ))/2)
    (hblock : ∀ rho ∈ S, V ≤ detectorDyadicCount N *
      ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖) :
    ∃ (xi : ℂ → ℝ) (P : Finset ℝ),
      P = S.image (fun rho => -rho.im+2*Real.pi*xi rho) ∧
      OneSeparated P ∧ P.card=S.card ∧
      (∀ rho ∈ S, |xi rho| ≤ H) ∧
      (∀ t ∈ P, V/(4*(1+MAPMontgomeryFullStripFourier.detectorFourierMomentConstant 0)*
        detectorDyadicCount N) ≤
        ‖dirichletPolynomial (detectorCommonCoefficient chi U N Y sigma) (2^(j : ℕ)) t‖) := by
  have hD : 1 ≤ 2^(j : ℕ) := Nat.one_le_pow _ _ (by norm_num)
  have hDN := detector_dyadic_length_le (hU.trans hUN) j
  have hA : 0 < 1+MAPMontgomeryFullStripFourier.detectorFourierMomentConstant 0 := by
    linarith [MAPMontgomeryFullStripFourier.detectorFourierMomentConstant_nonneg 0]
  have hmass : ∀ rho ∈ S,
      (∫ xi in Set.Icc (-H) H,
        ‖((𝓕 (detectorRealPartCutoff (rho.re-sigma) (2^(j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      1+MAPMontgomeryFullStripFourier.detectorFourierMomentConstant 0 := by
    intro rho hrho
    apply (MAPMontgomeryFullStripFourier.central_fourier_mass_le
      (a := rho.re-sigma) hD
      (by linarith [hbetaLow rho hrho]) (by linarith [hbetaHigh rho hrho]) H).trans
    linarith
  have htail : ∀ rho ∈ S,
      (∑ n ∈ Finset.Ioc (2^(j : ℕ)) (2*2^(j : ℕ)),
        ‖detectorCommonCoefficient chi U N Y sigma n‖) *
      (∫ xi in (Set.Icc (-H) H)ᶜ,
        ‖((𝓕 (detectorRealPartCutoff (rho.re-sigma) (2^(j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      (V/(detectorDyadicCount N : ℝ))/2 := by
    intro rho hrho
    have hm := detector_shell_coefficient_mass_le chi U N (sigma := sigma) hY (by linarith) hD hDN
    have ht := MAPMontgomeryFullStripFourier.fourier_tail_le (a := rho.re-sigma) hD
      (by linarith [hbetaLow rho hrho]) (by linarith [hbetaHigh rho hrho]) k hH
    apply (mul_le_mul hm ht (integral_nonneg fun _ => norm_nonneg _) (by positivity)).trans
    exact htailBudget
  obtain ⟨xi,hxi⟩ := exists_typeI_fourier_assignment chi hU Y sigma j S hA hV hmass htail hblock
  let P := S.image (fun rho => -rho.im+2*Real.pi*xi rho)
  have hx : ∀ rho ∈ S, |xi rho| ≤ H := by
    intro rho hrho
    exact abs_le.mpr (hxi rho hrho).1
  have hshift : ∀ rho ∈ S, |2*Real.pi*xi rho| ≤ C := by
    intro rho hrho
    rw [abs_mul,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (mul_le_mul_of_nonneg_left (hx rho hrho) (by positivity)).trans hHC
  obtain ⟨hsep',hcard⟩ := oneSeparated_image_neg_im_add_of_longSeparated
    S (fun rho => 2*Real.pi*xi rho) hshift hsep
  refine ⟨xi,P,rfl,hsep',hcard,hx,?_⟩
  intro t ht
  obtain ⟨rho,hrho,rfl⟩ := Finset.mem_image.mp ht
  exact (hxi rho hrho).2
end
end MAPMontgomeryFullScaleTypeISelection
#print axioms MAPMontgomeryFullScaleTypeISelection.exists_fullStrip_typeI_fourier_family
