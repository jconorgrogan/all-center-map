import MontgomeryFullScaleTypeISelection
import Mathlib.NumberTheory.Harmonic.Bounds
namespace MAPMontgomeryFullScaleTypeIFamily
open scoped BigOperators FourierTransform SchwartzMap
open Set Complex MeasureTheory CGLProofDAG
open MAPAppendixA4PostA5SetAdapter MAPAppendixA4DetectorDichotomy PostA5TypeIFourierAssembly
open MAPMontgomeryFullScaleTypeISelection MAPMontgomeryLowStripNonprincipalSelection
open MAPMontgomeryFullScaleTypeI MAPMontgomeryCharacterShellGrouping
noncomputable section

def fullStripFourierMass : ℝ := 1+MAPMontgomeryFullStripFourier.detectorFourierMomentConstant 0

theorem fullScale_typeI_family_budget
    {q U N : ℕ} [NeZero q] (hU : 1 ≤ U) (hUN : U ≤ N)
    (W : DirichletCharacter ℂ q → Finset ℂ)
    {Y sigma H V C T : ℝ} (hY : 0 < Y) (hsigma : 1/2 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (hH : 0 < H) (hV : 0 < V) (hHC : 2*Real.pi*H ≤ C) (hT : 0 ≤ T)
    (hfull : (q : ℝ)*(2*(T+C)+1) ≤ (U : ℝ))
    (k : ℕ)
    (hsep : ∀ chi rho, rho ∈ W chi → ∀ rho', rho' ∈ W chi →
      rho ≠ rho' → 2*C+1 ≤ |rho.im-rho'.im|)
    (hbetaLow : ∀ chi rho, rho ∈ W chi → sigma ≤ rho.re)
    (hbetaHigh : ∀ chi rho, rho ∈ W chi → rho.re ≤ 1)
    (hheight : ∀ chi rho, rho ∈ W chi → |rho.im| ≤ T)
    (htailBudget : 2*(N : ℝ)^2 * ((H^k)⁻¹ *
      MAPMontgomeryFullStripFourier.detectorFourierMomentConstant k) ≤
      (V/(detectorDyadicCount N : ℝ))/2)
    (hlarge : ∀ chi rho, rho ∈ W chi → V ≤ ‖arithmeticDetectorBlock chi U N rho Y‖) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) *
        (V/(4*fullStripFourierMass*detectorDyadicCount N))^2 ≤
      (detectorDyadicCount N : ℝ)^2 * 3*(2+8*Real.pi) *
        Real.rpow N (2*(1-sigma)) * (1+Real.log (2*(N : ℝ)))^4 := by
  classical
  have hJ : 0 < detectorDyadicCount N := by unfold detectorDyadicCount; omega
  have hJr : (0:ℝ)<detectorDyadicCount N := by exact_mod_cast hJ
  have hA : 0 < fullStripFourierMass := by
    unfold fullStripFourierMass
    linarith [MAPMontgomeryFullStripFourier.detectorFourierMomentConstant_nonneg 0]
  have hC : 0 ≤ C := le_trans (by positivity) hHC
  have hchoose : ∀ chi : DirichletCharacter ℂ q,
      ∃ j : Fin (detectorDyadicCount N), ∃ Z : Finset ℂ,
        Z ⊆ W chi ∧ (W chi).card ≤ detectorDyadicCount N * Z.card ∧
        ∀ rho ∈ Z, V ≤ detectorDyadicCount N *
          ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖ := by
    intro chi
    exact exists_common_arithmeticDetectorDyadicBlock chi hU hUN (hlarge chi)
  choose j Z hZ hcard hblock using hchoose
  have hchooseFourier : ∀ chi : DirichletCharacter ℂ q,
      ∃ (xi : ℂ → ℝ) (P : Finset ℝ),
        P= (Z chi).image (fun rho => -rho.im+2*Real.pi*xi rho) ∧
        OneSeparated P ∧ P.card=(Z chi).card ∧
        (∀ rho ∈ Z chi, |xi rho| ≤ H) ∧
        (∀ t ∈ P, V/(4*fullStripFourierMass*detectorDyadicCount N) ≤
          ‖dirichletPolynomial (detectorCommonCoefficient chi U N Y sigma) (2^((j chi : Fin _):ℕ)) t‖) := by
    intro chi
    exact exists_fullStrip_typeI_fourier_family chi hU hUN hY hsigma hH hV hHC k (j chi) (Z chi)
      (fun rho hrho rho' hrho' hne => hsep chi rho (hZ chi hrho) rho' (hZ chi hrho') hne)
      (fun rho hrho => hbetaLow chi rho (hZ chi hrho))
      (fun rho hrho => hbetaHigh chi rho (hZ chi hrho)) htailBudget (hblock chi)
  choose xi P hP hPsep hPcard hxi hPlarge using hchooseFourier
  have hPheight : ∀ chi, ∀ t ∈ P chi, |t| ≤ T+C := by
    intro chi t ht
    rw [hP chi] at ht
    obtain ⟨rho,hrho,rfl⟩ := Finset.mem_image.mp ht
    calc
      _ ≤ |-rho.im|+|2*Real.pi*xi chi rho| := abs_add_le _ _
      _ = |rho.im|+(2*Real.pi)*|xi chi rho| := by
        rw [abs_neg,abs_mul,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<2)]
      _ ≤ T+2*Real.pi*H := add_le_add (hheight chi rho (hZ chi hrho))
        (mul_le_mul_of_nonneg_left (hxi chi rho hrho) (by positivity))
      _ ≤ T+C := by linarith
  obtain ⟨i,hcommon,hsep',hheight',hlarge'⟩ := exists_common_typeI_detector_shell_family
    hJ j P Y sigma (V/(4*fullStripFourierMass*detectorDyadicCount N)) (T+C)
    hPsep hPheight hPlarge
  let P' := restrictFamilyByIndex j P i
  have hD : 1 ≤ 2^(i : ℕ) := Nat.one_le_pow _ _ (by norm_num)
  have hDN := detector_dyadic_length_le (hU.trans hUN) i
  have hbudget := detectorShell_direct_hybrid_count_of_fullMollifier hD hY hsigma
    (show 0 ≤ T+C by linarith) (div_pos hV (by positivity)) hfull P' hsep' hheight' hlarge'
  have hcard0 : (∑ chi : DirichletCharacter ℂ q, (W chi).card) ≤
      detectorDyadicCount N * ∑ chi : DirichletCharacter ℂ q, (P chi).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun chi hchi => by rw [hPcard chi]; exact hcard chi
  have hcard1 : (∑ chi : DirichletCharacter ℂ q, (W chi).card) ≤
      (detectorDyadicCount N)^2 * ∑ chi : DirichletCharacter ℂ q, (P' chi).card := by
    have h := hcard0.trans (Nat.mul_le_mul_left _ hcommon)
    simpa [P',pow_two,Nat.mul_assoc] using h
  have hcardR : (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) ≤
      (detectorDyadicCount N : ℝ)^2 * ∑ chi : DirichletCharacter ℂ q, ((P' chi).card : ℝ) := by
    exact_mod_cast hcard1
  have hfirst := mul_le_mul_of_nonneg_right hcardR
    (sq_nonneg (V/(4*fullStripFourierMass*detectorDyadicCount N)))
  have hsecond := mul_le_mul_of_nonneg_left hbudget (sq_nonneg (detectorDyadicCount N : ℝ))
  have hpow : Real.rpow (2^(i : ℕ) : ℕ) (2*(1-sigma)) ≤ Real.rpow N (2*(1-sigma)) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hDN) (by linarith)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0<U) hUN)
  have hDpos : 0 < ((2^(i : ℕ) : ℕ) : ℝ) := by positivity
  have hharm : (harmonic (2*2^(i : ℕ)) : ℝ) ≤ 1+Real.log (2*(N : ℝ)) := by
    apply (harmonic_le_one_add_log (2*2^(i : ℕ))).trans
    apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.mul_le_mul_left 2 hDN
  have hharm0 : 0 ≤ (harmonic (2*2^(i : ℕ)) : ℝ) := by
    unfold harmonic
    positivity
  have hterminal := mul_le_mul hpow (pow_le_pow_left₀ hharm0 hharm 4)
    (by positivity) (Real.rpow_nonneg hNpos.le _)
  have hterminal' := mul_le_mul_of_nonneg_left hterminal
    (show 0 ≤ (detectorDyadicCount N : ℝ)^2 * 3*(2+8*Real.pi) by positivity)
  nlinarith only [hfirst,hsecond,hterminal']
end
end MAPMontgomeryFullScaleTypeIFamily
#print axioms MAPMontgomeryFullScaleTypeIFamily.fullScale_typeI_family_budget
