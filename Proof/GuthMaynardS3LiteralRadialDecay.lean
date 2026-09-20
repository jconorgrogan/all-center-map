import GuthMaynardS3LiteralRadial

/-!
# Uniform radial Fourier decay in Proposition 7.1

The derivative constants below depend only on the fixed Section 3 cutoff
and the derivative order. They are uniform in both ratio variables on
[1/2,2], in W, and in every frequency and ambient parameter.
-/

namespace GuthMaynardS3LiteralRadialDecay

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open GuthMaynardS3LiteralRadial GuthMaynardSectionThreeCutoff
open GuthMaynardSectionThreeCutoffDerivativeBudget GuthMaynardLemma43FourierIBP

noncomputable section

def leibnizBudget (A B : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (q+1),(q.choose i : ℝ)*A i*B (q-i)

theorem norm_iteratedDeriv_mul_le {f g : ℝ → ℂ} {A B : ℕ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hA : ∀ q x,‖iteratedDeriv q f x‖ ≤ A q)
    (hB : ∀ q x,‖iteratedDeriv q g x‖ ≤ B q) (q : ℕ) (x : ℝ) :
    ‖iteratedDeriv q (f*g) x‖ ≤ leibnizBudget A B q := by
  rw [iteratedDeriv_mul
    (hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
    (hg.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  simp only [norm_mul,Complex.norm_natCast]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hA i x) (Nat.cast_nonneg _)) (hB (q-i) x)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hA i x)))

def radialBase (r : ℝ) : ℂ := (r : ℂ)^2*sectionThreeCutoff r

theorem radialBase_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialBase :=
  (Complex.ofRealCLM.contDiff.pow 2).mul sectionThreeCutoff_contDiff

theorem radialBase_hasCompactSupport : HasCompactSupport radialBase := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
  intro r hr
  simp [radialBase,sectionThreeCutoff_supported r hr]

def radialBaseSchwartz : 𝓢(ℝ,ℂ) :=
  radialBase_hasCompactSupport.toSchwartzMap radialBase_contDiff

def radialBaseDerivativeSup (q : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 (schwartzIteratedDerivative q radialBaseSchwartz)

theorem radialBaseDerivative_le (q : ℕ) (r : ℝ) :
    ‖iteratedDeriv q radialBase r‖ ≤ radialBaseDerivativeSup q := by
  have h := SchwartzMap.norm_le_seminorm ℂ (schwartzIteratedDerivative q radialBaseSchwartz) r
  rw [schwartzIteratedDerivative_apply] at h
  exact h

def scaledCutoffDerivativeSup (q : ℕ) : ℝ := 2^q*cutoffDerivativeSup q

theorem scaledCutoffDerivative_le {v : ℝ} (hv : |v| ≤ 2) (q : ℕ) (r : ℝ) :
    ‖iteratedDeriv q (fun x => sectionThreeCutoff (v*x)) r‖ ≤
      scaledCutoffDerivativeSup q := by
  rw [iteratedDeriv_comp_const_smul
    (sectionThreeCutoff_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) v]
  simp only [norm_smul,Real.norm_eq_abs,abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg v) hv q)
    (norm_iteratedDeriv_sectionThreeCutoff_le q (v*r)) (norm_nonneg _) (by positivity)

def radialDerivativeBudget (q : ℕ) : ℝ :=
  leibnizBudget (leibnizBudget radialBaseDerivativeSup scaledCutoffDerivativeSup)
    scaledCutoffDerivativeSup q

theorem radialWeight_contDiff (v1 v2 : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun r => radialWeight r v1 v2) := by
  unfold radialWeight
  exact (((Complex.ofRealCLM.contDiff.pow 2).mul sectionThreeCutoff_contDiff).mul
    (sectionThreeCutoff_contDiff.comp (contDiff_id.mul contDiff_const))).mul
      (sectionThreeCutoff_contDiff.comp (contDiff_id.mul contDiff_const))

theorem radialWeight_derivative_le {v1 v2 : ℝ} (h1 : |v1| ≤ 2) (h2 : |v2| ≤ 2)
    (q : ℕ) (r : ℝ) :
    ‖iteratedDeriv q (fun x => radialWeight x v1 v2) r‖ ≤ radialDerivativeBudget q := by
  have hc1 : ContDiff ℝ (⊤ : ℕ∞) (fun x => sectionThreeCutoff (v1*x)) :=
    sectionThreeCutoff_contDiff.comp (contDiff_const.mul contDiff_id)
  have hc2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => sectionThreeCutoff (v2*x)) :=
    sectionThreeCutoff_contDiff.comp (contDiff_const.mul contDiff_id)
  have hh := norm_iteratedDeriv_mul_le (radialBase_contDiff.mul hc1) hc2
    (norm_iteratedDeriv_mul_le radialBase_contDiff hc1 radialBaseDerivative_le
      (scaledCutoffDerivative_le h1)) (scaledCutoffDerivative_le h2) q r
  simpa only [Pi.mul_apply,radialBase,radialWeight,mul_comm] using hh

theorem radialWeight_hasCompactSupport (v1 v2 : ℝ) :
    HasCompactSupport (fun r => radialWeight r v1 v2) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
  intro r hr
  simp [radialWeight,sectionThreeCutoff_supported r hr]

def radialWeightSchwartz (v1 v2 : ℝ) : 𝓢(ℝ,ℂ) :=
  (radialWeight_hasCompactSupport v1 v2).toSchwartzMap (radialWeight_contDiff v1 v2)

theorem radialWeight_derivative_zero (v1 v2 : ℝ) (q : ℕ) {r : ℝ}
    (hr : r ∉ Set.Icc (1 : ℝ) 2) :
    iteratedDeriv q (fun x => radialWeight x v1 v2) r = 0 := by
  have heq : (fun x => radialWeight x v1 v2) =ᶠ[nhds r] fun _ => (0 : ℂ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hr] with x hx
    simp [radialWeight,sectionThreeCutoff_supported x hx]
  rw [heq.iteratedDeriv_eq q,iteratedDeriv_const]
  split <;> simp_all

theorem integral_radialWeight_derivative_le {v1 v2 : ℝ}
    (h1 : |v1| ≤ 2) (h2 : |v2| ≤ 2) (q : ℕ) :
    (∫ r : ℝ,‖iteratedDeriv q (fun x => radialWeight x v1 v2) r‖) ≤
      radialDerivativeBudget q := by
  have hi : Integrable (fun r => ‖iteratedDeriv q (fun x => radialWeight x v1 v2) r‖) := by
    have hh := ((schwartzIteratedDerivative q (radialWeightSchwartz v1 v2)).integrable (μ := (volume : Measure ℝ))).norm
    exact hh.congr (Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [schwartzIteratedDerivative_apply]
      rfl)
  have heq : (∫ r : ℝ,‖iteratedDeriv q (fun x => radialWeight x v1 v2) r‖) =
      ∫ r : ℝ in Set.Icc (1 : ℝ) 2,‖iteratedDeriv q (fun x => radialWeight x v1 v2) r‖ := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ Set.Icc (1 : ℝ) 2
    · simp [hr]
    · simp [hr,radialWeight_derivative_zero v1 v2 q hr]
  rw [heq]
  calc
    _ ≤ ∫ _ : ℝ in Set.Icc (1 : ℝ) 2,radialDerivativeBudget q := by
      apply integral_mono_ae hi.integrableOn
        (integrableOn_const (hs := by simp [Real.volume_Icc]))
      exact Filter.Eventually.of_forall (fun r => radialWeight_derivative_le h1 h2 q r)
    _ = _ := by rw [setIntegral_const]; norm_num [Real.volume_Icc]

/-- Arbitrary-order radial decay, uniform in the two source ratio variables. -/
theorem radialWeight_fourier_decay {v1 v2 xi : ℝ}
    (h1 : |v1| ≤ 2) (h2 : |v2| ≤ 2) (q : ℕ) (hxi : xi ≠ 0) :
    ‖FourierTransform.fourier (fun r => radialWeight r v1 v2) xi‖ ≤
      radialDerivativeBudget q / |xi|^q := by
  have hh := norm_fourier_le_derivativeBudget_div_absPow (radialWeightSchwartz v1 v2) q hxi
    (integral_radialWeight_derivative_le h1 h2 q)
  simpa only [SchwartzMap.fourier_coe] using hh

end
end GuthMaynardS3LiteralRadialDecay

#print axioms GuthMaynardS3LiteralRadialDecay.radialWeight_fourier_decay
