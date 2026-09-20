import GuthMaynardLemma117Convolution

/-!
# Cubic local constancy required by Guth--Maynard Lemma 11.8

The printed Lemma 11.7 is linear, but Lemma 11.8 immediately uses its cubic
analogue.  The missing bridge is to apply the same Fourier smoothing proof to
`K^2 * conj K`, a multiplicity-preserving weighted trigonometric polynomial
whose norm is `|K|^3` and whose frequency support has length `3T`.
-/

open scoped BigOperators FourierTransform ComplexConjugate SchwartzMap
open MeasureTheory

namespace GuthMaynardLemma117

open FourierRealPartRemoval GuthMaynardJIteration
open GuthMaynardRatioKernelIdentity

noncomputable section

def weightedPointMassFourierKernel {ι : Type*}
    (P : Finset ι) (x : ι → ℝ) (a : ι → ℂ) (tau : ℝ) : ℂ :=
  ∑ i ∈ P, a i *
    Complex.exp (-((2 * Real.pi * x i * tau : ℝ) : ℂ) * Complex.I)

def weightedCoefficientMass {ι : Type*}
    (P : Finset ι) (a : ι → ℂ) : ℝ :=
  ∑ i ∈ P, ‖a i‖

theorem norm_weightedPointMassFourierKernel_le_mass
    {ι : Type*} (P : Finset ι) (x : ι → ℝ) (a : ι → ℂ) (tau : ℝ) :
    ‖weightedPointMassFourierKernel P x a tau‖ ≤
      weightedCoefficientMass P a := by
  unfold weightedPointMassFourierKernel weightedCoefficientMass
  calc
    ‖∑ i ∈ P, a i *
        Complex.exp (-((2 * Real.pi * x i * tau : ℝ) : ℂ) * Complex.I)‖ ≤
      ∑ i ∈ P, ‖a i‖ := by
        apply norm_sum_le_of_le
        intro i hi
        rw [norm_mul, Complex.norm_exp]
        simp
    _ = _ := rfl

theorem weightedPointMassFourierKernel_eq_scaled_convolution
    {ι : Type*} (P : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
    {x0 L tau : ℝ} (hL : 0 < L)
    (hinterval : ∀ i ∈ P, x0 ≤ x i ∧ x i ≤ x0 + L) :
    weightedPointMassFourierKernel P x a tau =
      ∫ xi : ℝ,
        (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
          intervalTranslationPhase x0 L xi *
          weightedPointMassFourierKernel P x a (tau-xi/L) := by
  let psi : 𝓢(ℝ, ℂ) := sourceBumpSchwartz 1 zero_lt_one
  let b : ι → ℂ := fun i => a i *
    Complex.exp (-((2 * Real.pi * x i * tau : ℝ) : ℂ) * Complex.I)
  let u : ι → ℝ := fun i => (x i-x0)/L
  have hu : ∀ i ∈ P, |u i| ≤ 1 := by
    intro i hi
    have h := hinterval i hi
    have hu0 : 0 ≤ u i := div_nonneg (sub_nonneg.mpr h.1) hL.le
    have hu1 : u i ≤ 1 := (div_le_one hL).2 (by linarith)
    rw [abs_of_nonneg hu0]
    exact hu1
  have hpsi : ∀ i ∈ P, psi (u i) = 1 := by
    intro i hi
    change (sourceBump 1 zero_lt_one (u i) : ℂ) = 1
    rw [sourceBump_eq_one_of_abs_le 1 zero_lt_one (hu i hi)]
    norm_num
  have hfourier := finite_fourier_real_part_removal P b u psi
  calc
    weightedPointMassFourierKernel P x a tau =
        ∑ i ∈ P, b i * psi (u i) := by
      unfold weightedPointMassFourierKernel b
      apply Finset.sum_congr rfl
      intro i hi
      rw [hpsi i hi]
      simp
    _ = ∫ xi : ℝ, (𝓕 psi : 𝓢(ℝ,ℂ)) xi *
        ∑ i ∈ P, b i * positiveFourierPhase (u i) xi := hfourier
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with xi
      dsimp only [psi]
      calc
        (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
            ∑ i ∈ P, b i * positiveFourierPhase (u i) xi =
          (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
            (intervalTranslationPhase x0 L xi *
              weightedPointMassFourierKernel P x a (tau-xi/L)) := by
          congr 1
          unfold weightedPointMassFourierKernel intervalTranslationPhase
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          dsimp only [b, u, positiveFourierPhase]
          calc
            a i * Complex.exp (-((2 * Real.pi * x i * tau : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((2 * Real.pi * ((x i-x0)/L) * xi : ℝ) : ℂ) * Complex.I) =
              a i * Complex.exp
                (-((2 * Real.pi * x i * tau : ℝ) : ℂ) * Complex.I +
                  (((2 * Real.pi * ((x i-x0)/L) * xi : ℝ) : ℂ) * Complex.I)) := by
                rw [Complex.exp_add]
                ring
            _ = Complex.exp (-((2 * Real.pi * x0 * xi / L : ℝ) : ℂ) * Complex.I) *
                (a i * Complex.exp
                  (-((2 * Real.pi * x i * (tau-xi/L) : ℝ) : ℂ) * Complex.I)) := by
              have hexp :
                  -((2 * Real.pi * x i * tau : ℝ) : ℂ) * Complex.I +
                    (((2 * Real.pi * ((x i-x0)/L) * xi : ℝ) : ℂ) * Complex.I) =
                  -((2 * Real.pi * x0 * xi / L : ℝ) : ℂ) * Complex.I +
                    (-((2 * Real.pi * x i * (tau-xi/L) : ℝ) : ℂ) * Complex.I) := by
                push_cast
                field_simp [hL.ne']
                ring
              rw [hexp, Complex.exp_add]
              ring
        _ = _ := by ring
  all_goals rfl

set_option maxHeartbeats 900000 in
theorem norm_weightedPointMassFourierKernel_le_central_add_tail
    {ι : Type*} (P : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
    {x0 L tau A : ℝ} (hL : 0 < L)
    (hinterval : ∀ i ∈ P, x0 ≤ x i ∧ x i ≤ x0 + L) :
    ‖weightedPointMassFourierKernel P x a tau‖ ≤
      (∫ xi in Set.Icc (-A) A,
        ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
          ‖weightedPointMassFourierKernel P x a (tau-xi/L)‖) +
      weightedCoefficientMass P a *
        ∫ xi in (Set.Icc (-A) A)ᶜ,
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ := by
  rw [weightedPointMassFourierKernel_eq_scaled_convolution P x a hL hinterval]
  let f : ℝ → ℝ := fun xi =>
    ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
      ‖weightedPointMassFourierKernel P x a (tau-xi/L)‖
  let g : ℝ → ℝ := fun xi =>
    ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
      weightedCoefficientMass P a
  have hfmeas : AEStronglyMeasurable f := by
    apply Continuous.aestronglyMeasurable
    dsimp [f, weightedPointMassFourierKernel]
    fun_prop
  have hg : Integrable g :=
    (𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)).integrable.norm.mul_const _
  have hfg : ∀ xi, f xi ≤ g xi := by
    intro xi
    exact mul_le_mul_of_nonneg_left
      (norm_weightedPointMassFourierKernel_le_mass P x a _) (norm_nonneg _)
  have hf : Integrable f := hg.mono' hfmeas (Filter.Eventually.of_forall fun xi => by
    have hf0 : 0 ≤ f xi := by dsimp [f]; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hf0] using hfg xi)
  have hnorm :
      ‖∫ xi : ℝ,
        (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
          intervalTranslationPhase x0 L xi *
          weightedPointMassFourierKernel P x a (tau-xi/L)‖ ≤
        ∫ xi : ℝ, f xi := by
    apply MeasureTheory.norm_integral_le_of_norm_le hf
    filter_upwards with xi
    change ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
      intervalTranslationPhase x0 L xi *
      weightedPointMassFourierKernel P x a (tau-xi/L)‖ ≤ f xi
    dsimp only [f]
    rw [norm_mul, norm_mul, norm_intervalTranslationPhase]
    simp
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Icc (-A) A) measurableSet_Icc hf
  have htail : (∫ xi in (Set.Icc (-A) A)ᶜ, f xi) ≤
      weightedCoefficientMass P a *
        ∫ xi in (Set.Icc (-A) A)ᶜ,
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ := by
    calc
      (∫ xi in (Set.Icc (-A) A)ᶜ, f xi) ≤
          ∫ xi in (Set.Icc (-A) A)ᶜ, g xi := by
        apply MeasureTheory.setIntegral_mono_on hf.integrableOn hg.integrableOn
          measurableSet_Icc.compl
        intro xi hxi
        exact hfg xi
      _ = _ := by
        dsimp [g]
        rw [MeasureTheory.integral_mul_const]
        ring
  rw [← hsplit] at hnorm
  exact hnorm.trans (add_le_add le_rfl htail)

/-- The multiplicity-preserving cubic frequency field. -/
def cubicFrequency (z : ℝ × (ℝ × ℝ)) : ℝ := z.1+z.2.1-z.2.2

def cubicIndexSet (W : Finset ℝ) : Finset (ℝ × (ℝ × ℝ)) :=
  W.product (W.product W)

theorem weightedCubicKernel_eq_mul_conj_mul
    (W : Finset ℝ) (tau : ℝ) :
    weightedPointMassFourierKernel (cubicIndexSet W) cubicFrequency
        (fun _ => (1:ℂ)) tau =
      pointMassFourierKernel W tau *
        star (pointMassFourierKernel W tau) *
          pointMassFourierKernel W tau := by
  unfold weightedPointMassFourierKernel cubicIndexSet cubicFrequency
  simp only [one_mul]
  change (∑ z ∈ W ×ˢ (W ×ˢ W),
      Complex.exp (-((2 * Real.pi * (z.1+z.2.1-z.2.2) * tau : ℝ) : ℂ) *
        Complex.I)) = _
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  have hstar :
      star (pointMassFourierKernel W tau) =
        ∑ t ∈ W, Complex.exp
          (((2 * Real.pi * t * tau : ℝ) : ℂ) * Complex.I) := by
    unfold pointMassFourierKernel
    change (starRingEnd ℂ) (∑ t ∈ W,
      Complex.exp (-((2 * Real.pi * t * tau : ℝ) : ℂ) * Complex.I)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro t ht
    change star (Complex.exp
      (-((2 * Real.pi * t * tau : ℝ) : ℂ) * Complex.I)) = _
    rw [Complex.star_def, ← Complex.exp_conj]
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    ring
  rw [hstar]
  unfold pointMassFourierKernel
  have hprod :
      (∑ t1 ∈ W, Complex.exp
          (-((2 * Real.pi * t1 * tau : ℝ) : ℂ) * Complex.I)) *
        (∑ t2 ∈ W, Complex.exp
          (((2 * Real.pi * t2 * tau : ℝ) : ℂ) * Complex.I)) *
        (∑ t3 ∈ W, Complex.exp
          (-((2 * Real.pi * t3 * tau : ℝ) : ℂ) * Complex.I)) =
      ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        Complex.exp (-((2 * Real.pi * t1 * tau : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((2 * Real.pi * t2 * tau : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * t3 * tau : ℝ) : ℂ) * Complex.I) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t1 ht1
    apply Finset.sum_congr rfl
    intro t2 ht2
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t3 ht3
    ring
  rw [hprod]
  apply Finset.sum_congr rfl
  intro t1 ht1
  apply Finset.sum_congr rfl
  intro t2 ht2
  apply Finset.sum_congr rfl
  intro t3 ht3
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_weightedCubicKernel
    (W : Finset ℝ) (tau : ℝ) :
    ‖weightedPointMassFourierKernel (cubicIndexSet W) cubicFrequency
        (fun _ => (1:ℂ)) tau‖ = ‖pointMassFourierKernel W tau‖^3 := by
  rw [weightedCubicKernel_eq_mul_conj_mul, norm_mul, norm_mul, norm_star]
  ring

theorem cubicFrequency_mem_interval
    (W : Finset ℝ) {x0 T : ℝ}
    (hinterval : ∀ t ∈ W, x0 ≤ t ∧ t ≤ x0+T) :
    ∀ z ∈ cubicIndexSet W,
      x0-T ≤ cubicFrequency z ∧ cubicFrequency z ≤ (x0-T)+3*T := by
  intro z hz
  rcases Finset.mem_product.mp hz with ⟨hz1,hz23⟩
  rcases Finset.mem_product.mp hz23 with ⟨hz2,hz3⟩
  have h1 := hinterval z.1 hz1
  have h2 := hinterval z.2.1 hz2
  have h3 := hinterval z.2.2 hz3
  unfold cubicFrequency
  constructor <;> linarith

theorem weightedCoefficientMass_cubicIndex
    (W : Finset ℝ) :
    weightedCoefficientMass (cubicIndexSet W) (fun _ => (1:ℂ)) =
      (W.card : ℝ)^3 := by
  classical
  simp [weightedCoefficientMass, cubicIndexSet, Finset.card_product]
  ring

set_option maxHeartbeats 900000 in
/-- The cubic consequence silently used in the proof of Lemma 11.8.  Unlike
naively cubing the printed Lemma 11.7, this has only one factor of the
bandwidth `3T`; multiplicities are preserved by the triple index set. -/
theorem pointMassFourierKernel_cube_localConstancy_explicit
    (W : Finset ℝ) {x0 T tau A : ℝ} (k : ℕ)
    (hT : 0 < T) (hA : 0 < A)
    (hinterval : ∀ t ∈ W, x0 ≤ t ∧ t ≤ x0+T) :
    ‖pointMassFourierKernel W tau‖^3 ≤
      sourceBumpFourierConstant 1 zero_lt_one 0 * (3*T) *
        (∫ u in Set.Icc (tau-A/(3*T)) (tau+A/(3*T)),
          ‖pointMassFourierKernel W u‖^3) +
      (W.card : ℝ)^3 * (A^k)⁻¹ *
        (∫ xi : ℝ, |xi|^k *
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)) xi‖) := by
  have h3T : 0 < 3*T := by positivity
  have hraw := norm_weightedPointMassFourierKernel_le_central_add_tail
    (cubicIndexSet W) cubicFrequency (fun _ => (1:ℂ)) h3T
      (cubicFrequency_mem_interval W hinterval) (tau:=tau) (A:=A)
  simp_rw [norm_weightedCubicKernel] at hraw
  rw [weightedCoefficientMass_cubicIndex] at hraw
  have hfourier : ∀ xi : ℝ,
      ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)) xi‖ ≤
        sourceBumpFourierConstant 1 zero_lt_one 0 := by
    intro xi
    simpa using sourceBump_fourier_decay 1 zero_lt_one 0 xi
  have hcentral :
      (∫ xi in Set.Icc (-A) A,
        ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
          ‖pointMassFourierKernel W (tau-xi/(3*T))‖^3) ≤
      sourceBumpFourierConstant 1 zero_lt_one 0 * (3*T) *
        (∫ u in Set.Icc (tau-A/(3*T)) (tau+A/(3*T)),
          ‖pointMassFourierKernel W u‖^3) := by
    have hcont : Continuous (fun xi : ℝ =>
        sourceBumpFourierConstant 1 zero_lt_one 0 *
          ‖pointMassFourierKernel W (tau-xi/(3*T))‖^3) := by
      unfold pointMassFourierKernel
      fun_prop
    calc
      (∫ xi in Set.Icc (-A) A,
        ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
          ‖pointMassFourierKernel W (tau-xi/(3*T))‖^3) ≤
        ∫ xi in Set.Icc (-A) A,
          sourceBumpFourierConstant 1 zero_lt_one 0 *
            ‖pointMassFourierKernel W (tau-xi/(3*T))‖^3 := by
          apply MeasureTheory.setIntegral_mono_on
          · apply Integrable.integrableOn
            exact ((𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)).integrable.norm.mul_const
              ((W.card:ℝ)^3)).mono' (by
                apply Continuous.aestronglyMeasurable
                unfold pointMassFourierKernel
                fun_prop) (Filter.Eventually.of_forall fun xi => by
                  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                  have hk : ‖pointMassFourierKernel W (tau-xi/(3*T))‖ ≤
                      (W.card:ℝ) := by
                    unfold pointMassFourierKernel
                    calc
                      ‖∑ t ∈ W, Complex.exp
                        (-((2*Real.pi*t*(tau-xi/(3*T)):ℝ):ℂ)*Complex.I)‖ ≤
                          ∑ _t ∈ W, (1:ℝ) := by
                        apply norm_sum_le_of_le
                        intro t ht
                        have hn : ‖Complex.exp
                            (-((2*Real.pi*t*(tau-xi/(3*T)):ℝ):ℂ)*Complex.I)‖ = 1 := by
                          convert Complex.norm_exp_ofReal_mul_I
                            (-2*Real.pi*t*(tau-xi/(3*T))) using 1 <;> push_cast <;> ring
                        rw [hn]
                      _ = (W.card:ℝ) := by simp
                  have hp : ‖pointMassFourierKernel W (tau-xi/(3*T))‖^3 ≤
                      (W.card:ℝ)^3 := pow_le_pow_left₀ (norm_nonneg _) hk 3
                  exact mul_le_mul_of_nonneg_left hp (norm_nonneg _))
          · exact hcont.continuousOn.integrableOn_compact isCompact_Icc
          · exact measurableSet_Icc
          · intro xi hxi
            exact mul_le_mul_of_nonneg_right (hfourier xi) (by positivity)
      _ = sourceBumpFourierConstant 1 zero_lt_one 0 *
          (∫ xi in Set.Icc (-A) A,
            ‖pointMassFourierKernel W (tau-xi/(3*T))‖^3) := by
          rw [MeasureTheory.integral_const_mul]
      _ = _ := by
          rw [integral_Icc_tau_sub_div
            (fun u => ‖pointMassFourierKernel W u‖^3) h3T hA.le]
          ring
  have htail := sourceBump_fourier_compl_Icc_le k hA
  calc
    ‖pointMassFourierKernel W tau‖^3 ≤ _ := hraw
    _ ≤ sourceBumpFourierConstant 1 zero_lt_one 0 * (3*T) *
          (∫ u in Set.Icc (tau-A/(3*T)) (tau+A/(3*T)),
            ‖pointMassFourierKernel W u‖^3) +
        (W.card:ℝ)^3 * ((A^k)⁻¹ *
          ∫ xi : ℝ, |xi|^k *
            ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)) xi‖) := by
      exact add_le_add hcentral
        (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = _ := by ring

end
end GuthMaynardLemma117

#print axioms GuthMaynardLemma117.weightedPointMassFourierKernel_eq_scaled_convolution
#print axioms GuthMaynardLemma117.norm_weightedPointMassFourierKernel_le_central_add_tail
#print axioms GuthMaynardLemma117.weightedCubicKernel_eq_mul_conj_mul
#print axioms GuthMaynardLemma117.norm_weightedCubicKernel
#print axioms GuthMaynardLemma117.cubicFrequency_mem_interval
#print axioms GuthMaynardLemma117.weightedCoefficientMass_cubicIndex
#print axioms GuthMaynardLemma117.pointMassFourierKernel_cube_localConstancy_explicit
