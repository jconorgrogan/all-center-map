import MRTProposition51SmoothGallagher72

/-!
# Smooth Gallagher and duality weld for MRT equation (72)

This module turns the faithful-cutoff Plancherel identity into the literal
`beta ± 1/H` band estimate and constructs the normalized dual witness used
by the subsequent logarithmic change of variables.  There is no change of
cutoff between these steps.
-/

namespace MAPMRTProposition51SmoothDualityWeld

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51Source
open MAPMRTProposition51FirstAnalytic MAPMRTProposition51HardBranch
open MAPMRTFaithfulSmoothCutoff MAPMRTProposition51SmoothGallagher72
open MAPMRTProposition51Duality72

noncomputable section

/-- The Fourier lower bound for the faithful cutoff converts the exact smooth
Plancherel identity into the centered frequency-band estimate. -/
theorem smoothGallagher_band_le
    {X H beta : ℝ} (f : ℕ → ℂ) (hH : 0 < H) :
    (∫ xi in Icc (-(1 / H)) (1 / H),
      ‖exponentialSum X f (beta - xi)‖ ^ 2) ≤
      100 / H ^ 2 *
        ∫ x : ℝ, ‖smoothCoefficientField X H beta f x‖ ^ 2 := by
  have hfreq := memLp_two_smoothFrequencyProduct
    (X := X) (H := H) (beta := beta) f hH
  have hfreqInt : Integrable (fun xi : ℝ ↦
      ‖(H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
        exponentialSum X f (beta - xi)‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfreq.1).1 hfreq
  have hsumInt : IntegrableOn (fun xi : ℝ ↦
      ‖exponentialSum X f (beta - xi)‖ ^ 2)
      (Icc (-(1 / H)) (1 / H)) :=
    (((continuous_exponentialSum_real X f).comp (by fun_prop)).norm.pow 2)
      |>.integrableOn_Icc
  have hpoint : ∀ xi ∈ Icc (-(1 / H)) (1 / H),
      ‖exponentialSum X f (beta - xi)‖ ^ 2 ≤
        100 / H ^ 2 *
          ‖(H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
            exponentialSum X f (beta - xi)‖ ^ 2 := by
    intro xi hxi
    have hxiAbs : |xi| ≤ 1 / H := (abs_le).2 hxi
    have hscaled : |-H * xi| ≤ 1 := by
      rw [abs_mul, abs_neg, abs_of_pos hH]
      have := mul_le_mul_of_nonneg_left hxiAbs hH.le
      field_simp [hH.ne'] at this ⊢
      exact this
    have hk := faithfulCutoffFourierKernel_norm_lower hscaled
    have hHsq : 0 < H ^ 2 := sq_pos_of_pos hH
    have hs0 := sq_nonneg ‖exponentialSum X f (beta - xi)‖
    have hk2 : (1 / 100 : ℝ) ≤
        ‖cutoffFourierKernel faithfulCutoff (-H * xi)‖ ^ 2 := by
      nlinarith [sq_nonneg
        (‖cutoffFourierKernel faithfulCutoff (-H * xi)‖ - 1 / 10)]
    rw [norm_mul, norm_mul, mul_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
    have hmul := mul_le_mul_of_nonneg_right hk2 hs0
    calc
      ‖exponentialSum X f (beta - xi)‖ ^ 2 =
          (100 / H ^ 2) * ((H ^ 2 / 100) *
            ‖exponentialSum X f (beta - xi)‖ ^ 2) := by
              field_simp [hH.ne']
      _ ≤ (100 / H ^ 2) *
          (H ^ 2 * ‖cutoffFourierKernel faithfulCutoff (-H * xi)‖ ^ 2 *
            ‖exponentialSum X f (beta - xi)‖ ^ 2) := by
              gcongr
              nlinarith
      _ = 100 / H ^ 2 *
          ((H * ‖cutoffFourierKernel faithfulCutoff (-H * xi)‖) ^ 2 *
            ‖exponentialSum X f (beta - xi)‖ ^ 2) := by ring
  have hband :
      (∫ xi in Icc (-(1 / H)) (1 / H),
        ‖exponentialSum X f (beta - xi)‖ ^ 2) ≤
      100 / H ^ 2 *
        ∫ xi in Icc (-(1 / H)) (1 / H),
          ‖(H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
            exponentialSum X f (beta - xi)‖ ^ 2 := by
    calc
      _ ≤ ∫ xi in Icc (-(1 / H)) (1 / H),
          (100 / H ^ 2) *
            ‖(H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
              exponentialSum X f (beta - xi)‖ ^ 2 := by
        apply integral_mono_ae hsumInt
          (hfreqInt.integrableOn.const_mul (100 / H ^ 2))
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with xi hxi
        exact hpoint xi hxi
      _ = _ := by rw [integral_const_mul]
  have hrestrict :
      (∫ xi in Icc (-(1 / H)) (1 / H),
          ‖(H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
            exponentialSum X f (beta - xi)‖ ^ 2) ≤
        ∫ xi : ℝ,
          ‖(H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
            exponentialSum X f (beta - xi)‖ ^ 2 :=
    setIntegral_le_integral hfreqInt
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
  calc
    _ ≤ 100 / H ^ 2 *
        ∫ xi in Icc (-(1 / H)) (1 / H),
          ‖(H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
            exponentialSum X f (beta - xi)‖ ^ 2 := hband
    _ ≤ 100 / H ^ 2 *
        ∫ xi : ℝ,
          ‖(H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
            exponentialSum X f (beta - xi)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hrestrict (by positivity)
    _ = 100 / H ^ 2 *
        ∫ x : ℝ, ‖smoothCoefficientField X H beta f x‖ ^ 2 := by
      rw [smoothGallagher_plancherel_identity f hH]

/-- Literal equation-(72) arc bound, using the same smooth cutoff that enters
the logarithmic dual function. -/
theorem smoothGallagher_arc_le
    {X H beta : ℝ} (f : ℕ → ℂ) (hH : 0 < H) :
    (∫ theta in (beta - 1 / H)..(beta + 1 / H),
      ‖exponentialSum X f theta‖ ^ 2) ≤
      100 / H ^ 2 *
        ∫ x : ℝ, ‖smoothCoefficientField X H beta f x‖ ^ 2 := by
  let r : ℝ := 1 / H
  let F : ℝ → ℝ := fun theta ↦ ‖exponentialSum X f theta‖ ^ 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hneg := intervalIntegral.integral_comp_neg
    (f := fun u : ℝ ↦ F (beta + u)) (a := -r) (b := r)
  have hshift := intervalIntegral.integral_comp_add_right
    F beta (a := -r) (b := r)
  have harc :
      (∫ theta in (beta - r)..(beta + r), F theta) =
        ∫ xi in (-r)..r, F (beta - xi) := by
    calc
      (∫ theta in (beta - r)..(beta + r), F theta) =
          ∫ u in (-r)..r, F (u + beta) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          hshift.symm
      _ = ∫ u in (-r)..r, F (beta + u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        change F (u + beta) = F (beta + u)
        rw [add_comm]
      _ = ∫ xi in (-r)..r, F (beta - xi) := by
        simp only [sub_eq_add_neg]
        simpa using hneg.symm
  have hband := smoothGallagher_band_le
    (X := X) (H := H) (beta := beta) f hH
  change (∫ theta in (beta - r)..(beta + r), F theta) ≤ _
  rw [harc]
  have hset :
      (∫ xi in (-r)..r, F (beta - xi)) =
        ∫ xi in Icc (-r) r, F (beta - xi) := by
    symm
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  rw [hset]
  simpa [r, F] using hband

/-- In the Proposition-5.1 half range, the smooth field and hence its
normalized dual witness are supported inside the source interval
`[X/2,4X]`. -/
theorem smoothCoefficientField_eq_zero_off_sourceInterval
    {X H beta x : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hx : x ∉ Icc (X / 2) (4 * X)) :
    smoothCoefficientField X H beta f x = 0 := by
  unfold smoothCoefficientField
  apply Finset.sum_eq_zero
  intro n hn
  rw [smoothCoefficientAtom_eq_zero_off hH, mul_zero]
  intro hlocal
  have hnbox := Finset.mem_Ioc.mp hn
  have hnLower : X < (n : ℝ) :=
    (Nat.floor_lt hX.le).mp hnbox.1
  have hnFloor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by
    exact_mod_cast hnbox.2
  have hnUpper : (n : ℝ) ≤ 2 * X :=
    hnFloor.trans (Nat.floor_le (by positivity : 0 ≤ 2 * X))
  apply hx
  constructor
  · nlinarith [hlocal.1]
  · nlinarith [hlocal.2]

private theorem realPhaseTwist_eq_mul_additivePhase
    (beta : ℝ) (f : ℕ → ℂ) (n : ℕ) :
    realPhaseTwist beta f n = f n * additivePhase (beta * n) := by
  unfold realPhaseTwist additivePhase
  rw [fourier_coe_apply]
  congr 2
  push_cast
  ring

private theorem integrable_smoothAtom_mul
    {H : ℝ} (hH : 0 < H) (n : ℕ) {g : ℝ → ℂ}
    (hg : Integrable g) :
    Integrable (fun x : ℝ ↦ smoothCoefficientAtom H n x * g x) := by
  have hb : ∀ x : ℝ, ‖smoothCoefficientAtom H n x‖ ≤ 1 := by
    intro x
    unfold smoothCoefficientAtom
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_faithfulCutoff_le_one _
  have hi := hg.bdd_mul (continuous_smoothCoefficientAtom n).aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  exact hi.congr (by
    filter_upwards with x
    ring)

/-- The smooth spatial pairing is exactly the critical Dirichlet sum with the
logarithmic dual function from equation (74). -/
theorem smoothPairing_eq_criticalSum
    {X H beta : ℝ} (hX : 0 < X) (hH : 0 < H)
    (f : ℕ → ℂ) {g : ℝ → ℂ} (hg : Integrable g) :
    (∫ x : ℝ, smoothCoefficientField X H beta f x * g x) =
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        f n * (Real.sqrt n : ℂ)⁻¹ *
          logarithmicDualFunction X H beta faithfulCutoff g
            (Real.log n - Real.log X) := by
  have hpair :
      (∫ x : ℝ, smoothCoefficientField X H beta f x * g x) =
        ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          realPhaseTwist beta f n *
            ∫ x : ℝ, smoothCoefficientAtom H n x * g x := by
    unfold smoothCoefficientField
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul]
    · intro n hn
      simpa only [mul_assoc] using
        (integrable_smoothAtom_mul hH n hg).const_mul
          (realPhaseTwist beta f n)
  rw [hpair]
  apply Finset.sum_congr rfl
  intro n hn
  have hnLower : X < (n : ℝ) :=
    (Nat.floor_lt hX.le).mp (Finset.mem_Ioc.mp hn).1
  have hnOne : 1 ≤ n := by
    have hnPos : 0 < n := by exact_mod_cast (hX.trans hnLower)
    omega
  rw [criticalCoefficient_mul_logarithmicDualFunction
    hX faithfulCutoff g hnOne f]
  rw [realPhaseTwist_eq_mul_additivePhase]
  rfl

/-- Zero-assumption equation-(72) constructor.  It produces the actual
normalized source-supported dual function and bounds the Proposition-5.1 arc
by the critical Dirichlet sum which is subsequently split in equation (76).
The zero-energy case is handled explicitly with the zero witness. -/
theorem smoothEquation72_dual_witness
    {X H beta : ℝ} (f : ℕ → ℂ)
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2) :
    ∃ g : ℝ → ℂ,
      Integrable g ∧
      Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2) ∧
      (∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) ∧
      (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1 ∧
      (∫ theta in (beta - 1 / H)..(beta + 1 / H),
          ‖exponentialSum X f theta‖ ^ 2) ≤
        100 / H ^ 2 *
          ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
            f n * (Real.sqrt n : ℂ)⁻¹ *
              logarithmicDualFunction X H beta faithfulCutoff g
                (Real.log n - Real.log X)‖ ^ 2 := by
  let F : ℝ → ℂ := smoothCoefficientField X H beta f
  let E : ℝ := ∫ x : ℝ, ‖F x‖ ^ 2
  have hF : Integrable F := integrable_smoothCoefficientField f hH
  have hFLp : MemLp F 2 := memLp_two_smoothCoefficientField f hH
  have hF2 : Integrable (fun x : ℝ ↦ ‖F x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hFLp.1).1 hFLp
  have hE0 : 0 ≤ E := integral_nonneg fun _ ↦ sq_nonneg _
  by_cases hEpos : 0 < E
  · let g := normalizedDualWitness F
    obtain ⟨hg, hgLp, hgSupportF, hgNorm, hgPair⟩ :=
      normalizedDualWitness_spec hF hF2 hEpos
    have hg2 : Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hgLp.1).1 hgLp
    refine ⟨g, hg, hg2, ?_, hgNorm.le, ?_⟩
    · intro x hx
      exact hgSupportF x
        (smoothCoefficientField_eq_zero_off_sourceInterval
          hX hH hHalf hx)
    · have harc := smoothGallagher_arc_le
        (X := X) (H := H) (beta := beta) f hH
      have hcritical := smoothPairing_eq_criticalSum
        (X := X) (H := H) (beta := beta) hX hH f hg
      change _ ≤ 100 / H ^ 2 * E at harc
      calc
        _ ≤ 100 / H ^ 2 * E := harc
        _ = 100 / H ^ 2 * ‖∫ x : ℝ, F x * g x‖ ^ 2 := by
          rw [hgPair]
        _ = _ := by rw [hcritical]
  · have hEzero : E = 0 := le_antisymm (le_of_not_gt hEpos) hE0
    refine ⟨fun _ ↦ 0, MeasureTheory.integrable_zero ℝ ℂ volume, ?_, ?_, ?_, ?_⟩
    · simpa using (MeasureTheory.integrable_zero ℝ ℝ volume)
    · intro x hx
      rfl
    · simp
    · have harc := smoothGallagher_arc_le
        (X := X) (H := H) (beta := beta) f hH
      change _ ≤ 100 / H ^ 2 * E at harc
      have hcritical := smoothPairing_eq_criticalSum
        (X := X) (H := H) (beta := beta) hX hH f
          (MeasureTheory.integrable_zero ℝ ℂ volume)
      have hcritZero :
          (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
            f n * (Real.sqrt n : ℂ)⁻¹ *
              logarithmicDualFunction X H beta faithfulCutoff (fun _ ↦ 0)
                (Real.log n - Real.log X)) = 0 := by
        rw [← hcritical]
        simp
      rw [hEzero] at harc
      rw [hcritZero]
      simpa using harc

#print axioms smoothGallagher_band_le
#print axioms smoothGallagher_arc_le
#print axioms smoothCoefficientField_eq_zero_off_sourceInterval
#print axioms smoothPairing_eq_criticalSum
#print axioms smoothEquation72_dual_witness

end
end MAPMRTProposition51SmoothDualityWeld
