import MRTDynamicD12SmoothSampled
import Mathlib.Analysis.MeanInequalitiesPow
namespace MRTDynamicD12SmoothSampled
open scoped BigOperators
noncomputable section

theorem weighted_fourth {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hf : ∀ i ∈ S, 0 ≤ f i)
    (hW : 0 < ∑ i ∈ S, w i) :
    (∑ i ∈ S, w i * f i)^4 ≤ (∑ i ∈ S, w i)^3 *
      ∑ i ∈ S, w i * f i^4 := by
  let W := ∑ i ∈ S, w i
  have h := Real.pow_arith_mean_le_arith_mean_pow S (fun i ↦ w i / W) f
    (fun i hi ↦ div_nonneg (hw i hi) hW.le)
    (by rw [← Finset.sum_div]; exact div_self hW.ne') hf 4
  have heq (g : ι → ℝ) : (∑ i ∈ S, w i / W * g i) =
      (∑ i ∈ S, w i * g i) / W := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq f, heq (fun i ↦ f i^4), div_pow] at h
  have hh := (div_le_iff₀ (pow_pos hW 4)).mp h
  have hh2 : ((∑ i ∈ S, w i * f i^4) / W) * W^4 =
      W^3 * (∑ i ∈ S, w i * f i^4) := by field_simp
  rw [hh2] at hh
  exact hh

theorem two_add_sum_weighted_fourth {ι : Type*} (S : Finset ι)
    (A B a b : ℝ) (w f : ι → ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hf : ∀ i ∈ S, 0 ≤ f i)
    (hW : 0 < A + B + ∑ i ∈ S, w i) :
    (A*a + B*b + ∑ i ∈ S, w i*f i)^4 ≤
      (A+B+∑ i ∈ S, w i)^3 * (A*a^4+B*b^4+∑ i ∈ S, w i*f i^4) := by
  let ww : Fin 2 ⊕ ι → ℝ := Sum.elim (fun j ↦ if j = 0 then A else B) w
  let ff : Fin 2 ⊕ ι → ℝ := Sum.elim (fun j ↦ if j = 0 then a else b) f
  have h := weighted_fourth ((Finset.univ : Finset (Fin 2)).disjSum S) ww ff
  have hh := h
    (by intro i hi; cases i with
        | inl j => fin_cases j <;> simp [ww, hA, hB]
        | inr i => exact hw i (by simpa using hi))
    (by intro i hi; cases i with
        | inl j => fin_cases j <;> simp [ff, ha, hb]
        | inr i => exact hf i (by simpa using hi))
    (by simpa [ww, Finset.sum_disjSum, Fin.sum_univ_two] using hW)
  simpa [ww, ff, Finset.sum_disjSum, Fin.sum_univ_two] using hh
open MAPMRTLemma211AllCharacterSource

theorem smoothLogInterval_fourth_le_weighted_prefixes {q L U : ℕ}
    (hL : 1 ≤ L) (hLU : L < U) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖smoothLogIntervalPolynomial q L U chi t‖^4 ≤
      (2 * Real.log (U : ℝ))^3 *
        (Real.log (U : ℝ) * ‖criticalPrefixPolynomial q U chi t‖^4 +
         Real.log ((L+1 : ℕ) : ℝ) * ‖criticalPrefixPolynomial q L chi t‖^4 +
         ∑ n ∈ Finset.Ioc L (U-1),
           (Real.log ((n+1 : ℕ) : ℝ) - Real.log (n : ℝ)) *
             ‖criticalPrefixPolynomial q n chi t‖^4) := by
  let A := Real.log (U : ℝ)
  let B := Real.log ((L+1 : ℕ) : ℝ)
  let w := fun n : ℕ ↦ Real.log ((n+1 : ℕ) : ℝ) - Real.log (n : ℝ)
  let f := fun n : ℕ ↦ ‖criticalPrefixPolynomial q n chi t‖
  have hA : 0 < A := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hB : 0 ≤ B := Real.log_nonneg (by exact_mod_cast (show 1 ≤ L+1 by omega))
  have hw : ∀ n ∈ Finset.Ioc L (U-1), 0 ≤ w n := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    apply sub_nonneg.mpr
    exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast Nat.le_succ n)
  have hW : A+B+(∑ n ∈ Finset.Ioc L (U-1), w n) = 2*A := by
    have hv := logAbelVariation_eq hLU
    unfold logAbelVariation at hv
    rw [abs_of_nonneg hA.le, abs_of_nonneg hB] at hv
    have heq : (∑ n ∈ Finset.Ioc L (U-1), |w n|) =
        ∑ n ∈ Finset.Ioc L (U-1), w n :=
      Finset.sum_congr rfl (fun n hn ↦ abs_of_nonneg (hw n hn))
    change A+B+(∑ n ∈ Finset.Ioc L (U-1), |w n|) = 2*A at hv
    rw [heq] at hv
    exact hv
  have hnorm : ‖smoothLogIntervalPolynomial q L U chi t‖ ≤
      A*f U+B*f L+∑ n ∈ Finset.Ioc L (U-1), w n*f n := by
    rw [smoothLogInterval_eq_abel hLU]
    calc
      _ ≤ (‖(A : ℂ) * criticalPrefixPolynomial q U chi t‖ +
            ‖(B : ℂ) * criticalPrefixPolynomial q L chi t‖) +
          ∑ n ∈ Finset.Ioc L (U-1),
            ‖((w n) : ℂ) * criticalPrefixPolynomial q n chi t‖ := by
        apply (norm_sub_le _ _).trans
        apply add_le_add (norm_sub_le _ _)
        simpa [w, Complex.ofReal_sub] using
          (norm_sum_le (Finset.Ioc L (U-1)) (fun n ↦
            ((w n : ℝ) : ℂ) * criticalPrefixPolynomial q n chi t))
      _ = _ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hA.le, abs_of_nonneg hB]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        rw [abs_of_nonneg (hw n hn)]
  have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 4
  have hj := two_add_sum_weighted_fourth (Finset.Ioc L (U-1)) A B (f U) (f L) w f
    hA.le hB (norm_nonneg _) (norm_nonneg _) hw (fun n hn ↦ norm_nonneg _)
    (by rw [hW]; positivity)
  rw [hW] at hj
  exact hp.trans hj

open MAPMRTProposition61TypeD1FirstInequality
open MAPMRTLemma210OrthogonalityReduction

theorem smoothLogInterval_sampled_le_weighted_prefixes {q L U : ℕ} [NeZero q]
    (hL : 1 ≤ L) (hLU : L < U)
    (S : Finset (DirichletCharacter ℂ q × ℝ))
    (left right : DirichletCharacter ℂ q × ℝ → ℝ)
    (hlen : ∀ z ∈ S, left z ≤ right z) :
    bhpSampledPieceMass (fun chi t ↦ ‖smoothLogIntervalPolynomial q L U chi t‖)
      S left right ≤
      (2 * Real.log (U : ℝ))^3 *
        (Real.log (U : ℝ) * bhpSampledPieceMass
          (fun chi t ↦ ‖criticalPrefixPolynomial q U chi t‖) S left right +
         Real.log ((L+1 : ℕ) : ℝ) * bhpSampledPieceMass
          (fun chi t ↦ ‖criticalPrefixPolynomial q L chi t‖) S left right +
         ∑ n ∈ Finset.Ioc L (U-1),
           (Real.log ((n+1 : ℕ) : ℝ) - Real.log (n : ℝ)) *
             bhpSampledPieceMass (fun chi t ↦ ‖criticalPrefixPolynomial q n chi t‖)
               S left right) := by
  let w := fun n : ℕ ↦ Real.log ((n+1 : ℕ) : ℝ) - Real.log (n : ℝ)
  let F := fun (J : ℕ) (chi : DirichletCharacter ℂ q) (t : ℝ) ↦
    ‖criticalPrefixPolynomial q J chi t‖^4
  have hc (J : ℕ) (chi : DirichletCharacter ℂ q) : Continuous (F J chi) := by
    unfold F criticalPrefixPolynomial twistedFinitePolynomial twistedPhase
    fun_prop
  have hd (chi : DirichletCharacter ℂ q) :
      Continuous (fun t ↦ ‖smoothLogIntervalPolynomial q L U chi t‖^4) := by
    unfold smoothLogIntervalPolynomial MAPMRTProposition61TypeD1Factorization.normalizedTwistedTerm
      MixedMeanFrontend.mellinPhase
    fun_prop
  have hpoint (z : DirichletCharacter ℂ q × ℝ) (hz : z ∈ S) :
      (∫ t in left z..right z, ‖smoothLogIntervalPolynomial q L U z.1 t‖^4) ≤
      (2 * Real.log (U : ℝ))^3 *
        (Real.log (U : ℝ) * (∫ t in left z..right z, F U z.1 t) +
         Real.log ((L+1 : ℕ) : ℝ) * (∫ t in left z..right z, F L z.1 t) +
         ∑ n ∈ Finset.Ioc L (U-1), w n * (∫ t in left z..right z, F n z.1 t)) := by
    calc
      _ ≤ ∫ t in left z..right z, (2 * Real.log (U : ℝ))^3 *
          (Real.log (U : ℝ) * F U z.1 t + Real.log ((L+1 : ℕ) : ℝ) * F L z.1 t +
           ∑ n ∈ Finset.Ioc L (U-1), w n * F n z.1 t) := by
        apply intervalIntegral.integral_mono_on (hlen z hz) ((hd z.1).intervalIntegrable _ _)
        · apply Continuous.intervalIntegrable
          exact continuous_const.mul (((continuous_const.mul (hc U z.1)).add
            (continuous_const.mul (hc L z.1))).add
              (continuous_finsetSum _ (fun n hn ↦ continuous_const.mul (hc n z.1))))
        · intro t ht
          exact smoothLogInterval_fourth_le_weighted_prefixes hL hLU z.1 t
      _ = _ := by
        have hIU : IntervalIntegrable (fun t ↦ Real.log (U : ℝ) * F U z.1 t)
            MeasureTheory.volume (left z) (right z) :=
          (continuous_const.mul (hc U z.1)).intervalIntegrable _ _
        have hIL : IntervalIntegrable (fun t ↦ Real.log ((L+1 : ℕ) : ℝ) * F L z.1 t)
            MeasureTheory.volume (left z) (right z) :=
          (continuous_const.mul (hc L z.1)).intervalIntegrable _ _
        have hIN (n : ℕ) : IntervalIntegrable (fun t ↦ w n * F n z.1 t)
            MeasureTheory.volume (left z) (right z) :=
          (continuous_const.mul (hc n z.1)).intervalIntegrable _ _
        have hIS : IntervalIntegrable (fun t ↦ ∑ n ∈ Finset.Ioc L (U-1), w n * F n z.1 t)
            MeasureTheory.volume (left z) (right z) :=
          (continuous_finsetSum _ (fun n hn ↦ continuous_const.mul (hc n z.1))).intervalIntegrable _ _
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add (hIU.add hIL) hIS,
          intervalIntegral.integral_add hIU hIL,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_finsetSum (fun n hn ↦ hIN n)]
        simp_rw [intervalIntegral.integral_const_mul]
  unfold bhpSampledPieceMass
  calc
    _ ≤ ∑ z ∈ S, (2 * Real.log (U : ℝ))^3 *
        (Real.log (U : ℝ) * (∫ t in left z..right z, F U z.1 t) +
         Real.log ((L+1 : ℕ) : ℝ) * (∫ t in left z..right z, F L z.1 t) +
         ∑ n ∈ Finset.Ioc L (U-1), w n * (∫ t in left z..right z, F n z.1 t)) :=
      Finset.sum_le_sum hpoint
    _ = _ := by
      rw [← Finset.mul_sum]
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      rfl

end
end MRTDynamicD12SmoothSampled
#print axioms MRTDynamicD12SmoothSampled.smoothLogInterval_fourth_le_weighted_prefixes
#print axioms MRTDynamicD12SmoothSampled.smoothLogInterval_sampled_le_weighted_prefixes
#print axioms MRTDynamicD12SmoothSampled.smoothInterval_sampled_budget
