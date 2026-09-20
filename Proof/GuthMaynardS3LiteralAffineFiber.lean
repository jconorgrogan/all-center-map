import GuthMaynardS3LiteralProfile

/-!
# The concrete Cauchy--Schwarz fiber in Proposition 7.2

At width 1/(2B), the two ratio factors are dominated by the actual positive
profile (7.5) at c/v and c. The Jacobian v and both smoothing factors are
retained before using v ≤ 2. No scalar profile budget is assumed.
-/

namespace GuthMaynardS3LiteralAffineFiber

open MeasureTheory
open scoped BigOperators
open GuthMaynardS3LiteralProfile GuthMaynardRatioKernelIdentity GuthMaynardJIteration

noncomputable section

def affineFiberWindow (B c : ℝ) : Set ℝ :=
  Set.Icc (1/2 : ℝ) 2 ∩ {u : ℝ | |u-c| ≤ 1/(2*B)}

def affineFiberMass (B c v : ℝ) (W : Finset ℝ) : ℝ :=
  ∫ u : ℝ in affineFiberWindow B c,
    ‖ratioDirichletKernel W (u/v)‖*‖ratioDirichletKernel W u‖

set_option maxHeartbeats 900000 in
/-- Literal localized affine fiber estimate with a constructed smoothing
profile; the only assumptions are the legal geometric scales. -/
theorem affineFiberMass_le {B c v : ℝ} (hB : 0<B)
    (hv : v ∈ Set.Icc (1/2 : ℝ) 2) (W : Finset ℝ) :
    affineFiberMass B c v W  ≤  (2/B)*smoothedRatio B W (c/v)*smoothedRatio B W c := by
  have hvpos : 0<v := by linarith [hv.1]
  let E := affineFiberWindow B c
  have hEs : E ⊆ Set.Icc (1/2 : ℝ) 2 := fun u hu => hu.1
  have hEclosed : IsClosed E := isClosed_Icc.inter (isClosed_le (by fun_prop) continuous_const)
  have hEc : IsCompact E := isCompact_Icc.of_isClosed_subset hEclosed hEs
  have hEm : MeasurableSet E := hEclosed.measurableSet
  let a : ℝ → ℝ := E.indicator (fun u => ‖ratioDirichletKernel W (u/v)‖)
  let b : ℝ → ℝ := E.indicator (fun u => ‖ratioDirichletKernel W u‖)
  have haCont : ContinuousOn (fun u => ‖ratioDirichletKernel W (u/v)‖) E := by
    intro u hu
    have huPos : 0<u := by have := hu.1.1; linarith
    have hh : ContinuousAt (fun x : ℝ => ratioDirichletKernel W (x/v)) u :=
      (continuousAt_ratioDirichletKernel W (div_ne_zero huPos.ne' hvpos.ne')).comp
        (f := fun x : ℝ => x/v) (continuousAt_id.div_const v)
    exact hh.norm.continuousWithinAt
  have hbCont : ContinuousOn (fun u => ‖ratioDirichletKernel W u‖) E := by
    intro u hu
    have huPos : 0<u := by have := hu.1.1; linarith
    exact (continuousAt_ratioDirichletKernel W huPos.ne').norm.continuousWithinAt
  have haI : Integrable a := (haCont.integrableOn_compact (μ := volume) hEc).integrable_indicator hEm
  have hbI : Integrable b := (hbCont.integrableOn_compact (μ := volume) hEc).integrable_indicator hEm
  have haEq (u : ℝ) : a u ^2 = E.indicator (fun u => ‖ratioDirichletKernel W (u/v)‖^2) u := by
    by_cases hu : u∈E <;> simp [a,hu]
  have hbEq (u : ℝ) : b u ^2 = E.indicator (fun u => ‖ratioDirichletKernel W u‖^2) u := by
    by_cases hu : u∈E <;> simp [b,hu]
  have ha2 : Integrable (fun u => a u ^2) := by
    simp_rw [haEq]
    exact ((haCont.pow 2).integrableOn_compact (μ := volume) hEc).integrable_indicator hEm
  have hb2 : Integrable (fun u => b u ^2) := by
    simp_rw [hbEq]
    exact ((hbCont.pow 2).integrableOn_compact (μ := volume) hEc).integrable_indicator hEm
  have ha0 : ∀ u,0 ≤ a u := by intro u; exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) u
  have hb0 : ∀ u,0 ≤ b u := by intro u; exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) u
  have hcs := integral_mul_sq_le a b haI.aestronglyMeasurable hbI.aestronglyMeasurable ha2 hb2 ha0 hb0
  have hmass : (∫ u : ℝ,a u*b u)=affineFiberMass B c v W := by
    change (∫ u : ℝ,a u*b u) = ∫ u : ℝ in E,
      ‖ratioDirichletKernel W (u/v)‖*‖ratioDirichletKernel W u‖
    rw [← integral_indicator hEm]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u∈E <;> simp [a,b,hu,affineFiberMass,E]
  rw [hmass] at hcs
  have hfBound : ∀ u,|ratioProfile W u| ≤ (W.card : ℝ)^2 := by
    intro u
    rw [abs_of_nonneg (ratioProfile_nonneg W u)]
    exact ratioProfile_le_card_sq W u
  let k : ℝ → ℝ → ℝ := fun d u =>
    B*sourceBump 1 zero_lt_one (B*(d-u))*ratioProfile W u
  have hkI (d : ℝ) : Integrable (k d) :=
    integrable_affineSmoothing_section hB _ _ (sourceBump 1 zero_lt_one).integrable
      (ratioProfile_continuous W) (sq_nonneg _) hfBound d
  have hk0 (d u : ℝ) : 0 ≤ k d u := by
    exact mul_nonneg (mul_nonneg hB.le (sourceBump_nonneg _ _ _)) (ratioProfile_nonneg W u)
  have hkScale : Integrable (fun u => k (c/v) (u/v)) := by
    have hh := (hkI (c/v)).comp_mul_left' (inv_ne_zero hvpos.ne')
    simpa only [div_eq_mul_inv,mul_comm] using hh
  have hscaleInt : (∫ u : ℝ,k (c/v) (u/v)) = v*smoothedRatioSquare B W (c/v) := by
    have heq : (fun u => k (c/v) (u/v)) = fun u => k (c/v) (v⁻¹*u) := by funext u; congr 1; ring
    rw [heq,Measure.integral_comp_mul_left]
    simp only [inv_inv,abs_of_pos hvpos,smul_eq_mul]
    rfl
  have hgeom (u : ℝ) (hu : u∈E) :
      ratioCutoff u=1 ∧ ratioCutoff (u/v)=1 ∧
      sourceBump 1 zero_lt_one (B*(c-u))=1 ∧
      sourceBump 1 zero_lt_one (B*(c/v-u/v))=1 := by
    have huPos : 0<u := by have := hu.1.1; linarith
    have hband := (le_div_iff₀ (show 0<2*B by positivity)).mp hu.2
    have hhalf : B*|c-u| ≤ 1/2 := by rw [abs_sub_comm]; nlinarith only [hband]
    have huPlateau : u∈Set.Icc (1/8 : ℝ) 4 := ⟨by linarith [hu.1.1],by linarith [hu.1.2]⟩
    have hrPlateau : u/v∈Set.Icc (1/8 : ℝ) 4 := by
      constructor
      · apply (le_div_iff₀ hvpos).2
        nlinarith [hu.1.1,hv.2]
      · apply (div_le_iff₀ hvpos).2
        nlinarith [hu.1.2,hv.1]
    refine ⟨ratioCutoff_eq_one huPlateau,ratioCutoff_eq_one hrPlateau,?_,?_⟩
    · apply sourceBump_eq_one_of_abs_le
      rw [abs_mul,abs_of_pos hB]
      linarith
    · apply sourceBump_eq_one_of_abs_le
      rw [show c/v-u/v=(c-u)/v by ring,abs_mul,abs_of_pos hB,abs_div,abs_of_pos hvpos]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hvpos).2
      nlinarith [hv.1]
  have hleA : B*(∫ u : ℝ,a u^2)  ≤  v*smoothedRatioSquare B W (c/v) := by
    rw [← integral_const_mul,← hscaleInt]
    apply integral_mono (ha2.const_mul B) hkScale
    intro u
    by_cases hu : u∈E
    · obtain ⟨_,hcut,_,hpsi⟩ := hgeom u hu
      simp [a,hu,k,ratioProfile,hcut,hpsi]
    · simp only [a,Set.indicator_of_notMem hu,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]
      exact hk0 _ _
  have hleB : B*(∫ u : ℝ,b u^2)  ≤  smoothedRatioSquare B W c := by
    change B*(∫ u : ℝ,b u^2)  ≤  ∫ u : ℝ,k c u
    rw [← integral_const_mul]
    apply integral_mono (hb2.const_mul B) (hkI c)
    intro u
    by_cases hu : u∈E
    · obtain ⟨hcut,_,hpsi,_⟩ := hgeom u hu
      simp [b,hu,k,ratioProfile,hcut,hpsi]
    · simp only [b,Set.indicator_of_notMem hu,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]
      exact hk0 _ _
  have hIA : 0 ≤ ∫ u : ℝ,a u^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hIB : 0 ≤ ∫ u : ℝ,b u^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hS1 := smoothedRatioSquare_nonneg hB W (c/v)
  have hS2 := smoothedRatioSquare_nonneg hB W c
  have hm := mul_le_mul hleA hleB (mul_nonneg hB.le hIB) (mul_nonneg hvpos.le hS1)
  have hs := mul_le_mul_of_nonneg_left hcs (sq_nonneg B)
  have hroot1 := smoothedRatio_sq hB W (c/v)
  have hroot2 := smoothedRatio_sq hB W c
  have hroot0 : 0 ≤ smoothedRatio B W (c/v)*smoothedRatio B W c := by unfold smoothedRatio; positivity
  have hmass0 : 0 ≤ affineFiberMass B c v W := integral_nonneg (fun _ => by positivity)
  have hfour := mul_le_mul_of_nonneg_right hv.2 (mul_nonneg hS1 hS2)
  have hsquare : (B*affineFiberMass B c v W)^2  ≤ 
      (2*(smoothedRatio B W (c/v)*smoothedRatio B W c))^2 := by
    have hrootprod : (smoothedRatio B W (c/v)*smoothedRatio B W c)^2 =
        smoothedRatioSquare B W (c/v)*smoothedRatioSquare B W c := by rw [mul_pow,hroot1,hroot2]
    nlinarith only [hm,hs,hfour,hrootprod,mul_nonneg hS1 hS2]
  have hlin := (sq_le_sq₀ (mul_nonneg hB.le hmass0) (by positivity : 0 ≤ 2*(smoothedRatio B W (c/v)*smoothedRatio B W c))).mp hsquare
  rw [show (2/B)*smoothedRatio B W (c/v)*smoothedRatio B W c =
    (2*(smoothedRatio B W (c/v)*smoothedRatio B W c))/B by ring]
  apply (le_div_iff₀ hB).2
  nlinarith only [hlin]

end
end GuthMaynardS3LiteralAffineFiber

#print axioms GuthMaynardS3LiteralAffineFiber.affineFiberMass_le
