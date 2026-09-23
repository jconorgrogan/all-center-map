import MRTEquation81Averaging

/-! Tonelli completion of the symmetric averaging step in equation (81). -/

namespace MAPMRTEquation81AveragingBilinear

open MeasureTheory Set
open MAPMRTEquation81Kernel MAPMRTEquation81Averaging

noncomputable section

/-- Indicator of the symmetric radius-`R` box, written as an `ENNReal` weight
so that all four integrations can be exchanged by Tonelli. -/
def symmetricBoxWeight (R c u : ℝ) : ENNReal :=
  (Icc (-R) R).indicator (fun _ ↦ (1 : ENNReal)) (u - c)

theorem measurable_symmetricBoxWeight (R : ℝ) :
    Measurable fun z : ℝ × ℝ ↦ symmetricBoxWeight R z.1 z.2 := by
  unfold symmetricBoxWeight
  exact (measurable_const.indicator measurableSet_Icc).comp
    (measurable_snd.sub measurable_fst)

theorem symmetricBoxWeight_symm (R c u : ℝ) :
    symmetricBoxWeight R c u = symmetricBoxWeight R u c := by
  unfold symmetricBoxWeight
  by_cases h : u - c ∈ Icc (-R) R
  · have h' : c - u ∈ Icc (-R) R := by
      constructor <;> linarith [h.1, h.2]
    simp [h, h']
  · have h' : c - u ∉ Icc (-R) R := by
      intro hm
      apply h
      constructor <;> linarith [hm.1, hm.2]
    simp [h, h']

/-- The moving integral in weight form. -/
def equation81Average (R : ℝ) (F : ℝ → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ u : ℝ, F u * symmetricBoxWeight R x u

theorem equation81Average_eq_symmetricMovingIntegral
    (R : ℝ) (F : ℝ → ENNReal) (x : ℝ) :
    equation81Average R F x = symmetricMovingIntegral R F x := by
  unfold equation81Average symmetricMovingIntegral symmetricBoxWeight
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro u
  by_cases h : u ∈ Icc (x - R) (x + R)
  · have h' : u - x ∈ Icc (-R) R := by
      constructor <;> linarith [h.1, h.2]
    simp [h, h']
  · have h' : u - x ∉ Icc (-R) R := by
      intro hm
      apply h
      constructor <;> linarith [hm.1, hm.2]
    simp [h, h']

theorem measurable_equation81Average
    {R : ℝ} {F : ℝ → ENNReal} (hF : Measurable F) :
    Measurable (equation81Average R F) := by
  unfold equation81Average
  have hprod : Measurable fun z : ℝ × ℝ ↦
      F z.2 * symmetricBoxWeight R z.1 z.2 :=
    (hF.comp measurable_snd).mul (measurable_symmetricBoxWeight R)
  exact hprod.lintegral_prod_right'

/-- The equation-(81) kernel averaged over the two radius-`R` boxes. -/
def averagedEquation81Kernel (R u v : ℝ) : ENNReal :=
  ∫⁻ z : ℝ × ℝ,
    symmetricBoxWeight R u z.1 * symmetricBoxWeight R v z.2 *
      ENNReal.ofReal (equation81Kernel R z.1 z.2) ∂volume.prod volume

theorem averagedEquation81Kernel_eq_boxes
    {R u v : ℝ} (hR : 0 < R) :
    averagedEquation81Kernel R u v =
      ∫⁻ x in Icc (u - R) (u + R),
        ∫⁻ y in Icc (v - R) (v + R),
          ENNReal.ofReal (equation81Kernel R x y) := by
  let k : ℝ → ℝ → ENNReal := fun x y ↦
    ENNReal.ofReal (equation81Kernel R x y)
  have hk : Measurable fun z : ℝ × ℝ ↦ k z.1 z.2 :=
    (continuous_equation81Kernel hR).measurable.ennreal_ofReal
  have hw₁ : Measurable fun z : ℝ × ℝ ↦ symmetricBoxWeight R u z.1 :=
    ((measurable_symmetricBoxWeight R).comp
      (measurable_const.prodMk measurable_fst))
  have hw₂ : Measurable fun z : ℝ × ℝ ↦ symmetricBoxWeight R v z.2 :=
    ((measurable_symmetricBoxWeight R).comp
      (measurable_const.prodMk measurable_snd))
  unfold averagedEquation81Kernel
  have hm : AEMeasurable (fun z : ℝ × ℝ => symmetricBoxWeight R u z.1 * symmetricBoxWeight R v z.2 * k z.1 z.2) (volume.prod volume) := by
    exact ((hw₁.mul hw₂).mul hk).aemeasurable
  rw [lintegral_prod _ hm]
  simp only [Prod.fst, Prod.snd]
  have hinner (x : ℝ) :
      (∫⁻ y : ℝ, symmetricBoxWeight R u x * symmetricBoxWeight R v y * k x y) =
      symmetricBoxWeight R u x * equation81Average R (k x) v := by
    rw [show (fun y : ℝ ↦
        symmetricBoxWeight R u x * symmetricBoxWeight R v y * k x y) =
        (fun y : ℝ ↦ symmetricBoxWeight R u x *
          (symmetricBoxWeight R v y * k x y)) by
      funext y
      ring]
    rw [lintegral_const_mul' (symmetricBoxWeight R u x) _]
    · congr 1
      apply lintegral_congr
      intro y
      ring
    · unfold symmetricBoxWeight
      by_cases hx : x - u ∈ Icc (-R) R <;> simp [hx]
  simp_rw [hinner]
  have havg : (∫⁻ x : ℝ,
      symmetricBoxWeight R u x * equation81Average R (k x) v) =
      equation81Average R (fun x ↦ equation81Average R (k x) v) u := by
    unfold equation81Average
    apply lintegral_congr
    intro x
    ring
  rw [havg, equation81Average_eq_symmetricMovingIntegral]
  unfold symmetricMovingIntegral
  congr 1
  funext x
  simpa [symmetricMovingIntegral, k] using
    equation81Average_eq_symmetricMovingIntegral R (k x) v

theorem averagedEquation81Kernel_lower
    {R u v : ℝ} (hR : 0 < R) :
    (ENNReal.ofReal (2 * R)) ^ 2 *
        ENNReal.ofReal (equation81Kernel R u v) ≤
      9 * averagedEquation81Kernel R u v := by
  rw [averagedEquation81Kernel_eq_boxes hR]
  exact box_lintegral_kernel_lower hR

/-- Bilinear form with the literal equation-(81) kernel. -/
def equation81Bilinear (R : ℝ) (F : ℝ → ENNReal) : ENNReal :=
  ∫⁻ z : ℝ × ℝ,
    F z.1 * F z.2 * ENNReal.ofReal (equation81Kernel R z.1 z.2)
      ∂volume.prod volume

/-- Tonelli identifies averaging the kernel around both input points with
putting the two symmetric moving integrals into the original bilinear form. -/
theorem lintegral_mul_averagedKernel_eq_bilinear_average
    {R : ℝ} {F : ℝ → ENNReal} (hR : 0 < R) (hF : Measurable F) :
    (∫⁻ z : ℝ × ℝ,
      F z.1 * F z.2 * averagedEquation81Kernel R z.1 z.2
        ∂volume.prod volume) =
      equation81Bilinear R (equation81Average R F) := by
  let μ : Measure (ℝ × ℝ) := volume.prod volume
  let Q : (ℝ × ℝ) → (ℝ × ℝ) → ENNReal := fun p q ↦
    F p.1 * F p.2 *
      (symmetricBoxWeight R p.1 q.1 * symmetricBoxWeight R p.2 q.2 *
        ENNReal.ofReal (equation81Kernel R q.1 q.2))
  have hFp : Measurable fun p : ℝ × ℝ ↦ F p.1 * F p.2 :=
    (hF.comp measurable_fst).mul (hF.comp measurable_snd)
  have hw₁ : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦
      symmetricBoxWeight R z.1.1 z.2.1 :=
    (measurable_symmetricBoxWeight R).comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))
  have hw₂ : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦
      symmetricBoxWeight R z.1.2 z.2.2 :=
    (measurable_symmetricBoxWeight R).comp
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))
  have hk : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦
      ENNReal.ofReal (equation81Kernel R z.2.1 z.2.2) :=
    ((continuous_equation81Kernel hR).measurable.ennreal_ofReal).comp measurable_snd
  have hQ : Measurable (Function.uncurry Q) := by
    unfold Q Function.uncurry
    exact (hFp.comp measurable_fst).mul ((hw₁.mul hw₂).mul hk)
  have hleft (p : ℝ × ℝ) :
      (∫⁻ q : ℝ × ℝ, Q p q ∂μ) =
        (F p.1 * F p.2) * averagedEquation81Kernel R p.1 p.2 := by
    unfold Q averagedEquation81Kernel μ
    rw [show (fun q : ℝ × ℝ ↦
        F p.1 * F p.2 *
          (symmetricBoxWeight R p.1 q.1 * symmetricBoxWeight R p.2 q.2 *
            ENNReal.ofReal (equation81Kernel R q.1 q.2))) =
        (fun q : ℝ × ℝ ↦ (F p.1 * F p.2) *
          (symmetricBoxWeight R p.1 q.1 * symmetricBoxWeight R p.2 q.2 *
            ENNReal.ofReal (equation81Kernel R q.1 q.2))) by rfl]
    apply lintegral_const_mul
    exact (((measurable_symmetricBoxWeight R).comp
      (measurable_const.prodMk measurable_fst)).mul
      ((measurable_symmetricBoxWeight R).comp
        (measurable_const.prodMk measurable_snd))).mul
      ((continuous_equation81Kernel hR).measurable.ennreal_ofReal)
  have hright (q : ℝ × ℝ) :
      (∫⁻ p : ℝ × ℝ, Q p q ∂μ) =
        equation81Average R F q.1 * equation81Average R F q.2 *
          ENNReal.ofReal (equation81Kernel R q.1 q.2) := by
    let f : ℝ → ENNReal := fun u ↦ F u * symmetricBoxWeight R q.1 u
    let g : ℝ → ENNReal := fun v ↦ F v * symmetricBoxWeight R q.2 v
    have hf : Measurable f := hF.mul
      ((measurable_symmetricBoxWeight R).comp
        (measurable_const.prodMk measurable_id))
    have hg : Measurable g := hF.mul
      ((measurable_symmetricBoxWeight R).comp
        (measurable_const.prodMk measurable_id))
    unfold Q μ
    rw [show (fun p : ℝ × ℝ ↦
        F p.1 * F p.2 *
          (symmetricBoxWeight R p.1 q.1 * symmetricBoxWeight R p.2 q.2 *
            ENNReal.ofReal (equation81Kernel R q.1 q.2))) =
        (fun p : ℝ × ℝ ↦ f p.1 * g p.2 *
          ENNReal.ofReal (equation81Kernel R q.1 q.2)) by
          funext p
          simp only [f, g, symmetricBoxWeight_symm R p.1 q.1,
            symmetricBoxWeight_symm R p.2 q.2]
          ring]
    have hconst := lintegral_mul_const'
      (μ := volume.prod volume)
      (ENNReal.ofReal (equation81Kernel R q.1 q.2))
      (fun p : ℝ × ℝ ↦ f p.1 * g p.2) ENNReal.ofReal_ne_top
    change (∫⁻ p : ℝ × ℝ,
        f p.1 * g p.2 * ENNReal.ofReal (equation81Kernel R q.1 q.2)
          ∂volume.prod volume) =
      (∫⁻ p : ℝ × ℝ, f p.1 * g p.2 ∂volume.prod volume) *
        ENNReal.ofReal (equation81Kernel R q.1 q.2) at hconst
    rw [hconst]
    rw [lintegral_prod_mul hf.aemeasurable hg.aemeasurable]
    change ((∫⁻ u : ℝ, f u) * ∫⁻ v : ℝ, g v) * _ = _
    simp only [f, g, equation81Average]
  have hswap :
      (∫⁻ p : ℝ × ℝ, ∫⁻ q : ℝ × ℝ, Q p q ∂μ ∂μ) =
      ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ, Q p q ∂μ ∂μ :=
    lintegral_lintegral_swap hQ.aemeasurable
  unfold equation81Bilinear
  change (∫⁻ p : ℝ × ℝ,
      F p.1 * F p.2 * averagedEquation81Kernel R p.1 p.2 ∂μ) = _
  rw [← show (∫⁻ p : ℝ × ℝ, ∫⁻ q : ℝ × ℝ, Q p q ∂μ ∂μ) =
      (∫⁻ p : ℝ × ℝ,
        F p.1 * F p.2 * averagedEquation81Kernel R p.1 p.2 ∂μ) by
    apply lintegral_congr
    intro p
    exact hleft p]
  rw [hswap]
  apply lintegral_congr
  intro q
  exact hright q

/-- The complete averaging inequality used in (81), before Schur: the two
unnormalized radius-`R` moving integrals pay exactly the geometric factor `9`
and recover the square box mass `(2R)^2`. -/
theorem equation81_bilinear_averaging
    {R : ℝ} {F : ℝ → ENNReal} (hR : 0 < R) (hF : Measurable F) :
    (ENNReal.ofReal (2 * R)) ^ 2 * equation81Bilinear R F ≤
      9 * equation81Bilinear R (equation81Average R F) := by
  let s : ENNReal := (ENNReal.ofReal (2 * R)) ^ 2
  let K : ℝ × ℝ → ENNReal := fun z ↦
    ENNReal.ofReal (equation81Kernel R z.1 z.2)
  let KA : ℝ × ℝ → ENNReal := fun z ↦
    averagedEquation81Kernel R z.1 z.2
  have hs_top : s ≠ ⊤ := by
    unfold s
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hpoint (z : ℝ × ℝ) :
      F z.1 * F z.2 * (s * K z) ≤
        F z.1 * F z.2 * (9 * KA z) := by
    apply mul_le_mul_right
    exact averagedEquation81Kernel_lower hR
  have hmono :
      (∫⁻ z : ℝ × ℝ, F z.1 * F z.2 * (s * K z)
        ∂volume.prod volume) ≤
      ∫⁻ z : ℝ × ℝ, F z.1 * F z.2 * (9 * KA z)
        ∂volume.prod volume := lintegral_mono hpoint
  have hleft :
      (∫⁻ z : ℝ × ℝ, F z.1 * F z.2 * (s * K z)
        ∂volume.prod volume) = s * equation81Bilinear R F := by
    have hs := lintegral_const_mul'
      (μ := volume.prod volume) s
      (fun z : ℝ × ℝ ↦ F z.1 * F z.2 * K z) hs_top
    calc
      (∫⁻ z : ℝ × ℝ, F z.1 * F z.2 * (s * K z)
          ∂volume.prod volume) =
          ∫⁻ z : ℝ × ℝ, s * (F z.1 * F z.2 * K z)
            ∂volume.prod volume := by
        apply lintegral_congr
        intro z
        ring
      _ = s * (∫⁻ z : ℝ × ℝ, F z.1 * F z.2 * K z
          ∂volume.prod volume) := hs
      _ = s * equation81Bilinear R F := by rfl
  have hright :
      (∫⁻ z : ℝ × ℝ, F z.1 * F z.2 * (9 * KA z)
        ∂volume.prod volume) =
      9 * (∫⁻ z : ℝ × ℝ, F z.1 * F z.2 * KA z
        ∂volume.prod volume) := by
    have hn := lintegral_const_mul'
      (μ := volume.prod volume) 9
      (fun z : ℝ × ℝ ↦ F z.1 * F z.2 * KA z) (by norm_num)
    rw [← hn]
    apply lintegral_congr
    intro z
    ring
  rw [hleft, hright] at hmono
  dsimp only [KA] at hmono
  rw [lintegral_mul_averagedKernel_eq_bilinear_average hR hF] at hmono
  exact hmono

#print axioms equation81Average_eq_symmetricMovingIntegral
#print axioms measurable_equation81Average
#print axioms averagedEquation81Kernel_lower
#print axioms lintegral_mul_averagedKernel_eq_bilinear_average
#print axioms equation81_bilinear_averaging

end
end MAPMRTEquation81AveragingBilinear
