import MRTMediumEq79ParallelTransform
import MRTMediumEq79ParallelMovingWindow
import MRTSourceBaseApertureOuterCutoffWeld

/-!
# Proposition 5.1: the exact medium-frequency (79) seam at the MAP aperture

This file packages the three exact identities which have to meet at the
medium-frequency branch: equation (79), the equation-(81) moving-window
normalization, and insertion of the compact outer packet cutoff.  The last
identity is specialized to the actual MAP `baseAperture`; in particular it
uses the proved quarter-range collar lemma, not the false uniform-support
argument at `H = X / 2`.

The two `MRTOneScaleEquation79Transform` inputs of the combined theorem remain
visible, but are no longer opaque source obligations:
`oneScaleEquation79Transform_of_integrable` below constructs each from the
literal two-dimensional Bochner-integrability hypotheses.  Thus equation (79)
has been reduced to cutoff/kernel integrability, with its phases and constants
proved exactly.
-/

namespace MAPFinishP51Medium79

open MeasureTheory Set
open MAPAllCenterApertureTransfer
open MAPMRTCorollary53Source
open MAPMRTProposition51HardBranch MAPMRTProposition51Source
open MAPMRTMediumEq79Parallel
open MAPMRTSourceBaseApertureOuterCutoffWeld

noncomputable section

theorem local_cutoffFourierKernel_eq_integral_additivePhase
    (cutoff : ℝ → ℝ) (v : ℝ) :
    cutoffFourierKernel cutoff v =
      ∫ y : ℝ, additivePhase (-v * y) * (cutoff y : ℂ) := by
  unfold cutoffFourierKernel
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [smul_eq_mul]
  unfold additivePhase
  congr 1
  push_cast
  ring_nf

theorem local_integral_v_affine_eq_integral_w
    {T : ℝ} (hT : 0 < T) (u y : ℝ) (G : ℝ → ℂ) :
    (∫ v : ℝ, G (u - 2 * Real.pi * v / T) * additivePhase (-v * y)) =
      ((T / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ w : ℝ, G w *
          Complex.exp (-(((T * y * u : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((((T * y * w : ℝ) : ℂ) * Complex.I)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  let a : ℝ := 2 * Real.pi / T
  have ha : 0 < a := div_pos (by positivity) hT
  let r : ℝ → ℂ := fun w ↦ G w *
    Complex.exp (-(((T * y * u : ℝ) : ℂ) * Complex.I)) *
    Complex.exp ((((T * y * w : ℝ) : ℂ) * Complex.I))
  have htranslate : (∫ z : ℝ, r (u - z)) = ∫ w : ℝ, r w :=
    MeasureTheory.integral_sub_left_eq_self r volume u
  have hpoint (v : ℝ) :
      G (u - 2 * Real.pi * v / T) * additivePhase (-v * y) =
        r (u - a * v) := by
    unfold r a additivePhase
    rw [show 2 * Real.pi * v / T = (2 * Real.pi / T) * v by ring_nf]
    rw [show Complex.exp
          (2 * (Real.pi : ℂ) * ((-v * y : ℝ) : ℂ) * Complex.I) =
        Complex.exp (-(((T * y * u : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((((T * y * (u - (2 * Real.pi / T) * v) : ℝ) : ℂ) *
            Complex.I)) by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp [hT.ne', hpi.ne']
      ring_nf]
    ring_nf
  have hscale := Measure.integral_comp_mul_left (fun z : ℝ ↦ r (u - z)) a
  calc
    _ = ∫ v : ℝ, r (u - a * v) := by
      apply integral_congr_ae
      filter_upwards with v
      exact hpoint v
    _ = |a⁻¹| • ∫ z : ℝ, r (u - z) := hscale
    _ = |a⁻¹| • ∫ w : ℝ, r w := by rw [htranslate]
    _ = ((T / (2 * Real.pi) : ℝ) : ℂ) * ∫ w : ℝ, r w := by
      change ((|a⁻¹| : ℝ) : ℂ) * (∫ w : ℝ, r w) = _
      have habsa : |a⁻¹| = T / (2 * Real.pi) := by
        rw [abs_of_pos (inv_pos.mpr ha)]
        unfold a
        field_simp [hT.ne', hpi.ne']
      rw [habsa]
    _ = _ := by rfl

theorem local_T_div_two_pi_mul_integral_y_eq_one_div_two_pi_mul_integral_t
    {T : ℝ} (hT : 0 < T) (u : ℝ) (cutoff : ℝ → ℝ) (G : ℝ → ℂ) :
    ((T / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ y : ℝ, (cutoff y : ℂ) *
          (∫ w : ℝ, G w *
            Complex.exp (-(((T * y * u : ℝ) : ℂ) * Complex.I)) *
            Complex.exp ((((T * y * w : ℝ) : ℂ) * Complex.I))) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, (cutoff (t / T) : ℂ) *
          (∫ w : ℝ, G w *
            Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I)) *
            Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  let Q : ℝ → ℂ := fun t ↦ (cutoff (t / T) : ℂ) *
    (∫ w : ℝ, G w * Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I)) *
      Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)))
  have hpoint (y : ℝ) : Q (T * y) =
      (cutoff y : ℂ) * (∫ w : ℝ, G w *
        Complex.exp (-(((T * y * u : ℝ) : ℂ) * Complex.I)) *
        Complex.exp ((((T * y * w : ℝ) : ℂ) * Complex.I))) := by
    unfold Q
    rw [mul_div_cancel_left₀ y hT.ne']
  simp_rw [← hpoint]
  have hscale := Measure.integral_comp_mul_left Q T
  have habs : |T⁻¹| = T⁻¹ := abs_of_pos (inv_pos.mpr hT)
  rw [hscale]
  change ((T / (2 * Real.pi) : ℝ) : ℂ) *
      (((|T⁻¹| : ℝ) : ℂ) * ∫ t : ℝ, Q t) =
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, Q t
  rw [habs]
  have hcoef : ((T / (2 * Real.pi) : ℝ) : ℂ) * (T⁻¹ : ℝ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp [hT.ne', hpi.ne']
  rw [← mul_assoc, hcoef]

/-- The two-variable kernel whose Fubini interchange opens the cutoff Fourier
transform in the one-scale calculation.  The coordinates are `(v,y)`. -/
def oneScaleFubiniKernel
    (T u : ℝ) (cutoff : ℝ → ℝ) (G : ℝ → ℂ) (v y : ℝ) : ℂ :=
  G (u - 2 * Real.pi * v / T) * (additivePhase (-v * y) * (cutoff y : ℂ))

/-- The one-scale transform after stating exactly the analytic legality needed
to interchange the `v` and `y` integrals.  Positivity of `T` supplies both
affine Jacobians. -/
theorem rescaledProjection_eq_oneScaleKernel_of_integrable
    {T u : ℝ} (hT : 0 < T) (cutoff : ℝ → ℝ) (G : ℝ → ℂ)
    (hFubini : Integrable
      (Function.uncurry (oneScaleFubiniKernel T u cutoff G))
      (volume.prod volume)) :
    rescaledProjection (cutoffFourierKernel cutoff) T G u =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, (cutoff (t / T) : ℂ) *
          ∫ w : ℝ, G w *
            Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I)) *
            Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) := by
  have hswap := MeasureTheory.integral_integral_swap hFubini
  unfold rescaledProjection
  simp_rw [local_cutoffFourierKernel_eq_integral_additivePhase]
  rw [show (∫ v : ℝ, G (u - 2 * Real.pi * v / T) *
        ∫ y : ℝ, additivePhase (-v * y) * (cutoff y : ℂ)) =
      ∫ v : ℝ, ∫ y : ℝ,
        G (u - 2 * Real.pi * v / T) *
          (additivePhase (-v * y) * (cutoff y : ℂ)) by
    apply integral_congr_ae
    filter_upwards with v
    rw [MeasureTheory.integral_const_mul]]
  change (∫ v : ℝ, ∫ y : ℝ, oneScaleFubiniKernel T u cutoff G v y) = _
  rw [hswap]
  have haffine (y : ℝ) :
      (∫ v : ℝ, oneScaleFubiniKernel T u cutoff G v y) =
        ((T / (2 * Real.pi) : ℝ) : ℂ) *
          ((cutoff y : ℂ) *
            ∫ w : ℝ, G w *
              Complex.exp (-(((T * y * u : ℝ) : ℂ) * Complex.I)) *
              Complex.exp ((((T * y * w : ℝ) : ℂ) * Complex.I))) := by
    unfold oneScaleFubiniKernel
    rw [show (∫ v : ℝ, G (u - 2 * Real.pi * v / T) *
          (additivePhase (-v * y) * (cutoff y : ℂ))) =
        (∫ v : ℝ, G (u - 2 * Real.pi * v / T) *
          additivePhase (-v * y)) * (cutoff y : ℂ) by
      rw [← MeasureTheory.integral_mul_const]
      apply integral_congr_ae
      filter_upwards with v
      ring]
    rw [local_integral_v_affine_eq_integral_w hT]
    ring
  calc
    (∫ y : ℝ, ∫ v : ℝ, oneScaleFubiniKernel T u cutoff G v y) =
        ((T / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ y : ℝ, (cutoff y : ℂ) *
            (∫ w : ℝ, G w *
              Complex.exp (-(((T * y * u : ℝ) : ℂ) * Complex.I)) *
              Complex.exp ((((T * y * w : ℝ) : ℂ) * Complex.I))) := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [haffine]
    _ = _ :=
      local_T_div_two_pi_mul_integral_y_eq_one_div_two_pi_mul_integral_t
        hT u cutoff G

/-! ## Finite Dirichlet-polynomial phase weld

The remaining one-scale transform is a Fubini problem, not a phase or
normalization problem.  The next identity closes the latter pointwise: after
summing the transformed coefficient kernels, the factors
`n^{-it}` and `X^{it}` are exactly the source polynomial and Mellin phase.
-/

/-- The coefficient-level kernel obtained from the one-scale affine transform. -/
def transformedOneScaleSummand
    (X T : ℝ) (cutoff : ℝ → ℝ) (f : ℕ → ℂ) (G : ℝ → ℂ)
    (n : ℕ) (t w : ℝ) : ℂ :=
  f n * (Real.sqrt n : ℂ)⁻¹ *
    ((cutoff (t / T) : ℂ) *
      (G w *
        Complex.exp
          (-(((t * (Real.log n - Real.log X) : ℝ) : ℂ) * Complex.I)) *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I))))

/-- Exact pointwise weld from the transformed finite coefficient sum to the
integrand on the right of the one-scale equation-(79) identity.  This removes
all sign, `2π`, and Mellin-phase ambiguity before the final Fubini step. -/
theorem sum_transformedOneScaleSummand_eq_source_integrand
    {N : ℕ} {X T t w : ℝ} {cutoff : ℝ → ℝ}
    {f : ℕ → ℂ} {G : ℝ → ℂ} :
    (∑ n ∈ Finset.Icc 1 N,
      transformedOneScaleSummand X T cutoff f G n t w) =
      finiteCriticalPolynomial N f t * G w * xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (cutoff (t / T) : ℂ) := by
  unfold transformedOneScaleSummand finiteCriticalPolynomial
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  unfold MixedMeanFrontend.mellinPhase xMellinPhase
  have hphase :
      Complex.exp
          (-(((t * (Real.log n - Real.log X) : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((t * Real.log X : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

/-- The previously uninhabited one-scale equation-(79) transform follows
from its two literal Fubini obligations.  The hypotheses are only Bochner
integrability of the kernels that are actually interchanged; the conclusion
is the named exact identity used by the medium-frequency branch. -/
theorem oneScaleEquation79Transform_of_integrable
    {N : ℕ} {X T : ℝ} {cutoff : ℝ → ℝ}
    {f : ℕ → ℂ} {G : ℝ → ℂ}
    (hT : 0 < T)
    (hprojection : ∀ n ∈ Finset.Icc 1 N,
      Integrable
        (Function.uncurry
          (oneScaleFubiniKernel T (Real.log n - Real.log X) cutoff G))
        (volume.prod volume))
    (htransformed : ∀ n ∈ Finset.Icc 1 N,
      Integrable
        (Function.uncurry
          (transformedOneScaleSummand X T cutoff f G n))
        (volume.prod volume)) :
    MRTOneScaleEquation79Transform N X T cutoff f G := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      f n * (Real.sqrt n : ℂ)⁻¹ *
          rescaledProjection (cutoffFourierKernel cutoff) T G
            (Real.log n - Real.log X) =
        c * ∫ t : ℝ, ∫ w : ℝ,
          transformedOneScaleSummand X T cutoff f G n t w := by
    have hprojection' := rescaledProjection_eq_oneScaleKernel_of_integrable
      hT cutoff G (hprojection n hn)
    rw [hprojection']
    change _ * (c * _) = c * _
    calc
      f n * (Real.sqrt n : ℂ)⁻¹ *
          (c * ∫ t : ℝ, (cutoff (t / T) : ℂ) *
            ∫ w : ℝ, G w *
              Complex.exp
                (-(((t * (Real.log n - Real.log X) : ℝ) : ℂ) * Complex.I)) *
              Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I))) =
        c * ((f n * (Real.sqrt n : ℂ)⁻¹) *
          ∫ t : ℝ, (cutoff (t / T) : ℂ) *
            ∫ w : ℝ, G w *
              Complex.exp
                (-(((t * (Real.log n - Real.log X) : ℝ) : ℂ) * Complex.I)) *
              Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I))) := by ring
      _ = c * ∫ t : ℝ,
          (f n * (Real.sqrt n : ℂ)⁻¹) *
            ((cutoff (t / T) : ℂ) *
              ∫ w : ℝ, G w *
                Complex.exp
                  (-(((t * (Real.log n - Real.log X) : ℝ) : ℂ) * Complex.I)) *
                Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I))) := by
        rw [integral_const_mul]
      _ = c * ∫ t : ℝ, ∫ w : ℝ,
          transformedOneScaleSummand X T cutoff f G n t w := by
        congr 1
        apply integral_congr_ae
        filter_upwards with t
        calc
          (f n * (Real.sqrt n : ℂ)⁻¹) *
              ((cutoff (t / T) : ℂ) *
                ∫ w : ℝ, G w *
                  Complex.exp
                    (-(((t * (Real.log n - Real.log X) : ℝ) : ℂ) *
                      Complex.I)) *
                  Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I))) =
            ((f n * (Real.sqrt n : ℂ)⁻¹) * (cutoff (t / T) : ℂ)) *
              ∫ w : ℝ, G w *
                Complex.exp
                  (-(((t * (Real.log n - Real.log X) : ℝ) : ℂ) *
                    Complex.I)) *
                Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) := by ring
          _ = ∫ w : ℝ,
              ((f n * (Real.sqrt n : ℂ)⁻¹) * (cutoff (t / T) : ℂ)) *
                (G w *
                  Complex.exp
                    (-(((t * (Real.log n - Real.log X) : ℝ) : ℂ) *
                      Complex.I)) *
                  Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I))) := by
            rw [MeasureTheory.integral_const_mul]
          _ = ∫ w : ℝ,
              transformedOneScaleSummand X T cutoff f G n t w := by
            apply integral_congr_ae
            filter_upwards with w
            unfold transformedOneScaleSummand
            ring
  unfold MRTOneScaleEquation79Transform oneScaleProjectedCriticalSum
    oneScaleEquation79Integral
  rw [Finset.sum_congr rfl (fun n hn ↦ hterm n hn)]
  rw [← Finset.mul_sum]
  congr 1
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    filter_upwards [((Finset.eventually_all (Finset.Icc 1 N)).2
      (fun n hn ↦ (htransformed n hn).prod_right_ae))] with t ht
    rw [← integral_finset_sum]
    · apply integral_congr_ae
      filter_upwards with w
      exact sum_transformedOneScaleSummand_eq_source_integrand
    · intro n hn
      exact ht n hn
  · intro n hn
    exact (htransformed n hn).integral_prod_left

/-- The complete exact normalization seam needed by the medium branch of MRT
Proposition 5.1 at the aperture actually used by MAP.

The first conjunct is the literal double integral (79).  The second says that
the Schur-side `ENNReal` moving-window mass is exactly the manuscript's real
quantity `proposition51I`, with radius `|beta| * baseAperture epsilon X`.
The third is the exact packet outer-cutoff insertion. -/
theorem medium79_transform_movingWindow_and_baseAperture_collar
    {epsilon X beta eta packetT : ℝ} {cutoff outer : ℝ → ℝ}
    {f : ℕ → ℂ} {G : ℝ → ℂ} {g : ℝ → ℂ}
    (hX : 4 ≤ X)
    (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hhiId : MRTOneScaleEquation79Transform ⌊2 * X⌋₊ X
      (|beta| * X / eta) cutoff f G)
    (hloId : MRTOneScaleEquation79Transform ⌊2 * X⌋₊ X
      (10 * eta * |beta| * X) cutoff f G)
    (hhi : Integrable (Function.uncurry (fun t w : ℝ ↦
      finiteCriticalPolynomial ⌊2 * X⌋₊ f t * G w * xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (cutoff (t / (|beta| * X / eta)) : ℂ)))
        (volume.prod volume))
    (hlo : Integrable (Function.uncurry (fun t w : ℝ ↦
      finiteCriticalPolynomial ⌊2 * X⌋₊ f t * G w * xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (cutoff (t / (10 * eta * |beta| * X)) : ℂ)))
        (volume.prod volume))
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1)
    (hNoOuter : Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
        cutoff (fun _ ↦ 1)))
    (hOuter : Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
        cutoff outer)) :
    ((∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊,
        f n * (Real.sqrt n : ℂ)⁻¹ *
          mediumFrequencyProjection X beta eta cutoff G
            (Real.log n - Real.log X)) =
      equation79Integral ⌊2 * X⌋₊ X beta eta cutoff f G) ∧
    proposition51ILintegral ⌊2 * X⌋₊ X (baseAperture epsilon X)
        f beta eta = ENNReal.ofReal
          (proposition51I X (baseAperture epsilon X) f beta eta) ∧
    (∫ x : ℝ, g x *
        sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
          cutoff (fun _ ↦ 1)) =
      ∫ x : ℝ, g x *
        sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
          cutoff outer := by
  have hXnonneg : 0 ≤ X := by linarith
  have hHnonneg : 0 ≤ baseAperture epsilon X :=
    (baseAperture_pos (by linarith : 0 < X)).le
  refine ⟨?_, ?_, ?_⟩
  · exact mediumProjectedCriticalSum_eq_equation79Integral
      heta.ne' hhiId hloId hhi hlo
  · exact proposition51ILintegral_eq_ofReal_proposition51I
      hXnonneg hHnonneg heta hetaOne
  · exact integral_mul_packet_withoutOuter_eq_outer_baseAperture
      hX hgSupport hcutoffSupport houterOne hNoOuter hOuter

/-- Source-facing version of the complete equation-(79)/window/collar weld.
Unlike the bookkeeping theorem above, this version has no
`MRTOneScaleEquation79Transform` premise: both named identities are generated
from the literal kernels' Bochner integrability. -/
theorem medium79_transform_movingWindow_and_baseAperture_collar_of_integrable
    {epsilon X beta eta packetT : ℝ} {cutoff outer : ℝ → ℝ}
    {f : ℕ → ℂ} {G : ℝ → ℂ} {g : ℝ → ℂ}
    (hX : 4 ≤ X)
    (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hhiProjection : ∀ n ∈ Finset.Icc 1 ⌊2 * X⌋₊,
      Integrable
        (Function.uncurry (oneScaleFubiniKernel (|beta| * X / eta)
          (Real.log n - Real.log X) cutoff G)) (volume.prod volume))
    (hloProjection : ∀ n ∈ Finset.Icc 1 ⌊2 * X⌋₊,
      Integrable
        (Function.uncurry (oneScaleFubiniKernel
          (10 * eta * |beta| * X) (Real.log n - Real.log X) cutoff G))
        (volume.prod volume))
    (hhiTransformed : ∀ n ∈ Finset.Icc 1 ⌊2 * X⌋₊,
      Integrable (Function.uncurry (transformedOneScaleSummand X
        (|beta| * X / eta) cutoff f G n)) (volume.prod volume))
    (hloTransformed : ∀ n ∈ Finset.Icc 1 ⌊2 * X⌋₊,
      Integrable (Function.uncurry (transformedOneScaleSummand X
        (10 * eta * |beta| * X) cutoff f G n)) (volume.prod volume))
    (hhi : Integrable (Function.uncurry (fun t w : ℝ ↦
      finiteCriticalPolynomial ⌊2 * X⌋₊ f t * G w * xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (cutoff (t / (|beta| * X / eta)) : ℂ)))
        (volume.prod volume))
    (hlo : Integrable (Function.uncurry (fun t w : ℝ ↦
      finiteCriticalPolynomial ⌊2 * X⌋₊ f t * G w * xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (cutoff (t / (10 * eta * |beta| * X)) : ℂ)))
        (volume.prod volume))
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1)
    (hNoOuter : Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
        cutoff (fun _ ↦ 1)))
    (hOuter : Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
        cutoff outer)) :
    ((∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊,
        f n * (Real.sqrt n : ℂ)⁻¹ *
          mediumFrequencyProjection X beta eta cutoff G
            (Real.log n - Real.log X)) =
      equation79Integral ⌊2 * X⌋₊ X beta eta cutoff f G) ∧
    proposition51ILintegral ⌊2 * X⌋₊ X (baseAperture epsilon X)
        f beta eta = ENNReal.ofReal
          (proposition51I X (baseAperture epsilon X) f beta eta) ∧
    (∫ x : ℝ, g x *
        sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
          cutoff (fun _ ↦ 1)) =
      ∫ x : ℝ, g x *
        sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
          cutoff outer := by
  have hXpos : 0 < X := by linarith
  have hhiT : 0 < |beta| * X / eta := by positivity
  have hloT : 0 < 10 * eta * |beta| * X := by positivity
  exact medium79_transform_movingWindow_and_baseAperture_collar
    hX heta hetaOne
    (oneScaleEquation79Transform_of_integrable hhiT
      hhiProjection hhiTransformed)
    (oneScaleEquation79Transform_of_integrable hloT
      hloProjection hloTransformed)
    hhi hlo hgSupport hcutoffSupport houterOne hNoOuter hOuter

end
end MAPFinishP51Medium79

#print axioms MAPFinishP51Medium79.medium79_transform_movingWindow_and_baseAperture_collar
#print axioms MAPFinishP51Medium79.local_cutoffFourierKernel_eq_integral_additivePhase
#print axioms MAPFinishP51Medium79.local_integral_v_affine_eq_integral_w
#print axioms MAPFinishP51Medium79.local_T_div_two_pi_mul_integral_y_eq_one_div_two_pi_mul_integral_t
#print axioms MAPFinishP51Medium79.rescaledProjection_eq_oneScaleKernel_of_integrable
#print axioms MAPFinishP51Medium79.sum_transformedOneScaleSummand_eq_source_integrand
#print axioms MAPFinishP51Medium79.oneScaleEquation79Transform_of_integrable
#print axioms MAPFinishP51Medium79.medium79_transform_movingWindow_and_baseAperture_collar_of_integrable
