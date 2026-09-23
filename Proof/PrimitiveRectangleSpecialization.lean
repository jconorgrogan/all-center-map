import FinitePoleRectangle
import PrimitiveTruncatedExplicitFormulaBridge
import APZeroDensityCertificate
import Mathlib.Analysis.Complex.RemovableSingularity

set_option maxHeartbeats 800000

/-!
# Specialization of the finite-pole rectangle theorem to Dirichlet L-functions

The geometric residue theorem is unconditional.  This module identifies its
literal boundary with `normalizedRectangleBoundary`, packages the actual
principal and divisor-backed poles, and states the exact removable-extension
regularity which is still needed to close the specialization.
-/

namespace PrimitiveRectangleSpecialization

open Set Filter Topology MeasureTheory Complex
open scoped BigOperators Interval ArithmeticFunction
open DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge FinitePoleRectangle
open TruncatedTwistedPerron

noncomputable section

/-- The named normalized contour is exactly `(2πi)⁻¹` times the geometric
rectangle boundary, with no orientation convention left implicit. -/
theorem normalizedRectangleBoundary_eq_inv_mul_rectangleBoundaryIntegral
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (σ c T : ℝ) :
    normalizedRectangleBoundary χ x σ c T =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        rectangleBoundaryIntegral (perronContourIntegrand χ x)
          σ c (-T) T := by
  have hright := rightLineIntegral_eq_contourIntegrand χ hx c T
  have hbottom :
      (∫ u in σ..c, perronContourIntegrand χ x
        ((u : ℂ) - Complex.I * (T : ℂ))) =
      ∫ u in σ..c, perronContourIntegrand χ x
        ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro u hu
    apply congrArg (perronContourIntegrand χ x)
    push_cast
    ring
  have hnorm : (2 * Real.pi * Complex.I : ℂ)⁻¹ =
      -(((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.I) := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num]
    rw [mul_inv_rev, Complex.inv_I]
    ring
  unfold normalizedRectangleBoundary leftLineIntegral
    horizontalBoundaryIntegral rectangleBoundaryIntegral
  rw [hright, hbottom, hnorm]
  have halg (A D U R L : ℂ) :
      A * R - A * L + (A * Complex.I) * U - (A * Complex.I) * D =
        -(A * Complex.I) *
          (D - U + Complex.I * R - Complex.I * L) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  simpa only [mul_comm, sub_eq_add_neg, add_assoc] using halg
    (((2 * Real.pi : ℝ) : ℂ)⁻¹)
    (∫ u in σ..c, perronContourIntegrand χ x
      ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
    (∫ u in σ..c, perronContourIntegrand χ x
      ((u : ℂ) + Complex.I * (T : ℂ)))
    (∫ t in (-T)..T, perronContourIntegrand χ x
      ((c : ℂ) + Complex.I * (t : ℂ)))
    (∫ t in (-T)..T, perronContourIntegrand χ x
      ((σ : ℂ) + Complex.I * (t : ℂ)))

/-- The finite set of poles of the source Perron integrand in the shifted
rectangle: actual regularized-L zeros, plus `s=1` exactly for the principal
character. -/
def sourcePoleSupport {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) : Finset ℂ :=
  if χ = 1 then insert 1 (zeroSupport χ σ T) else zeroSupport χ σ T

/-- The actual source residue attached to a supported pole. -/
def sourcePoleResidue {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ T x : ℝ) (ρ : ℂ) : ℂ :=
  if χ = 1 ∧ ρ = 1 then (x : ℂ)
  else -(zeroMultiplicity χ σ T ρ : ℂ) * (x : ℂ) ^ ρ / ρ

/-- The source integrand with every displayed principal part subtracted. -/
def sourcePrincipalPartRemoved {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ T x : ℝ) (s : ℂ) : ℂ :=
  perronContourIntegrand χ x s -
    ∑ ρ ∈ sourcePoleSupport χ σ T,
      sourcePoleResidue χ σ T x ρ * (s - ρ)⁻¹

/-- Canonical finite removable extension: at each recorded pole use the
punctured-neighborhood limit of the principal-part-removed integrand. -/
def patchedSourcePerronIntegrand {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ T x : ℝ) (s : ℂ) : ℂ :=
  if s ∈ sourcePoleSupport χ σ T then
    limUnder (𝓝[≠] s) (sourcePrincipalPartRemoved χ σ T x)
  else sourcePrincipalPartRemoved χ σ T x s

theorem one_not_mem_zeroSupport {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    (1 : ℂ) ∉ zeroSupport χ σ T := by
  intro h
  exact (regularizedLFunction_one_ne_zero χ)
    (regularizedLFunction_eq_zero_of_mem_zeroSupport χ σ T h)

/-- The finite sum of the actual source residues is exactly the main term
minus the multiplicity-weighted Perron zero sum. -/
theorem sum_sourcePoleResidue
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T x : ℝ) :
    (∑ ρ ∈ sourcePoleSupport χ σ T,
        sourcePoleResidue χ σ T x ρ) =
      residueMain χ x - multiplicityWeightedPerronZeroSum χ σ T x := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    have hone := one_not_mem_zeroSupport (1 : DirichletCharacter ℂ q) σ T
    rw [sourcePoleSupport, if_pos rfl, Finset.sum_insert hone]
    have hzeroSum :
        (∑ ρ ∈ zeroSupport (1 : DirichletCharacter ℂ q) σ T,
          sourcePoleResidue (1 : DirichletCharacter ℂ q) σ T x ρ) =
          -multiplicityWeightedPerronZeroSum
            (1 : DirichletCharacter ℂ q) σ T x := by
      unfold multiplicityWeightedPerronZeroSum
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hρ1 : ρ ≠ 1 := fun heq => hone (heq ▸ hρ)
      simp only [sourcePoleResidue, if_neg (not_and_of_not_right _ hρ1)]
      ring
    rw [hzeroSum]
    simp [sourcePoleResidue, residueMain]
    ring
  · simp only [sourcePoleSupport, if_neg hχ, sourcePoleResidue,
      hχ, false_and, if_false, residueMain,
      multiplicityWeightedPerronZeroSum]
    calc
      (∑ ρ ∈ zeroSupport χ σ T,
          -(zeroMultiplicity χ σ T ρ : ℂ) * (x : ℂ) ^ ρ / ρ) =
          ∑ ρ ∈ zeroSupport χ σ T,
            -((zeroMultiplicity χ σ T ρ : ℂ) * (x : ℂ) ^ ρ / ρ) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
      _ =
          -(∑ ρ ∈ zeroSupport χ σ T,
            (zeroMultiplicity χ σ T ρ : ℂ) * (x : ℂ) ^ ρ / ρ) :=
        Finset.sum_neg_distrib _
      _ = 0 - ∑ ρ ∈ zeroSupport χ σ T,
            (zeroMultiplicity χ σ T ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
        ring

/-- The source integrand itself has residue `x` at the principal pole. -/
theorem tendsto_mul_perronContourIntegrand_one
    {q : ℕ} [NeZero q] (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun s => (s - 1) * perronContourIntegrand
        (1 : DirichletCharacter ℂ q) x s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (x : ℂ)) := by
  have hlog := tendsto_mul_neg_logDeriv_LFunctionTrivChar_one q
  have hpow : Tendsto (fun s : ℂ => (x : ℂ) ^ s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (x : ℂ)) := by
    have hdiff : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
      differentiable_id.const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    have ht := hdiff.continuous.continuousAt.tendsto.mono_left
      (show 𝓝[≠] (1 : ℂ) ≤ 𝓝 (1 : ℂ) from nhdsWithin_le_nhds)
    simpa [Complex.ofReal_cpow hx.le, Real.rpow_one] using ht
  have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hfactor : Tendsto (fun s : ℂ => (x : ℂ) ^ s / s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (x : ℂ)) := by
    simpa using! hpow.div hid (by norm_num)
  have hmul := hlog.mul hfactor
  convert hmul using 1
  · ext s
    simp only [perronContourIntegrand]
    ring
  · ring

/-- Every member of `sourcePoleSupport` has the residue advertised by
`sourcePoleResidue`.  This is the local small-excision input, proved from the
actual divisor multiplicities and the actual principal-character pole. -/
theorem tendsto_mul_perronContourIntegrand_at_sourcePole
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ T x : ℝ} (hx : 0 < x) (hσ : 0 < σ) {ρ : ℂ}
    (hρ : ρ ∈ sourcePoleSupport χ σ T) :
    Tendsto (fun s => (s - ρ) * perronContourIntegrand χ x s)
      (𝓝[≠] ρ) (𝓝 (sourcePoleResidue χ σ T x ρ)) := by
  classical
  by_cases hχ : χ = 1
  · rw [sourcePoleSupport, if_pos hχ] at hρ
    rcases Finset.mem_insert.mp hρ with hρ1 | hρzero
    · subst ρ
      subst χ
      simpa [sourcePoleResidue] using
        (tendsto_mul_perronContourIntegrand_one (q := q) x hx)
    · have hρne : ρ ≠ 1 := fun heq =>
        (one_not_mem_zeroSupport χ σ T) (heq ▸ hρzero)
      simpa [sourcePoleResidue, hρne] using
        (tendsto_mul_perronContourIntegrand_at_zero χ hx hρzero hσ)
  · rw [sourcePoleSupport, if_neg hχ] at hρ
    simpa [sourcePoleResidue, hχ] using
      (tendsto_mul_perronContourIntegrand_at_zero χ hx hρ hσ)

/-- Explicit boundary nonvanishing pushes every divisor-backed zero off the
left and horizontal edges.  The right edge is already zero-free because
every recorded zero has real part at most one and `c > 1`. -/
theorem sourcePoleSupport_strictly_inside
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ c T : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ∀ ρ ∈ sourcePoleSupport χ σ T,
      σ < ρ.re ∧ ρ.re < c ∧ -T < ρ.im ∧ ρ.im < T := by
  classical
  intro ρ hρ
  by_cases hχ : χ = 1
  · rw [sourcePoleSupport, if_pos hχ] at hρ
    rcases Finset.mem_insert.mp hρ with rfl | hρzero
    · simp only [Complex.one_re, Complex.one_im]
      exact ⟨hσ1, hc, by linarith, hT⟩
    · have hrect := mem_zeroRectangle_of_mem_zeroSupport χ σ T hρzero
      rw [zeroRectangle, Complex.mem_reProdIm] at hrect
      have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
        χ σ T hρzero
      have hreLower : σ < ρ.re := by
        apply lt_of_le_of_ne hrect.1.1
        intro heq
        have hp : ((σ : ℂ) + (ρ.im : ℂ) * Complex.I) = ρ := by
          apply Complex.ext <;> simp
          linarith
        exact (hleftNonzero ρ.im hrect.2)
          ((congrArg (regularizedLFunction χ) hp).trans hzero)
      have himLower : -T < ρ.im := by
        apply lt_of_le_of_ne hrect.2.1
        intro heq
        have hp : ((ρ.re : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) = ρ := by
          apply Complex.ext <;> simp
          linarith
        have hreIcc : ρ.re ∈ Set.Icc σ c :=
          ⟨hrect.1.1, hrect.1.2.trans hc.le⟩
        exact (hbottomNonzero ρ.re hreIcc)
          ((congrArg (regularizedLFunction χ) hp).trans hzero)
      have himUpper : ρ.im < T := by
        apply lt_of_le_of_ne hrect.2.2
        intro heq
        have hp : ((ρ.re : ℂ) + (T : ℂ) * Complex.I) = ρ := by
          apply Complex.ext <;> simp
          linarith
        have hreIcc : ρ.re ∈ Set.Icc σ c :=
          ⟨hrect.1.1, hrect.1.2.trans hc.le⟩
        exact (htopNonzero ρ.re hreIcc)
          ((congrArg (regularizedLFunction χ) hp).trans hzero)
      exact ⟨hreLower, hrect.1.2.trans_lt hc, himLower, himUpper⟩
  · rw [sourcePoleSupport, if_neg hχ] at hρ
    have hrect := mem_zeroRectangle_of_mem_zeroSupport χ σ T hρ
    rw [zeroRectangle, Complex.mem_reProdIm] at hrect
    have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport χ σ T hρ
    have hreLower : σ < ρ.re := by
      apply lt_of_le_of_ne hrect.1.1
      intro heq
      have hp : ((σ : ℂ) + (ρ.im : ℂ) * Complex.I) = ρ := by
        apply Complex.ext <;> simp
        linarith
      exact (hleftNonzero ρ.im hrect.2)
        ((congrArg (regularizedLFunction χ) hp).trans hzero)
    have himLower : -T < ρ.im := by
      apply lt_of_le_of_ne hrect.2.1
      intro heq
      have hp : ((ρ.re : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) = ρ := by
        apply Complex.ext <;> simp
        linarith
      have hreIcc : ρ.re ∈ Set.Icc σ c :=
        ⟨hrect.1.1, hrect.1.2.trans hc.le⟩
      exact (hbottomNonzero ρ.re hreIcc)
        ((congrArg (regularizedLFunction χ) hp).trans hzero)
    have himUpper : ρ.im < T := by
      apply lt_of_le_of_ne hrect.2.2
      intro heq
      have hp : ((ρ.re : ℂ) + (T : ℂ) * Complex.I) = ρ := by
        apply Complex.ext <;> simp
        linarith
      have hreIcc : ρ.re ∈ Set.Icc σ c :=
        ⟨hrect.1.1, hrect.1.2.trans hc.le⟩
      exact (htopNonzero ρ.re hreIcc)
        ((congrArg (regularizedLFunction χ) hp).trans hzero)
    exact ⟨hreLower, hrect.1.2.trans_lt hc, himLower, himUpper⟩

/-- A canonical positive square-excision radius obtained from the four
distances to the outer rectangle. -/
def rectangleInteriorRadius (a b u v : ℝ) (ρ : ℂ) : ℝ :=
  min (min (ρ.re - a) (b - ρ.re))
      (min (ρ.im - u) (v - ρ.im)) / 2

theorem rectangleInteriorRadius_spec
    {a b u v : ℝ} {ρ : ℂ}
    (ha : a < ρ.re) (hb : ρ.re < b)
    (hu : u < ρ.im) (hv : ρ.im < v) :
    0 < rectangleInteriorRadius a b u v ρ ∧
      a < ρ.re - rectangleInteriorRadius a b u v ρ ∧
      ρ.re + rectangleInteriorRadius a b u v ρ < b ∧
      u < ρ.im - rectangleInteriorRadius a b u v ρ ∧
      ρ.im + rectangleInteriorRadius a b u v ρ < v := by
  have hp : 0 < min (min (ρ.re - a) (b - ρ.re))
      (min (ρ.im - u) (v - ρ.im)) := by
    rw [lt_min_iff, lt_min_iff, lt_min_iff]
    constructor
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hleA : min (min (ρ.re - a) (b - ρ.re))
      (min (ρ.im - u) (v - ρ.im)) ≤ ρ.re - a :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hleB : min (min (ρ.re - a) (b - ρ.re))
      (min (ρ.im - u) (v - ρ.im)) ≤ b - ρ.re :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hleU : min (min (ρ.re - a) (b - ρ.re))
      (min (ρ.im - u) (v - ρ.im)) ≤ ρ.im - u :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hleV : min (min (ρ.re - a) (b - ρ.re))
      (min (ρ.im - u) (v - ρ.im)) ≤ v - ρ.im :=
    (min_le_right _ _).trans (min_le_right _ _)
  unfold rectangleInteriorRadius
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Exact specialization of the finite-pole rectangle theorem.  The only
analytic input not discharged here is holomorphy of the canonical removable
extension after subtracting the already certified principal parts.  Boundary
nonvanishing is explicit and is used solely to keep every pole strictly off
the four contour edges. -/
theorem normalizedRectangleBoundary_eq_residueMain_sub_zeroSum
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ c T : ℝ} (hx : 0 < x) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0)
    (hpatched : DifferentiableOn ℂ
      (patchedSourcePerronIntegrand χ σ T x)
      (uIcc σ c ×ℂ uIcc (-T) T)) :
    normalizedRectangleBoundary χ x σ c T =
      residueMain χ x - multiplicityWeightedPerronZeroSum χ σ T x := by
  classical
  let S := sourcePoleSupport χ σ T
  let R : ℂ → ℝ := rectangleInteriorRadius σ c (-T) T
  have hinterior : ∀ ρ ∈ S,
      σ < ρ.re ∧ ρ.re < c ∧ -T < ρ.im ∧ ρ.im < T := by
    simpa only [S] using sourcePoleSupport_strictly_inside χ hσ0 hσ1 hc hT
      hleftNonzero hbottomNonzero htopNonzero
  have hRspec : ∀ ρ ∈ S,
      0 < R ρ ∧ σ < ρ.re - R ρ ∧ ρ.re + R ρ < c ∧
        -T < ρ.im - R ρ ∧ ρ.im + R ρ < T := by
    intro ρ hρ
    have hi := hinterior ρ hρ
    simpa only [R] using rectangleInteriorRadius_spec
      hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hedge (z : ℂ) (hz : z ∉ S) :
      perronContourIntegrand χ x z =
        patchedSourcePerronIntegrand χ σ T x z +
          ∑ ρ ∈ S, sourcePoleResidue χ σ T x ρ * (z - ρ)⁻¹ := by
    simp only [patchedSourcePerronIntegrand, sourcePrincipalPartRemoved,
      show sourcePoleSupport χ σ T = S from rfl, hz, if_false]
    ring
  have hbotEdge : ∀ r : ℝ,
      perronContourIntegrand χ x ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) =
        patchedSourcePerronIntegrand χ σ T x
            ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) +
          ∑ ρ ∈ S, sourcePoleResidue χ σ T x ρ *
            (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - ρ)⁻¹ := by
    intro r
    apply hedge
    intro hz
    have hi := hinterior _ hz
    have him : (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)).im = -T := by simp
    rw [him] at hi
    linarith [hi.2.2.1]
  have htopEdge : ∀ r : ℝ,
      perronContourIntegrand χ x ((r : ℂ) + (T : ℂ) * Complex.I) =
        patchedSourcePerronIntegrand χ σ T x
            ((r : ℂ) + (T : ℂ) * Complex.I) +
          ∑ ρ ∈ S, sourcePoleResidue χ σ T x ρ *
            (((r : ℂ) + (T : ℂ) * Complex.I) - ρ)⁻¹ := by
    intro r
    apply hedge
    intro hz
    have hi := hinterior _ hz
    have him : (((r : ℂ) + (T : ℂ) * Complex.I)).im = T := by simp
    rw [him] at hi
    linarith [hi.2.2.2]
  have hrightEdge : ∀ t : ℝ,
      perronContourIntegrand χ x ((c : ℂ) + (t : ℂ) * Complex.I) =
        patchedSourcePerronIntegrand χ σ T x
            ((c : ℂ) + (t : ℂ) * Complex.I) +
          ∑ ρ ∈ S, sourcePoleResidue χ σ T x ρ *
            (((c : ℂ) + (t : ℂ) * Complex.I) - ρ)⁻¹ := by
    intro t
    apply hedge
    intro hz
    have hi := hinterior _ hz
    have hre : (((c : ℂ) + (t : ℂ) * Complex.I)).re = c := by simp
    rw [hre] at hi
    linarith [hi.2.1]
  have hleftEdge : ∀ t : ℝ,
      perronContourIntegrand χ x ((σ : ℂ) + (t : ℂ) * Complex.I) =
        patchedSourcePerronIntegrand χ σ T x
            ((σ : ℂ) + (t : ℂ) * Complex.I) +
          ∑ ρ ∈ S, sourcePoleResidue χ σ T x ρ *
            (((σ : ℂ) + (t : ℂ) * Complex.I) - ρ)⁻¹ := by
    intro t
    apply hedge
    intro hz
    have hi := hinterior _ hz
    have hre : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
    rw [hre] at hi
    linarith [hi.1]
  have hrect := rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
    S (fun ρ : ℂ => ρ) (sourcePoleResidue χ σ T x) R
    (perronContourIntegrand χ x) (patchedSourcePerronIntegrand χ σ T x)
    σ c (-T) T
    (fun ρ hρ => (hRspec ρ hρ).1)
    (fun ρ hρ => (hRspec ρ hρ).2.1)
    (fun ρ hρ => (hRspec ρ hρ).2.2.1)
    (fun ρ hρ => (hRspec ρ hρ).2.2.2.1)
    (fun ρ hρ => (hRspec ρ hρ).2.2.2.2)
    (boundaryIntervalIntegrable_of_differentiableOn hpatched) hpatched
    hbotEdge htopEdge hrightEdge hleftEdge
  rw [normalizedRectangleBoundary_eq_inv_mul_rectangleBoundaryIntegral χ hx σ c T,
    hrect]
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ htwoPiI, one_mul]
  exact sum_sourcePoleResidue χ σ T x

/-- Paper-facing primitive-character truncated explicit formula.  Every
remainder is still the literal contour or Perron term from the source bridge;
the residue side is exact and multiplicity weighted. -/
theorem twistedMangoldtPrefix_eq_explicit_formula_decomposition
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ)
    {σ c T : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0)
    (hpatched : DifferentiableOn ℂ
      (patchedSourcePerronIntegrand χ σ T (halfIntegerPoint N))
      (uIcc σ c ×ℂ uIcc (-T) T)) :
    APFoundation.twistedMangoldtSum χ (Finset.Icc 1 N) =
      residueMain χ (halfIntegerPoint N) -
        multiplicityWeightedPerronZeroSum χ σ T (halfIntegerPoint N) +
      leftLineIntegral χ (halfIntegerPoint N) σ T -
      horizontalBoundaryIntegral χ (halfIntegerPoint N) σ c T +
      insideKernelError χ N c T -
      coefficientTail χ (halfIntegerPoint N) c T (Finset.Icc 1 N) := by
  rw [twistedMangoldtPrefix_eq_rightLine_add_errors χ N hc]
  rw [rightLineIntegral_eq_boundary_add_left_sub_horizontal]
  rw [normalizedRectangleBoundary_eq_residueMain_sub_zeroSum χ
    (halfIntegerPoint_pos N) hσ0 hσ1 hc hT hleftNonzero
    hbottomNonzero htopNonzero hpatched]

end

end PrimitiveRectangleSpecialization
