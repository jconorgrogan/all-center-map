import KoukTheorem113Residues
import FiniteRemovableExtension

/-!
# The finite negative-left rectangle in Koukoulopoulos Theorem 11.3

This module moves the exact endpoint-regularized integrand across an arbitrary
finite rectangle whose left edge may be negative.  Unlike the older MAP
positive-sigma rectangle, the kernel has no pole at zero and the divisor may
contain the endpoint zero `rho = 0` as well as negative trivial zeros.

The theorem here is the exact finite contour identity.  It assumes only that
the selected four edges contain no zeros; quantitative estimates for sending
the left edge to `-N-1/2` belong to the next layer.
-/

namespace KoukTheorem113NegativeRectangle

open Set Filter Topology Asymptotics Function Complex MeasureTheory
open scoped BigOperators Topology
open DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveRectangleSpecialization FinitePoleRectangle
open PrimitiveTruncatedExplicitFormulaBridge
open FiniteRemovableExtension KoukTheorem113EndpointKernel
open KoukTheorem113Residues

noncomputable section

/-- Subtract every exact endpoint principal part in the chosen rectangle. -/
def endpointPrincipalPartsRemoved {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma T x : ℝ) (s : ℂ) : ℂ :=
  principalPartsRemoved (endpointSourcePoleSupport chi sigma T)
    (endpointSourcePoleResidue chi sigma T x)
    (endpointDecomposedContourIntegrand chi x) s

/-- Patch all finitely many endpoint contour poles simultaneously. -/
def patchedEndpointContourIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma T x : ℝ) (s : ℂ) : ℂ :=
  finiteRemovableExtension (endpointSourcePoleSupport chi sigma T)
    (endpointPrincipalPartsRemoved chi sigma T x) s

private theorem regularizedLFunction_ne_zero_on_rectangle_off_support
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma c T : ℝ} (hsigmac : sigma ≤ c) (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ uIcc sigma c ×ℂ uIcc (-T) T)
    (hzS : z ∉ zeroSupport chi sigma T) :
    regularizedLFunction chi z ≠ 0 := by
  have hz' := Complex.mem_reProdIm.mp hz
  rw [uIcc_of_le hsigmac] at hz'
  rw [uIcc_of_le (by linarith : -T ≤ T)] at hz'
  by_cases hre : z.re ≤ 1
  · have hrect : z ∈ zeroRectangle sigma T := by
      rw [zeroRectangle, Complex.mem_reProdIm]
      exact ⟨⟨hz'.1.1, hre⟩, hz'.2⟩
    intro hzero
    exact hzS ((MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      chi sigma T hrect).mpr hzero)
  · exact regularizedLFunction_ne_zero_of_one_lt_re chi (lt_of_not_ge hre)

/-- The decomposed endpoint integrand is holomorphic off the exact finite
support throughout a rectangle, even when the left edge is negative. -/
theorem differentiableOn_endpointDecomposed_off_support
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma c T : ℝ} (hx : 0 < x) (hsigmac : sigma ≤ c)
    (hT : 0 ≤ T) :
    DifferentiableOn ℂ (endpointDecomposedContourIntegrand chi x)
      ((uIcc sigma c ×ℂ uIcc (-T) T) \
        (↑(endpointSourcePoleSupport chi sigma T) : Set ℂ)) := by
  classical
  intro z hz
  have hzRect := hz.1
  have hzSource := hz.2
  have hzZero : z ∉ zeroSupport chi sigma T := by
    intro hzMem
    apply hzSource
    unfold endpointSourcePoleSupport
    split_ifs <;> simp [hzMem]
  have hreg := regularizedLFunction_ne_zero_on_rectangle_off_support
    chi hsigmac hT hzRect hzZero
  have hregDiff :=
    differentiableAt_endpointRegularizedContourIntegrand chi hx hreg
  have hpoleDiff : DifferentiableAt ℂ
      (endpointPrincipalPoleIntegrand chi x) z := by
    by_cases hchi : chi = 1
    · have hz1 : z ≠ 1 := by
        intro hzEq
        subst z
        apply hzSource
        simp [endpointSourcePoleSupport, hchi]
      exact differentiableAt_endpointPrincipalPoleIntegrand chi hx hz1
    · unfold endpointPrincipalPoleIntegrand
      simpa only [hchi, if_false] using
        (differentiableAt_const (c := (0 : ℂ)))
  exact (hregDiff.add hpoleDiff).differentiableWithinAt

/-- Removing the finite principal-part sum is holomorphic away from the
support. -/
theorem differentiableOn_endpointPrincipalPartsRemoved_off_support
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma c T : ℝ} (hx : 0 < x) (hsigmac : sigma ≤ c)
    (hT : 0 ≤ T) :
    DifferentiableOn ℂ (endpointPrincipalPartsRemoved chi sigma T x)
      ((uIcc sigma c ×ℂ uIcc (-T) T) \
        (↑(endpointSourcePoleSupport chi sigma T) : Set ℂ)) := by
  classical
  intro z hz
  have hsource := differentiableOn_endpointDecomposed_off_support
    chi hx hsigmac hT z hz
  have hsum : DifferentiableAt ℂ
      (fun s => ∑ rho ∈ endpointSourcePoleSupport chi sigma T,
        endpointSourcePoleResidue chi sigma T x rho * (s - rho)⁻¹) z := by
    apply DifferentiableAt.fun_sum
    intro rho hrho
    apply DifferentiableAt.const_mul
    exact (differentiableAt_id.sub_const rho).inv
      (sub_ne_zero.mpr fun h => by
        apply hz.2
        have hzrho : z = rho := by simpa only [id_eq] using h
        simpa [hzrho] using hrho)
  exact hsource.sub hsum.differentiableWithinAt

/-- Boundary nonvanishing places every zero and the possible principal pole
strictly inside the rectangle.  No positivity assumption on `sigma` occurs. -/
theorem endpointSourcePoleSupport_strictly_inside
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma c T : ℝ} (hsigma1 : sigma < 1) (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ∀ rho ∈ endpointSourcePoleSupport chi sigma T,
      sigma < rho.re ∧ rho.re < c ∧ -T < rho.im ∧ rho.im < T := by
  classical
  have hzeroInterior : ∀ rho ∈ zeroSupport chi sigma T,
      sigma < rho.re ∧ rho.re < c ∧ -T < rho.im ∧ rho.im < T := by
    intro rho hrho
    have hrect := mem_zeroRectangle_of_mem_zeroSupport chi sigma T hrho
    rw [zeroRectangle, Complex.mem_reProdIm] at hrect
    have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
      chi sigma T hrho
    have hreLower : sigma < rho.re := by
      apply lt_of_le_of_ne hrect.1.1
      intro heq
      have hp : ((sigma : ℂ) + (rho.im : ℂ) * Complex.I) = rho := by
        apply Complex.ext <;> simp
        linarith
      exact (hleftNonzero rho.im hrect.2)
        ((congrArg (regularizedLFunction chi) hp).trans hzero)
    have hreIcc : rho.re ∈ Set.Icc sigma c :=
      ⟨hrect.1.1, hrect.1.2.trans hc.le⟩
    have himLower : -T < rho.im := by
      apply lt_of_le_of_ne hrect.2.1
      intro heq
      have hp : ((rho.re : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) = rho := by
        apply Complex.ext <;> simp
        linarith
      exact (hbottomNonzero rho.re hreIcc)
        ((congrArg (regularizedLFunction chi) hp).trans hzero)
    have himUpper : rho.im < T := by
      apply lt_of_le_of_ne hrect.2.2
      intro heq
      have hp : ((rho.re : ℂ) + (T : ℂ) * Complex.I) = rho := by
        apply Complex.ext <;> simp
        linarith
      exact (htopNonzero rho.re hreIcc)
        ((congrArg (regularizedLFunction chi) hp).trans hzero)
    exact ⟨hreLower, hrect.1.2.trans_lt hc, himLower, himUpper⟩
  intro rho hrho
  by_cases hchi : chi = 1
  · rw [endpointSourcePoleSupport, if_pos hchi] at hrho
    rcases Finset.mem_insert.mp hrho with hrho1 | hrhoZero
    · subst rho
      simp only [Complex.one_re, Complex.one_im]
      exact ⟨hsigma1, hc, by linarith, hT⟩
    · exact hzeroInterior rho hrhoZero
  · rw [endpointSourcePoleSupport, if_neg hchi] at hrho
    exact hzeroInterior rho hrho

/-- The canonical simultaneous removable extension is holomorphic on a
negative-left rectangle. -/
theorem differentiableOn_patchedEndpointContourIntegrand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma c T : ℝ} (hx : 0 < x) (hsigma1 : sigma < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    DifferentiableOn ℂ (patchedEndpointContourIntegrand chi sigma T x)
      (uIcc sigma c ×ℂ uIcc (-T) T) := by
  classical
  let S : Finset ℂ := endpointSourcePoleSupport chi sigma T
  let residue : ℂ → ℂ := endpointSourcePoleResidue chi sigma T x
  let f : ℂ → ℂ := endpointDecomposedContourIntegrand chi x
  let g : ℂ → ℂ := principalPartsRemoved S residue f
  let U : Set ℂ := uIcc sigma c ×ℂ uIcc (-T) T
  have hsigmac : sigma ≤ c := (hsigma1.trans hc).le
  have hinteriorCoords : ∀ rho ∈ S,
      sigma < rho.re ∧ rho.re < c ∧ -T < rho.im ∧ rho.im < T := by
    simpa only [S] using endpointSourcePoleSupport_strictly_inside
      chi hsigma1 hc hT hleftNonzero hbottomNonzero htopNonzero
  have hInterior : ∀ rho ∈ S, U ∈ nhds rho := by
    intro rho hrho
    have hi := hinteriorCoords rho hrho
    have hopen : (Set.Ioo sigma c ×ℂ Set.Ioo (-T) T) ∈ nhds rho :=
      (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds
        (Complex.mem_reProdIm.mpr
          ⟨⟨hi.1, hi.2.1⟩, ⟨hi.2.2.1, hi.2.2.2⟩⟩)
    apply Filter.mem_of_superset hopen
    intro z hz
    have hz' := Complex.mem_reProdIm.mp hz
    apply Complex.mem_reProdIm.mpr
    rw [uIcc_of_le hsigmac, uIcc_of_le (by linarith : -T ≤ T)]
    exact ⟨⟨hz'.1.1.le, hz'.1.2.le⟩,
      ⟨hz'.2.1.le, hz'.2.2.le⟩⟩
  have hDiff : DifferentiableOn ℂ g (U \ (↑S : Set ℂ)) := by
    simpa only [g, U, S, residue, f, endpointPrincipalPartsRemoved,
      principalPartsRemoved, principalPartSum] using!
      differentiableOn_endpointPrincipalPartsRemoved_off_support
        chi hx hsigmac hT.le
  have hLittle : ∀ rho ∈ S,
      (fun z => g z - g rho) =o[𝓝[≠] rho] fun z => (z - rho)⁻¹ := by
    intro rho hrho
    apply principalPartsRemoved_isLittleO (S := S) residue f hrho
    have hres :=
      tendsto_mul_endpointDecomposedContourIntegrand_at_sourcePole
        chi hx (show rho ∈ endpointSourcePoleSupport chi sigma T by
          simpa only [S] using hrho)
    simpa only [f, residue] using hres
  have hfinal := differentiableOn_finiteRemovableExtension
    (S := S) U g hInterior hDiff hLittle
  simpa only [patchedEndpointContourIntegrand, finiteRemovableExtension,
    endpointPrincipalPartsRemoved, principalPartsRemoved, principalPartSum,
    S, residue, f, g, U] using! hfinal

/-- The normalized boundary of the endpoint-regularized rectangle. -/
def normalizedEndpointRectangleBoundary {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x sigma c T : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    rectangleBoundaryIntegral (endpointDecomposedContourIntegrand chi x)
      sigma c (-T) T

/-- Exact finite negative-left contour identity, with every zero counted by
analytic multiplicity and the endpoint value at `rho = 0` already regularized.
The left edge may lie anywhere below `1`. -/
theorem normalizedEndpointRectangleBoundary_eq_main_sub_zeroSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma c T : ℝ} (hx : 0 < x) (hsigma1 : sigma < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    normalizedEndpointRectangleBoundary chi x sigma c T =
      (if chi = 1 then endpointPerronKernel x 1 else 0) -
        ∑ rho ∈ zeroSupport chi sigma T,
          (zeroMultiplicity chi sigma T rho : ℂ) *
            endpointPerronKernel x rho := by
  classical
  let S := endpointSourcePoleSupport chi sigma T
  let R : ℂ → ℝ := rectangleInteriorRadius sigma c (-T) T
  have hinterior : ∀ rho ∈ S,
      sigma < rho.re ∧ rho.re < c ∧ -T < rho.im ∧ rho.im < T := by
    simpa only [S] using endpointSourcePoleSupport_strictly_inside
      chi hsigma1 hc hT hleftNonzero hbottomNonzero htopNonzero
  have hRspec : ∀ rho ∈ S,
      0 < R rho ∧ sigma < rho.re - R rho ∧ rho.re + R rho < c ∧
        -T < rho.im - R rho ∧ rho.im + R rho < T := by
    intro rho hrho
    have hi := hinterior rho hrho
    simpa only [R] using rectangleInteriorRadius_spec
      hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hedge (z : ℂ) (hz : z ∉ S) :
      endpointDecomposedContourIntegrand chi x z =
        patchedEndpointContourIntegrand chi sigma T x z +
          ∑ rho ∈ S, endpointSourcePoleResidue chi sigma T x rho *
            (z - rho)⁻¹ := by
    have hz' : z ∉ endpointSourcePoleSupport chi sigma T := by
      simpa only [S] using hz
    rw [patchedEndpointContourIntegrand, finiteRemovableExtension,
      if_neg hz']
    simp only [
      endpointPrincipalPartsRemoved, principalPartsRemoved,
      principalPartSum, show endpointSourcePoleSupport chi sigma T = S from rfl]
    ring
  have hbotEdge : ∀ r : ℝ,
      endpointDecomposedContourIntegrand chi x
          ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) =
        patchedEndpointContourIntegrand chi sigma T x
            ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) +
          ∑ rho ∈ S, endpointSourcePoleResidue chi sigma T x rho *
            (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho)⁻¹ := by
    intro r
    apply hedge
    intro hz
    have hi := hinterior _ hz
    have him : (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)).im = -T := by
      simp
    rw [him] at hi
    linarith [hi.2.2.1]
  have htopEdge : ∀ r : ℝ,
      endpointDecomposedContourIntegrand chi x
          ((r : ℂ) + (T : ℂ) * Complex.I) =
        patchedEndpointContourIntegrand chi sigma T x
            ((r : ℂ) + (T : ℂ) * Complex.I) +
          ∑ rho ∈ S, endpointSourcePoleResidue chi sigma T x rho *
            (((r : ℂ) + (T : ℂ) * Complex.I) - rho)⁻¹ := by
    intro r
    apply hedge
    intro hz
    have hi := hinterior _ hz
    have him : (((r : ℂ) + (T : ℂ) * Complex.I)).im = T := by simp
    rw [him] at hi
    linarith [hi.2.2.2]
  have hrightEdge : ∀ t : ℝ,
      endpointDecomposedContourIntegrand chi x
          ((c : ℂ) + (t : ℂ) * Complex.I) =
        patchedEndpointContourIntegrand chi sigma T x
            ((c : ℂ) + (t : ℂ) * Complex.I) +
          ∑ rho ∈ S, endpointSourcePoleResidue chi sigma T x rho *
            (((c : ℂ) + (t : ℂ) * Complex.I) - rho)⁻¹ := by
    intro t
    apply hedge
    intro hz
    have hi := hinterior _ hz
    have hre : (((c : ℂ) + (t : ℂ) * Complex.I)).re = c := by simp
    rw [hre] at hi
    linarith [hi.2.1]
  have hleftEdge : ∀ t : ℝ,
      endpointDecomposedContourIntegrand chi x
          ((sigma : ℂ) + (t : ℂ) * Complex.I) =
        patchedEndpointContourIntegrand chi sigma T x
            ((sigma : ℂ) + (t : ℂ) * Complex.I) +
          ∑ rho ∈ S, endpointSourcePoleResidue chi sigma T x rho *
            (((sigma : ℂ) + (t : ℂ) * Complex.I) - rho)⁻¹ := by
    intro t
    apply hedge
    intro hz
    have hi := hinterior _ hz
    have hre : (((sigma : ℂ) + (t : ℂ) * Complex.I)).re = sigma := by simp
    rw [hre] at hi
    linarith [hi.1]
  have hpatched := differentiableOn_patchedEndpointContourIntegrand
    chi hx hsigma1 hc hT hleftNonzero hbottomNonzero htopNonzero
  have hrect := rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
    S (fun rho : ℂ => rho) (endpointSourcePoleResidue chi sigma T x) R
    (endpointDecomposedContourIntegrand chi x)
    (patchedEndpointContourIntegrand chi sigma T x)
    sigma c (-T) T
    (fun rho hrho => (hRspec rho hrho).1)
    (fun rho hrho => (hRspec rho hrho).2.1)
    (fun rho hrho => (hRspec rho hrho).2.2.1)
    (fun rho hrho => (hRspec rho hrho).2.2.2.1)
    (fun rho hrho => (hRspec rho hrho).2.2.2.2)
    (boundaryIntervalIntegrable_of_differentiableOn hpatched) hpatched
    hbotEdge htopEdge hrightEdge hleftEdge
  unfold normalizedEndpointRectangleBoundary
  rw [hrect]
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ htwoPiI, one_mul]
  exact sum_endpointSourcePoleResidue chi sigma T x

end
end KoukTheorem113NegativeRectangle
