import FiniteRemovableExtension

/-!
# Removal of every source Perron pole in a finite rectangle
-/

namespace PrimitiveRemovableClosure

open Set Filter Topology Asymptotics Function Complex
open scoped BigOperators
open DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge
open PrimitiveRectangleSpecialization
open FiniteRemovableExtension
open TruncatedTwistedPerron

noncomputable section

private theorem regularizedLFunction_ne_zero_on_rectangle_off_support
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ c T : ℝ} (hσc : σ ≤ c) (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ uIcc σ c ×ℂ uIcc (-T) T)
    (hzS : z ∉ zeroSupport χ σ T) :
    regularizedLFunction χ z ≠ 0 := by
  have hz' := Complex.mem_reProdIm.mp hz
  rw [uIcc_of_le hσc] at hz'
  rw [uIcc_of_le (by linarith : -T ≤ T)] at hz'
  by_cases hre : z.re ≤ 1
  · have hrect : z ∈ zeroRectangle σ T := by
      rw [zeroRectangle, Complex.mem_reProdIm]
      exact ⟨⟨hz'.1.1, hre⟩, hz'.2⟩
    intro hzero
    exact hzS ((MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      χ σ T hrect).mpr hzero)
  · exact regularizedLFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge hre)

private theorem LFunction_ne_zero_of_regularized_ne_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ}
    (hz1 : z ≠ 1) (hreg : regularizedLFunction χ z ≠ 0) :
    DirichletCharacter.LFunction χ z ≠ 0 := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    intro hL
    apply hreg
    simp only [regularizedLFunction, if_pos]
    unfold DirichletCharacter.LFunctionTrivChar₁
    rw [Function.update_of_ne hz1]
    have hL' : DirichletCharacter.LFunctionTrivChar q z = 0 := by
      simpa using hL
    rw [hL', mul_zero]
  · simpa [regularizedLFunction, hχ] using hreg

private theorem differentiableAt_regularizedPerronContourIntegrand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {z : ℂ} (hz0 : z ≠ 0)
    (hreg : regularizedLFunction χ z ≠ 0) :
    DifferentiableAt ℂ (regularizedPerronContourIntegrand χ x) z := by
  have han := (differentiable_regularizedLFunction χ).analyticAt z
  have hlog : DifferentiableAt ℂ
      (logDeriv (regularizedLFunction χ)) z := by
    rw [show logDeriv (regularizedLFunction χ) =
      fun s => deriv (regularizedLFunction χ) s /
        regularizedLFunction χ s by rfl]
    exact han.deriv.differentiableAt.div han.differentiableAt hreg
  have hpow : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) z :=
    (differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))) z
  simpa only [regularizedPerronContourIntegrand] using
    (hlog.neg.mul hpow).div differentiableAt_id hz0

private theorem differentiableAt_principalPoleIntegrand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    DifferentiableAt ℂ (principalPoleIntegrand χ x) z := by
  classical
  by_cases hχ : χ = 1
  · unfold principalPoleIntegrand
    have hpow : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) z :=
      (differentiable_id.const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))) z
    simpa only [hχ, if_true] using hpow.div
        (differentiableAt_id.mul (differentiableAt_id.sub_const 1))
        (mul_ne_zero hz0 (sub_ne_zero.mpr hz1))
  · unfold principalPoleIntegrand
    have hzero : DifferentiableAt ℂ (fun _s : ℂ => (0 : ℂ)) z :=
      differentiableAt_const (c := (0 : ℂ))
    simpa only [hχ, if_false] using hzero

private theorem differentiableAt_perronContourIntegrand_of_regularized_ne_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) (hreg : regularizedLFunction χ z ≠ 0) :
    DifferentiableAt ℂ (perronContourIntegrand χ x) z := by
  have hregDiff := differentiableAt_regularizedPerronContourIntegrand χ hx hz0 hreg
  have hpoleDiff := differentiableAt_principalPoleIntegrand χ hx hz0 hz1
  have hsum := hregDiff.add hpoleDiff
  have hregEventually : ∀ᶠ s in nhds z, regularizedLFunction χ s ≠ 0 :=
    ((differentiable_regularizedLFunction χ).continuous.continuousAt.eventually_ne hreg)
  have hs1 : ∀ᶠ s in nhds z, s ≠ 1 := eventually_ne_nhds hz1
  have heq : perronContourIntegrand χ x =ᶠ[nhds z]
      fun s => regularizedPerronContourIntegrand χ x s +
        principalPoleIntegrand χ x s := by
    filter_upwards [hregEventually, hs1] with s hregs hs
    exact perronContourIntegrand_eq_regularized_add_principal χ hs
      (LFunction_ne_zero_of_regularized_ne_zero χ hs hregs)
  exact hsum.congr_of_eventuallyEq heq

/-- The literal (unpatched) Perron contour integrand is holomorphic at every
point away from `0`, the possible principal pole at `1`, and the zeros of the
regularized primitive `L`-function.  This is public because parameter-dependent
contour integrals use it to derive measurability from the same nonvanishing
data used by the contour identity. -/
theorem differentiableAt_perronContourIntegrand_of_regularized_ne_zero_public
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) (hreg : regularizedLFunction χ z ≠ 0) :
    DifferentiableAt ℂ (perronContourIntegrand χ x) z :=
  differentiableAt_perronContourIntegrand_of_regularized_ne_zero
    χ hx hz0 hz1 hreg

/-- Away from the actual finite source pole set, subtracting the finite
principal-part sum leaves a holomorphic function on the rectangle. -/
theorem differentiableOn_sourcePrincipalPartRemoved_off_support
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ c T : ℝ} (hx : 0 < x) (hσ : 0 < σ)
    (hσc : σ ≤ c) (hT : 0 ≤ T) :
    DifferentiableOn ℂ (sourcePrincipalPartRemoved χ σ T x)
      ((uIcc σ c ×ℂ uIcc (-T) T) \
        (↑(sourcePoleSupport χ σ T) : Set ℂ)) := by
  classical
  intro z hz
  have hzRect := hz.1
  have hzSource : z ∉ sourcePoleSupport χ σ T := hz.2
  have hzZero : z ∉ zeroSupport χ σ T := by
    intro hzMem
    apply hzSource
    unfold sourcePoleSupport
    split_ifs <;> simp [hzMem]
  have hzcoord := Complex.mem_reProdIm.mp hzRect
  rw [uIcc_of_le hσc] at hzcoord
  have hz0 : z ≠ 0 := by
    intro hzEq
    subst z
    simp at hzcoord
    linarith [hzcoord.1.1]
  have hreg := regularizedLFunction_ne_zero_on_rectangle_off_support
    χ hσc hT hzRect hzZero
  have hsource : DifferentiableAt ℂ (perronContourIntegrand χ x) z := by
    by_cases hχ : χ = 1
    · have hz1 : z ≠ 1 := by
        intro hzEq
        subst z
        apply hzSource
        simp [sourcePoleSupport, hχ]
      exact differentiableAt_perronContourIntegrand_of_regularized_ne_zero
        χ hx hz0 hz1 hreg
    · have hregDiff :=
        differentiableAt_regularizedPerronContourIntegrand χ hx hz0 hreg
      have heq : perronContourIntegrand χ x =
          regularizedPerronContourIntegrand χ x := by
        funext s
        simp [perronContourIntegrand, regularizedPerronContourIntegrand,
          regularizedLFunction, hχ]
      exact hregDiff.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => congrFun heq s)
  have hsum : DifferentiableAt ℂ
      (fun s => ∑ ρ ∈ sourcePoleSupport χ σ T,
        sourcePoleResidue χ σ T x ρ * (s - ρ)⁻¹) z := by
    apply DifferentiableAt.fun_sum
    intro ρ hρ
    apply DifferentiableAt.const_mul
    exact (differentiableAt_id.sub_const ρ).inv
      (sub_ne_zero.mpr fun h => by
        apply hzSource
        have hzρ : z = ρ := by simpa only [id_eq] using h
        simpa [hzρ] using hρ)
  exact (hsource.sub hsum).differentiableWithinAt

/-- The canonical simultaneous `limUnder` patch of the actual source Perron
integrand is holomorphic on the whole closed rectangle.  This discharges the
last equality-side premise in the staged primitive explicit formula. -/
theorem differentiableOn_patchedSourcePerronIntegrand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ c T : ℝ} (hx : 0 < x) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    DifferentiableOn ℂ (patchedSourcePerronIntegrand χ σ T x)
      (uIcc σ c ×ℂ uIcc (-T) T) := by
  classical
  let S : Finset ℂ := sourcePoleSupport χ σ T
  let residue : ℂ → ℂ := sourcePoleResidue χ σ T x
  let f : ℂ → ℂ := perronContourIntegrand χ x
  let g : ℂ → ℂ := principalPartsRemoved S residue f
  let U : Set ℂ := uIcc σ c ×ℂ uIcc (-T) T
  have hσc : σ ≤ c := le_trans hσ1.le hc.le
  have hinteriorCoords : ∀ ρ ∈ S,
      σ < ρ.re ∧ ρ.re < c ∧ -T < ρ.im ∧ ρ.im < T := by
    simpa only [S] using sourcePoleSupport_strictly_inside χ hσ0 hσ1 hc hT
      hleftNonzero hbottomNonzero htopNonzero
  have hInterior : ∀ ρ ∈ S, U ∈ nhds ρ := by
    intro ρ hρ
    have hi := hinteriorCoords ρ hρ
    have hopen : (Set.Ioo σ c ×ℂ Set.Ioo (-T) T) ∈ nhds ρ :=
      (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds
        (Complex.mem_reProdIm.mpr ⟨⟨hi.1, hi.2.1⟩,
          ⟨hi.2.2.1, hi.2.2.2⟩⟩)
    apply Filter.mem_of_superset hopen
    intro z hz
    have hz' := Complex.mem_reProdIm.mp hz
    apply Complex.mem_reProdIm.mpr
    dsimp only [U]
    rw [uIcc_of_le hσc, uIcc_of_le (by linarith : -T ≤ T)]
    exact ⟨⟨hz'.1.1.le, hz'.1.2.le⟩, ⟨hz'.2.1.le, hz'.2.2.le⟩⟩
  have hDiff : DifferentiableOn ℂ g (U \ (↑S : Set ℂ)) := by
    simpa only [g, U, S, residue, f, principalPartsRemoved,
      principalPartSum, sourcePrincipalPartRemoved] using
      differentiableOn_sourcePrincipalPartRemoved_off_support
        χ hx hσ0 hσc hT.le
  have hLittle : ∀ ρ ∈ S,
      (fun z => g z - g ρ) =o[𝓝[≠] ρ] fun z => (z - ρ)⁻¹ := by
    intro ρ hρ
    apply principalPartsRemoved_isLittleO (S := S) residue f hρ
    have hres := tendsto_mul_perronContourIntegrand_at_sourcePole
      χ hx hσ0 (show ρ ∈ sourcePoleSupport χ σ T by simpa only [S] using hρ)
    simpa only [f, residue] using hres
  have hfinal := differentiableOn_finiteRemovableExtension
    (S := S) U g hInterior hDiff hLittle
  simpa only [patchedSourcePerronIntegrand, finiteRemovableExtension,
    sourcePrincipalPartRemoved, principalPartsRemoved, principalPartSum,
    S, residue, f, g, U] using hfinal

/-- Premise-free finite-pole rectangle equality: the removable-extension
holomorphy required by the geometric specialization is now derived above. -/
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
      regularizedLFunction χ ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    normalizedRectangleBoundary χ x σ c T =
      residueMain χ x - multiplicityWeightedPerronZeroSum χ σ T x := by
  exact PrimitiveRectangleSpecialization.normalizedRectangleBoundary_eq_residueMain_sub_zeroSum
    χ hx hσ0 hσ1 hc hT hleftNonzero hbottomNonzero htopNonzero
    (differentiableOn_patchedSourcePerronIntegrand χ hx hσ0 hσ1 hc hT
      hleftNonzero hbottomNonzero htopNonzero)

/-- Paper-facing primitive-character truncated explicit formula with no
removable-singularity premise.  The only hypotheses are the legal rectangle
geometry and literal nonvanishing on its left and horizontal edges. -/
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
      regularizedLFunction χ ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    APFoundation.twistedMangoldtSum χ (Finset.Icc 1 N) =
      residueMain χ (halfIntegerPoint N) -
        multiplicityWeightedPerronZeroSum χ σ T (halfIntegerPoint N) +
      leftLineIntegral χ (halfIntegerPoint N) σ T -
      horizontalBoundaryIntegral χ (halfIntegerPoint N) σ c T +
      insideKernelError χ N c T -
      coefficientTail χ (halfIntegerPoint N) c T (Finset.Icc 1 N) := by
  exact PrimitiveRectangleSpecialization.twistedMangoldtPrefix_eq_explicit_formula_decomposition
    χ N hσ0 hσ1 hc hT hleftNonzero hbottomNonzero htopNonzero
    (differentiableOn_patchedSourcePerronIntegrand χ
      (halfIntegerPoint_pos N) hσ0 hσ1 hc hT hleftNonzero
      hbottomNonzero htopNonzero)

end

end PrimitiveRemovableClosure
