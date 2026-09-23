import KoukTheorem113EndpointKernel
import ZeroDistanceLogDerivativeBounds

/-!
# Exact residues for the endpoint-regularized Koukoulopoulos contour

This file identifies every finite residue of

`-(L'/L)(s) * (x^s - 1) / s`

with analytic multiplicity retained.  In particular, a zero at `rho = 0`
contributes `-m * log x`, while the principal pole at `s = 1` contributes
`x - 1`.  The latter is the exact contour residue; the harmless `+1` needed
to display the conventional main term `x` belongs in the final remainder
normalization, not in the residue computation.
-/

namespace KoukTheorem113Residues

open Complex Set Filter
open scoped BigOperators Topology
open DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveRectangleSpecialization
open KoukTheorem113EndpointKernel

noncomputable section

/-- The zero-divisor part of the endpoint-regularized integrand. -/
def endpointRegularizedContourIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  (-logDeriv (regularizedLFunction chi) s) * endpointPerronKernel x s

/-- The separated principal-character pole for the endpoint kernel. -/
def endpointPrincipalPoleIntegrand {q : ℕ}
    (chi : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  @ite ℂ (chi = 1) (Classical.propDecidable _)
    (endpointPerronKernel x s / (s - 1)) 0

/-- The meromorphic function used for the residue argument.  It agrees with
the literal source integrand off `0`, `1`, and the zeros of `L`, while its two
summands expose all poles without dividing by the removable endpoint. -/
def endpointDecomposedContourIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  endpointRegularizedContourIntegrand chi x s +
    endpointPrincipalPoleIntegrand chi x s

/-- Holomorphy of the regularized summand away from divisor zeros. -/
theorem differentiableAt_endpointRegularizedContourIntegrand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hreg : regularizedLFunction chi s ≠ 0) :
    DifferentiableAt ℂ (endpointRegularizedContourIntegrand chi x) s := by
  have han := (differentiable_regularizedLFunction chi).analyticAt s
  have hlog : DifferentiableAt ℂ
      (logDeriv (regularizedLFunction chi)) s := by
    simpa only [logDeriv, Pi.div_apply] using
      (han.deriv.div han hreg).differentiableAt
  unfold endpointRegularizedContourIntegrand
  exact hlog.neg.mul (differentiable_endpointPerronKernel hx s)

/-- Holomorphy of the separated principal term away from `1`. -/
theorem differentiableAt_endpointPrincipalPoleIntegrand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (endpointPrincipalPoleIntegrand chi x) s := by
  classical
  by_cases hchi : chi = 1
  · unfold endpointPrincipalPoleIntegrand
    simpa only [hchi, if_true] using!
      (differentiable_endpointPerronKernel hx s).div
        (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1)
  · unfold endpointPrincipalPoleIntegrand
    simpa only [hchi, if_false] using
      (differentiableAt_const (c := (0 : ℂ)))

/-- Away from `0`, `1`, and source zeros, the literal source integrand
splits into its globally analytic regularization and the principal pole. -/
theorem endpointPerronContourIntegrand_eq_regularized_add_principal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x : ℝ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hL : DirichletCharacter.LFunction chi s ≠ 0) :
    endpointPerronContourIntegrand chi x s =
      endpointRegularizedContourIntegrand chi x s +
        endpointPrincipalPoleIntegrand chi x s := by
  have hlog :=
    ZeroDistanceLogDerivativeBounds.neg_logDeriv_LFunction_eq_regularized_add_principalCorrection
      chi hs0 hs1 hL
  unfold endpointPerronContourIntegrand endpointRegularizedContourIntegrand
    endpointPrincipalPoleIntegrand
  rw [hlog]
  by_cases hchi : chi = 1 <;> simp only [hchi, if_true, if_false]
  · ring
  · ring

/-- The regularized endpoint integrand has residue `-m K_x(rho)` at every
divisor-backed zero, including the zero endpoint. -/
theorem tendsto_mul_endpointRegularizedContourIntegrand_at_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma T : ℝ} (hx : 0 < x) {rho : ℂ}
    (hrho : rho ∈ zeroSupport chi sigma T) :
    Tendsto
      (fun s => (s - rho) * endpointRegularizedContourIntegrand chi x s)
      (𝓝[≠] rho)
      (𝓝 (-(zeroMultiplicity chi sigma T rho : ℂ) *
        endpointPerronKernel x rho)) := by
  have hlog := tendsto_mul_neg_logDeriv_regularizedLFunction
    chi sigma T hrho
  have hker : Tendsto (endpointPerronKernel x) (𝓝[≠] rho)
      (𝓝 (endpointPerronKernel x rho)) :=
    ((differentiable_endpointPerronKernel hx rho).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
  have hmul := hlog.mul hker
  apply hmul.congr'
  filter_upwards with s
  unfold endpointRegularizedContourIntegrand
  ring

/-- The endpoint principal pole has the exact residue `x - 1`. -/
theorem tendsto_mul_endpointPrincipalPoleIntegrand_one
    {q : ℕ} [NeZero q] (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun s => (s - 1) *
        endpointPrincipalPoleIntegrand (1 : DirichletCharacter ℂ q) x s)
      (𝓝[≠] (1 : ℂ)) (𝓝 ((x : ℂ) - 1)) := by
  have hker : Tendsto (endpointPerronKernel x) (𝓝[≠] (1 : ℂ))
      (𝓝 (endpointPerronKernel x 1)) :=
    ((differentiable_endpointPerronKernel hx 1).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
  have hvalue : endpointPerronKernel x 1 = (x : ℂ) - 1 := by
    rw [endpointPerronKernel_of_ne one_ne_zero]
    simp
  rw [hvalue] at hker
  apply hker.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  unfold endpointPrincipalPoleIntegrand
  rw [if_pos rfl]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  exact (mul_div_cancel₀ (endpointPerronKernel x s) hsub).symm

/-- At every point other than `1`, the separated principal term has zero
residue.  No exclusion of `rho = 0` is needed because the endpoint kernel is
holomorphic there. -/
theorem tendsto_sub_mul_endpointPrincipalPoleIntegrand_at_other
    {q : ℕ} [NeZero q] (x : ℝ) (hx : 0 < x) {rho : ℂ}
    (hrho1 : rho ≠ 1) :
    Tendsto
      (fun s => (s - rho) *
        endpointPrincipalPoleIntegrand (1 : DirichletCharacter ℂ q) x s)
      (𝓝[≠] rho) (𝓝 0) := by
  have hsub : Tendsto (fun s : ℂ => s - rho) (𝓝[≠] rho) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℂ => s - rho) rho :=
      (continuousAt_id.sub
        (continuousAt_const : ContinuousAt (fun _s : ℂ => rho) rho))
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] rho) (𝓝 (rho - 1)) :=
    ((continuousAt_id.sub
      (continuousAt_const : ContinuousAt (fun _s : ℂ => (1 : ℂ)) rho)).tendsto.mono_left
        nhdsWithin_le_nhds)
  have hker : Tendsto (endpointPerronKernel x) (𝓝[≠] rho)
      (𝓝 (endpointPerronKernel x rho)) :=
    ((differentiable_endpointPerronKernel hx rho).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
  have hquot := hker.div hden (sub_ne_zero.mpr hrho1)
  have hmul := hsub.mul hquot
  simpa [endpointPrincipalPoleIntegrand] using! hmul

/-- Multiplying a holomorphic regularized summand by `s-rho` gives zero. -/
theorem tendsto_sub_mul_endpointRegularizedContourIntegrand_of_nonzero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {rho : ℂ}
    (hreg : regularizedLFunction chi rho ≠ 0) :
    Tendsto
      (fun s => (s - rho) * endpointRegularizedContourIntegrand chi x s)
      (𝓝[≠] rho) (𝓝 0) := by
  have hsub : Tendsto (fun s : ℂ => s - rho) (𝓝[≠] rho) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℂ => s - rho) rho :=
      continuousAt_id.sub
        (continuousAt_const : ContinuousAt (fun _s : ℂ => rho) rho)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hint : Tendsto (endpointRegularizedContourIntegrand chi x)
      (𝓝[≠] rho) (𝓝 (endpointRegularizedContourIntegrand chi x rho)) :=
    ((differentiableAt_endpointRegularizedContourIntegrand chi hx hreg).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
  simpa using hsub.mul hint

/-- Pole support for a finite endpoint contour: all divisor-backed zeros,
plus `1` exactly for the principal character. -/
def endpointSourcePoleSupport {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma T : ℝ) : Finset ℂ :=
  if chi = 1 then insert 1 (zeroSupport chi sigma T)
  else zeroSupport chi sigma T

/-- Exact multiplicity-aware residue attached to the endpoint contour. -/
def endpointSourcePoleResidue {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma T x : ℝ) (rho : ℂ) : ℂ :=
  if chi = 1 ∧ rho = 1 then endpointPerronKernel x 1
  else -(zeroMultiplicity chi sigma T rho : ℂ) * endpointPerronKernel x rho

/-- Every member of the endpoint pole support has exactly its advertised
residue, with no simple-zero assumption. -/
theorem tendsto_mul_endpointDecomposedContourIntegrand_at_sourcePole
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T x : ℝ} (hx : 0 < x) {rho : ℂ}
    (hrho : rho ∈ endpointSourcePoleSupport chi sigma T) :
    Tendsto
      (fun s => (s - rho) * endpointDecomposedContourIntegrand chi x s)
      (𝓝[≠] rho) (𝓝 (endpointSourcePoleResidue chi sigma T x rho)) := by
  classical
  by_cases hchi : chi = 1
  · rw [endpointSourcePoleSupport, if_pos hchi] at hrho
    rcases Finset.mem_insert.mp hrho with hrho1 | hrhoZero
    · subst rho
      subst chi
      have hreg := regularizedLFunction_one_ne_zero
        (1 : DirichletCharacter ℂ q)
      have hzero :=
        tendsto_sub_mul_endpointRegularizedContourIntegrand_of_nonzero
          (1 : DirichletCharacter ℂ q) hx hreg
      have hprincipal :=
        tendsto_mul_endpointPrincipalPoleIntegrand_one (q := q) x hx
      have hadd := hzero.add hprincipal
      convert hadd using 1
      · ext s
        simp only [endpointDecomposedContourIntegrand]
        ring
      · simp [endpointSourcePoleResidue,
          endpointPerronKernel_of_ne one_ne_zero]
    · have hrho1 : rho ≠ 1 := fun h =>
        (one_not_mem_zeroSupport chi sigma T) (h ▸ hrhoZero)
      have hzero :=
        tendsto_mul_endpointRegularizedContourIntegrand_at_zero
          chi hx hrhoZero
      subst chi
      have hprincipal :=
        tendsto_sub_mul_endpointPrincipalPoleIntegrand_at_other
          (q := q) x hx hrho1
      have hadd := hzero.add hprincipal
      convert hadd using 1
      · ext s
        simp only [endpointDecomposedContourIntegrand]
        ring
      · simp [endpointSourcePoleResidue, hrho1]
  · rw [endpointSourcePoleSupport, if_neg hchi] at hrho
    have hzero := tendsto_mul_endpointRegularizedContourIntegrand_at_zero
      chi hx hrho
    have hprincipal : Tendsto
        (fun s => (s - rho) * endpointPrincipalPoleIntegrand chi x s)
        (𝓝[≠] rho) (𝓝 0) := by
      simp only [endpointPrincipalPoleIntegrand, hchi, if_false, mul_zero]
      exact tendsto_const_nhds
    have hadd := hzero.add hprincipal
    convert hadd using 1
    · ext s
      simp only [endpointDecomposedContourIntegrand]
      ring
    · simp [endpointSourcePoleResidue, hchi]

/-- The finite residue sum is the exact endpoint main residue minus the
endpoint-regularized multiplicity sum. -/
theorem sum_endpointSourcePoleResidue
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma T x : ℝ) :
    (∑ rho ∈ endpointSourcePoleSupport chi sigma T,
        endpointSourcePoleResidue chi sigma T x rho) =
      (if chi = 1 then endpointPerronKernel x 1 else 0) -
        ∑ rho ∈ zeroSupport chi sigma T,
          (zeroMultiplicity chi sigma T rho : ℂ) *
            endpointPerronKernel x rho := by
  classical
  by_cases hchi : chi = 1
  · subst chi
    have hone := one_not_mem_zeroSupport
      (1 : DirichletCharacter ℂ q) sigma T
    rw [endpointSourcePoleSupport, if_pos rfl, Finset.sum_insert hone]
    have honeResidue :
        endpointSourcePoleResidue (1 : DirichletCharacter ℂ q)
          sigma T x 1 = endpointPerronKernel x 1 := by
      simp [endpointSourcePoleResidue]
    rw [honeResidue, if_pos rfl]
    have hzeroSum :
        (∑ rho ∈ zeroSupport (1 : DirichletCharacter ℂ q) sigma T,
          endpointSourcePoleResidue (1 : DirichletCharacter ℂ q)
            sigma T x rho) =
        -(∑ rho ∈ zeroSupport (1 : DirichletCharacter ℂ q) sigma T,
          (zeroMultiplicity (1 : DirichletCharacter ℂ q) sigma T rho : ℂ) *
            endpointPerronKernel x rho) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro rho hrho
      have hrho1 : rho ≠ 1 := fun h => hone (h ▸ hrho)
      simp only [endpointSourcePoleResidue,
        if_neg (not_and_of_not_right _ hrho1)]
      ring
    rw [hzeroSum]
    ring
  · simp only [endpointSourcePoleSupport, if_neg hchi,
      endpointSourcePoleResidue, hchi, false_and, if_false, zero_sub]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro rho hrho
    ring

end
end KoukTheorem113Residues

#print axioms KoukTheorem113Residues.tendsto_mul_endpointRegularizedContourIntegrand_at_zero
#print axioms KoukTheorem113Residues.tendsto_mul_endpointPrincipalPoleIntegrand_one
#print axioms KoukTheorem113Residues.tendsto_sub_mul_endpointPrincipalPoleIntegrand_at_other
#print axioms KoukTheorem113Residues.sum_endpointSourcePoleResidue
