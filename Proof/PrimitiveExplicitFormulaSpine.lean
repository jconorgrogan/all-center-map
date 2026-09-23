import APFoundation
import DirichletZeros
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Certified spine toward the primitive-character truncated explicit formula

This file formalizes the largest present unconditional bridge available from
Mathlib: the exact von-Mangoldt/logarithmic-derivative identity, an elementary
Chebyshev bound uniform in the character, an exact Abel-Mellin representation
of the logarithmic derivative by twisted Mangoldt partial sums, and the
multiplicity-aware finite logarithmic derivative of the actual compact
Dirichlet-L zero divisor.

It deliberately does not postulate a contour-shift, a zero-free boundary
estimate, or a truncated explicit-formula remainder.
-/

namespace PrimitiveExplicitFormulaSpine

open Set Filter Topology MeasureTheory Asymptotics
open scoped BigOperators ArithmeticFunction LSeries.notation

noncomputable section

/-- The coefficient sequence in the primitive-character explicit formula. -/
def twistedMangoldtCoeff {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- Exact equality between the twisted Mangoldt Dirichlet series and the
negative logarithmic derivative of the continued Dirichlet L-function on the
absolute-convergence half-plane. -/
theorem LSeries_twistedMangoldtCoeff_eq_neg_logDeriv_LFunction
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (twistedMangoldtCoeff χ) s =
      -logDeriv (DirichletCharacter.LFunction χ) s := by
  rw [logDeriv_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  convert DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  · ext n; simp [twistedMangoldtCoeff]
  · simp [neg_div]

/-- Each twisted Mangoldt coefficient is bounded by the untwisted Mangoldt
coefficient, uniformly in the level and character. -/
theorem norm_twistedMangoldtCoeff_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖twistedMangoldtCoeff χ n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  rw [twistedMangoldtCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one n)

/-- The natural-number specialization of Chebyshev's psi is the exact finite
Mangoldt sum on `1 ≤ k ≤ n`. -/
theorem sum_vonMangoldt_Icc_eq_psi (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi (n : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · intro k _
    rfl

/-- Uniform Chebyshev majorant for partial sums of the norms of twisted
Mangoldt coefficients. -/
theorem sum_norm_twistedMangoldtCoeff_le_psi
    {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ‖twistedMangoldtCoeff χ k‖) ≤
      Chebyshev.psi (n : ℝ) := by
  rw [← sum_vonMangoldt_Icc_eq_psi]
  exact Finset.sum_le_sum fun k _ => norm_twistedMangoldtCoeff_le χ k

/-- A character-uniform linear Big-O bound for the norm partial sums.  This is
the elementary growth input needed by Mathlib's Abel-Mellin identity. -/
theorem sum_norm_twistedMangoldtCoeff_isBigO
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖twistedMangoldtCoeff χ k‖) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
  have hnonneg :
      0 ≤ ∑ k ∈ Finset.Icc 1 n, ‖twistedMangoldtCoeff χ k‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  exact (sum_norm_twistedMangoldtCoeff_le_psi χ n).trans
    (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n))

/-- Exact Abel-Mellin representation of the primitive-character logarithmic
derivative.  The vertical-line condition is the sharp elementary `Re s > 1`;
no prime number theorem is assumed. -/
theorem neg_logDeriv_LFunction_eq_partialSum_integral
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (DirichletCharacter.LFunction χ) s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, twistedMangoldtCoeff χ k) *
          (t : ℂ) ^ (-(s + 1)) := by
  rw [← LSeries_twistedMangoldtCoeff_eq_neg_logDeriv_LFunction χ hs]
  exact LSeries_eq_mul_integral'
    (twistedMangoldtCoeff χ) zero_le_one hs
    (by simpa only [Real.rpow_one] using
      sum_norm_twistedMangoldtCoeff_isBigO χ)

/-! ## Local zero residues with arbitrary analytic multiplicity -/

/-- At a zero of any finite analytic order, the logarithmic derivative has
residue equal to that order.  Mathlib previously exposed the simple-zero case;
this version is the multiplicity statement needed by a Dirichlet-L explicit
formula. -/
theorem tendsto_mul_logDeriv_of_analyticOrder
    {f : ℂ → ℂ} {x : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f x) (horder : analyticOrderAt f x = n) :
    Tendsto (fun w => (w - x) * logDeriv f w)
      (𝓝[≠] x) (𝓝 (n : ℂ)) := by
  obtain ⟨g, hg, hg_ne, hfg⟩ :=
    (hf.analyticOrderAt_eq_natCast).mp horder
  let model : ℂ → ℂ := fun z => (z - x) ^ n * g z
  have hfg' : f =ᶠ[𝓝[≠] x] model :=
    hfg.filter_mono nhdsWithin_le_nhds
  have hderiv : deriv f =ᶠ[𝓝[≠] x] deriv model :=
    hfg'.nhdsNE_deriv
  have hg_event : ∀ᶠ w in 𝓝[≠] x, g w ≠ 0 :=
    (eventually_nhdsWithin_of_eventually_nhds
      (hg.continuousAt.eventually_ne hg_ne))
  have hg_analytic_event : ∀ᶠ w in 𝓝[≠] x, AnalyticAt ℂ g w :=
    eventually_nhdsWithin_of_eventually_nhds hg.eventually_analyticAt
  have hlog : logDeriv f =ᶠ[𝓝[≠] x] logDeriv model := by
    filter_upwards [hfg', hderiv] with w hw hdw
    simp only [logDeriv_apply, hw, hdw]
  have hmodel :
      (fun w => (w - x) * logDeriv model w) =ᶠ[𝓝[≠] x]
        (fun w => (n : ℂ) + (w - x) * logDeriv g w) := by
    filter_upwards [self_mem_nhdsWithin, hg_event, hg_analytic_event]
      with w hwx hgw hga
    have hsub : w - x ≠ 0 := sub_ne_zero.mpr hwx
    have hpow : (w - x) ^ n ≠ 0 := pow_ne_zero n hsub
    have hdiffPow : DifferentiableAt ℂ (fun z : ℂ => (z - x) ^ n) w := by
      fun_prop
    rw [show model = fun z => (z - x) ^ n * g z by rfl,
      logDeriv_fun_mul w hpow hgw hdiffPow hga.differentiableAt,
      logDeriv_fun_pow (by fun_prop)]
    have hderivSub : deriv (fun z : ℂ => z - x) w = 1 := by
      rw [deriv_sub_const]
      simpa using congrArg (fun f => f w) deriv_id'
    simp only [logDeriv_apply, hderivSub]
    field_simp
  have hlog_cont : ContinuousAt (logDeriv g) x :=
    hg.deriv.continuousAt.div hg.continuousAt hg_ne
  have htail :
      Tendsto (fun w => (w - x) * logDeriv g w)
        (𝓝[≠] x) (𝓝 0) := by
    have hsubzero :
        Tendsto (fun w : ℂ => w - x) (𝓝[≠] x) (𝓝 0) := by
      have hid : ContinuousAt (fun w : ℂ => w) x := continuousAt_id
      have hc : ContinuousAt (fun _ : ℂ => x) x := continuousAt_const
      convert (hid.sub hc).tendsto.mono_left
        (show 𝓝[≠] x ≤ 𝓝 x from nhdsWithin_le_nhds)
      simp
    have hglog :
        Tendsto (logDeriv g) (𝓝[≠] x) (𝓝 (logDeriv g x)) := by
      exact hlog_cont.tendsto.mono_left
        (show 𝓝[≠] x ≤ 𝓝 x from nhdsWithin_le_nhds)
    simpa using hsubzero.mul hglog
  have hmodel_limit :
      Tendsto (fun w => (n : ℂ) + (w - x) * logDeriv g w)
        (𝓝[≠] x) (𝓝 (n : ℂ)) := by
    simpa using tendsto_const_nhds.add htail
  have hmul :
      (fun w => (w - x) * logDeriv f w) =ᶠ[𝓝[≠] x]
        (fun w => (w - x) * logDeriv model w) :=
    hlog.mul_left
  exact hmodel_limit.congr' (hmul.trans hmodel).symm

/-! ## The actual compact zero divisor and its multiplicity polynomial -/

variable {q : ℕ} [NeZero q]

open DirichletZeros

/-- The regularized L-function is globally nonzero, witnessed at one.  This
prevents an infinite analytic order at every zero. -/
theorem regularizedLFunction_one_ne_zero
    (χ : DirichletCharacter ℂ q) :
    regularizedLFunction χ 1 ≠ 0 := by
  classical
  by_cases hχ : χ = 1
  · simp only [regularizedLFunction, if_pos hχ]
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
  · simp only [regularizedLFunction, if_neg hχ]
    exact DirichletCharacter.LFunction_apply_one_ne_zero hχ

/-- Every analytic order of the regularized L-function is finite. -/
theorem regularizedLFunction_order_ne_top
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    meromorphicOrderAt (regularizedLFunction χ) ρ ≠ ⊤ := by
  have hone : meromorphicOrderAt (regularizedLFunction χ) 1 = 0 :=
    ((differentiable_regularizedLFunction χ).analyticAt 1).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr
        (regularizedLFunction_one_ne_zero χ)
  exact (meromorphicOn_regularizedLFunction χ Set.univ)
    |>.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ 1) (Set.mem_univ ρ) (by simp [hone])

/-- Every supported point belongs to the literal closed zero rectangle. -/
theorem mem_zeroRectangle_of_mem_zeroSupport
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ σ T) :
    ρ ∈ zeroRectangle σ T := by
  exact (zeroDivisor χ σ T).supportWithinDomain
    ((zeroSupport_mem_iff χ σ T ρ).mp hρ)

/-- The divisor multiplicity is exactly the finite analytic order, not merely
an arbitrary natural weight attached to the support. -/
theorem analyticOrderAt_eq_zeroMultiplicity
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ σ T) :
    analyticOrderAt (regularizedLFunction χ) ρ =
      (zeroMultiplicity χ σ T ρ : ℕ∞) := by
  let f := regularizedLFunction χ
  have han : AnalyticAt ℂ f ρ :=
    (differentiable_regularizedLFunction χ).analyticAt ρ
  have hmerfinite : meromorphicOrderAt f ρ ≠ ⊤ :=
    regularizedLFunction_order_ne_top χ ρ
  have hanfinite : analyticOrderAt f ρ ≠ ⊤ := by
    intro htop
    apply hmerfinite
    rw [han.meromorphicOrderAt_eq, htop]
    simp
  let m := analyticOrderNatAt f ρ
  have horder : analyticOrderAt f ρ = (m : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt hanfinite).symm
  have hrect : ρ ∈ zeroRectangle σ T :=
    mem_zeroRectangle_of_mem_zeroSupport χ σ T hρ
  have hdiv : zeroDivisor χ σ T ρ = (m : ℤ) := by
    rw [zeroDivisor_apply_of_mem χ σ T hrect,
      han.meromorphicOrderAt_eq, horder, ENat.map_coe,
      WithTop.untop₀_coe]
  have hmult : zeroMultiplicity χ σ T ρ = m := by
    simp only [zeroMultiplicity, hdiv, Int.toNat_natCast]
  simpa only [f, hmult] using horder

/-- The logarithmic derivative of the actual regularized Dirichlet L-function
has residue equal to the divisor-backed analytic multiplicity at every
supported zero. -/
theorem tendsto_mul_logDeriv_regularizedLFunction
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ σ T) :
    Tendsto
      (fun s => (s - ρ) * logDeriv (regularizedLFunction χ) s)
      (𝓝[≠] ρ) (𝓝 (zeroMultiplicity χ σ T ρ : ℂ)) := by
  apply tendsto_mul_logDeriv_of_analyticOrder
    ((differentiable_regularizedLFunction χ).analyticAt ρ)
  exact analyticOrderAt_eq_zeroMultiplicity χ σ T hρ

/-- The residue of the *negative* logarithmic derivative at an actual
Dirichlet-L zero is the negative analytic multiplicity, matching the sign in
the Perron contour integrand. -/
theorem tendsto_mul_neg_logDeriv_regularizedLFunction
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ σ T) :
    Tendsto
      (fun s => (s - ρ) * (-logDeriv (regularizedLFunction χ) s))
      (𝓝[≠] ρ) (𝓝 (-(zeroMultiplicity χ σ T ρ : ℂ))) := by
  convert (tendsto_mul_logDeriv_regularizedLFunction χ σ T hρ).neg using 1
  · ext s
    ring

/-- The negative logarithmic derivative of the trivial-character L-function
has residue (+1) at its pole (s=1).  This certifies the main-term residue
in the explicit formula independently of the zero residues. -/
theorem tendsto_mul_neg_logDeriv_LFunctionTrivChar_one
    (q : ℕ) [NeZero q] :
    Tendsto
      (fun s => (s - 1) *
        (-logDeriv (DirichletCharacter.LFunctionTrivChar q) s))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  let regularizedLF := DirichletCharacter.LFunctionTrivChar₁ q
  let trivialLF := DirichletCharacter.LFunctionTrivChar q
  have hRanalytic : AnalyticAt ℂ regularizedLF 1 :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).analyticAt 1
  have hRone : regularizedLF 1 ≠ 0 :=
    DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
  have hRne : ∀ᶠ s in 𝓝[≠] (1 : ℂ), regularizedLF s ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds
      (hRanalytic.continuousAt.eventually_ne hRone)
  have hidentity :
      (fun s => (s - 1) * (-logDeriv trivialLF s)) =ᶠ[𝓝[≠] (1 : ℂ)]
        (fun s => 1 - (s - 1) * logDeriv regularizedLF s) := by
    filter_upwards [self_mem_nhdsWithin, hRne] with s hs hRs
    have hsne : s ≠ 1 := hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
    have hRrel : regularizedLF s = (s - 1) * trivialLF s := by
      dsimp only [regularizedLF, trivialLF,
        DirichletCharacter.LFunctionTrivChar₁]
      rw [Function.update_of_ne hsne]
    have hLs : trivialLF s ≠ 0 := by
      intro hL
      apply hRs
      rw [hRrel, hL, mul_zero]
    have hRderiv :
        deriv regularizedLF s =
          (s - 1) * deriv trivialLF s + trivialLF s := by
      exact DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hsne
    simp only [logDeriv_apply, hRderiv, hRrel]
    field_simp
    ring
  have hRlogcont : ContinuousAt (logDeriv regularizedLF) 1 :=
    hRanalytic.deriv.continuousAt.div hRanalytic.continuousAt hRone
  have hsubzero :
      Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hid : ContinuousAt (fun s : ℂ => s) 1 := continuousAt_id
    have hc : ContinuousAt (fun _ : ℂ => (1 : ℂ)) 1 := continuousAt_const
    convert (hid.sub hc).tendsto.mono_left
      (show 𝓝[≠] (1 : ℂ) ≤ 𝓝 (1 : ℂ) from nhdsWithin_le_nhds)
    simp
  have hRlog :
      Tendsto (logDeriv regularizedLF) (𝓝[≠] (1 : ℂ))
        (𝓝 (logDeriv regularizedLF 1)) :=
    hRlogcont.tendsto.mono_left
      (show 𝓝[≠] (1 : ℂ) ≤ 𝓝 (1 : ℂ) from nhdsWithin_le_nhds)
  have htail :
      Tendsto (fun s => (s - 1) * logDeriv regularizedLF s)
        (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa using hsubzero.mul hRlog
  have hright :
      Tendsto (fun s => 1 - (s - 1) * logDeriv regularizedLF s)
        (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub htail
  exact hright.congr' hidentity.symm

/-- The finite polynomial-like product whose zeros are exactly the supported
zeros in the compact rectangle, repeated by analytic multiplicity. -/
def zeroFactorProduct
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) (s : ℂ) : ℂ :=
  ∏ ρ ∈ zeroSupport χ σ T,
    (s - ρ) ^ zeroMultiplicity χ σ T ρ

/-- A point outside the compact zero support does not vanish in any factor. -/
theorem zeroFactor_ne_zero_of_not_mem
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {s ρ : ℂ}
    (hs : s ∉ zeroSupport χ σ T) (hρ : ρ ∈ zeroSupport χ σ T) :
    s - ρ ≠ 0 := by
  intro h
  apply hs
  have : s = ρ := sub_eq_zero.mp h
  simpa [this] using hρ

/-- The finite product is nonzero away from the compact zero support. -/
theorem zeroFactorProduct_ne_zero_of_not_mem
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {s : ℂ}
    (hs : s ∉ zeroSupport χ σ T) :
    zeroFactorProduct χ σ T s ≠ 0 := by
  simp only [zeroFactorProduct, Finset.prod_ne_zero_iff]
  intro ρ hρ
  exact pow_ne_zero _ (zeroFactor_ne_zero_of_not_mem χ σ T hs hρ)

/-- Multiplicity-aware logarithmic derivative of the actual compact zero
product.  This is the exact finite zero-sum algebra used after a contour shift. -/
theorem logDeriv_zeroFactorProduct
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {s : ℂ}
    (hs : s ∉ zeroSupport χ σ T) :
    logDeriv (zeroFactorProduct χ σ T) s =
      ∑ ρ ∈ zeroSupport χ σ T,
        (zeroMultiplicity χ σ T ρ : ℂ) / (s - ρ) := by
  rw [show zeroFactorProduct χ σ T =
      fun z => ∏ ρ ∈ zeroSupport χ σ T,
        (z - ρ) ^ zeroMultiplicity χ σ T ρ by rfl]
  rw [logDeriv_fun_prod]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [logDeriv_fun_pow (by fun_prop)]
    simp only [logDeriv_apply, deriv_sub_const]
    have hderiv : deriv (fun y : ℂ => y) s = 1 := by
      simpa using congrArg (fun f => f s) deriv_id'
    rw [hderiv]
    ring
  · intro ρ hρ
    exact pow_ne_zero _ (zeroFactor_ne_zero_of_not_mem χ σ T hs hρ)
  · intro ρ hρ
    fun_prop

/-- The total degree of the compact zero product is the analytic zero count,
including multiplicity. -/
theorem sum_zeroMultiplicity_eq_dirichletZeroCount
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    (∑ ρ ∈ zeroSupport χ σ T, zeroMultiplicity χ σ T ρ) =
      dirichletZeroCount χ σ T := by
  rfl

/-- Multiplicity-weighted finite zero term appearing in a truncated explicit
formula. -/
def multiplicityWeightedZeroTerm
    (χ : DirichletCharacter ℂ q) (σ T t : ℝ) : ℂ :=
  ∑ ρ ∈ zeroSupport χ σ T,
    (zeroMultiplicity χ σ T ρ : ℂ) * APFoundation.regularizedZeroTerm t ρ

/-- Subtracting two multiplicity-weighted finite zero truncations cancels every
regularizing constant, with the actual analytic divisor and multiplicities. -/
theorem multiplicityWeightedZeroTerm_interval
    (χ : DirichletCharacter ℂ q) (σ T x Y : ℝ) :
    multiplicityWeightedZeroTerm χ σ T (x + Y) -
        multiplicityWeightedZeroTerm χ σ T x =
      ∑ ρ ∈ zeroSupport χ σ T,
        (zeroMultiplicity χ σ T ρ : ℂ) *
          ((Complex.cpow ((x + Y : ℝ) : ℂ) ρ -
              Complex.cpow (x : ℂ) ρ) / ρ) := by
  classical
  simp only [multiplicityWeightedZeroTerm, ← Finset.sum_sub_distrib,
    APFoundation.regularizedZeroTerm, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

end
end PrimitiveExplicitFormulaSpine
