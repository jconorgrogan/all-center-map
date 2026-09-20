import PrincipalZetaA5
import FunctionalZeroTransport

namespace MAPPrincipalZetaTransport

open Complex Filter Topology Function
open DirichletZeros MAPLocalZeroWindow

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

theorem regularized_principal_eq :
    regularizedLFunction (1 : DirichletCharacter ℂ 1) =
      MAPPrincipalZetaFixedStrip.principalRegularized := by
  funext z
  simp [regularizedLFunction,
    MAPPrincipalZetaFixedStrip.principalRegularized]

private theorem analyticAt_GammaReal_inv (s : ℂ) :
    AnalyticAt ℂ (fun z => (Complex.Gammaℝ z)⁻¹) s :=
  Complex.differentiable_Gammaℝ_inv.analyticAt s

private theorem GammaReal_inv_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    (Complex.Gammaℝ s)⁻¹ ≠ 0 :=
  inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs)

/-- In positive real part, the regularized principal zeta function and the
completed zeta function have the same analytic vanishing order. -/
theorem analyticOrderAt_principalRegularized_eq_completed
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt MAPPrincipalZetaFixedStrip.principalRegularized s =
      analyticOrderAt completedRiemannZeta s := by
  let a : ℂ → ℂ := fun z => z - 1
  let g : ℂ → ℂ := fun z => (Complex.Gammaℝ z)⁻¹
  have ha : AnalyticAt ℂ a s := by dsimp [a]; fun_prop
  have haNe : a s ≠ 0 := by simpa [a, sub_ne_zero] using hs1
  have hg : AnalyticAt ℂ g s := analyticAt_GammaReal_inv s
  have hgNe : g s ≠ 0 := GammaReal_inv_ne_zero_of_re_pos hs
  have hcomp : AnalyticAt ℂ completedRiemannZeta s := by
    let U : Set ℂ := ({0, 1} : Set ℂ)ᶜ
    have hUopen : IsOpen U := Set.toFinite {0, 1} |>.isClosed.isOpen_compl
    have hsU : s ∈ U := by
      simp only [U, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or]
      exact ⟨by intro h; subst s; norm_num at hs, hs1⟩
    have hdiff : DifferentiableOn ℂ completedRiemannZeta U := by
      intro z hz
      simp only [U, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at hz
      exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
    exact hdiff.analyticAt (hUopen.mem_nhds hsU)
  have heq : MAPPrincipalZetaFixedStrip.principalRegularized =ᶠ[𝓝 s]
      fun z => a z * completedRiemannZeta z * g z := by
    filter_upwards [eventually_ne_nhds (by
      intro h; subst s; norm_num at hs : s ≠ 0),
      eventually_ne_nhds hs1] with z hz0 hz1
    rw [MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hz1,
      riemannZeta_def_of_ne_zero hz0]
    simp only [a, g, div_eq_mul_inv]
    ring
  rw [analyticOrderAt_congr heq]
  rw [show analyticOrderAt
      (fun z => a z * completedRiemannZeta z * g z) s =
        analyticOrderAt (fun z => a z * completedRiemannZeta z) s +
          analyticOrderAt g s by
      simpa only [Pi.mul_apply] using analyticOrderAt_mul (ha.mul hcomp) hg,
    show analyticOrderAt (fun z => a z * completedRiemannZeta z) s =
        analyticOrderAt a s + analyticOrderAt completedRiemannZeta s by
      simpa only [Pi.mul_apply] using analyticOrderAt_mul ha hcomp,
    ha.analyticOrderAt_eq_zero.mpr haNe,
    hg.analyticOrderAt_eq_zero.mpr hgNe,
    zero_add, add_zero]

/-- Reflection preserves the exact multiplicity of strict critical-strip zeros
of the regularized principal zeta function. -/
theorem analyticOrderAt_principalRegularized_transport
    {ρ : ℂ} (hρpos : 0 < ρ.re) (hρhalf : ρ.re < 1 / 2) :
    analyticOrderAt MAPPrincipalZetaFixedStrip.principalRegularized ρ =
      analyticOrderAt MAPPrincipalZetaFixedStrip.principalRegularized (1 - ρ) := by
  have hρ1 : ρ ≠ 1 := by
    intro h; subst ρ; norm_num at hρhalf
  have hrefPos : 0 < (1 - ρ).re := by simp; linarith
  have href1 : 1 - ρ ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  calc
    analyticOrderAt MAPPrincipalZetaFixedStrip.principalRegularized ρ =
        analyticOrderAt completedRiemannZeta ρ :=
      analyticOrderAt_principalRegularized_eq_completed hρpos hρ1
    _ = analyticOrderAt (fun z => completedRiemannZeta (1 - z)) (1 - ρ) := by
      symm
      simpa using MAPFunctionalZeroTransport.analyticOrderAt_one_sub_comp
        completedRiemannZeta ρ
    _ = analyticOrderAt completedRiemannZeta (1 - ρ) := by
      apply analyticOrderAt_congr
      exact Filter.Eventually.of_forall fun z => completedRiemannZeta_one_sub z
    _ = analyticOrderAt MAPPrincipalZetaFixedStrip.principalRegularized (1 - ρ) :=
      (analyticOrderAt_principalRegularized_eq_completed hrefPos href1).symm

/-- The conductor-one regularized zeta function has no zero on `Re s = 0`. -/
theorem principalRegularized_ne_zero_of_re_zero
    {s : ℂ} (hre : s.re = 0) :
    MAPPrincipalZetaFixedStrip.principalRegularized s ≠ 0 := by
  by_cases hs0 : s = 0
  · subst s
    rw [MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one (by norm_num),
      riemannZeta_zero]
    norm_num
  · have him : s.im ≠ 0 := by
      intro him
      apply hs0
      apply Complex.ext <;> simp [hre, him]
    have hs1 : s ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp [hre] at this
    rw [MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hs1]
    apply mul_ne_zero (sub_ne_zero.mpr hs1)
    intro hzeta
    have hcompS : completedRiemannZeta s = 0 := by
      have heq := riemannZeta_def_of_ne_zero hs0
      rw [hzeta] at heq
      by_contra hc
      have hdiv : completedRiemannZeta s / Complex.Gammaℝ s ≠ 0 :=
        div_ne_zero hc (by
          rw [Ne, Complex.Gammaℝ_eq_zero_iff]
          push_neg
          intro n hn
          have hi := congrArg Complex.im hn
          simp at hi
          exact him hi)
      exact hdiv heq.symm
    let u : ℂ := 1 - s
    have hcompU : completedRiemannZeta u = 0 := by
      dsimp [u]
      rw [completedRiemannZeta_one_sub, hcompS]
    have hu0 : u ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp [u, hre] at this
    have huRe : u.re = 1 := by simp [u, hre]
    have hzetaU : riemannZeta u = 0 := by
      rw [riemannZeta_def_of_ne_zero hu0, hcompU, zero_div]
    exact (riemannZeta_ne_zero_of_one_le_re (by rw [huRe])) hzetaU

/-- A strict-lower supported principal zero reflects into the upper-half
support at the same symmetric height. -/
theorem one_sub_mem_upper_zeroSupport
    {σ T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport (1 : DirichletCharacter ℂ 1) σ T)
    (hρpos : 0 < ρ.re) (hρhalf : ρ.re < 1 / 2) :
    1 - ρ ∈ zeroSupport (1 : DirichletCharacter ℂ 1) (1 / 2) T := by
  have hrectρ : ρ ∈ zeroRectangle σ T :=
    (zeroDivisor (1 : DirichletCharacter ℂ 1) σ T).supportWithinDomain
      ((zeroSupport_mem_iff _ _ _ _).mp hρ)
  have hrectReflect : 1 - ρ ∈ zeroRectangle (1 / 2) T := by
    rw [zeroRectangle, Complex.mem_reProdIm] at hrectρ ⊢
    constructor
    · constructor <;> simp <;> linarith
    · have him : (1 - ρ).im = -ρ.im := by simp
      rw [him]
      exact ⟨by linarith [hrectρ.2.2], by linarith [hrectρ.2.1]⟩
  apply (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero _ _ _ hrectReflect).mpr
  have hzero : regularizedLFunction (1 : DirichletCharacter ℂ 1) ρ = 0 :=
    regularizedLFunction_eq_zero_of_mem_zeroSupport _ _ _ hρ
  have hanS := (differentiable_regularizedLFunction
    (1 : DirichletCharacter ℂ 1)).analyticAt ρ
  have hanT := (differentiable_regularizedLFunction
    (1 : DirichletCharacter ℂ 1)).analyticAt (1 - ρ)
  apply hanT.analyticOrderAt_ne_zero.mp
  rw [regularized_principal_eq,
    ← analyticOrderAt_principalRegularized_transport hρpos hρhalf,
    ← regularized_principal_eq]
  exact hanS.analyticOrderAt_ne_zero.mpr hzero

/-- A strict-lower supported zero reflects into upper support at equal
multiplicity. -/
theorem zeroMultiplicity_one_sub
    {σ T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport (1 : DirichletCharacter ℂ 1) σ T)
    (hρpos : 0 < ρ.re) (hρhalf : ρ.re < 1 / 2) :
    zeroMultiplicity (1 : DirichletCharacter ℂ 1) σ T ρ =
      zeroMultiplicity (1 : DirichletCharacter ℂ 1) (1 / 2) T (1 - ρ) := by
  have htarget := one_sub_mem_upper_zeroSupport hρ hρpos hρhalf
  have htransport := analyticOrderAt_principalRegularized_transport hρpos hρhalf
  have hsourceOrder := PrimitiveExplicitFormulaSpine.analyticOrderAt_eq_zeroMultiplicity
    (1 : DirichletCharacter ℂ 1) σ T hρ
  have htargetOrder := PrimitiveExplicitFormulaSpine.analyticOrderAt_eq_zeroMultiplicity
    (1 : DirichletCharacter ℂ 1) (1 / 2) T htarget
  rw [regularized_principal_eq] at hsourceOrder htargetOrder
  rw [hsourceOrder, htargetOrder] at htransport
  exact ENat.coe_inj.mp htransport

#print axioms analyticOrderAt_principalRegularized_transport
#print axioms principalRegularized_ne_zero_of_re_zero
#print axioms one_sub_mem_upper_zeroSupport
#print axioms zeroMultiplicity_one_sub

end
end MAPPrincipalZetaTransport
