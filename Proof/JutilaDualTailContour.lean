import JutilaCriticalPartialTruncation
import RamachandraShiftedHeadFiniteContour
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Finite contour deformation of Jutila's dual-series remainder

This is the deterministic contour step for the `I₂` remainder in Jutila,
Acta Arith. 32 (1977), Lemma 1, p. 58.  The source moves this piece from
`Re(s+w)=-1/2` to `Re w=-h/2`.  Here the literal remainder is defined as
the full absolutely convergent dual L-series minus its finite head, its
identification with the shifted `tsum` is proved, and the finite rectangle
deformation is certified.  The subsequent numerical estimate on the new
vertical line is separate.
-/

namespace JutilaDualTailContour

open Complex Real MeasureTheory Set DirichletCharacter
open scoped BigOperators LSeries.notation
open JutilaTwoScaleSmoothing
open JutilaCriticalPartialTruncation
open JutilaReflectedFunctionalEquationIntegrand
open JutilaTwoScaleHorizontalDecay
open RamachandraShiftedHeadFiniteContour
open BHPRamachandraMeanValueFromDyadicAFE

noncomputable section

variable {q : ℕ} [NeZero q]

def dualTail
    (chi : DirichletCharacter ℂ q) (z : ℂ) (M : ℕ) : ℂ :=
  LSeries (fun n : ℕ => chi⁻¹ n) (1 - z) - dualPartialSum chi z M

theorem dualTail_eq_shifted_tsum
    (chi : DirichletCharacter ℂ q) {z : ℂ}
    (hzre : z.re = -(1 : ℝ) / 2) (M : ℕ) :
    dualTail chi z M =
      ∑' n : ℕ,
        LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) (n + M) := by
  have hsplit := dual_LSeries_eq_partialSum_add_tail chi hzre M
  unfold dualTail dualPartialSum
  rw [hsplit]
  ring

theorem differentiable_dualPartialSum
    (chi : DirichletCharacter ℂ q) (M : ℕ) :
    Differentiable ℂ (fun z : ℂ => dualPartialSum chi z M) := by
  unfold dualPartialSum
  have hsum : Differentiable ℂ
      (∑ n ∈ Finset.range M,
        (fun z : ℂ => LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) n)) := by
    apply Differentiable.sum
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [LSeries.term_zero]
    · simp_rw [LSeries.term_of_ne_zero hn0]
      apply Differentiable.div (differentiable_const _)
        (((differentiable_const (1 : ℂ)).sub differentiable_id).const_cpow
          (Or.inl (Nat.cast_ne_zero.mpr hn0)))
      intro z
      exact Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Nat.cast_ne_zero.mpr hn0))
  convert hsum using 1
  ext z
  simp

theorem abscissa_dualCharacter_le_one
    (chi : DirichletCharacter ℂ q) :
    LSeries.abscissaOfAbsConv (fun n : ℕ => chi⁻¹ n) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const
  refine ⟨1, ?_⟩
  intro n hn
  exact chi⁻¹.norm_le_one (n : ZMod q)

/-- The literal dual tail is holomorphic throughout `Re z<0`, which is the
entire strip traversed by the source deformation. -/
theorem differentiableAt_dualTail
    (chi : DirichletCharacter ℂ q) (M : ℕ) {z : ℂ} (hz : z.re < 0) :
    DifferentiableAt ℂ (fun u : ℂ => dualTail chi u M) z := by
  have habsc := abscissa_dualCharacter_le_one chi
  have hhalf : LSeries.abscissaOfAbsConv (fun n : ℕ => chi⁻¹ n) <
      (1 - z).re := by
    have hone : (1 : ℝ) < 1 - z.re := by linarith
    exact lt_of_le_of_lt habsc (by
      have honeE : (1 : EReal) < (1 - z.re : ℝ) :=
        EReal.coe_lt_coe hone
      simpa using honeE)
  have hL : DifferentiableAt ℂ
      (fun u : ℂ => LSeries (fun n : ℕ => chi⁻¹ n) (1 - u)) z :=
    (LSeries_hasDerivAt hhalf).differentiableAt.comp z (by fun_prop)
  exact hL.sub (differentiable_dualPartialSum chi M).differentiableAt

theorem reflectedDualMultiplier_eq_ramachandra
    (chi : DirichletCharacter ℂ q) (z : ℂ) :
    reflectedDualMultiplier chi z = ramachandraFunctionalFactor chi z := by
  unfold reflectedDualMultiplier ramachandraFunctionalFactor
  ring

/-- The exact `I₂` integrand after the dual-series split. -/
def dualTailIntegrand
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (N h : ℝ) (M : ℕ) (w : ℂ) : ℂ :=
  Complex.Gamma (1 + w / (h : ℂ)) *
    twoScaleRemovableQuotient N w *
      reflectedDualMultiplier chi (s + w) * dualTail chi (s + w) M

/-- Holomorphy on the exact source strip.  The hypotheses say only that the
dual argument remains in its absolute-convergence half-plane and the Mellin
Gamma argument remains in the positive half-plane. -/
theorem differentiableAt_dualTailIntegrand
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    {N h : ℝ} (hN : 0 < N) (M : ℕ) {w : ℂ}
    (hz : (s + w).re < 0)
    (hGamma : 0 < (1 + w / (h : ℂ)).re) :
    DifferentiableAt ℂ (dualTailIntegrand chi s N h M) w := by
  have hGammaNoPole : ∀ n : ℕ,
      (1 + w / (h : ℂ)) ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hneg : (1 + w / (h : ℂ)).re = -(n : ℝ) := by
      simpa using hre
    linarith
  have hG : DifferentiableAt ℂ
      (fun u : ℂ => Complex.Gamma (1 + u / (h : ℂ))) w :=
    (Complex.differentiableAt_Gamma _ hGammaNoPole).comp w (by fun_prop)
  have hQ := differentiableAt_twoScaleRemovableQuotient hN w
  have hinner : DifferentiableAt ℂ (fun u : ℂ => s + u) w := by fun_prop
  have hfactor : DifferentiableAt ℂ (fun u : ℂ =>
      reflectedDualMultiplier chi (s + u)) w := by
    rw [show (fun u : ℂ => reflectedDualMultiplier chi (s + u)) =
        fun u : ℂ => ramachandraFunctionalFactor chi (s + u) by
      funext u
      exact reflectedDualMultiplier_eq_ramachandra chi (s + u)]
    have hreflect : 0 < (1 - (s + w)).re := by
      have hz' : s.re + w.re < 0 := by simpa using hz
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re]
      linarith [hz']
    exact (differentiableAt_ramachandraFunctionalFactor chi
      (z := s + w) hreflect).comp w hinner
  have htail : DifferentiableAt ℂ (fun u : ℂ =>
      dualTail chi (s + u) M) w :=
    (differentiableAt_dualTail chi M hz).comp w hinner
  unfold dualTailIntegrand
  exact ((hG.mul hQ).mul hfactor).mul htail

/-- Finite Cauchy--Goursat rectangle for the literal remainder, specialized
to Jutila's two vertical lines. -/
theorem dualTailIntegrand_boundary_sourceRectangle
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    {N h B : ℝ} (hN : 0 < N) (hh : 3 ≤ h)
    (hsigma0 : 0 ≤ s.re) (hsigma1 : s.re ≤ 1)
    (M : ℕ) :
    let a : ℝ := -(h / 2)
    let b : ℝ := -(1 / 2) - s.re
    (∫ x : ℝ in a..b,
          dualTailIntegrand chi s N h M (x - B * I)) -
        (∫ x : ℝ in a..b,
          dualTailIntegrand chi s N h M (x + B * I)) +
        I • (∫ y : ℝ in (-B)..B,
          dualTailIntegrand chi s N h M (b + y * I)) -
        I • (∫ y : ℝ in (-B)..B,
          dualTailIntegrand chi s N h M (a + y * I)) = 0 := by
  dsimp
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hab : -(h / 2) ≤ -(1 / 2) - s.re := by nlinarith
  let a : ℝ := -(h / 2)
  let b : ℝ := -(1 / 2) - s.re
  let z : ℂ := (a : ℂ) - B * I
  let w : ℂ := (b : ℂ) + B * I
  have hdiff : DifferentiableOn ℂ (dualTailIntegrand chi s N h M)
      (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    intro u hu
    have hure := hu.1
    have hzre : z.re = a := by simp [z, a]
    have hwre : w.re = b := by simp [w, b]
    rw [hzre, hwre, Set.uIcc_of_le hab] at hure
    apply (differentiableAt_dualTailIntegrand chi s hN M
      (show (s + u).re < 0 by
        simp only [Complex.add_re]
        linarith [hure.2])
      (show 0 < (1 + u / (h : ℂ)).re by
        have hreal : (1 + u / (h : ℂ)).re = 1 + u.re / h := by
          simp
        rw [hreal]
        have : -(1 / 2 : ℝ) ≤ u.re / h := by
          apply (le_div_iff₀ hh0).2
          linarith [hure.1]
        linarith)).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (dualTailIntegrand chi s N h M) z w hdiff
  simpa [z, w, a, b, sub_eq_add_neg, mul_comm, mul_left_comm,
    mul_assoc] using hrect

end

end JutilaDualTailContour

#print axioms JutilaDualTailContour.dualTail_eq_shifted_tsum
#print axioms JutilaDualTailContour.differentiableAt_dualTail
#print axioms JutilaDualTailContour.differentiableAt_dualTailIntegrand
#print axioms JutilaDualTailContour.dualTailIntegrand_boundary_sourceRectangle
