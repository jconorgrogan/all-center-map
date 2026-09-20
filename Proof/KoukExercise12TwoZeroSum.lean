import KoukTheorem12ThreeUniqueness
import PointwisePerronZeroSumBounds

/-!
# The zero-sum input to Koukoulopoulos, Exercise 12.2(a)

Theorem 12.3 leaves at most one zero inside its reciprocal-logarithmic
collar.  This file performs the exact finite-divisor split used in the
explicit formula: every other zero receives a uniform gap at height `T`,
while the possible exceptional atom is kept separate for Siegel absorption.
-/

namespace MAPKoukExercise12TwoZeroSum

open Complex Set DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge
open MAPLocalZeroWindow
open MAPPrimitiveLogDerivativeRemainderUnconditional
open MAPKoukTheorem12ThreeGlobal MAPKoukTheorem12ThreeUniqueness
open scoped BigOperators

noncomputable section

/-- The literal Theorem 12.3 collar predicate. -/
def inTheorem12ThreeCollar {q : ℕ} [NeZero q] (rho : ℂ) : Prop :=
  1 - rho.re <
    1 / (100000000000 * Real.log (arithmeticScale q rho.im))

/-- The collar portion of an arbitrary finite Perron divisor. -/
def theorem12ThreeCollarSupport
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma T : ℝ) : Finset ℂ := by
  classical
  exact (zeroSupport chi sigma T).filter
    (fun rho : ℂ => inTheorem12ThreeCollar (q := q) rho)

/-- The height-uniform reciprocal-logarithmic gap used in Exercise 12.2(a). -/
def exercise12TwoGap (q : ℕ) (T : ℝ) : ℝ :=
  1 / (100000000000 * Real.log ((q : ℝ) * (T + 2)))

theorem theorem12ThreeCollar_lt_half
    {q : ℕ} [NeZero q] {rho : ℂ}
    (hnear : inTheorem12ThreeCollar (q := q) rho) :
    1 / 2 < rho.re := by
  have htwo := two_le_arithmeticScale (q := q) rho.im
  have hlog : 1 / 2 < Real.log (arithmeticScale q rho.im) := by
    have hlog2 : 1 / 2 < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    exact hlog2.trans_le (Real.log_le_log (by norm_num) htwo)
  have hden : 2 < 100000000000 * Real.log (arithmeticScale q rho.im) := by
    nlinarith
  have hhalf :
      1 / (100000000000 * Real.log (arithmeticScale q rho.im)) <
        (1 / 2 : ℝ) := by
    exact one_div_lt_one_div_of_lt (by norm_num) hden
  unfold inTheorem12ThreeCollar at hnear
  linarith

/-- Every collar zero has precisely the exceptional shape and is simple. -/
theorem mem_collarSupport_exceptional
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma T : ℝ} {rho : ℂ}
    (hrho : rho ∈ theorem12ThreeCollarSupport chi sigma T) :
    chi ^ 2 = 1 ∧ rho.im = 0 ∧
      zeroMultiplicity chi sigma T rho = 1 := by
  classical
  rw [theorem12ThreeCollarSupport, Finset.mem_filter] at hrho
  have hmem := hrho.1
  have hnear := hrho.2
  exact primitive_global_nearOne_zero_is_exceptional chi hprim hchi hmem
    (theorem12ThreeCollar_lt_half hnear).le hnear

/-- The possible exceptional part of one primitive character's divisor has
cardinality at most one. -/
theorem card_theorem12ThreeCollarSupport_le_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    (sigma T : ℝ) :
    (theorem12ThreeCollarSupport chi sigma T).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro rho₁ rho₂ h₁ h₂
  have h₁' := h₁
  have h₂' := h₂
  rw [theorem12ThreeCollarSupport, Finset.mem_filter] at h₁' h₂'
  have hmem₁ := h₁'.1
  have hmem₂ := h₂'.1
  have hnear₁ := h₁'.2
  have hnear₂ := h₂'.2
  obtain ⟨hsq, him₁, _hm₁⟩ :=
    mem_collarSupport_exceptional chi hprim hchi h₁
  obtain ⟨_hsq₂, him₂, _hm₂⟩ :=
    mem_collarSupport_exceptional chi hprim hchi h₂
  have hcenter₁ := mem_centered_of_mem_zeroSupport chi hmem₁
    (theorem12ThreeCollar_lt_half hnear₁).le
  have hcenter₂ := mem_centered_of_mem_zeroSupport chi hmem₂
    (theorem12ThreeCollar_lt_half hnear₂).le
  have hcenter₁' : rho₁ ∈ centeredUnitWindowSupport chi (1 / 2) 0 := by
    simpa [him₁] using hcenter₁
  have hcenter₂' : rho₂ ∈ centeredUnitWindowSupport chi (1 / 2) 0 := by
    simpa [him₂] using hcenter₂
  apply primitive_nearOne_real_zero_unique chi hprim hchi hsq
    hcenter₁' hcenter₂' him₁ him₂
  · simpa [inTheorem12ThreeCollar, him₁, div_eq_mul_inv,
      mul_assoc, mul_comm] using hnear₁
  · simpa [inTheorem12ThreeCollar, him₂, div_eq_mul_inv,
      mul_assoc, mul_comm] using hnear₂

theorem exercise12TwoGap_pos
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 0 ≤ T) :
    0 < exercise12TwoGap q T := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
  have harg : 1 < (q : ℝ) * (T + 2) := by nlinarith
  have hlog : 0 < Real.log ((q : ℝ) * (T + 2)) := Real.log_pos harg
  unfold exercise12TwoGap
  exact one_div_pos.mpr (mul_pos (by norm_num) hlog)

/-- Outside the unique collar atom, Theorem 12.3 gives one gap uniform over
the whole Perron rectangle. -/
theorem exercise12TwoGap_le_one_sub_re_of_not_collar
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T : ℝ} (hT : 0 ≤ T) {rho : ℂ}
    (hrho : rho ∈ zeroSupport chi sigma T)
    (hregular : ¬ inTheorem12ThreeCollar (q := q) rho) :
    exercise12TwoGap q T ≤ 1 - rho.re := by
  have hrect := mem_zeroRectangle_of_mem_zeroSupport chi sigma T hrho
  have him : |rho.im| ≤ T := abs_le.mpr hrect.2
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hscalePos : 0 < arithmeticScale q rho.im := by
    linarith [two_le_arithmeticScale (q := q) rho.im]
  have hglobalPos : 0 < (q : ℝ) * (T + 2) := by
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    positivity
  have hscale : arithmeticScale q rho.im ≤ (q : ℝ) * (T + 2) := by
    unfold arithmeticScale
    exact mul_le_mul_of_nonneg_left (by linarith) hq0
  have hlogle : Real.log (arithmeticScale q rho.im) ≤
      Real.log ((q : ℝ) * (T + 2)) :=
    Real.log_le_log hscalePos hscale
  have hlocalLogPos : 0 < Real.log (arithmeticScale q rho.im) :=
    Real.log_pos (one_lt_two.trans_le (two_le_arithmeticScale (q := q) rho.im))
  have hden :
      0 < 100000000000 * Real.log (arithmeticScale q rho.im) := by
    positivity
  have hcollarCompare : exercise12TwoGap q T ≤
      1 / (100000000000 * Real.log (arithmeticScale q rho.im)) := by
    unfold exercise12TwoGap
    apply one_div_le_one_div_of_le hden
    exact mul_le_mul_of_nonneg_left hlogle (by norm_num)
  have hnotNear :
      1 / (100000000000 * Real.log (arithmeticScale q rho.im)) ≤
        1 - rho.re := by
    exact le_of_not_gt hregular
  exact hcollarCompare.trans hnotNear

/-- Source-shaped zero-sum estimate: all regular zeros receive the uniform
Exercise 12.2(a) gap, and the unique collar atom is supplied as one explicit
pointwise budget. -/
theorem norm_multiplicityWeightedPerronZeroSum_le_regular_add_exceptional
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma T x E : ℝ} (hT : 0 ≤ T) (hx : 1 ≤ x)
    (hsigma : 0 < sigma) (hE : 0 ≤ E)
    (hExceptional : ∀ rho ∈ theorem12ThreeCollarSupport chi sigma T,
      x ^ rho.re / sigma ≤ E) :
    ‖multiplicityWeightedPerronZeroSum chi sigma T x‖ ≤
      ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
          x ^ (1 - exercise12TwoGap q T) + E := by
  classical
  let S := zeroSupport chi sigma T
  let P : ℂ → Prop := inTheorem12ThreeCollar (q := q)
  let F : ℂ → ℝ := fun rho =>
    ‖(zeroMultiplicity chi sigma T rho : ℂ) * (x : ℂ) ^ rho / rho‖
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have htriangle : ‖multiplicityWeightedPerronZeroSum chi sigma T x‖ ≤
      ∑ rho ∈ S, F rho := by
    unfold multiplicityWeightedPerronZeroSum
    exact norm_sum_le _ _
  have hsplit : (∑ rho ∈ S, F rho) =
      (∑ rho ∈ S.filter P, F rho) +
        ∑ rho ∈ S.filter (fun rho => ¬ P rho), F rho := by
    simpa only [P] using (Finset.sum_filter_add_sum_filter_not S P F).symm
  have hcollarEq : S.filter P = theorem12ThreeCollarSupport chi sigma T := by
    dsimp [S, P, theorem12ThreeCollarSupport]
  have hnear : (∑ rho ∈ S.filter P, F rho) ≤ E := by
    rw [hcollarEq]
    calc
      (∑ rho ∈ theorem12ThreeCollarSupport chi sigma T, F rho) ≤
          ∑ _rho ∈ theorem12ThreeCollarSupport chi sigma T, E := by
        apply Finset.sum_le_sum
        intro rho hrho
        have hm := (mem_collarSupport_exceptional chi hprim hchi hrho).2.2
        have hrho' := hrho
        rw [theorem12ThreeCollarSupport, Finset.mem_filter] at hrho'
        have hmem := hrho'.1
        have hre := (mem_zeroRectangle_of_mem_zeroSupport chi sigma T hmem).1.1
        have hden : sigma ≤ ‖rho‖ := by
          calc
            sigma ≤ |rho.re| := by
              rw [abs_of_nonneg (hsigma.le.trans hre)]
              exact hre
            _ ≤ ‖rho‖ := Complex.abs_re_le_norm rho
        have hterm : F rho = x ^ rho.re / ‖rho‖ := by
          dsimp [F]
          rw [norm_div, norm_mul, Complex.norm_natCast,
            Complex.norm_cpow_eq_rpow_re_of_pos hx0, hm]
          norm_num
        rw [hterm]
        exact (div_le_div_of_nonneg_left
          (Real.rpow_nonneg hx0.le _) hsigma hden).trans
            (hExceptional rho hrho)
      _ = ((theorem12ThreeCollarSupport chi sigma T).card : ℝ) * E := by
        simp
      _ ≤ E := by
        have hcard := card_theorem12ThreeCollarSupport_le_one
          chi hprim hchi sigma T
        have hcardReal :
            ((theorem12ThreeCollarSupport chi sigma T).card : ℝ) ≤ 1 := by
          exact_mod_cast hcard
        nlinarith
  have hregular : (∑ rho ∈ S.filter (fun rho => ¬ P rho), F rho) ≤
      ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
        x ^ (1 - exercise12TwoGap q T) := by
    calc
      (∑ rho ∈ S.filter (fun rho => ¬ P rho), F rho) ≤
          ∑ rho ∈ S.filter (fun rho => ¬ P rho),
            ((zeroMultiplicity chi sigma T rho : ℝ) *
              x ^ (1 - exercise12TwoGap q T)) / sigma := by
        apply Finset.sum_le_sum
        intro rho hrho
        have hmem : rho ∈ zeroSupport chi sigma T :=
          (Finset.mem_filter.mp hrho).1
        have hnP : ¬ inTheorem12ThreeCollar (q := q) rho :=
          (Finset.mem_filter.mp hrho).2
        have hreGap := exercise12TwoGap_le_one_sub_re_of_not_collar
          chi hT hmem hnP
        have hreGap' : rho.re ≤ 1 - exercise12TwoGap q T := by
          linarith
        have hre := (mem_zeroRectangle_of_mem_zeroSupport chi sigma T hmem).1.1
        have hden : sigma ≤ ‖rho‖ := by
          calc
            sigma ≤ |rho.re| := by
              rw [abs_of_nonneg (hsigma.le.trans hre)]
              exact hre
            _ ≤ ‖rho‖ := Complex.abs_re_le_norm rho
        dsimp [F]
        rw [norm_div, norm_mul, Complex.norm_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        calc
          (zeroMultiplicity chi sigma T rho : ℝ) * x ^ rho.re / ‖rho‖ ≤
              (zeroMultiplicity chi sigma T rho : ℝ) * x ^ rho.re /
                sigma :=
            div_le_div_of_nonneg_left
              (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hx0.le _))
              hsigma hden
          _ ≤ (zeroMultiplicity chi sigma T rho : ℝ) *
                x ^ (1 - exercise12TwoGap q T) / sigma :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le hx hreGap')
                (Nat.cast_nonneg _)) hsigma.le
      _ ≤ ∑ rho ∈ S,
            ((zeroMultiplicity chi sigma T rho : ℝ) *
              x ^ (1 - exercise12TwoGap q T)) / sigma := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
          x ^ (1 - exercise12TwoGap q T) := by
        rw [show (∑ rho ∈ S,
              ((zeroMultiplicity chi sigma T rho : ℝ) *
                x ^ (1 - exercise12TwoGap q T)) / sigma) =
            ((∑ rho ∈ S, (zeroMultiplicity chi sigma T rho : ℝ)) /
              sigma) * x ^ (1 - exercise12TwoGap q T) by
          calc
            _ = ∑ rho ∈ S,
                ((zeroMultiplicity chi sigma T rho : ℝ) / sigma) *
                  x ^ (1 - exercise12TwoGap q T) := by
                    apply Finset.sum_congr rfl
                    intro rho hrho
                    ring
            _ = (∑ rho ∈ S,
                  (zeroMultiplicity chi sigma T rho : ℝ) / sigma) *
                    x ^ (1 - exercise12TwoGap q T) := by rw [Finset.sum_mul]
            _ = ((∑ rho ∈ S,
                  (zeroMultiplicity chi sigma T rho : ℝ)) / sigma) *
                    x ^ (1 - exercise12TwoGap q T) := by rw [Finset.sum_div]]
        dsimp only [S]
        rw [← Nat.cast_sum, sum_zeroMultiplicity_eq_dirichletZeroCount]
  calc
    ‖multiplicityWeightedPerronZeroSum chi sigma T x‖ ≤
        ∑ rho ∈ S, F rho := htriangle
    _ = (∑ rho ∈ S.filter P, F rho) +
        ∑ rho ∈ S.filter (fun rho => ¬ P rho), F rho := hsplit
    _ ≤ E + ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
        x ^ (1 - exercise12TwoGap q T) := add_le_add hnear hregular
    _ = ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
        x ^ (1 - exercise12TwoGap q T) + E := by ring

#print axioms MAPKoukExercise12TwoZeroSum.card_theorem12ThreeCollarSupport_le_one
#print axioms MAPKoukExercise12TwoZeroSum.norm_multiplicityWeightedPerronZeroSum_le_regular_add_exceptional

end

end MAPKoukExercise12TwoZeroSum
