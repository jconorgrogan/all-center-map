import MontgomeryTheorem83Halasz
import GammaMellinInversion

/-!
# Montgomery's equation-(30) positive exponential majorant

This is the weight used in the proof of Theorem 3 of H. L. Montgomery,
*Mean and Large Values of Dirichlet Polynomials*, Invent. Math. 8 (1969),
334--345:

`f_N(n) = exp (1 - n/N)`.

Unlike the equation-(33) weight used for the mean-value theorem, this
majorant is designed for the Halasz large-value corollary.  It is at least
one on `1 <= n <= N`, its full positive-integer mass is strictly less than
`exp(1) * N`, and it has the literal Gamma Mellin representation printed in
equation (32).  All three facts are proved here without an analytic source
premise.
-/

namespace MAPMontgomeryEquation30Majorant

open scoped BigOperators
open Complex MeasureTheory

noncomputable section

/-- Montgomery's equation-(30) weight. -/
def equation30Weight (N : ℝ) (n : ℕ) : ℝ :=
  Real.exp (1 - (n : ℝ) / N)

theorem equation30Weight_pos (N : ℝ) (n : ℕ) :
    0 < equation30Weight N n := by
  exact Real.exp_pos _

/-- Source condition (20) for `M=0`: the exponential weight majorizes the
hard initial interval. -/
theorem equation30Weight_ge_one
    {N : ℝ} (hN : 0 < N) {n : ℕ}
    (hn : (n : ℝ) ≤ N) :
    1 ≤ equation30Weight N n := by
  have : (n : ℝ) / N ≤ 1 := (div_le_one hN).2 hn
  exact Real.one_le_exp (by linarith)

/-- Dyadic specialization used by the detector shell: equation (30) with
scale `2D` majorizes every coefficient supported on `(D,2D]`. -/
theorem equation30Weight_two_mul_ge_one_on_dyadic
    {D : ℕ} (hD : 1 ≤ D) {n : ℕ}
    (hn : n ∈ MontgomeryVaughanFiniteReduction.dyadicSupport D) :
    1 ≤ equation30Weight (2 * (D : ℝ)) n := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hnle : (n : ℝ) ≤ 2 * (D : ℝ) := by
    have := (Finset.mem_Ioc.mp hn).2
    exact_mod_cast this
  exact equation30Weight_ge_one (by positivity) hnle

/-- Equation (30) is a scalar multiple of a geometric progression. -/
theorem equation30Weight_eq_geometric
    {N : ℝ} (hN : 0 < N) (n : ℕ) :
    equation30Weight N n =
      Real.exp 1 * (Real.exp (-(1 / N))) ^ n := by
  unfold equation30Weight
  rw [← Real.exp_nat_mul]
  rw [← Real.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem summable_equation30Weight_nat
    {N : ℝ} (hN : 0 < N) :
    Summable (fun n : ℕ => equation30Weight N n) := by
  have hr : Real.exp (-(1 / N)) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by
      have : -(1 / N) < 0 := neg_lt_zero.mpr (one_div_pos.mpr hN)
      simpa using this)
  simpa only [equation30Weight_eq_geometric hN] using
    (summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left
      (Real.exp 1)

theorem summable_equation30Weight_positive
    {N : ℝ} (hN : 0 < N) :
    Summable (fun n : {n : ℕ // 0 < n} => equation30Weight N n) := by
  exact (summable_equation30Weight_nat hN).subtype {n : ℕ | 0 < n}

/-- Exact full mass on the positive integers, Montgomery's equation (31). -/
theorem equation30_mass_eq
    {N : ℝ} (hN : 0 < N) :
    (∑' n : ℕ, equation30Weight N (n + 1)) =
      Real.exp 1 * Real.exp (-(1 / N)) /
        (1 - Real.exp (-(1 / N))) := by
  let r : ℝ := Real.exp (-(1 / N))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    have hneg : -(1 / N) < 0 := neg_lt_zero.mpr (one_div_pos.mpr hN)
    exact Real.exp_lt_exp.mpr (by simpa using hneg)
  have hgeom := tsum_geometric_of_lt_one hr0 hr1
  simp_rw [equation30Weight_eq_geometric hN]
  rw [show (∑' n : ℕ, Real.exp 1 * r ^ (n + 1)) =
      Real.exp 1 * ∑' n : ℕ, r ^ (n + 1) by
        exact (tsum_mul_left : (∑' n : ℕ, Real.exp 1 * r ^ (n + 1)) = _)]
  simp_rw [pow_succ']
  rw [tsum_mul_left, hgeom]
  dsimp [r]
  field_simp

/-- The source's strict mass bound `F < eN`. -/
theorem equation30_mass_lt
    {N : ℝ} (hN : 0 < N) :
    (∑' n : ℕ, equation30Weight N (n + 1)) <
      Real.exp 1 * N := by
  rw [equation30_mass_eq hN]
  have hx : 0 < 1 / N := one_div_pos.mpr hN
  have hexp : 1 / N + 1 < Real.exp (1 / N) :=
    Real.add_one_lt_exp hx.ne'
  have hden : 0 < Real.exp (1 / N) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]
    exact hx
  have hrecip : 1 / (Real.exp (1 / N) - 1) < N := by
    rw [div_lt_iff₀ hden]
    have hNpos := hN
    have := sub_lt_sub_right hexp 1
    field_simp at this ⊢
    nlinarith
  have hratio :
      Real.exp (-(1 / N)) / (1 - Real.exp (-(1 / N))) =
        1 / (Real.exp (1 / N) - 1) := by
    rw [Real.exp_neg]
    have he : Real.exp (1 / N) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  rw [mul_div_assoc, hratio]
  exact mul_lt_mul_of_pos_left hrecip (Real.exp_pos 1)

/-- Exact mass when the harmless zeroth term is included.  This form is
convenient for finite-Hilbert approximations because every finite carrier is
a subset of `ℕ`. -/
theorem equation30_full_mass_eq
    {N : ℝ} (hN : 0 < N) :
    (∑' n : ℕ, equation30Weight N n) =
      Real.exp 1 / (1 - Real.exp (-(1 / N))) := by
  let r : ℝ := Real.exp (-(1 / N))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by
      have : -(1 / N) < 0 := neg_lt_zero.mpr (one_div_pos.mpr hN)
      simpa using this)
  simp_rw [equation30Weight_eq_geometric hN]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rfl

/-- Including `n=0` costs only one additional unit of the source scale. -/
theorem equation30_full_mass_lt
    {N : ℝ} (hN : 0 < N) :
    (∑' n : ℕ, equation30Weight N n) <
      Real.exp 1 * (N + 1) := by
  rw [equation30_full_mass_eq hN]
  have hx : 0 < 1 / N := one_div_pos.mpr hN
  have hexp : 1 / N + 1 < Real.exp (1 / N) :=
    Real.add_one_lt_exp hx.ne'
  have hden : 0 < Real.exp (1 / N) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]
    exact hx
  have hrecip : 1 / (Real.exp (1 / N) - 1) < N := by
    rw [div_lt_iff₀ hden]
    have := sub_lt_sub_right hexp 1
    field_simp at this ⊢
    nlinarith
  have hratio :
      1 / (1 - Real.exp (-(1 / N))) =
        1 + 1 / (Real.exp (1 / N) - 1) := by
    rw [Real.exp_neg]
    have he : Real.exp (1 / N) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    ring
  have hratio' :
      (1 - Real.exp (-(1 / N)))⁻¹ =
        1 + 1 / (Real.exp (1 / N) - 1) := by
    simpa only [one_div] using hratio
  rw [div_eq_mul_inv, hratio']
  exact mul_lt_mul_of_pos_left (by linarith) (Real.exp_pos 1)

/-! ## Exact coefficientwise Mellin formula -/

/-- Montgomery's equation (32), coefficientwise and with the standard
`1/(2*pi)` vertical-line normalization. -/
theorem equation30Weight_eq_gamma_vertical_integral
    {N c : ℝ} (hN : 0 < N) (hc : 0 < c)
    {n : ℕ} (hn : 0 < n) :
    (equation30Weight N n : ℂ) =
      (Real.exp 1 : ℂ) *
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, Complex.Gamma ((c : ℂ) + t * Complex.I) *
            ((N / n : ℝ) : ℂ) ^ ((c : ℂ) + t * Complex.I)) := by
  have hMellin :=
    MAPGammaMellinInversion.exp_neg_nat_div_eq_detector_right_line
      hc hN hn
  calc
    (equation30Weight N n : ℂ) =
        ((Real.exp 1 * Real.exp (-((n : ℝ) / N)) : ℝ) : ℂ) := by
      congr 1
      unfold equation30Weight
      rw [show 1 - (n : ℝ) / N = 1 + (-((n : ℝ) / N)) by ring,
        Real.exp_add]
    _ = (Real.exp 1 : ℂ) *
        (Real.exp (-((n : ℝ) / N)) : ℂ) := by
      exact Complex.ofReal_mul _ _
    _ = _ := by rw [hMellin]

end
end MAPMontgomeryEquation30Majorant

#print axioms MAPMontgomeryEquation30Majorant.equation30Weight_ge_one
#print axioms MAPMontgomeryEquation30Majorant.equation30_mass_eq
#print axioms MAPMontgomeryEquation30Majorant.equation30_mass_lt
#print axioms MAPMontgomeryEquation30Majorant.equation30Weight_eq_gamma_vertical_integral
