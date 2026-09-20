import GuthMaynardS3Assembly

set_option maxHeartbeats 500000

namespace GuthMaynardProp31DirectAbsorption
noncomputable section
open scoped BigOperators

/-- The eight affine exponent rows in the optimized `k=2` Prop.31 source. -/
def a (σ : ℝ) : Fin 8 → ℝ :=
  ![3, 2, 11 / 5, 23 / 10, 12 / 5,
    21 / 5 - 2 * σ, 27 / 10 - σ, 57 / 20 - σ]

def b : Fin 8 → ℝ :=
  ![0, 2, 3 / 2, 13 / 8, 3 / 2, 1, 2, 29 / 16]

def q (σ : ℝ) : ℝ := 18 / 5 - 4 * σ
def l (σ : ℝ) : ℝ := 6 * σ - 3

/-- Every row has the exact affine margin needed for the `R>N^q` branch. -/
theorem exponent_margin
    {σ : ℝ} (hσlo : (7 / 10 : ℝ) ≤ σ) (hσhi : σ ≤ (4 / 5 : ℝ)) :
    ∀ i : Fin 8, a σ i + (b i - 2) * q σ ≤ q σ + l σ := by
  intro i
  fin_cases i <;> simp [a, b, q, l] <;> linarith

/-- All eight radial exponents are at most two. -/
theorem radial_exponent_bound (i : Fin 8) : b i ≤ (2 : ℝ) := by
  fin_cases i <;> simp [b] <;> norm_num

/-- Direct eight-monomial absorption, with no hidden source estimate. -/
theorem prop31_direct_absorption
    {σ N R F : ℝ}
    (hσlo : (7 / 10 : ℝ) ≤ σ) (hσhi : σ ≤ (4 / 5 : ℝ))
    (hN : 1 ≤ N) (hR : 0 ≤ R) (hF : 1 ≤ F)
    (hprem : R ^ 3 * Real.rpow N (l σ) ≤
      F * ∑ i : Fin 8, (Real.rpow N (a σ i) * Real.rpow R (b i))) :
    R ≤ 8 * F * Real.rpow N (q σ) := by
  have hqlo : 0 ≤ q σ := by dsimp [q]; linarith
  have hlpos : 0 < Real.rpow N (l σ) := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  by_cases hsmall : R ≤ Real.rpow N (q σ)
  · exact hsmall.trans (by nlinarith [hF, Real.rpow_nonneg hNpos.le (q σ)])
  · have hNqpos : 0 < Real.rpow N (q σ) := Real.rpow_pos_of_pos hNpos _
    have hRpos : 0 < R := hNqpos.trans (lt_of_not_ge hsmall)
    have hR1 : 1 ≤ R := by
      have hNq1 : 1 ≤ Real.rpow N (q σ) := by
        calc
          (1 : ℝ) = Real.rpow N (0 : ℝ) := (Real.rpow_zero N).symm
          _ ≤ Real.rpow N (q σ) := Real.rpow_le_rpow_of_exponent_le hN hqlo
      exact hNq1.trans (le_of_lt (lt_of_not_ge hsmall))
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
    have hloggap : 0 ≤ Real.log R - q σ * Real.log N := by
      have hlog := Real.log_le_log hNqpos (le_of_not_ge hsmall)
      have hlogpow : Real.log (Real.rpow N (q σ)) = q σ * Real.log N :=
        Real.log_rpow hNpos _
      rw [hlogpow] at hlog
      linarith
    have hrow : ∀ i : Fin 8,
        Real.rpow N (a σ i) * Real.rpow R (b i) ≤
          Real.rpow R 2 * Real.rpow N (q σ + l σ) := by
      intro i
      have hb : b i ≤ (2 : ℝ) := radial_exponent_bound i
      have hm := exponent_margin hσlo hσhi i
      have hlogineq :
          (a σ i) * Real.log N + (b i) * Real.log R ≤
            (q σ + l σ) * Real.log N + 2 * Real.log R := by
        have hcoef : 0 ≤ 2 - b i := by linarith
        nlinarith
      have hleft : 0 < Real.rpow N (a σ i) * Real.rpow R (b i) :=
        mul_pos (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hRpos _)
      have hright : 0 < Real.rpow R 2 * Real.rpow N (q σ + l σ) :=
        mul_pos (Real.rpow_pos_of_pos hRpos _) (Real.rpow_pos_of_pos hNpos _)
      have hNexp : Real.rpow N (a σ i) = Real.exp (a σ i * Real.log N) := by
        calc
          Real.rpow N (a σ i) = Real.exp (Real.log N * a σ i) :=
            Real.rpow_def_of_pos hNpos (a σ i)
          _ = Real.exp (a σ i * Real.log N) := by congr 1 <;> ring
      have hRexp : Real.rpow R (b i) = Real.exp (b i * Real.log R) := by
        calc
          Real.rpow R (b i) = Real.exp (Real.log R * b i) :=
            Real.rpow_def_of_pos hRpos (b i)
          _ = Real.exp (b i * Real.log R) := by congr 1 <;> ring
      have hleftExp : Real.rpow N (a σ i) * Real.rpow R (b i) =
          Real.exp (a σ i * Real.log N + b i * Real.log R) := by
        rw [hNexp, hRexp, ← Real.exp_add]
      have hR2exp : Real.rpow R 2 = Real.exp (2 * Real.log R) := by
        calc
          Real.rpow R 2 = Real.exp (Real.log R * 2) :=
            Real.rpow_def_of_pos hRpos (2 : ℝ)
          _ = Real.exp (2 * Real.log R) := by congr 1 <;> ring
      have hNqlExp : Real.rpow N (q σ + l σ) =
          Real.exp ((q σ + l σ) * Real.log N) := by
        calc
          Real.rpow N (q σ + l σ) =
              Real.exp (Real.log N * (q σ + l σ)) :=
            Real.rpow_def_of_pos hNpos (q σ + l σ)
          _ = Real.exp ((q σ + l σ) * Real.log N) := by congr 1 <;> ring
      have hrightExp : Real.rpow R 2 * Real.rpow N (q σ + l σ) =
          Real.exp ((q σ + l σ) * Real.log N + 2 * Real.log R) := by
        rw [hR2exp, hNqlExp, ← Real.exp_add]
        ring_nf
      rw [hleftExp, hrightExp]
      exact Real.exp_le_exp.mpr hlogineq
    have hsum :
        (∑ i : Fin 8, (Real.rpow N (a σ i) * Real.rpow R (b i))) ≤
          8 * (Real.rpow R 2 * Real.rpow N (q σ + l σ)) := by
      calc
        _ ≤ ∑ _i : Fin 8, (Real.rpow R 2 * Real.rpow N (q σ + l σ)) :=
          Finset.sum_le_sum (fun i _ => hrow i)
        _ = 8 * (Real.rpow R 2 * Real.rpow N (q σ + l σ)) := by simp
    have hcombined : R ^ 3 * Real.rpow N (l σ) ≤
        8 * F * (Real.rpow R 2 * Real.rpow N (q σ + l σ)) := by
      calc
        R ^ 3 * Real.rpow N (l σ) ≤
            F * ∑ i : Fin 8, (Real.rpow N (a σ i) * Real.rpow R (b i)) := hprem
        _ ≤ F * (8 * (Real.rpow R 2 * Real.rpow N (q σ + l σ))) := by
          gcongr
        _ = 8 * F * (Real.rpow R 2 * Real.rpow N (q σ + l σ)) := by ring
    have hpowadd : Real.rpow N (q σ + l σ) =
        Real.rpow N (q σ) * Real.rpow N (l σ) :=
      Real.rpow_add hNpos (q σ) (l σ)
    have hcancel : 0 < Real.rpow R 2 * Real.rpow N (l σ) :=
      mul_pos (Real.rpow_pos_of_pos hRpos _) (Real.rpow_pos_of_pos hNpos _)
    rw [hpowadd] at hcombined
    have hR2pow : R ^ 2 = Real.rpow R (2 : ℝ) := by
      simpa using (Real.rpow_natCast R 2).symm
    have hcancel' :
        (Real.rpow R 2 * Real.rpow N (l σ)) * R ≤
          (Real.rpow R 2 * Real.rpow N (l σ)) *
            (8 * F * Real.rpow N (q σ)) := by
      calc
        (Real.rpow R 2 * Real.rpow N (l σ)) * R =
            R ^ 3 * Real.rpow N (l σ) := by
          rw [← hR2pow]
          ring
        _ ≤ 8 * F * (Real.rpow R 2 *
            (Real.rpow N (q σ) * Real.rpow N (l σ))) := hcombined
        _ = (Real.rpow R 2 * Real.rpow N (l σ)) *
            (8 * F * Real.rpow N (q σ)) := by ring
    exact le_of_mul_le_mul_left hcancel' hcancel

end
end GuthMaynardProp31DirectAbsorption

#print axioms GuthMaynardProp31DirectAbsorption.exponent_margin
#print axioms GuthMaynardProp31DirectAbsorption.prop31_direct_absorption
