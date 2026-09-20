import GuthMaynardJIterationDeterministic

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

def iterSqrt : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => Real.sqrt (iterSqrt n x)

@[simp] theorem iterSqrt_zero (x : ℝ) : iterSqrt 0 x = x := rfl
@[simp] theorem iterSqrt_succ (n : ℕ) (x : ℝ) :
    iterSqrt (n + 1) x = Real.sqrt (iterSqrt n x) := rfl

theorem iterSqrt_one_le
    {n : ℕ} {x : ℝ} (hx : 1 ≤ x) : 1 ≤ iterSqrt n x := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [iterSqrt_succ]
      exact Real.one_le_sqrt.2 ih

theorem iterSqrt_eq_rpow
    {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    iterSqrt n x = Real.rpow x ((2 : ℝ) ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterSqrt_succ, ih, Real.sqrt_eq_rpow]
      calc
        Real.rpow (Real.rpow x ((2 : ℝ) ^ n)⁻¹) (1 / 2) =
            Real.rpow x (((2 : ℝ) ^ n)⁻¹ * (1 / 2)) :=
          (Real.rpow_mul hx _ _).symm
        _ = Real.rpow x ((2 : ℝ) ^ (n + 1))⁻¹ := by
          congr 1
          field_simp
          ring

/-- One normalized square-root step.  The scale `D` pays for both additive
terms, while `y ≥ 1` lets the additive term be absorbed into `D * sqrt y`. -/
theorem normalized_sqrt_step
    {A B D x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 1 ≤ D)
    (hA2 : 2 * A ≤ D) (hB4 : 4 * B ^ 2 ≤ D)
    (hx : 0 ≤ x) (hy : 1 ≤ y) (hxy : x ≤ D * y) :
    A + B * Real.sqrt x ≤ D * Real.sqrt y := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hsy : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
  have hsd : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hsx : Real.sqrt x ≤ Real.sqrt D * Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt hxy
    rw [Real.sqrt_mul hD0] at hh
    exact hh
  have hBsq : B ^ 2 ≤ (Real.sqrt D / 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hD0]
    nlinarith [hB4]
  have hBroot : B ≤ Real.sqrt D / 2 := by
    apply (sq_le_sq₀ hB (by positivity)).1
    exact hBsq
  have hBroot' : B * Real.sqrt D ≤ D / 2 := by
    have hh := mul_le_mul_of_nonneg_right hBroot hsd
    calc
      B * Real.sqrt D ≤ (Real.sqrt D / 2) * Real.sqrt D := hh
      _ = D / 2 := by
        rw [show (Real.sqrt D / 2) * Real.sqrt D =
          (Real.sqrt D * Real.sqrt D) / 2 by ring]
        rw [← pow_two, Real.sq_sqrt hD0]
  have hsy1 : 1 ≤ Real.sqrt y := Real.one_le_sqrt.2 hy
  calc
    A + B * Real.sqrt x ≤ A + B * (Real.sqrt D * Real.sqrt y) := by
      gcongr
    _ ≤ D * Real.sqrt y := by nlinarith [hA2, hBroot', hsy1]

/-- Finite downward bootstrap.  The endcap enters only through an iterated
square root, so its contribution has exponent `1 / 2^N` after the standard
iterated-square-root identity. -/
theorem finite_sqrt_recurrence_bound
    {A B H : ℝ} {N : ℕ} {K : ℕ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hK : ∀ n, 0 ≤ K n)
    (hrec : ∀ n, n < N → K n ≤ A + B * Real.sqrt (K (n + 1)))
    (hend : K N ≤ H) :
    K 0 ≤ (max 1 (max (2 * A) (4 * B ^ 2))) *
      iterSqrt N (max 1 (H / max 1 (max (2 * A) (4 * B ^ 2)))) := by
  let D : ℝ := max 1 (max (2 * A) (4 * B ^ 2))
  let U : ℝ := max 1 (H / D)
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_max_left _ _
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hU : 1 ≤ U := by
    dsimp [U]
    exact le_max_left _ _
  have hHle : H ≤ D * U := by
    dsimp [U]
    by_cases hHD : H / D ≤ 1
    · have hmul : H ≤ D := by
        have hh := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hD)).mp hHD
        simpa using hh
      calc H ≤ D := hmul
           _ = D * 1 := by ring
           _ ≤ D * max 1 (H / D) :=
             mul_le_mul_of_nonneg_left (le_max_left _ _) hD0
    · have hmul : H / D ≤ max 1 (H / D) := le_max_right _ _
      have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
      calc H = D * (H / D) := by field_simp
           _ ≤ D * max 1 (H / D) := mul_le_mul_of_nonneg_left hmul hD0
  have hstep : ∀ n, n < N →
      K (n + 1) ≤ D * iterSqrt (N - (n + 1)) U →
      K n ≤ D * iterSqrt (N - n) U := by
    intro n hn hbound
    have hy : 1 ≤ iterSqrt (N - (n + 1)) U := iterSqrt_one_le hU
    have hmap := normalized_sqrt_step hA hB hD
      (by
        dsimp [D]
        exact le_trans (le_max_left _ _) (le_max_right _ _))
      (by
        dsimp [D]
        exact le_trans (le_max_right _ _) (le_max_right _ _))
      (hK (n + 1)) hy hbound
    calc
      K n ≤ A + B * Real.sqrt (K (n + 1)) := hrec n hn
      _ ≤ D * Real.sqrt (iterSqrt (N - (n + 1)) U) := hmap
      _ = D * iterSqrt (N - n) U := by
        have hidx : N - (n + 1) + 1 = N - n := by omega
        rw [← hidx, iterSqrt_succ]
  have hdown : ∀ k : ℕ, k ≤ N → K (N - k) ≤ D * iterSqrt k U := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa using (hend.trans hHle)
    | succ k ih =>
        intro hk
        have hkN : k ≤ N := by omega
        have hprev := ih hkN
        have hidx : N - k = N - (k + 1) + 1 := by omega
        have hprev' : K (N - (k + 1) + 1) ≤ D * iterSqrt k U := by
          simpa [hidx] using hprev
        have hlt : N - (k + 1) < N := by omega
        have harg : N - (N - (k + 1) + 1) = k := by omega
        have hh := hstep (N - (k + 1)) hlt (by simpa [harg] using hprev')
        have harg2 : N - (N - (k + 1)) = k + 1 := by omega
        rw [harg2] at hh
        exact hh
  have hzero := hdown N (le_refl N)
  simpa [D, U] using hzero

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.normalized_sqrt_step
#print axioms GuthMaynardJIteration.finite_sqrt_recurrence_bound
#print axioms GuthMaynardJIteration.iterSqrt_eq_rpow
