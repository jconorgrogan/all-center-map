import JutilaDualTailIntegrandBound

/-!
# Two-step recurrence for Jutila's deep-left multiplier

This replaces a black-box Stirling invocation by the exact `Gammaℝ(s+2)`
recurrence.  The exceptional real ordinates are excluded here; on a vertical
integral they form a null singleton and can be restored by an a.e. argument.
-/

namespace JutilaMultiplierRecurrence

open Complex DirichletCharacter
open JutilaCriticalPartialTruncation

noncomputable section

variable {q : ℕ} [NeZero q]

private theorem gammaR_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.Gammaℝ z ≠ 0 := by
  intro hzero
  rw [Complex.Gammaℝ_eq_zero_iff] at hzero
  obtain ⟨n, hn⟩ := hzero
  have him := congrArg Complex.im hn
  simp at him
  exact hz him

private theorem inv_even (chi : DirichletCharacter ℂ q) (hchi : chi.Even) :
    chi⁻¹.Even := by
  simpa only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_one] using
    congrArg (fun z : ℂ => z⁻¹) hchi

private theorem inv_odd (chi : DirichletCharacter ℂ q) (hchi : chi.Odd) :
    chi⁻¹.Odd := by
  simpa only [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', inv_neg,
    inv_one] using congrArg (fun z : ℂ => z⁻¹) hchi

/-- Even-parity archimedean quotient under a two-unit shift to the right. -/
theorem even_gammaQuotient_shift_two (z : ℂ) (hz : z.im ≠ 0) :
    Complex.Gammaℝ (1 - z) / Complex.Gammaℝ z =
      ((-1 - z) * z / ((2 : ℂ) * Real.pi) ^ 2) *
        (Complex.Gammaℝ (1 - (z + 2)) / Complex.Gammaℝ (z + 2)) := by
  have hzm : -1 - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hz (by linarith)
  have hz0 : z ≠ 0 := by
    intro h
    exact hz (by simp [h])
  have hGz := gammaR_ne_zero_of_im_ne_zero hz
  have hGz2 : Complex.Gammaℝ (z + 2) ≠ 0 := by
    apply gammaR_ne_zero_of_im_ne_zero
    simpa using hz
  have hnum := Complex.Gammaℝ_add_two hzm
  have hden := Complex.Gammaℝ_add_two hz0
  rw [show (-1 - z) + 2 = 1 - z by ring] at hnum
  rw [hnum, hden]
  field_simp [hGz, hGz2, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

/-- Odd-parity archimedean quotient under a two-unit shift to the right. -/
theorem odd_gammaQuotient_shift_two (z : ℂ) (hz : z.im ≠ 0) :
    Complex.Gammaℝ (2 - z) / Complex.Gammaℝ (z + 1) =
      ((-z) * (z + 1) / ((2 : ℂ) * Real.pi) ^ 2) *
        (Complex.Gammaℝ (2 - (z + 2)) /
          Complex.Gammaℝ ((z + 2) + 1)) := by
  have hzm : -z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    exact hz (by simpa using him)
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hz (by linarith)
  have hGz1 : Complex.Gammaℝ (z + 1) ≠ 0 := by
    apply gammaR_ne_zero_of_im_ne_zero
    simpa using hz
  have hGz3 : Complex.Gammaℝ ((z + 2) + 1) ≠ 0 := by
    apply gammaR_ne_zero_of_im_ne_zero
    simpa using hz
  have hnum := Complex.Gammaℝ_add_two hzm
  have hden := Complex.Gammaℝ_add_two hz1
  rw [show (-z) + 2 = 2 - z by ring] at hnum
  rw [show (z + 1) + 2 = (z + 2) + 1 by ring] at hden
  rw [hnum, hden]
  field_simp [hGz1, hGz3, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

private theorem conductor_cpow_shift_two (z : ℂ) :
    (q : ℂ) ^ ((1 : ℂ) / 2 - z) =
      (q : ℂ) ^ (2 : ℕ) *
        (q : ℂ) ^ ((1 : ℂ) / 2 - (z + 2)) := by
  calc
    (q : ℂ) ^ ((1 : ℂ) / 2 - z) =
        (q : ℂ) ^ ((2 : ℂ) + ((1 : ℂ) / 2 - (z + 2))) := by
      congr 1
      ring
    _ = (q : ℂ) ^ (2 : ℂ) *
        (q : ℂ) ^ ((1 : ℂ) / 2 - (z + 2)) := by
      rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (NeZero.ne q))]
    _ = (q : ℂ) ^ (2 : ℕ) *
        (q : ℂ) ^ ((1 : ℂ) / 2 - (z + 2)) := by
      congr 1
      exact Complex.cpow_natCast (q : ℂ) 2

/-- Exact even-parity two-step recurrence for the complete multiplier. -/
theorem reflectedDualMultiplier_shift_two_even
    (chi : DirichletCharacter ℂ q) (hchi : chi.Even)
    (z : ℂ) (hz : z.im ≠ 0) :
    reflectedDualMultiplier chi z =
      (q : ℂ) ^ (2 : ℕ) *
        ((-1 - z) * z / ((2 : ℂ) * Real.pi) ^ 2) *
        reflectedDualMultiplier chi (z + 2) := by
  have hinv := inv_even chi hchi
  unfold reflectedDualMultiplier
  rw [hinv.gammaFactor_def, hchi.gammaFactor_def,
    hinv.gammaFactor_def, hchi.gammaFactor_def,
    conductor_cpow_shift_two (q := q) z,
    even_gammaQuotient_shift_two z hz]
  ring

/-- Exact odd-parity two-step recurrence for the complete multiplier. -/
theorem reflectedDualMultiplier_shift_two_odd
    (chi : DirichletCharacter ℂ q) (hchi : chi.Odd)
    (z : ℂ) (hz : z.im ≠ 0) :
    reflectedDualMultiplier chi z =
      (q : ℂ) ^ (2 : ℕ) *
        ((-z) * (z + 1) / ((2 : ℂ) * Real.pi) ^ 2) *
        reflectedDualMultiplier chi (z + 2) := by
  have hinv := inv_odd chi hchi
  unfold reflectedDualMultiplier
  rw [hinv.gammaFactor_def, hchi.gammaFactor_def,
    hinv.gammaFactor_def, hchi.gammaFactor_def]
  rw [show 1 - z + 1 = 2 - z by ring,
    show 1 - (z + 2) + 1 = 2 - (z + 2) by ring,
    conductor_cpow_shift_two (q := q) z,
    odd_gammaQuotient_shift_two z hz]
  ring

def shiftTwo (z : ℂ) (n : ℕ) : ℂ := z + (2 * n : ℕ)

def evenStep (q : ℕ) (z : ℂ) : ℂ :=
  (q : ℂ) ^ (2 : ℕ) *
    ((-1 - z) * z / ((2 : ℂ) * Real.pi) ^ 2)

def oddStep (q : ℕ) (z : ℂ) : ℂ :=
  (q : ℂ) ^ (2 : ℕ) *
    ((-z) * (z + 1) / ((2 : ℂ) * Real.pi) ^ 2)

def evenStepProduct (q : ℕ) (z : ℂ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, ‖evenStep q (shiftTwo z j)‖

def oddStepProduct (q : ℕ) (z : ℂ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, ‖oddStep q (shiftTwo z j)‖

theorem norm_evenStep_le (q : ℕ) (z : ℂ) :
    ‖evenStep q z‖ ≤ (q : ℝ) ^ 2 * (1 + ‖z‖) ^ 2 := by
  have hpi : (1 : ℝ) ≤ ‖((2 : ℂ) * Real.pi) ^ 2‖ := by
    rw [norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hdiv :
      ‖(-1 - z) * z / ((2 : ℂ) * Real.pi) ^ 2‖ ≤
        ‖(-1 - z) * z‖ := by
    rw [norm_div]
    exact (div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hpi).trans_eq
      (div_one _)
  have hleft : ‖-1 - z‖ ≤ 1 + ‖z‖ := by
    calc
      ‖-1 - z‖ ≤ ‖(-1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ := by norm_num
  have hzle : ‖z‖ ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hqnorm : ‖(q : ℂ) ^ (2 : ℕ)‖ = (q : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_natCast]
  unfold evenStep
  rw [norm_mul, hqnorm]
  gcongr
  exact hdiv.trans (by
    simpa [pow_two] using
      mul_le_mul hleft hzle (norm_nonneg _) (by positivity))

theorem norm_oddStep_le (q : ℕ) (z : ℂ) :
    ‖oddStep q z‖ ≤ (q : ℝ) ^ 2 * (1 + ‖z‖) ^ 2 := by
  have hpi : (1 : ℝ) ≤ ‖((2 : ℂ) * Real.pi) ^ 2‖ := by
    rw [norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hdiv :
      ‖(-z) * (z + 1) / ((2 : ℂ) * Real.pi) ^ 2‖ ≤
        ‖(-z) * (z + 1)‖ := by
    rw [norm_div]
    exact (div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hpi).trans_eq
      (div_one _)
  have hright : ‖z + 1‖ ≤ 1 + ‖z‖ := by
    calc
      ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 1 + ‖z‖ := by norm_num; ring
  have hzle : ‖-z‖ ≤ 1 + ‖z‖ := by
    rw [norm_neg]
    linarith [norm_nonneg z]
  have hqnorm : ‖(q : ℂ) ^ (2 : ℕ)‖ = (q : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_natCast]
  unfold oddStep
  rw [norm_mul, hqnorm]
  gcongr
  exact hdiv.trans (by
    simpa [pow_two] using
      mul_le_mul hzle hright (norm_nonneg _) (by positivity))

theorem shiftTwo_succ (z : ℂ) (n : ℕ) :
    shiftTwo z n + 2 = shiftTwo z (n + 1) := by
  unfold shiftTwo
  push_cast
  ring

theorem shiftTwo_im (z : ℂ) (n : ℕ) : (shiftTwo z n).im = z.im := by
  simp [shiftTwo]

theorem norm_shiftTwo_le (z : ℂ) (n : ℕ) :
    ‖shiftTwo z n‖ ≤ ‖z‖ + 2 * n := by
  unfold shiftTwo
  calc
    ‖z + (2 * n : ℕ)‖ ≤ ‖z‖ + ‖((2 * n : ℕ) : ℂ)‖ := norm_add_le _ _
    _ = ‖z‖ + 2 * n := by
      rw [Complex.norm_natCast]
      norm_num

theorem evenStepProduct_le (q : ℕ) (z : ℂ) (n : ℕ) :
    evenStepProduct q z n ≤
      ((q : ℝ) ^ 2 * (1 + ‖z‖ + 2 * n) ^ 2) ^ n := by
  unfold evenStepProduct
  calc
    (∏ j ∈ Finset.range n, ‖evenStep q (shiftTwo z j)‖) ≤
        ∏ _j ∈ Finset.range n,
          ((q : ℝ) ^ 2 * (1 + ‖z‖ + 2 * n) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        have hjn : j < n := Finset.mem_range.mp hj
        have hshift := norm_shiftTwo_le z j
        have hrad : 1 + ‖shiftTwo z j‖ ≤ 1 + ‖z‖ + 2 * n := by
          have hjR : (j : ℝ) ≤ n := by exact_mod_cast hjn.le
          linarith
        exact (norm_evenStep_le q (shiftTwo z j)).trans (by gcongr)
    _ = ((q : ℝ) ^ 2 * (1 + ‖z‖ + 2 * n) ^ 2) ^ n := by simp

theorem oddStepProduct_le (q : ℕ) (z : ℂ) (n : ℕ) :
    oddStepProduct q z n ≤
      ((q : ℝ) ^ 2 * (1 + ‖z‖ + 2 * n) ^ 2) ^ n := by
  unfold oddStepProduct
  calc
    (∏ j ∈ Finset.range n, ‖oddStep q (shiftTwo z j)‖) ≤
        ∏ _j ∈ Finset.range n,
          ((q : ℝ) ^ 2 * (1 + ‖z‖ + 2 * n) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        have hjn : j < n := Finset.mem_range.mp hj
        have hshift := norm_shiftTwo_le z j
        have hrad : 1 + ‖shiftTwo z j‖ ≤ 1 + ‖z‖ + 2 * n := by
          have hjR : (j : ℝ) ≤ n := by exact_mod_cast hjn.le
          linarith
        exact (norm_oddStep_le q (shiftTwo z j)).trans (by gcongr)
    _ = ((q : ℝ) ^ 2 * (1 + ‖z‖ + 2 * n) ^ 2) ^ n := by simp

/-- Exact `n`-fold even recurrence.  This is the finite algebraic substitute
for the deep-left Stirling reduction. -/
theorem norm_reflectedDualMultiplier_eq_evenStepProduct
    (chi : DirichletCharacter ℂ q) (hchi : chi.Even)
    (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    ‖reflectedDualMultiplier chi z‖ =
      evenStepProduct q z n *
        ‖reflectedDualMultiplier chi (shiftTwo z n)‖ := by
  induction n with
  | zero => simp [evenStepProduct, shiftTwo]
  | succ n ih =>
      have hzim : (shiftTwo z n).im ≠ 0 := by
        rw [shiftTwo_im]
        exact hz
      have hstep := reflectedDualMultiplier_shift_two_even
        chi hchi (shiftTwo z n) hzim
      rw [ih, hstep, norm_mul]
      simp only [evenStepProduct, Finset.prod_range_succ, evenStep,
        shiftTwo_succ]
      ring

/-- Exact `n`-fold odd recurrence. -/
theorem norm_reflectedDualMultiplier_eq_oddStepProduct
    (chi : DirichletCharacter ℂ q) (hchi : chi.Odd)
    (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    ‖reflectedDualMultiplier chi z‖ =
      oddStepProduct q z n *
        ‖reflectedDualMultiplier chi (shiftTwo z n)‖ := by
  induction n with
  | zero => simp [oddStepProduct, shiftTwo]
  | succ n ih =>
      have hzim : (shiftTwo z n).im ≠ 0 := by
        rw [shiftTwo_im]
        exact hz
      have hstep := reflectedDualMultiplier_shift_two_odd
        chi hchi (shiftTwo z n) hzim
      rw [ih, hstep, norm_mul]
      simp only [oddStepProduct, Finset.prod_range_succ, oddStep,
        shiftTwo_succ]
      ring

end

end JutilaMultiplierRecurrence

#print axioms JutilaMultiplierRecurrence.even_gammaQuotient_shift_two
#print axioms JutilaMultiplierRecurrence.odd_gammaQuotient_shift_two
#print axioms JutilaMultiplierRecurrence.reflectedDualMultiplier_shift_two_even
#print axioms JutilaMultiplierRecurrence.reflectedDualMultiplier_shift_two_odd
#print axioms JutilaMultiplierRecurrence.norm_reflectedDualMultiplier_eq_evenStepProduct
#print axioms JutilaMultiplierRecurrence.norm_reflectedDualMultiplier_eq_oddStepProduct
