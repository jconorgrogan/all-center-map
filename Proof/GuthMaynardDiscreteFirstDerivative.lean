import GuthMaynardSectionFourTrace

open scoped BigOperators ComplexConjugate

noncomputable section
namespace GuthMaynardDiscreteFirstDerivative

/-- The inverse coefficient in the finite first-derivative test. -/
def inverseCoeff (d : ℝ) : ℂ :=
  1 / (Complex.exp (Complex.I * (d : ℂ)) - 1)

theorem inverseCoeff_mul_increment {d : ℝ}
    (hd : Complex.exp (Complex.I * (d : ℂ)) - 1 ≠ 0) :
    inverseCoeff d * (Complex.exp (Complex.I * (d : ℂ)) - 1) = 1 := by
  unfold inverseCoeff
  field_simp

theorem exp_mul_I_sub_one_ne_zero_of_unit_interval {d : ℝ}
    (hd0 : 0 < d) (hd1 : d ≤ 1) :
    Complex.exp (Complex.I * (d : ℂ)) - 1 ≠ 0 := by
  intro h
  have he : Complex.exp (Complex.I * (d : ℂ)) = 1 := sub_eq_zero.mp h
  obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff.mp he)
  have him := congrArg Complex.im hn
  have him' : d = (n : ℝ) * (2 * Real.pi) := by
    simpa [Complex.mul_re, Complex.mul_im] using him
  have hn0 : 0 < (n : ℝ) := by nlinarith [him', hd0, Real.pi_pos]
  have hnpos : 0 < n := Int.cast_pos.mp hn0
  have hn1i : (1 : ℤ) ≤ n := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1i
  nlinarith [Real.pi_gt_three]

/-- Finite Abel summation in the form used by the first-derivative test.
The recurrence says `aₙ (zₙ₊₁-zₙ)=zₙ`; the result is exact, with endpoint
terms and the discrete coefficient variation exposed. -/
theorem sum_range_eq_boundary_sub_variation
    (k : ℕ) (z a : ℕ → ℂ)
    (hrec : ∀ n < k + 1, a n * (z (n + 1) - z n) = z n) :
    ∑ n ∈ Finset.range (k + 1), z n =
      a k * z (k + 1) - a 0 * z 0 -
        ∑ n ∈ Finset.range k, (a (n + 1) - a n) * z (n + 1) := by
  induction k with
  | zero =>
      have h0 := hrec 0 (by omega)
      simpa [mul_sub] using h0.symm
  | succ k ih =>
      rw [Finset.sum_range_succ, ih (fun n hn => hrec n (by omega))]
      have hk := hrec (k + 1) (by omega)
      calc
        a k * z (k + 1) - a 0 * z 0 -
            ∑ n ∈ Finset.range k, (a (n + 1) - a n) * z (n + 1) + z (k + 1) =
          a (k + 1) * z (k + 2) - a 0 * z 0 -
            (∑ n ∈ Finset.range k, (a (n + 1) - a n) * z (n + 1) +
              (a (k + 1) - a k) * z (k + 1)) := by
                have hk' : a (k + 1) * (z (k + 2) - z (k + 1)) = z (k + 1) := by
                  simpa [Nat.add_assoc] using hk
                have hrel : a k * z (k + 1) + z (k + 1) =
                    a (k + 1) * z (k + 2) -
                      (a (k + 1) - a k) * z (k + 1) := by
                  linear_combination -hk'
                calc
                  _ = (a k * z (k + 1) + z (k + 1)) - a 0 * z 0 -
                      ∑ n ∈ Finset.range k, (a (n + 1) - a n) * z (n + 1) := by ring
                  _ = _ := by rw [hrel]
                  _ = _ := by ring
        _ = a (k + 1) * z (k + 2) - a 0 * z 0 -
            ∑ n ∈ Finset.range (k + 1),
              (a (n + 1) - a n) * z (n + 1) := by
                rw [Finset.sum_range_succ]

/-- Norm consequence of the exact summation identity.  The supplied `hvar`
is the finite variation estimate; proving it from monotone imaginary parts is
the separate real-variable step in the first-derivative test. -/
theorem norm_sum_range_le_boundary_add_variation
    (k : ℕ) (z a : ℕ → ℂ)
    (hrec : ∀ n < k + 1, a n * (z (n + 1) - z n) = z n)
    (hz : ∀ n ≤ k + 1, ‖z n‖ = 1)
    {V : ℝ}
    (hvar : ∑ n ∈ Finset.range k, ‖a (n + 1) - a n‖ ≤ V) :
    ‖∑ n ∈ Finset.range (k + 1), z n‖ ≤
      ‖a k‖ + ‖a 0‖ + V := by
  rw [sum_range_eq_boundary_sub_variation k z a hrec]
  calc
    ‖a k * z (k + 1) - a 0 * z 0 -
        ∑ n ∈ Finset.range k, (a (n + 1) - a n) * z (n + 1)‖ ≤
      ‖a k * z (k + 1)‖ + ‖a 0 * z 0‖ +
        ‖∑ n ∈ Finset.range k, (a (n + 1) - a n) * z (n + 1)‖ := by
          calc
            _ ≤ ‖a k * z (k + 1) - a 0 * z 0‖ +
                ‖∑ n ∈ Finset.range k, (a (n + 1) - a n) * z (n + 1)‖ :=
              norm_sub_le _ _
            _ ≤ (‖a k * z (k + 1)‖ + ‖a 0 * z 0‖) +
                ‖∑ n ∈ Finset.range k, (a (n + 1) - a n) * z (n + 1)‖ := by
              have hfirst := norm_sub_le (a k * z (k + 1)) (a 0 * z 0)
              simpa [add_comm, add_left_comm, add_assoc] using
                (add_le_add_right hfirst
                  (‖∑ n ∈ Finset.range k,
                    (a (n + 1) - a n) * z (n + 1)‖))
            _ = _ := by ring
    _ ≤ ‖a k‖ + ‖a 0‖ + V := by
      have hsum : ‖∑ n ∈ Finset.range k,
          (a (n + 1) - a n) * z (n + 1)‖ ≤
          ∑ n ∈ Finset.range k, ‖a (n + 1) - a n‖ := by
        calc
          _ ≤ ∑ n ∈ Finset.range k,
              ‖(a (n + 1) - a n) * z (n + 1)‖ := norm_sum_le _ _
          _ = ∑ n ∈ Finset.range k, ‖a (n + 1) - a n‖ := by
            apply Finset.sum_congr rfl
            intro n hn
            have hn' := Finset.mem_range.mp hn
            rw [norm_mul, hz (n + 1) (by omega), mul_one]
      have hkz : ‖a k * z (k + 1)‖ = ‖a k‖ := by
        rw [norm_mul, hz (k + 1) (by omega), mul_one]
      have h0z : ‖a 0 * z 0‖ = ‖a 0‖ := by
        rw [norm_mul, hz 0 (by omega), mul_one]
      rw [hkz, h0z]
      linarith

end GuthMaynardDiscreteFirstDerivative

#print axioms GuthMaynardDiscreteFirstDerivative.inverseCoeff_mul_increment
#print axioms GuthMaynardDiscreteFirstDerivative.exp_mul_I_sub_one_ne_zero_of_unit_interval
#print axioms GuthMaynardDiscreteFirstDerivative.sum_range_eq_boundary_sub_variation
#print axioms GuthMaynardDiscreteFirstDerivative.norm_sum_range_le_boundary_add_variation
