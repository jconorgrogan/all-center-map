import GuthMaynardHeathBrownMajorant

/-!
# The exact ratio-kernel identity in Guth--Maynard Lemma 11.5

Guth--Maynard (7.2) defines

`R(v) = sum_{t in W} |v|^(it)
      = W-hat (log |v| / (-2 * pi))`,

where the Fourier transform uses the phase `exp (-2 * pi * i * t * xi)`.
The proof of Lemma 11.5 then identifies its discrete second moment with the
coefficient-one difference quadratic form to which Heath--Brown's theorem is
applied.  This file certifies that finite identity, including the sign and
logarithm conventions.  The only positivity used is the positivity of the
natural-number ratios in the dyadic block; it is exposed explicitly before
the source-facing `1 <= M` specialization.
-/

namespace GuthMaynardRatioKernelIdentity

open scoped BigOperators
open GuthMaynardHeathBrownInterface
open GuthMaynardHeathBrownMajorant

noncomputable section

/-- The Fourier transform of the point masses at `W`, with the paper's
`exp (-2 * pi * i * t * xi)` convention. -/
def pointMassFourierKernel (W : Finset ℝ) (xi : ℝ) : ℂ :=
  ∑ t ∈ W,
    Complex.exp (-((2 * Real.pi * t * xi : ℝ) : ℂ) * Complex.I)

/-- The literal kernel `R(v)` from Guth--Maynard (7.2), written as
`exp (i * t * log |v|)` so that its branch and sign are explicit. -/
def ratioDirichletKernel (W : Finset ℝ) (v : ℝ) : ℂ :=
  ∑ t ∈ W,
    Complex.exp (Complex.I * ((t * Real.log |v| : ℝ) : ℂ))

/-- Equation (7.2), including the minus sign in the Fourier frequency. -/
theorem ratioDirichletKernel_eq_pointMassFourierKernel
    (W : Finset ℝ) (v : ℝ) :
    ratioDirichletKernel W v =
      pointMassFourierKernel W (Real.log |v| / (-2 * Real.pi)) := by
  unfold ratioDirichletKernel pointMassFourierKernel
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- On a positive rational ratio, the Gram kernel of the Dirichlet phases is
exactly the source kernel `R(n / m)`.  The hypotheses are precisely those
needed for `log (n / m) = log n - log m`; no convention at zero is used. -/
theorem gramKernel_dirichletPhase_eq_ratioDirichletKernel
    (W : Finset ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    gramKernel W dirichletPhase n m =
      ratioDirichletKernel W ((n : ℝ) / (m : ℝ)) := by
  unfold gramKernel ratioDirichletKernel
  apply Finset.sum_congr rfl
  intro t ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hratio : (0 : ℝ) < (n : ℝ) / (m : ℝ) := div_pos hnR hmR
  have hstar :
      star (dirichletPhase m t) =
        Complex.exp (-Complex.I * ((t * Real.log m : ℝ) : ℂ)) := by
    unfold dirichletPhase
    rw [show star
        (Complex.exp (((((t * Real.log m) : ℝ) : ℂ) * Complex.I))) =
          Complex.exp
            (star (((((t * Real.log m) : ℝ) : ℂ) * Complex.I))) by
      exact (Complex.exp_conj _).symm]
    congr 1
    change (starRingEnd ℂ)
        (((((t * Real.log m) : ℝ) : ℂ) * Complex.I)) = _
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hstar]
  unfold dirichletPhase
  rw [← Complex.exp_add]
  rw [abs_of_pos hratio, Real.log_div hnR.ne' hmR.ne']
  congr 1
  push_cast
  ring

/-- The coefficient-one difference quadratic form is the exact discrete
second moment of `R(n/m)`, assuming positivity directly on the finite dyadic
range.  This is the finite identity displayed in the proof of Lemma 11.5. -/
theorem differenceQuadraticForm_one_eq_ratioKernelSecondMoment_of_pos
    (M : ℕ) (W : Finset ℝ)
    (hpos : ∀ n ∈ Finset.Icc M (2 * M), 0 < n) :
    differenceQuadraticForm (fun _ => (1 : ℂ)) M W =
      ∑ n ∈ Finset.Icc M (2 * M),
        ∑ m ∈ Finset.Icc M (2 * M),
          ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 2 := by
  rw [← realGramQuadratic_dirichletPhase_eq]
  have habsolute :
      absoluteCoefficientMajorant (Finset.Icc M (2 * M)) W
          (fun _ => (1 : ℂ)) dirichletPhase =
        realGramQuadratic (Finset.Icc M (2 * M)) W
          (fun _ => (1 : ℂ)) dirichletPhase := by
    simpa using
      (absoluteCoefficientMajorant_real_nonnegative_eq
        (Finset.Icc M (2 * M)) W (fun _ => (1 : ℝ)) dirichletPhase
          (by simp))
  rw [← habsolute]
  unfold absoluteCoefficientMajorant
  simp only [norm_one, one_mul]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [gramKernel_dirichletPhase_eq_ratioDirichletKernel W
    (hpos n hn) (hpos m hm)]

/-- Source-facing form of the Lemma 11.5 identity.  The printed assumption
`M >= 1` supplies positivity for every `n,m in [M,2M]`. -/
theorem differenceQuadraticForm_one_eq_ratioKernelSecondMoment
    (M : ℕ) (W : Finset ℝ) (hM : 1 ≤ M) :
    differenceQuadraticForm (fun _ => (1 : ℂ)) M W =
      ∑ n ∈ Finset.Icc M (2 * M),
        ∑ m ∈ Finset.Icc M (2 * M),
          ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 2 := by
  exact differenceQuadraticForm_one_eq_ratioKernelSecondMoment_of_pos M W
    (fun n hn => by
      have hMn : M ≤ n := (Finset.mem_Icc.mp hn).1
      exact lt_of_lt_of_le Nat.zero_lt_one (hM.trans hMn))

end

end GuthMaynardRatioKernelIdentity

#print axioms GuthMaynardRatioKernelIdentity.ratioDirichletKernel_eq_pointMassFourierKernel
#print axioms GuthMaynardRatioKernelIdentity.gramKernel_dirichletPhase_eq_ratioDirichletKernel
#print axioms GuthMaynardRatioKernelIdentity.differenceQuadraticForm_one_eq_ratioKernelSecondMoment_of_pos
#print axioms GuthMaynardRatioKernelIdentity.differenceQuadraticForm_one_eq_ratioKernelSecondMoment
