import GuthMaynardLemma41Operator

/-! # Deterministic algebra in Guth--Maynard Proposition 4.6 -/
namespace GuthMaynardProposition46Algebra

noncomputable section

/-- Squaring Lemma 4.2 costs the source's harmless absolute constant `8`.
This is the exact deterministic passage from Lemmas 4.1--4.2 to the
cube-root trace defect plus average trace. -/
theorem largeValue_of_singular_trace_defect
    {R N s D A : ℝ} (hN : 0 ≤ N) (hs : 0 ≤ s)
    (hD : 0 ≤ D) (hA : 0 ≤ A)
    (henergy : R ≤ N * s ^ 2)
    (hlemma42 : s ≤ 2 * D ^ (1 / 6 : ℝ) + 2 * Real.sqrt A) :
    R ≤ 8 * N * (D ^ (1 / 3 : ℝ) + A) := by
  have hrootD : (D ^ (1 / 6 : ℝ)) ^ 2 = D ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hD]
    norm_num
  have hsqrtA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hsq : s ^ 2 ≤
      (2 * D ^ (1 / 6 : ℝ) + 2 * Real.sqrt A) ^ 2 :=
    pow_le_pow_left₀ hs hlemma42 2
  calc
    R ≤ N * s ^ 2 := henergy
    _ ≤ N * (2 * D ^ (1 / 6 : ℝ) + 2 * Real.sqrt A) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hN
    _ = N * (4 * (D ^ (1 / 6 : ℝ)) ^ 2 +
        8 * D ^ (1 / 6 : ℝ) * Real.sqrt A +
        4 * (Real.sqrt A) ^ 2) := by ring
    _ ≤ 8 * N * (D ^ (1 / 3 : ℝ) + A) := by
      rw [hrootD, hsqrtA]
      have hcross := sq_nonneg (D ^ (1 / 6 : ℝ) - Real.sqrt A)
      nlinarith

end
end GuthMaynardProposition46Algebra

#print axioms GuthMaynardProposition46Algebra.largeValue_of_singular_trace_defect
