import FordFiniteGrowthStrip
import FordEulerHurwitzContinuation
import FordEulerCutoff
import FordEulerRemainderEnvelope

open scoped BigOperators
noncomputable section
namespace FordHurwitzGrowthStrip
open FordFiniteGrowthBound FordEulerCellAnalytic

/-- An actual uniform Hurwitz growth estimate on a strip crossing `Re(s)=1`. -/
theorem hurwitz_growth_strip :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ (t u eta sigma : ℝ),
      2 ≤ t → 0 ≤ u → u ≤ 1 → 0 ≤ eta → eta ≤ (1 : ℝ) / 2 →
      1 - eta ≤ sigma → sigma ≤ 2 →
      ‖HurwitzZeta.hurwitzZeta (u : UnitAddCircle)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) -
        (u : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        6 * Real.log t * commonEnvelope R t eta + 14 := by
  obtain ⟨R, hR, hfinite⟩ := FordFiniteGrowthStrip.finite_sum_le_common_envelope_strip
  refine ⟨R, hR, ?_⟩
  intro t u eta sigma ht hu hu1 heta heta1 hsigma hsigma2
  let M := FordEulerCutoff.cutoffM t
  let r := FordEulerCutoff.cutoffR t
  let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
  have hsre : s.re = sigma := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hsigma0 : (1 : ℝ) / 2 ≤ sigma := by linarith
  obtain ⟨hM, hMlo, hMhi, hMr, hr, hshift⟩ := FordEulerCutoff.cutoff_properties ht
  have htail := hfinite M r t u eta sigma hM hMr hMhi ht hu hu1 heta heta1 hsigma
  have htail' : ‖∑ n ∈ Finset.range (M - 1),
      ((((n + 1 : ℕ) : ℝ) + u : ℝ) : ℂ) ^ (-s)‖ ≤
      (r : ℝ) * commonEnvelope R t eta := by
    simpa only [s, Complex.ofReal_add] using htail
  have hformula := FordEulerHurwitzContinuation.hurwitz_eq_finite_add_cellSeries_upper_right
    (s := s) ⟨hu, hu1⟩ hM (by rw [hsre]; linarith) (by rw [hsim]; linarith)
  have hsplit : (∑ n ∈ Finset.range M, (((n : ℝ) + u : ℝ) : ℂ) ^ (-s)) =
      (u : ℂ) ^ (-s) +
        ∑ n ∈ Finset.range (M - 1), ((((n + 1 : ℕ) : ℝ) + u : ℝ) : ℂ) ^ (-s) := by
    conv_lhs => rw [show M = (M - 1) + 1 by omega, Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_add]
    ring
  have hsub : HurwitzZeta.hurwitzZeta (u : UnitAddCircle) s - (u : ℂ) ^ (-s) =
      (∑ n ∈ Finset.range (M - 1), ((((n + 1 : ℕ) : ℝ) + u : ℝ) : ℂ) ^ (-s)) +
        ((((M : ℝ) + u : ℝ) : ℂ) ^ (1 - s)) / (s - 1) + cellSeries M u s := by
    rw [hformula, hsplit]
    ring
  have hrest := FordEulerRemainderEnvelope.remainder_envelope
    (s := s) (a := (M : ℝ) + u)
    (by rw [hsre]; exact hsigma0) (by rw [hsre]; exact hsigma2)
    (by rw [hsim]; exact ht)
    (by rw [hsim]; exact (hshift u hu hu1).1)
    (by rw [hsim]; exact (hshift u hu hu1).2)
  have hC : 0 ≤ commonEnvelope R t eta := by
    unfold commonEnvelope
    positivity
  change ‖HurwitzZeta.hurwitzZeta (u : UnitAddCircle) s - (u : ℂ) ^ (-s)‖ ≤ _
  rw [hsub]
  calc
    _ ≤ ‖∑ n ∈ Finset.range (M - 1), ((((n + 1 : ℕ) : ℝ) + u : ℝ) : ℂ) ^ (-s)‖ +
        ‖((((M : ℝ) + u : ℝ) : ℂ) ^ (1 - s)) / (s - 1)‖ + ‖cellSeries M u s‖ :=
      norm_add₃_le
    _ ≤ (r : ℝ) * commonEnvelope R t eta + 2 + 12 := by
      exact add_le_add (add_le_add htail' hrest.2) hrest.1
    _ ≤ 6 * Real.log t * commonEnvelope R t eta + 14 := by
      have hh := mul_le_mul_of_nonneg_right hr hC
      linarith

end FordHurwitzGrowthStrip
#print axioms FordHurwitzGrowthStrip.hurwitz_growth_strip
