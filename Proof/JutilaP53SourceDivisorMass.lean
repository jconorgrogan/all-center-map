import JutilaP53DivisorKernelAbsoluteMass

/-! Exact endpoint cancellation at the source contour before the divisor norm sum. -/
namespace MAPJutilaP53SourceDivisorMass
open scoped BigOperators
open MAPJutilaP53DivisorKernelAbsoluteMass MAPJutilaP53PairEulerFactorization
open MAPJutilaP53Lemma2Bridge MAPJutilaLemma3AbsoluteMass
noncomputable section

def sourceEndpoint (U V epsilon : ℝ) : ℝ :=
  Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon)

theorem sourceEndpoint_nonneg {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (epsilon : ℝ) :
    0 ≤ sourceEndpoint U V epsilon :=
  add_nonneg (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg hV.le _)

theorem sourceEndpoint_div_le
    {U V epsilon sigma : ℝ} {d : ℕ} (hU : 0 < U) (hV : 0 < V)
    (hd : 0 < d) (heps : 0 ≤ epsilon) (hs : 0 ≤ sigma) :
    sourceEndpoint (U / d) (V / d) epsilon ≤
      Real.rpow (d : ℝ) (1 + sigma) * sourceEndpoint U V epsilon := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : Real.rpow (d : ℝ) (1 - epsilon) ≤ Real.rpow (d : ℝ) (1 + sigma) :=
    Real.rpow_le_rpow_of_exponent_le hdOne (by linarith)
  unfold sourceEndpoint
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow hU.le hdR.le, Real.div_rpow hV.le hdR.le]
  rw [show -1 + epsilon = -(1 - epsilon) by ring, Real.rpow_neg hdR.le,
    div_inv_eq_mul, div_inv_eq_mul]
  have hU0 : 0 ≤ Real.rpow U (-(1 - epsilon)) := Real.rpow_nonneg hU.le _
  have hV0 : 0 ≤ Real.rpow V (-(1 - epsilon)) := Real.rpow_nonneg hV.le _
  calc
    _ = Real.rpow (d : ℝ) (1 - epsilon) *
      (Real.rpow U (-(1 - epsilon)) + Real.rpow V (-(1 - epsilon))) := by
        simp only [Real.rpow_eq_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (add_nonneg hU0 hV0)

theorem twisted_term_mul_sourceEndpoint_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {U V epsilon : ℝ} {s : ℂ} {r r' d : ℕ}
    (hU : 0 < U) (hV : 0 < V) (hd : 0 < d)
    (heps : 0 ≤ epsilon) (hs : 0 ≤ s.re) :
    ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖ *
      sourceEndpoint (U / d) (V / d) epsilon ≤
      ‖p53PairDivisorKernel r r' d‖ * sourceEndpoint U V epsilon := by
  let D := Real.rpow (d : ℝ) (1 + s.re)
  have hD : 0 < D := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hd) _
  have hE := sourceEndpoint_nonneg (div_pos hU (Nat.cast_pos.mpr hd))
    (div_pos hV (Nat.cast_pos.mpr hd)) epsilon
  have hscale := sourceEndpoint_div_le hU hV hd heps hs
  calc
    _ ≤ (‖p53PairDivisorKernel r r' d‖ / D) * sourceEndpoint (U / d) (V / d) epsilon := by
      apply mul_le_mul_of_nonneg_right _ hE
      simpa [D] using norm_twisted_kernel_term_le chi hd (s := s)
    _ ≤ _ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hD]
      calc
        _ ≤ ‖p53PairDivisorKernel r r' d‖ * (D * sourceEndpoint U V epsilon) :=
          mul_le_mul_of_nonneg_left hscale (norm_nonneg _)
        _ = _ := by ring

end
end MAPJutilaP53SourceDivisorMass
#print axioms MAPJutilaP53SourceDivisorMass.twisted_term_mul_sourceEndpoint_le
