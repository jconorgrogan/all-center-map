import JutilaLemma6InfiniteShift
import JutilaLemma6SieveCoefficientBridge
import JutilaPseudocharacterHarmonicLower

/-! Literal sieve detector series bound after the certified infinite contour shift. -/
namespace MAPJutilaLemma6CanonicalMellinBound
open Complex Real MeasureTheory
open MAPJutilaLemma6InfiniteShift MAPJutilaLemma6SieveCoefficientBridge
open MAPJutilaLemma6FiniteContour MAPJutilaLemma6ErrorBound MAPJutilaLemma6DirectTail
open MAPJutilaPseudocharacterHarmonicLower MAPJutilaGappedGrahamBypass
open MAPJutilaLemma6GammaKernel MAPJutilaP48ConvexityAdapter MAPJutilaLemma6MellinIntegral
noncomputable section

theorem selected_directSeries_eq_errorIntegral
    {q R : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r) (hcop : ∀ r ∈ S, r.Coprime q)
    {z1 z2 beta omega t X : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    (homega : 0 < omega) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta ≤ 1 - omega)
    (hX : 1 ≤ X) (hrho : DirichletCharacter.LFunction chi (lemmaSixZeroPoint beta t) = 0) :
    (∑' n : ℕ, jutilaLemmaSixDirectTerm chi z1 z2 S (lemmaSixZeroPoint beta t) X n) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, lemmaSixMellinErrorIntegrand chi (jutilaLambdaComplex z1 z2)
          (jutilaLambdaSupport z2) S beta t X u) := by
  rw [← selected_lambda_smoothedSeries_eq_directSeries chi S hz1 hz12]
  apply selectedSmoothedSeries_eq_errorIntegral chi hprim hchi (jutilaLambdaComplex z1 z2)
    (z2 := Nat.floor z2) (R := R)
  · simp [jutilaLambdaSupport]
  · intro d hd
    exact (Finset.mem_Icc.mp hd).1
  · intro d hd
    simpa [jutilaLambdaComplex, Complex.norm_real, Real.norm_eq_abs] using abs_jutilaLambda_le_one hz1 hz12 d
  · exact hS
  · exact hSq
  · exact hcop
  · exact homega
  · exact hbetaLo
  · exact hbetaHi
  · exact hX
  · exact hrho

theorem norm_selected_directSeries_le_mellinBound
    {q R : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r) (hcop : ∀ r ∈ S, r.Coprime q)
    {z1 z2 beta omega t X : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    (homega : 0 < omega) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta ≤ 1 - omega)
    (hX : 1 ≤ X) (hrho : DirichletCharacter.LFunction chi (lemmaSixZeroPoint beta t) = 0) :
    ‖∑' n : ℕ, jutilaLemmaSixDirectTerm chi z1 z2 S (lemmaSixZeroPoint beta t) X n‖ ≤
      (Real.rpow X (-beta) * ((Nat.floor z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ)^4)) *
      (lemmaSixGammaSqConstant omega * p48ConvexityConstant *
        Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent) := by
  have hDcard : (jutilaLambdaSupport z2).card ≤ Nat.floor z2 := by simp [jutilaLambdaSupport]
  have hDpos : ∀ d ∈ jutilaLambdaSupport z2, 0 < d := fun d hd => (Finset.mem_Icc.mp hd).1
  have hxi : ∀ d ∈ jutilaLambdaSupport z2, ‖jutilaLambdaComplex z1 z2 d‖ ≤ 1 := by
    intro d hd
    simpa [jutilaLambdaComplex, Complex.norm_real, Real.norm_eq_abs] using abs_jutilaLambda_le_one hz1 hz12 d
  have hi := integral_norm_lemmaSixMellinErrorIntegrand_le chi hprim hchi (jutilaLambdaComplex z1 z2)
    hDcard hDpos hxi hS hSq hcop (t := t) homega hbetaLo hbetaHi (zero_lt_one.trans_le hX)
  rw [selected_directSeries_eq_errorIntegral chi hprim hchi hS hSq hcop hz1 hz12
    homega hbetaLo hbetaHi hX hrho, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
      ((Real.rpow X (-beta) * ((Nat.floor z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ)^4)) *
        (2 * Real.pi * lemmaSixGammaSqConstant omega * p48ConvexityConstant *
          Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent)) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans hi) (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero]

end
end MAPJutilaLemma6CanonicalMellinBound
#print axioms MAPJutilaLemma6CanonicalMellinBound.selected_directSeries_eq_errorIntegral
#print axioms MAPJutilaLemma6CanonicalMellinBound.norm_selected_directSeries_le_mellinBound
