import JutilaP53SourceInfiniteShift
import JutilaP53PrincipalSourceInfiniteShift
import JutilaP53PairContourExpansion
import JutilaP53SourceDivisorMass

/-! Exact p.53 finite divisor decomposition on the published source line. -/
namespace MAPJutilaP53SourcePairContours
open scoped BigOperators
open Complex MeasureTheory
open MAPJutilaP53PairRExpansion MAPJutilaP53PairEulerFactorization
open MAPJutilaP53PairContourExpansion MAPJutilaP53TwoScaleContour
open MAPJutilaP53SourceInfiniteShift MAPJutilaP53SourceDivisorMass
noncomputable section

def sourceContourTerm {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (s : ℂ) (M N epsilon : ℝ)
    (r r' d : ℕ) : ℂ :=
  LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
    ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, p53TwoScaleContourIntegrand chi s
        (N / (d : ℝ)) (M / (d : ℝ))
        (((-1 + epsilon : ℝ) : ℂ) + v * I)))

theorem pairRB_eq_sourceContours_nonprincipal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {M N epsilon : ℝ} (hM : 0 < M) (hMN : M < N)
    (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8)
    {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 2 * epsilon)
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    jutilaP53PairRB M N s chi r r' =
      (((r * r' : ℕ) : ℂ)⁻¹) *
        ∑ d ∈ (r.lcm r').divisors, sourceContourTerm chi s M N epsilon r r' d := by
  rw [pairRB_eq_divisorKernel_rightContours chi hM hMN hsLo hr hr']
  apply congrArg (((((r * r' : ℕ) : ℂ)⁻¹)) * ·)
  apply Finset.sum_congr rfl
  intro d hd
  have hdPos : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hd)
  unfold sourceContourTerm
  rw [p53TwoScale_right_eq_sourceLine chi hchi s
    (div_pos (hM.trans hMN) hdPos) (div_pos hM hdPos) heps hepsHi hsLo hsHi]

theorem pairRB_eq_sourceContours_principal_add_residue
    {q : ℕ} [NeZero q]
    {M N epsilon : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 2 * epsilon)
    (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8)
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    jutilaP53PairRB M N s (1 : DirichletCharacter ℂ q) r r' =
      (((r * r' : ℕ) : ℂ)⁻¹) *
        (∑ d ∈ (r.lcm r').divisors,
          sourceContourTerm (1 : DirichletCharacter ℂ q) s M N epsilon r r' d) +
      (((r * r' : ℕ) : ℂ)⁻¹) *
        MAPJutilaP53PrincipalDivisorResidueBound.p53PrincipalDivisorResidue q s M N r r' := by
  rw [MAPJutilaP53PairContourExpansion.pairRB_eq_divisorKernel_rightContours
    (1 : DirichletCharacter ℂ q) hM hMN hsLo hr hr']
  rw [← mul_add]
  apply congrArg (((((r * r' : ℕ) : ℂ)⁻¹)) * ·)
  unfold MAPJutilaP53PrincipalDivisorResidueBound.p53PrincipalDivisorResidue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hshift := MAPJutilaP53PrincipalSourceInfiniteShift.p53TwoScale_principal_right_eq_source_add_residue
    q s (div_pos (hM.trans hMN) hdR) (div_pos hM hdR) heps hepsHi hsLo hsHi
  unfold sourceContourTerm
  rw [hshift]
  push_cast
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  field_simp [hpi]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with v
  congr 2
  ring

end
end MAPJutilaP53SourcePairContours
#print axioms MAPJutilaP53SourcePairContours.pairRB_eq_sourceContours_nonprincipal

#print axioms MAPJutilaP53SourcePairContours.pairRB_eq_sourceContours_principal_add_residue
