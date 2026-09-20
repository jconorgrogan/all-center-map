import JutilaP53PrincipalRResidueAggregation
import JutilaP53PrincipalDivisorResidueBound
import JutilaP53SignedDivisorMass

/-! Exact scaling of the principal residue, preserving the signed divisor sum. -/
namespace MAPJutilaP53PrincipalResidueScaling
open scoped BigOperators
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53PrincipalDivisorResidueBound
open MAPJutilaP53PairEulerFactorization
open MAPJutilaP53Lemma2Bridge
noncomputable section

theorem scaled_cpow_mul {U d : ℝ} (hU : 0 < U) (hd : 0 < d) (w : ℂ) :
    ((U / d : ℝ) : ℂ) ^ w * (d : ℂ) ^ w = (U : ℂ) ^ w := by
  rw [← Complex.mul_cpow_ofReal_nonneg (div_pos hU hd).le hd.le]
  congr 1
  push_cast
  field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast hd.ne']

theorem scaleRemovableQuotient_div
    {U V d : ℝ} (hU : 0 < U) (hV : 0 < V) (hd : 0 < d) (w : ℂ) :
    p53ScaleRemovableQuotient (U / d) (V / d) w * (d : ℂ) ^ w =
      p53ScaleRemovableQuotient U V w := by
  by_cases hw : w = 0
  · subst w
    simp only [p53ScaleRemovableQuotient, Function.update_self, Complex.cpow_zero, mul_one]
    rw [← Complex.ofReal_log (div_pos hU hd).le,
      ← Complex.ofReal_log (div_pos hV hd).le,
      ← Complex.ofReal_log hU.le, ← Complex.ofReal_log hV.le,
      Real.log_div hU.ne' hd.ne', Real.log_div hV.ne' hd.ne']
    push_cast
    ring
  · simp only [p53ScaleRemovableQuotient, Function.update_of_ne hw,
      p53ScaleDifference]
    rw [div_mul_eq_mul_div, sub_mul, scaled_cpow_mul hU hd, scaled_cpow_mul hV hd]

theorem principalResidue_div
    (q : ℕ) [NeZero q] {U V d : ℝ}
    (hU : 0 < U) (hV : 0 < V) (hd : 0 < d) (s : ℂ) :
    p53PrincipalResidue q s (U / d) (V / d) =
      (d : ℂ) ^ s * p53PrincipalResidue q s U V := by
  have hscale := scaleRemovableQuotient_div hU hV hd (-s)
  rw [Complex.cpow_neg] at hscale
  have hpow : (d : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hd.ne'))
  have hscale' : p53ScaleRemovableQuotient (U / d) (V / d) (-s) =
      (d : ℂ) ^ s * p53ScaleRemovableQuotient U V (-s) := by
    field_simp at hscale
    linear_combination hscale
  unfold p53PrincipalResidue
  rw [hscale']
  ring

/-- Cancellation of the scale-dependent divisor power, before taking norms. -/
theorem term_mul_principalResidue_div
    (q : ℕ) [NeZero q] {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    {d r r' : ℕ} (hd : 0 < d) (s : ℂ) :
    LSeries.term (p53TwistedDivisorKernel (1 : DirichletCharacter ℂ q) r r')
      (1 + s) d * p53PrincipalResidue q s (U / d) (V / d) =
    ((1 : DirichletCharacter ℂ q) d * p53PairDivisorKernel r r' d / (d : ℂ)) *
      p53PrincipalResidue q s U V := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpow : (d : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hdC)
  rw [LSeries.term, if_neg hd.ne', principalResidue_div q hU hV (Nat.cast_pos.mpr hd),
    Complex.cpow_add _ _ hdC, Complex.cpow_one]
  unfold p53TwistedDivisorKernel
  push_cast
  field_simp

/-- The signed principal residue vanishes off the pseudocharacter diagonal.
Coprimality is retained explicitly, as required by the source's primed sums. -/
theorem principalDivisorResidue_eq_diagonal
    (q : ℕ) [NeZero q] {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hcop : (r.lcm r').Coprime q) (s : ℂ) :
    p53PrincipalDivisorResidue q s V U r r' =
      (if r = r' then (r.totient : ℂ) else 0) * p53PrincipalResidue q s U V := by
  unfold p53PrincipalDivisorResidue
  calc
    _ = ∑ d ∈ (r.lcm r').divisors,
        (p53PairDivisorKernel r r' d / (d : ℂ)) * p53PrincipalResidue q s U V := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [term_mul_principalResidue_div q hU hV (Nat.pos_of_mem_divisors hd)]
      have hdq : d.Coprime q := hcop.of_dvd_left (Nat.mem_divisors.mp hd).1
      have hone : (1 : DirichletCharacter ℂ q) d = 1 :=
        MulChar.one_apply ((ZMod.isUnit_iff_coprime d q).mpr hdq)
      rw [hone, one_mul]
    _ = _ := by
      rw [← Finset.sum_mul,
        MAPJutilaP53SignedDivisorMass.sum_p53PairDivisorKernel_div_eq_diagonal hr hr']

/-- Complete normalized residue after the signed divisor cancellation. -/
theorem principalRResidue_eq_diagonalMass
    (q : ℕ) [NeZero q] {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (S : Finset ℕ) (hSq : ∀ r ∈ S, Squarefree r)
    (hcop : ∀ r ∈ S, r.Coprime q) (s : ℂ) :
    MAPJutilaP53PrincipalRResidueAggregation.p53PrincipalRResidue q S s V U =
      (∑ r ∈ S, (r.totient : ℂ) / (r : ℂ) ^ 2) *
        p53PrincipalResidue q s U V := by
  unfold MAPJutilaP53PrincipalRResidueAggregation.p53PrincipalRResidue
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  have hinner : (∑ r' ∈ S,
      (((r * r' : ℕ) : ℂ)⁻¹) * p53PrincipalDivisorResidue q s V U r r') =
      ∑ r' ∈ S, if r = r' then
        (r.totient : ℂ) / (r : ℂ) ^ 2 * p53PrincipalResidue q s U V else 0 := by
    apply Finset.sum_congr rfl
    intro r' hr'
    have hcp : (r.lcm r').Coprime q :=
      ((hcop r hr).mul_left (hcop r' hr')).of_dvd_left (Nat.lcm_dvd_mul r r')
    rw [principalDivisorResidue_eq_diagonal q hU hV (hSq r hr) (hSq r' hr') hcp]
    split_ifs with heq
    · subst r'
      push_cast
      ring
    · simp
  rw [hinner]
  simp [hr]

end
end MAPJutilaP53PrincipalResidueScaling
#print axioms MAPJutilaP53PrincipalResidueScaling.principalResidue_div

#print axioms MAPJutilaP53PrincipalResidueScaling.principalDivisorResidue_eq_diagonal

#print axioms MAPJutilaP53PrincipalResidueScaling.principalRResidue_eq_diagonalMass
