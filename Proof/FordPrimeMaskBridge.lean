import FordSourceJacobianFormula
import FordP16LiteralResidueBridge

open scoped BigOperators
open MAPFordP16LiteralResidueBridge

namespace FordTypeJacobian
noncomputable section

lemma coprime_natAbs_of_cast_ne_zero
    {p : ℕ} (hp : p.Prime) (D : ℤ)
    (hD : (D : ZMod p) ≠ 0) :
    p.Coprime D.natAbs := by
  letI : Fact p.Prime := ⟨hp⟩
  have hunit : IsUnit (D : ZMod p) := isUnit_iff_ne_zero.mpr hD
  have hnat : IsUnit (D.natAbs : ZMod p) := by
    cases hDint : D with
    | ofNat n => simpa [hDint] using hunit
    | negSucc n =>
        have h' := hunit
        rw [hDint, Int.cast_negSucc] at h'
        simpa only [Int.natAbs_negSucc, neg_neg] using h'.neg
  exact (ZMod.isUnit_iff_coprime _ _).mp hnat |>.symm

/-- Once the literal determinant is shown nonzero modulo `p`, this transports
it to Ford's exact positivity plus Jacobian mask. -/
lemma fordPolynomialMask_of_det_cast_ne_zero
    {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) (z : Fin k → Fin (P + 1))
    (hpos : ∀ i, 1 ≤ (z i).val)
    (D : ℤ)
    (hdet : (MAPFordCoarseP18Jacobian.sourceJacobian
      (fordTailPolynomials hdk psi) (fordTailCoordinates hdk z)).det = D)
    (hD : (D : ZMod p) ≠ 0) :
    fordPolynomialMask (P := P) hdk hp psi z := by
  refine ⟨hpos, ?_⟩
  rw [hdet]
  exact coprime_natAbs_of_cast_ne_zero hp D hD

end
end FordTypeJacobian

#print axioms FordTypeJacobian.coprime_natAbs_of_cast_ne_zero
#print axioms FordTypeJacobian.fordPolynomialMask_of_det_cast_ne_zero
