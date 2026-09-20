import FordGeometricCoordinatePool
import FordPrimeMaskSpecialization

noncomputable section
namespace MAPFordGeometricMaskPool
open MAPFordP16LiteralResidueBridge MAPFordP16Source35Triangular MAPFordType

lemma tail_injective {k d P : ℕ} (hd : d ≤ k)
    (z : Fin k → Fin (P+1)) (hz : Function.Injective z) :
    Function.Injective (fordTailCoordinates hd z) := by
  intro i j hij
  have h := hz hij
  exact Fin.ext (congrArg (fun a : Fin k => a.val) h)

/-- A common finite prime pool supplies both actual Jacobian masks for every
positive pair with distinct source coordinates. No determinant input remains. -/
theorem exists_uniform_mask_pool
    (k d M P Q s : ℕ) (hk : 2 ≤ k) (hd : d ≤ k) (hM : k ≤ M)
    (hP : P ≤ (M+1)^(k+1))
    (hnative : (4*s)^2*(2^(k^3)*M) ≤ Q)
    (T : ℤ) (hT : T ≠ 0) (hTsize : T.natAbs ≤ P^d)
    (m : ℕ) (psi : Fin k → Polynomial ℤ)
    (htype : FordType k d T m (psiNatSucc psi)) :
    ∃ S : Finset ℕ, S.card = k^3 ∧
      (∀ p ∈ S, p.Prime ∧ k < p ∧ p ≤ 2^(k^3)*M ∧ (4*s)^2*p ≤ Q) ∧
      (∀ z w : Fin k → Fin (P+1),
        (∀ i, 1 ≤ (z i).val) → (∀ i, 1 ≤ (w i).val) →
        Function.Injective z → Function.Injective w →
        ∃ p : ℕ, ∃ hp : p.Prime, p ∈ S ∧
          fordPolynomialMask hd hp psi z ∧ fordPolynomialMask hd hp psi w) := by
  obtain ⟨S, hc, hS, hcoords⟩ :=
    MAPFordGeometricCoordinatePool.exists_uniform_coordinate_pool
      k d M P Q s hk hd hM hP hnative T hT hTsize
  refine ⟨S, hc, hS, ?_⟩
  intro z w hzpos hwpos hz hw
  obtain ⟨p, hpS, hpT, hpz, hpw⟩ := hcoords
    (fordTailCoordinates hd z) (fordTailCoordinates hd w)
    (tail_injective hd z hz) (tail_injective hd w hw)
  have hp := (hS p hpS).1
  refine ⟨p, hp, hpS, ?_, ?_⟩
  · exact FordTypeJacobian.fordPolynomialMask_of_fordType
      hd hk hp (hS p hpS).2.1 hpT psi htype z hzpos hpz
  · exact FordTypeJacobian.fordPolynomialMask_of_fordType
      hd hk hp (hS p hpS).2.1 hpT psi htype w hwpos hpw

end MAPFordGeometricMaskPool
#print axioms MAPFordGeometricMaskPool.exists_uniform_mask_pool
