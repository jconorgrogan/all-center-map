import FordMixedResidueCardinality
import FordMixedTriangularExponent
import FordP18MixedInjection

noncomputable section
namespace MAPFordMixedSourceCount
open MAPFordP18FixedTargetInjection MAPFordP18MixedInjection
open MAPFordMixedResidueCardinality MAPFordMixedTriangularExponent

def mixedToLiftedSource {p r n d : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : mixedTarget p r n d) :
    mixedSourceBstar hp hR phi m →
      liftedSource p r n d hp hR phi (equationExponent r d) m := by
  intro z
  let t := actualResidueVector_mem hp hR phi m z
  refine ⟨t, ⟨z.1, z.2.1, z.2.2.1, ?_, z.2.2.2.2⟩⟩
  intro i
  exact (intResidue_modEq (p ^ r) (Nat.pow_pos hp.pos) _).symm

theorem mixedToLiftedSource_injective {p r n d : ℕ}
    (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (m : mixedTarget p r n d) :
    Function.Injective (mixedToLiftedSource hp hR phi m) := by
  intro z w h
  apply Subtype.ext
  exact congrArg (fun s => s.2.1) h

/-- The literal mixed source fiber keeps interval positivity and Ford's
source Jacobian coprimality. The triangular cost comes from lifting each
actual equation modulo p^min(j,r) to a common p^r target. -/
theorem card_mixedSourceBstar_le {p r n d : ℕ}
    (hp : p.Prime) (hR : 1 ≤ r) (hr : r ≤ d+n)
    (phi : Fin n → Polynomial ℤ) (m : mixedTarget p r n d) :
    Fintype.card (mixedSourceBstar hp hR phi m) ≤
      p ^ ((r-d)*(r-d-1)/2 + r*d+n) := by
  classical
  letI : Fintype (MAPFordMixedResidueCardinality.residueVector p r (equationExponent r d) m) := by
    unfold MAPFordMixedResidueCardinality.residueVector
    exact @Pi.instFintype (Fin n)
      (fun i => residueFiber p r (equationExponent r d i) (m i))
      inferInstance inferInstance (fun i => residueFiberFintype p r _ (m i))
  letI (t : MAPFordMixedResidueCardinality.residueVector p r (equationExponent r d) m) :
      Fintype (sourceBstarAt (d := d) hp hR phi (fun i => ((t i).1.val : ℤ))) :=
    sourceBstarAtFintype hp hR phi _
  letI : Fintype (liftedSource p r n d hp hR phi (equationExponent r d) m) :=
    by unfold liftedSource; infer_instance
  have hcard := Fintype.card_le_of_injective (mixedToLiftedSource hp hR phi m)
    (mixedToLiftedSource_injective hp hR phi m)
  have hbound := card_liftedSource_le (d := d) hp hR phi
    (equationExponent r d) (fun i => equationExponent_le p r n d i) m
  have hexponent := mixed_exponent_eq_triangular hr
  have hbound' : Fintype.card (liftedSource p r n d hp hR phi (equationExponent r d) m) ≤
      p ^ ((r-d)*(r-d-1)/2 + r*d+n) := by
    simpa only [Fintype.card_eq_nat_card, equationExponent, hexponent] using! hbound
  exact hcard.trans hbound'

theorem card_sourceBstar_kd_le {p r k d : ℕ}
    (hp : p.Prime) (hR : 1 ≤ r) (hd : d ≤ k) (hr : r ≤ k)
    (phi : Fin (k-d) → Polynomial ℤ) (m : mixedTarget p r (k-d) d) :
    Fintype.card (mixedSourceBstar hp hR phi m) ≤
      p ^ ((r-d)*(r-d-1)/2 + r*d+(k-d)) := by
  exact card_mixedSourceBstar_le hp hR (by omega) phi m

end MAPFordMixedSourceCount
end

#print axioms MAPFordMixedSourceCount.card_mixedSourceBstar_le
#print axioms MAPFordMixedSourceCount.card_sourceBstar_kd_le
