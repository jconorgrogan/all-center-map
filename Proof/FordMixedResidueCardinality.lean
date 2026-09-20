import FordP18FixedTargetInjection

open scoped BigOperators

noncomputable section
namespace MAPFordMixedResidueCardinality
open MAPFordP18FixedTargetInjection

abbrev residueVector (p r : ℕ) {n : ℕ} (a : Fin n → ℕ)
    (m : (i : Fin n) → Fin (p ^ a i)) :=
  (i : Fin n) → residueFiber p r (a i) (m i)

theorem card_residueVector_le {p r n : ℕ} (hp : 0 < p)
    (a : Fin n → ℕ) (ha : ∀ i, a i ≤ r)
    (m : (i : Fin n) → Fin (p ^ a i)) :
    Fintype.card (residueVector p r a m) ≤ p ^ (Finset.univ.sum (fun (i : Fin n) => r - a i)) := by
  classical
  change Fintype.card ((i : Fin n) → residueFiber p r (a i) (m i)) ≤ _
  rw [Fintype.card_pi]
  calc
    (∏ i, Fintype.card (residueFiber p r (a i) (m i))) ≤
        ∏ i, p ^ (r - a i) := by
      apply Finset.prod_le_prod'
      intro i hi
      exact card_residueFiber_le hp (ha i) (m i)
    _ = p ^ (Finset.univ.sum (fun (i : Fin n) => r - a i)) := Finset.prod_pow_eq_pow_sum _ _ _

abbrev liftedSource (p r n d : ℕ) (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (a : Fin n → ℕ)
    (m : (i : Fin n) → Fin (p ^ a i)) :=
  Sigma (fun t : residueVector p r a m =>
    sourceBstarAt (d := d) hp hR phi (fun i => ((t i).1.val : ℤ)))

theorem card_liftedSource_le {p r n d : ℕ}
    (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (a : Fin n → ℕ)
    (ha : ∀ i, a i ≤ r) (m : (i : Fin n) → Fin (p ^ a i)) :
    Fintype.card (liftedSource p r n d hp hR phi a m) ≤
      p ^ ((Finset.univ.sum (fun (i : Fin n) => r - a i)) + r*d + n) := by
  classical
  unfold liftedSource
  rw [Fintype.card_sigma (α := fun t : residueVector p r a m =>
    sourceBstarAt (d := d) hp hR phi (fun i => ((t i).1.val : ℤ)))]
  calc
    (∑ t : residueVector p r a m,
        Fintype.card (sourceBstarAt (d := d) hp hR phi
          (fun i => ((t i).1.val : ℤ)))) ≤
        ∑ _t : residueVector p r a m, p ^ (r*d+n) := by
      apply Finset.sum_le_sum
      intro t ht
      exact card_sourceBstarAt_le hp hR phi _
    _ = Fintype.card (residueVector p r a m) * p ^ (r*d+n) := by simp
    _ ≤ p ^ (Finset.univ.sum (fun (i : Fin n) => r - a i)) * p ^ (r*d+n) :=
      Nat.mul_le_mul_right _ (card_residueVector_le hp.pos a ha m)
    _ = p ^ ((Finset.univ.sum (fun (i : Fin n) => r - a i)) + r*d+n) := by rw [← pow_add]; congr 1 <;> omega

end MAPFordMixedResidueCardinality
end

#print axioms MAPFordMixedResidueCardinality.card_residueVector_le
#print axioms MAPFordMixedResidueCardinality.card_liftedSource_le
