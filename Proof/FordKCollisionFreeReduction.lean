import FordGoodKEnergy
import FordEnergyCollisionExclusion

noncomputable section
namespace MAPFordKCollisionFreeReduction
open MAPFordType MAPFordP16Source35Triangular MAPFordLemma32LiteralContract
open FordKPointEnergy FordGoodKEnergy FordBoundaryCountGeometry

/-- An actual maximizing family has enough collision-free K solutions to
control the original family's full K count. -/
theorem exists_collision_free_reduction
    {s k d P Q q : ℕ} {T : ℤ}
    (hk : 2 ≤ k) (hP : 16*k^4 < P)
    (m0 : ℕ) (psi0 : Fin k → Polynomial ℤ)
    (h0 : FordType k d T m0 (psiNatSucc psi0)) :
    ∃ (m : ℕ) (psi : Fin k → Polynomial ℤ),
      FordType k d T m (psiNatSucc psi) ∧
      Fintype.card (KPoint s k P Q psi0 q) ≤
        2 * Fintype.card (GoodK (s := s) (P := P) (Q := Q) psi q) := by
  obtain ⟨m, psi, hpsi, hdouble, hKdouble, hEdouble, hmax⟩ :=
    FordMaxEnergyInput.exists_max_energy_input
      (s := s) (k := k) (d := d) (P := P) (Q := Q) (q := q) m0 psi0 h0
  let f : PowerWord (s := s) (Q := Q) → Fin k → ℤ := baseFreq (q := q)
  let g : SourcePoint (P := P) → Fin k → ℤ := sourceFreq psi
  have hU : 16*k^4 < Fintype.card (SourcePoint (P := P)) := by
    rw [FordMaxEnergyInput.sourcePoint_card]
    exact hP
  have hgood := FordEnergyCollisionExclusion.energy_le_twice_collisionGood
    hk hU f g hEdouble
  have hGE : Fintype.card (GoodEnergy (s := s) (P := P) (Q := Q) (q := q) psi) =
      Fintype.card (FordBoundaryCollisionGeometry.CollisionGood f g k) :=
    Fintype.card_congr (Equiv.refl _)
  refine ⟨m, psi, hpsi, ?_⟩
  calc
    Fintype.card (KPoint s k P Q psi0 q) ≤ Fintype.card (KPoint s k P Q psi q) :=
      hmax m0 psi0 h0
    _ = Fintype.card (EnergyZero f g k) := kpoint_card_eq_energy psi q
    _ ≤ 2 * Fintype.card (FordBoundaryCollisionGeometry.CollisionGood f g k) := hgood
    _ = 2 * Fintype.card (GoodK (s := s) (P := P) (Q := Q) psi q) := by
      rw [← hGE, goodK_card_eq_goodEnergy]

end MAPFordKCollisionFreeReduction
#print axioms MAPFordKCollisionFreeReduction.exists_collision_free_reduction
