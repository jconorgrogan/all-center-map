import FordCollisionActualHolder
import FordBoundaryCollisionGeometry
import FordCollisionHalfCount

noncomputable section
namespace FordEnergyCollisionExclusion
open FordBoundaryCountGeometry FordCollisionThreeMoments

/-- At a doubled-energy maximizing profile, collision-free solutions carry
at least half the energy once the source alphabet exceeds the explicit bound. -/
theorem energy_le_twice_collisionGood
    {A U : Type*} [Fintype A] [Fintype U] {k : ℕ}
    (hk : 2 ≤ k) (hU : 16*k^4 < Fintype.card U)
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (hmax : Fintype.card (EnergyZero f (doubled g) k) ≤
      Fintype.card (EnergyZero f g k)) :
    Fintype.card (EnergyZero f g k) ≤
      2 * Fintype.card (FordBoundaryCollisionGeometry.CollisionGood f g k) := by
  have hpinEq :
      Fintype.card (FordBoundaryCollisionGeometry.CollisionPinned f g (k-2)) =
      Fintype.card (FordCollisionPinnedBound.CollisionPinned f g (k-2)) :=
    Fintype.card_congr (Equiv.refl _)
  have hh : Fintype.card (FordCollisionPinnedBound.CollisionPinned f g (k-2))^(2*k) ≤
      Fintype.card (EnergyZero f (doubled g) k) *
        Fintype.card (EnergyZero f g k)^(2*k-2) * Fintype.card (BaseZero f) := by
    exact_mod_cast FordCollisionActualHolder.collision_pinned_holder hk f g
  have hd : (Fintype.card U)^k * Fintype.card (BaseZero f) ≤
      Fintype.card (EnergyZero f g k) := by
    simpa only [Nat.mul_comm] using diagonal_lower f g k
  have hb := FordBoundaryCollisionGeometry.collisionBad_card_le f g (k-2)
  rw [hpinEq] at hb
  have hs : k-2+2=k := by omega
  rw [hs] at hb
  apply MAPFordCollisionHalfCount.energy_le_twice_good
    k (Fintype.card U) (2*k*k)
    (Fintype.card (EnergyZero f g k)) (Fintype.card (EnergyZero f (doubled g) k))
    (Fintype.card (BaseZero f))
    (Fintype.card (FordCollisionPinnedBound.CollisionPinned f g (k-2)))
    (Fintype.card (FordBoundaryCollisionGeometry.CollisionBad f g k))
    (Fintype.card (FordBoundaryCollisionGeometry.CollisionGood f g k)) hk
    (by convert hU using 1 <;> ring) hh hmax hd hb
  exact FordBoundaryCollisionGeometry.collision_card_partition f g k

end FordEnergyCollisionExclusion
#print axioms FordEnergyCollisionExclusion.energy_le_twice_collisionGood
