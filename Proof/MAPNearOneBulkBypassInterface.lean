import CGLNearFineMeshSourceAdapter

/-! The exact fixed-strip output used by the near-one bypass.  This file
states no analytic theorem; the interface is inhabited by the powered/post-A.5
adapter, and its consumer retains literal multiplicity-aware zero counts. -/
namespace MAPNearOneBulkBypassInterface
open DirichletZeros MAPGuthMaynard
noncomputable section

def FixedPrimitiveBulkPolylogDensity : Prop :=
  ∀ K eta : ℝ, 0 < K → 0 < eta →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        4 / 5 ≤ sigma → sigma ≤ 559 / 560 →
        ∀ (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r),
          chi.IsPrimitive → r ≤ Q →
          (dirichletZeroCount chi sigma T : ℝ) ≤
            C * Real.rpow T (densityCoeff * (1 - sigma) + eta)

end
end MAPNearOneBulkBypassInterface
