import MAPVarianceTransferWeld

/-!
# Cutoff-faithful MAP-to-variance transfer

The first transfer theorem in `MAPVarianceTransferWeld` asks for a deterministic
remainder estimate at every pair of cutoff exponents.  The major-arc argument
in the manuscript has the weaker and natural quantifier order: after a target
saving and lower cutoff bounds have been fixed, one may choose sufficiently
large cutoffs.  This module proves that this selectable-cutoff interface is
enough, because enlarging the major arcs only shrinks the positive minor
weight and hence preserves the all-center local MAP bound.
-/

namespace MAPVarianceTransferCutoffWeld

open AddCircle MeasureTheory
open scoped BigOperators ComplexConjugate ArithmeticFunction

noncomputable section

open PrimePairEndpoints MAPHarmonicEndpoint
open MAPVarianceTransferWeld

/-- Exact family transfer with manuscript-faithful cutoff synchronization.
MAP first supplies `Bmap,Dmap`; the deterministic major/support theorem then
chooses `B,D` above those lower bounds.  Positivity and cutoff monotonicity
carry the local MAP estimate to the common enlarged mask. -/
theorem varianceFamily_of_allCenterLocalMAP_and_selectable_remainder
    (hMAP : AllCenterLocalMAP)
    (hRemainder :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B₀ D₀ : ℕ,
          ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
            ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
              ∀ X H h₀ : ℝ, X₀ ≤ X →
                LegalParameters ε X H h₀ →
                deterministicRemainderEnergy X H h₀ B D ≤
                  C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    VarianceFamily := by
  rcases exists_minorCoefficientWindowConstant with ⟨C₀, hC₀, hfejer⟩
  intro A ε hA hε
  have hAmap : 0 < A + 3 := by linarith
  obtain ⟨Bmap, Dmap, Cmap, Xmap, hCmap, hXmap, hlocal⟩ :=
    FejerMAPInterfaceWeld.allCenterLocalMAP_minorWeight hMAP
      (A + 3) ε hAmap hε
  obtain ⟨B, D, hBmap, hDmap, Crem, Xrem, hCrem, hXrem, hrem⟩ :=
    hRemainder A ε hA hε Bmap Dmap
  let C : ℝ := 16 * C₀ * Cmap + 2 * Crem
  let X₀ : ℝ := max 3 (max Xmap Xrem)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hX₀ : 2 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans (by norm_num) (le_max_left 3 (max Xmap Xrem))
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hX3 : 3 ≤ X :=
    (le_max_left 3 (max Xmap Xrem)).trans hXX₀
  have hXmap' : Xmap ≤ X :=
    (le_trans (le_max_left Xmap Xrem)
      (le_max_right 3 (max Xmap Xrem))).trans hXX₀
  have hXrem' : Xrem ≤ X :=
    (le_trans (le_max_right Xmap Xrem)
      (le_max_right 3 (max Xmap Xrem))).trans hXX₀
  have hX2 : 2 ≤ X := by linarith
  have hX1 : 1 ≤ X := one_le_two.trans hX2
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hLpos : 0 < Real.log X :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hX2)
  have hL3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
      Real.exp_one_lt_three
  have hlog3X : Real.log 3 ≤ Real.log X :=
    Real.log_le_log (by norm_num) hX3
  have hL : 1 ≤ Real.log X := hL3.le.trans hlog3X
  have hexp0 : 0 ≤ 2 / 15 + ε := by linarith
  have hH1 : 1 ≤ H :=
    (Real.one_le_rpow hX1 hexp0).trans hlegal.1
  let totalBound : ℝ := 8 * X * (Real.log X) ^ 2
  let localBound : ℝ :=
    Cmap * X * Real.rpow (Real.log X) (-(A + 3))
  let remainderBound : ℝ :=
    Crem * H * X ^ 2 * Real.rpow (Real.log X) (-A)
  have htotal0 : 0 ≤ totalBound := by
    dsimp [totalBound]
    positivity
  have hlocal0 : 0 ≤ localBound := by
    dsimp [localBound]
    positivity
  have htotal :
      (∫ a : UnitAddCircle, minorWeight X B D a
        ∂AddCircle.haarAddCircle) ≤ totalBound := by
    simpa [totalBound] using integral_minorWeight_le_eight_log_sq hX2 B D
  have hlocalMap : ∀ center : UnitAddCircle,
      (∫ a in centeredArc H center, minorWeight X Bmap Dmap a
        ∂AddCircle.haarAddCircle) ≤ localBound := by
    intro center
    simpa [localBound] using hlocal X H hXmap' hlegal.1 center
  have hlocal' : ∀ center : UnitAddCircle,
      (∫ a in centeredArc H center, minorWeight X B D a
        ∂AddCircle.haarAddCircle) ≤ localBound :=
    FejerMAPInterfaceWeld.localMassBound_preserved_of_enlarge_cutoffs
      hXpos hL hBmap hDmap hlocalMap
  have hrem' :
      deterministicRemainderEnergy X H h₀ B D ≤ remainderBound := by
    simpa [remainderBound] using hrem X H h₀ hXrem' hlegal
  have hfixed := primePairVariance_le_of_localMAP_and_remainder
    hfejer hH1 htotal0 hlocal0 htotal hlocal' hrem'
  have hrate := log_sq_mul_stronger_rpow_le
    (L := Real.log X) (A := A) hL
  calc
    primePairVariance X H h₀ ≤
        2 * C₀ * H * totalBound * localBound + 2 * remainderBound := hfixed
    _ = 16 * C₀ * Cmap * H * X ^ 2 *
          ((Real.log X) ^ 2 * Real.rpow (Real.log X) (-(A + 3))) +
        2 * Crem * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      dsimp [totalBound, localBound, remainderBound]
      ring
    _ ≤ 16 * C₀ * Cmap * H * X ^ 2 *
          Real.rpow (Real.log X) (-A) +
        2 * Crem * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      gcongr
    _ = C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      dsimp [C]
      ring

/-- End-to-end endpoint assembly with the corrected selectable-cutoff
remainder surface.  This remains conditional on the three explicitly named
analytic families; it does not claim that any of them has already been proved. -/
theorem certifiedMAPEndpoint_of_localMAP_selectableRemainder_singularSquare
    (hMAP : AllCenterLocalMAP)
    (hRemainder :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B₀ D₀ : ℕ,
          ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
            ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
              ∀ X H h₀ : ℝ, X₀ ≤ X →
                LegalParameters ε X H h₀ →
                deterministicRemainderEnergy X H h₀ B D ≤
                  C * H * X ^ 2 * Real.rpow (Real.log X) (-A))
    (hSingularSquare :
      ∀ ε : ℝ, 0 < ε →
        ∃ k : ℕ, ∃ C X₀ : ℝ,
          0 < C ∧ 2 ≤ X₀ ∧
          ∀ X H h₀ : ℝ, X₀ ≤ X →
            LegalParameters ε X H h₀ →
            singularSquareMain H h₀ ≤
              C * H * (Real.log X) ^ k) :
    CertifiedMAPEndpoint := by
  have hVariance :=
    varianceFamily_of_allCenterLocalMAP_and_selectable_remainder
      hMAP hRemainder
  have hQ4 := q4TwoSidedFamily_of_variance_and_singularSquare
    hVariance hSingularSquare
  exact certifiedMAPEndpoint_of_map_variance_q4TwoSided hMAP hVariance hQ4

end

end MAPVarianceTransferCutoffWeld
