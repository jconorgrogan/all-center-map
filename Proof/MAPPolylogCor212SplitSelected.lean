import MAPPolylogCor212SplitDefinitions
import MAPPolylogCor212SplitAlgebra

/-!
# Selected-prefix normalization in small compilation units

This is the source application and the one analytic kernel estimate.  The
large nonnegative normalization is delegated to `SplitAlgebra`.
-/

namespace MAPPolylogCor212SplitSelected

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open scoped BigOperators
open MAPMRTLemma211AllCharacterSource
open MAPBHPCanonicalAllCharacterLiteral
open MAPBHPCanonicalAllCharacterFromPrincipal
open MAPMRTCorollary25Minkowski
open MAPPolylogCor212SplitDefinitions
open MAPPolylogCor212SplitAlgebra

noncomputable section

/-- The literal no-order-obstruction BHP theorem implies the exact MAP
polylog source with globally quantified constants. -/
theorem selectedPrefixFourthMoment_of_canonical
    (hcanonical : CanonicalAllCharacterSelectedFourthMomentLiteral) :
    MAPPolylogSelectedPrefixFourthMomentLiteral := by
  classical
  obtain ⟨C, C₆, hC, hC₆, hsource⟩ := hcanonical
  let K₀ : ℝ := 256 * (1 / Real.log 2 + 4)
  let M₀ : ℝ := 4 * C₆ * (4 : ℝ) ^ 400
  let Cmap : ℝ := 125 * C ^ 4 * (K₀ * M₀ + 1)
  have hK₀ : 0 < K₀ := by
    dsimp [K₀]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hM₀ : 0 < M₀ := by dsimp [M₀]; positivity
  have hCmap : 0 < Cmap := by dsimp [Cmap]; positivity
  refine ⟨Cmap, hCmap, 413, by norm_num, ?_⟩
  intro X H Q lambda U T K q cutoff S hrange hheight hspacing
  letI : NeZero q :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hrange.q_ge_one)⟩
  have hT0 : 0 ≤ T := by linarith [hrange.T_ge_two]
  have hraw := hsource (q := q) (X := cutoff) (S := S)
    (T := T) (x0 := X) (K := K)
    hrange.cutoff_ge_two (by linarith [hrange.T_ge_two])
    hrange.X_large
    (hrange.q_le_T.trans (by linarith [hrange.two_T_le_X]))
    hrange.cutoff_le_X (by linarith [hrange.two_T_le_X])
    hrange.two_T_le_X hrange.K_nonneg hrange.K_le_loglog
    hrange.q_polylog hheight hspacing
  clear hsource hheight hspacing
  let L : ℝ := 1 + Real.log X
  let A : ℝ := (q : ℝ) * T
  let E : ℝ := (S.card : ℝ) *
    ((q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
      1 / (cutoff : ℝ) ^ 2)
  let P : ℝ := (cutoff : ℝ) ^ 2 * selectedPrincipalDecayMass S
  let F : ℝ :=
    ((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
      (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
      (M₀ * (q : ℝ) * T * Real.log X ^ 401)
  have hlog0 : 0 ≤ Real.log X :=
    Real.log_nonneg (by linarith [hrange.X_large])
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hP : 0 ≤ P := by
    dsimp [P]
    apply mul_nonneg (sq_nonneg _)
    unfold selectedPrincipalDecayMass
    positivity
  have hkernel := perronHolderKernel_le_log_four
    (T := 2 * T) (x0 := X) (by linarith [hrange.T_ge_two])
    hrange.two_T_le_X
  have hlog405 : Real.log X ^ 405 ≤ L ^ 405 :=
    pow_le_pow_left₀ hlog0 (by dsimp [L]; linarith) 405
  have hmean0 : 0 ≤ M₀ * (q : ℝ) * T * Real.log X ^ 401 := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hM₀.le (Nat.cast_nonneg q)) hT0)
      (pow_nonneg hlog0 401)
  have hF : F ≤ K₀ * M₀ * A * L ^ 405 := by
    dsimp only [F]
    calc
      ((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
          (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
          (M₀ * (q : ℝ) * T * Real.log X ^ 401) ≤
        (K₀ * Real.log X ^ 4) *
          (M₀ * (q : ℝ) * T * Real.log X ^ 401) :=
        mul_le_mul_of_nonneg_right hkernel hmean0
      _ = K₀ * M₀ * A * Real.log X ^ 405 := by
        dsimp [A]
        rw [show 405 = 4 + 401 by norm_num, pow_add]
        ring
      _ ≤ K₀ * M₀ * A * L ^ 405 :=
        mul_le_mul_of_nonneg_left hlog405
          (mul_nonneg (mul_nonneg hK₀.le hM₀.le) hA)
  have hraw' : selectedPrefixFourthMass cutoff S ≤
      125 * (C * L ^ 2) ^ 4 * (F + E + P) := by
    simpa only [L, F, M₀, E, P] using hraw
  have hnormalized := normalize_literal_inner_outer hC.le hK₀ hM₀ hL
    hA hE hP hF
  calc
    selectedPrefixFourthMass cutoff S ≤
        125 * (C * L ^ 2) ^ 4 * (F + E + P) := hraw'
    _ ≤ (125 * C ^ 4 * (K₀ * M₀ + 1)) * L ^ 413 *
          (A + E + P) := hnormalized
    _ = Cmap * (1 + Real.log X) ^ 413 *
        ((q : ℝ) * T +
          (S.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
              1 / (cutoff : ℝ) ^ 2) +
          (cutoff : ℝ) ^ 2 * selectedPrincipalDecayMass S) := by
      rfl

end
end MAPPolylogCor212SplitSelected

#print axioms MAPPolylogCor212SplitSelected.selectedPrefixFourthMoment_of_canonical
