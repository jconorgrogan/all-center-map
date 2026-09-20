import RamachandraTheorem6Unconditional
import MAPPolylogCor212SplitAlgebra

/-!
# Uniform prefix moments in the full dynamic d1/d2 range

The published error terms are retained for cutoffs larger than the time
height. The canonical theorem requires the cutoff below the ambient scale,
not below the height; the former source adapter's extra restriction was unused.
-/
namespace MRTDynamicD12MomentSource

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open scoped BigOperators
open MeasureTheory
open MAPMRTLemma211AllCharacterSource MAPBHPCanonicalAllCharacterLiteral
open MAPBHPCanonicalAllCharacterFromPrincipal MAPMRTCorollary25Minkowski
open MAPPolylogCor212SplitAlgebra MAPPolylogCor212SplitSampled
open MAPMRTProposition61TypeD1FirstInequality

noncomputable section

structure DynamicD12MomentRange (X T K : ℝ) (q cutoff : ℕ) : Prop where
  X_large : 8 ≤ X
  T_ge_two : 2 ≤ T
  q_ge_one : 1 ≤ q
  cutoff_ge_two : 2 ≤ cutoff
  K_nonneg : 0 ≤ K
  K_le_loglog : K ≤ Real.log (Real.log X)
  q_polylog : (q : ℝ) ≤ Real.rpow (Real.log X) K
  q_le_T : (q : ℝ) ≤ T
  cutoff_le_X : (cutoff : ℝ) ≤ X
  two_T_le_X : 2 * T ≤ X

def DynamicD12SelectedPrefixMoment : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
    ∀ (X T K : ℝ) (q cutoff : ℕ)
      (S : Finset (DirichletCharacter ℂ q × ℝ)),
      DynamicD12MomentRange X T K q cutoff →
      (∀ z ∈ S, |z.2| ≤ T) → SameCharacterOneSeparated S →
      selectedPrefixFourthMass cutoff S ≤ C * (1 + Real.log X) ^ B *
        ((q : ℝ) * T + (S.card : ℝ) *
          ((q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
            1 / (cutoff : ℝ) ^ 2) +
          (cutoff : ℝ) ^ 2 * selectedPrincipalDecayMass S)

/-- Global constants precede all dynamic source parameters. -/
theorem dynamicD12SelectedPrefixMoment_proved : DynamicD12SelectedPrefixMoment := by
  classical
  have hcanonical := MAPBHPCanonicalPrincipalSourceClosed.canonicalAllCharacterSelectedFourthMomentLiteral_of_ramachandra
    RamachandraTheorem6Unconditional.ramachandraTheorem6K2Source_proved
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
  intro X T K q cutoff S hrange hheight hspacing
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


def DynamicD12SampledBudget : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
    ∀ {X T K : ℝ} {q cutoff : ℕ} [NeZero q]
      {S : Finset (DirichletCharacter ℂ q × ℝ)}
      {left right : DirichletCharacter ℂ q × ℝ → ℝ} {A : ℝ},
      DynamicD12MomentRange X T K q cutoff →
      (∀ z ∈ S, 0 ≤ right z - left z ∧ right z - left z ≤ 1) →
      (∀ z ∈ S, ∀ t ∈ Set.Icc (left z) (right z),
        ‖criticalPrefixPolynomial q cutoff z.1 t‖ ^ 4 ≤
          ‖criticalPrefixPolynomial q cutoff z.1 z.2‖ ^ 4) →
      (∀ z ∈ S, T / 2 ≤ |z.2|) →
      (∀ z ∈ S, |z.2| ≤ T) →
      (S.card : ℝ) ≤ A * (q : ℝ) * T →
      SameCharacterOneSeparated S →
      bhpSampledPieceMass
          (fun chi t => ‖criticalPrefixPolynomial q cutoff chi t‖)
          S left right ≤ C * (1 + Real.log X) ^ B *
        ((q : ℝ) * T +
          (A * (q : ℝ) * T) *
            ((q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
              1 / (cutoff : ℝ) ^ 2) +
          (cutoff : ℝ) ^ 2 *
            ((A * (q : ℝ) * T) * (16 / T ^ 4)))


theorem dynamicD12SampledBudget_proved : DynamicD12SampledBudget := by
  classical
  have hSelected := dynamicD12SelectedPrefixMoment_proved
  obtain ⟨C, hC, B, hB, hsource⟩ := hSelected
  refine ⟨C, hC, B, hB, ?_⟩
  intro X T K q cutoff _inst S left right A
    hrange hlength hmax hannulus hheight hcard hspacing
  let F : DirichletCharacter ℂ q → ℝ → ℝ :=
    fun chi t => ‖criticalPrefixPolynomial q cutoff chi t‖
  have hF : ∀ chi, Continuous (F chi) := by
    intro chi
    unfold F criticalPrefixPolynomial
    unfold MAPMRTLemma210OrthogonalityReduction.twistedFinitePolynomial
      MAPMRTLemma210OrthogonalityReduction.twistedPhase
    fun_prop
  have hTpos : 0 < T := by linarith [hrange.T_ge_two]
  have hdisc := bhpSampledPieceMass_le_selectedFourthMass hF hlength hmax
  have hsource' := hsource X T K q cutoff S
    hrange hheight hspacing
  have htail0 := bhpPrincipalDecayMass_le_card_mul_sixteen_div
    (S := S) hTpos hannulus
  have htail : selectedPrincipalDecayMass S ≤
      (A * (q : ℝ) * T) * (16 / T ^ 4) := by
    rw [← principalDecayMass_eq_selected]
    exact htail0.trans
      (mul_le_mul_of_nonneg_right hcard (by positivity))
  have hshape0 : 0 ≤
      (q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
        1 / (cutoff : ℝ) ^ 2 := by positivity
  have hlog0 : 0 ≤ (1 + Real.log X) ^ B := by
    have hlog : 0 ≤ Real.log X :=
      Real.log_nonneg (by linarith [hrange.X_large])
    positivity
  calc
    bhpSampledPieceMass F S left right ≤
        bhpSelectedFourthMass F S := hdisc
    _ = selectedPrefixFourthMass cutoff S := selectedFourthMass_prefix_eq S
    _ ≤ C * (1 + Real.log X) ^ B *
        ((q : ℝ) * T +
          (S.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
              1 / (cutoff : ℝ) ^ 2) +
          (cutoff : ℝ) ^ 2 * selectedPrincipalDecayMass S) := hsource'
    _ ≤ C * (1 + Real.log X) ^ B *
        ((q : ℝ) * T +
          (A * (q : ℝ) * T) *
            ((q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
              1 / (cutoff : ℝ) ^ 2) +
          (cutoff : ℝ) ^ 2 *
            ((A * (q : ℝ) * T) * (16 / T ^ 4))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hlog0)
      gcongr


end
end MRTDynamicD12MomentSource

#print axioms MRTDynamicD12MomentSource.dynamicD12SelectedPrefixMoment_proved
#print axioms MRTDynamicD12MomentSource.dynamicD12SampledBudget_proved
