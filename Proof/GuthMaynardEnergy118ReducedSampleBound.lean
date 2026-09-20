import GuthMaynardEnergy118ActualMoments
import GuthMaynardEnergy118ActualSecondMoment
import GuthMaynardEnergy118Coordinates
import GuthMaynardEnergy118LogInterior
import GuthMaynardEnergy118ReducedGeometry
import GuthMaynardLemma118LogPacking

open scoped BigOperators FourierTransform SchwartzMap
open MeasureTheory
noncomputable section
namespace GuthMaynardEnergy118ReducedSampleBound
open CGLProofDAG GuthMaynardHeathBrownInterface
open GuthMaynardRatioKernelIdentity GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEnergy118ActualMoments GuthMaynardEnergy118ActualSecondMoment
open GuthMaynardEnergy118Coordinates GuthMaynardEnergy118LogInterior
open GuthMaynardEnergy118GCD GuthMaynardLemma118 GuthMaynardJIteration

def sourceFourierTailMoment (k : ℕ) : ℝ :=
  ∫ xi : ℝ, |xi|^k * ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖

theorem exists_compact_fourier_moments :
    ∃ C2 C4 : ℝ, 0 < C2 ∧ 0 < C4 ∧ ∀ W : Finset ℝ, OneSeparated W →
      (∫ u : ℝ in Set.Icc ((-1 : ℝ)/(2*Real.pi)) (1/(2*Real.pi)),
        ‖pointMassFourierKernel W u‖^2) ≤ C2*(W.card : ℝ) ∧
      (∫ u : ℝ in Set.Icc ((-1 : ℝ)/(2*Real.pi)) (1/(2*Real.pi)),
        ‖pointMassFourierKernel W u‖^4) ≤ C4*(sourceApproximateAdditiveEnergy W : ℝ) := by
  obtain ⟨C2,hC2,h2⟩ := exists_compact_second_card_constant
  obtain ⟨C4,hC4,h4⟩ := exists_compact_fourth_energy_constant
  refine ⟨(1/(2*Real.pi))*C2,(1/(2*Real.pi))*C4,by positivity,by positivity,?_⟩
  intro W hsep
  constructor
  · rw [compact_pointMass_moment_eq_log]
    have hh := mul_le_mul_of_nonneg_left (h2 W hsep) (by positivity : 0 ≤ 1/(2*Real.pi))
    simpa only [mul_assoc] using hh
  · rw [compact_pointMass_moment_eq_log]
    have hh := mul_le_mul_of_nonneg_left (h4 W) (by positivity : 0 ≤ 1/(2*Real.pi))
    simpa only [mul_assoc] using hh

/-- The actual reduced-ratio cubic sample bound. Both compact moments,
rational separation and the exact interior collar are supplied internally.
The displayed Fourier tail is retained literally for later epsilon budgeting. -/
theorem exists_reduced_cubic_sample_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N d : ℕ) (W : Finset ℝ) (T A : ℝ) (k : ℕ),
        1 ≤ N → 1 ≤ d → 0 < T → 0 < A → OneSeparated W →
        ContainedInIntervalOfLength W T → A/(3*T) ≤ logFrequencyMargin →
        (∑ p ∈ reducedPairs N d, ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^3) ≤
          C*(T+A*((N : ℝ)/(d : ℝ))^2)*Real.sqrt (W.card : ℝ)*
            Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ) +
          (reducedPairs N d).card*((W.card : ℝ)^3*(A^k)⁻¹*sourceFourierTailMoment k) := by
  obtain ⟨C2,C4,hC2,hC4,hmom⟩ := exists_compact_fourier_moments
  let C0 : ℝ := sourceBumpFourierConstant 1 zero_lt_one 0
  have hC0 : 0 ≤ C0 := sourceBumpFourierConstant_nonneg 1 zero_lt_one 0
  let C : ℝ := (C0+1)*(3+32*Real.pi)*Real.sqrt C2*Real.sqrt C4
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N d W T A k hN hd hT hA hsep hcontained hcollar
  obtain ⟨x0,hinterval⟩ := hcontained
  let X : ℝ := (N : ℝ)/(d : ℝ)
  let B : ℝ := 2*X
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hX : 0 < X := div_pos hNpos hdpos
  have hB : 0 < B := by dsimp [B]; positivity
  let P := reducedPairs N d
  have hnumden : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧ (p.2 : ℝ) ≤ B ∧
      (p.1 : ℝ)/(p.2 : ℝ) ≤ 2 := by
    intro p hp
    have hp0 := reducedPairs_coords_pos hN hd hp
    have hb := reducedPairs_denominator_le hN hd hp
    have hr := reducedPairs_ratio_bounds hN hd hp
    refine ⟨hp0.1,hp0.2,?_,hr.2⟩
    simpa only [B,X,mul_div_assoc] using hb
  have hcross : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1*q.2 ≠ q.1*p.2 := by
    intro p hp q hq hpq
    exact reducedPairs_cross_ne_of_ne hN hd hp hq hpq
  have hcenter : ∀ p ∈ P,
      (-1 : ℝ)/(2*Real.pi)+A/(3*T) ≤ Real.log ((p.1 : ℝ)/(p.2 : ℝ))/(-2*Real.pi) ∧
      Real.log ((p.1 : ℝ)/(p.2 : ℝ))/(-2*Real.pi) ≤ 1/(2*Real.pi)-A/(3*T) := by
    intro p hp
    have hr := reducedPairs_ratio_bounds hN hd hp
    exact ratio_log_frequency_interior hr.1 hr.2 hcollar
  have hsrc := sum_ratioKernel_cube_le_logPacking_mul_sqrtMoments_add_tail
    W P k hT hA hB hinterval hnumden hcross hcenter
  obtain ⟨h2,h4⟩ := hmom W hsep
  let I2 : ℝ := ∫ u : ℝ in Set.Icc ((-1 : ℝ)/(2*Real.pi)) (1/(2*Real.pi)),
    ‖pointMassFourierKernel W u‖^2
  let I4 : ℝ := ∫ u : ℝ in Set.Icc ((-1 : ℝ)/(2*Real.pi)) (1/(2*Real.pi)),
    ‖pointMassFourierKernel W u‖^4
  have hs2 : Real.sqrt I2 ≤ Real.sqrt C2*Real.sqrt (W.card : ℝ) := by
    rw [← Real.sqrt_mul hC2.le]
    exact Real.sqrt_le_sqrt h2
  have hs4 : Real.sqrt I4 ≤ Real.sqrt C4*Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ) := by
    rw [← Real.sqrt_mul hC4.le]
    exact Real.sqrt_le_sqrt h4
  let z : ℝ := (8*Real.pi*(A/(3*T)))*B^2
  let F : ℝ := ((⌊z⌋₊+1 : ℕ) : ℝ)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hF : F ≤ z+1 := by
    dsimp [F]
    push_cast
    exact add_le_add (Nat.floor_le hz) (le_refl 1)
  let L : ℝ := (C0+1)*(3+32*Real.pi)*(T+A*X^2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hcost : C0*(3*T)*F ≤ L := by
    calc
      _ ≤ C0*(3*T)*(z+1) := mul_le_mul_of_nonneg_left hF (by positivity)
      _ = C0*(3*T+32*Real.pi*A*X^2) := by
        dsimp [z,B]
        field_simp
        ring
      _ ≤ C0*((3+32*Real.pi)*(T+A*X^2)) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        have hh : 0 ≤ 32*Real.pi*T+3*A*X^2 := by positivity
        nlinarith
      _ ≤ (C0+1)*((3+32*Real.pi)*(T+A*X^2)) := by gcongr; linarith
      _ = L := by dsimp [L]; ring
  have hmain : C0*(3*T)*F*Real.sqrt I2*Real.sqrt I4 ≤
      C*(T+A*X^2)*Real.sqrt (W.card : ℝ)*Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ) := by
    calc
      _ ≤ L*(Real.sqrt C2*Real.sqrt (W.card : ℝ))*
          (Real.sqrt C4*Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ)) := by
        apply mul_le_mul _ hs4 (Real.sqrt_nonneg _) (by positivity)
        exact mul_le_mul hcost hs2 (Real.sqrt_nonneg _) hL
      _ = _ := by dsimp [L,C]; ring
  have hh := hsrc.trans (add_le_add hmain (le_refl _))
  exact hh

end GuthMaynardEnergy118ReducedSampleBound
#print axioms GuthMaynardEnergy118ReducedSampleBound.exists_compact_fourier_moments
#print axioms GuthMaynardEnergy118ReducedSampleBound.exists_reduced_cubic_sample_constant
