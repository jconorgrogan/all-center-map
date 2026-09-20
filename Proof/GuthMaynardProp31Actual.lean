import GuthMaynardProp31LargeN
import GuthMaynardProp31SmallRange
import GuthMaynardProp31PolynomialBridge
import GuthMaynardS3ProfileScaleGrowth

open GuthMaynardSmoothedProp31Consumer GuthMaynardProp31PolynomialBridge
open GuthMaynardHeathBrownInterface GuthMaynardS3LiteralLemma82
open GuthMaynardSectionThreeCutoff

noncomputable section
namespace GuthMaynardProp31Actual

/-- The fixed concrete plateau cutoff satisfies the full Proposition 3.1
contract, including finite small N and arbitrary values in the legal window. -/
theorem actual_fixedWeightProp31 : FixedWeightProp31 sectionThreeCutoffReal := by
  refine ⟨sectionThreeCutoffReal_plateau, ?_⟩
  intro eps heps
  obtain ⟨Cl, hCl, N0, hN0, hlargeN⟩ :=
    GuthMaynardProp31LargeN.exists_actual_prop31_largeN_bound eps heps
  let Cs : ℝ := 2 * (N0 : ℝ) ^ (6 / 5 : ℝ)
  let C : ℝ := Cl + Cs
  have hCs : 0 < Cs := by
    dsimp [Cs]
    have : 0 < (N0 : ℝ) := by exact_mod_cast (show 0 < N0 by omega)
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N V b W hN hV hlo hhi hb hsupp hsep hheight hlarge
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : 0 < (N : ℝ) := lt_trans zero_lt_one hNgt
  let T : ℝ := (N : ℝ) ^ (6 / 5 : ℝ)
  have hT1 : 1 ≤ T := Real.one_le_rpow hN1 (by norm_num)
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hcontained : ContainedInIntervalOfLength W T := by
    refine ⟨0, ?_⟩
    intro t ht
    simpa [T] using hheight t ht
  have hsep' : TEtaSeparated W T eps := hsep
  have hpack := GuthMaynardS3ProfileScaleGrowth.card_le_two_time_of_separation
    hT1 heps.le hsep' hcontained
  have htarget : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 := by positivity
  have hTeps : 0 ≤ T ^ eps := by positivity
  by_cases hbig : N0 ≤ N
  · by_cases hW : W.Nonempty
    · obtain ⟨hslo, hshi, hrepr⟩ :=
        GuthMaynardProp31ValueExponent.valueExponent_spec hNgt hV hlo
          (by convert hhi using 1 <;> norm_num)
      let sigma : ℝ := GuthMaynardProp31ValueExponent.valueExponent N V
      have hsharp : ∀ t ∈ W, (N : ℝ) ^ sigma ≤
          ‖CGLProofDAG.dirichletPolynomial b N t‖ := by
        intro t ht
        have hh := hlarge t ht
        rw [smoothed_eq_sharp_of_supported sectionThreeCutoffReal_plateau hN hsupp] at hh
        rw [hrepr] at hh
        exact hh
      have hbound := hlargeN N W T sigma b hbig rfl hslo
        (by convert hshi using 1 <;> norm_num) hW hsep' hcontained
        (fun n _ => hb n) hsupp hsharp
      have hfactor : (N : ℝ) ^ (18 / 5 - 4 * sigma : ℝ) =
          T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 := by
        rw [hrepr]
        change (N : ℝ) ^ (18 / 5 - 4 * sigma : ℝ) =
          (N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ) /
            ((N : ℝ) ^ sigma) ^ 4
        rw [← Real.rpow_mul_natCast hNp.le,
          ← Real.rpow_add hNp, ← Real.rpow_sub hNp]
        congr 1
        ring
      rw [hfactor] at hbound
      calc
        (W.card : ℝ) ≤ Cl * T ^ eps *
            (T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := hbound
        _ ≤ C * T ^ eps *
            (T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
          apply mul_le_mul_of_nonneg_right _ htarget
          apply mul_le_mul_of_nonneg_right _ hTeps
          dsimp [C]
          linarith
    · have hzero : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
      simp only [hzero, Finset.card_empty, Nat.cast_zero]
      positivity
  · have hsmall := GuthMaynardProp31SmallRange.small_range_cardinality hN1
      (show (N : ℝ) ≤ (N0 : ℝ) by exact_mod_cast (show N ≤ N0 by omega))
      hV hhi heps.le hpack
    calc
      (W.card : ℝ) ≤ Cs * T ^ eps *
          (T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := hsmall
      _ ≤ C * T ^ eps *
          (T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
        apply mul_le_mul_of_nonneg_right _ htarget
        apply mul_le_mul_of_nonneg_right _ hTeps
        dsimp [C]
        linarith

end GuthMaynardProp31Actual
#print axioms GuthMaynardProp31Actual.actual_fixedWeightProp31
