import GuthMaynardLemma295ContourAssembly
import GuthMaynardLemma295ExactMDeepLeft
import GuthMaynardLemma295ResidueExactM

/-! The source-scale approximate functional equation, with uniform constants. -/
namespace GuthMaynardLemma295ExactMAFE

open Complex Real MeasureTheory
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295ContourAssembly
open GuthMaynardLemma295VerticalIntegrability
open GuthMaynardLemma295ExactMDeepLeft
open GuthMaynardLemma295ResidueExactM
open GuthMaynardLemma295MellinAllLines
open GuthMaynardLemma295TailExponentLedger

noncomputable section

theorem lemma295CentralMajorant_nonneg (N M g R : ℝ) :
    0 ≤ lemma295CentralMajorant N M g R := by
  unfold lemma295CentralMajorant
  exact mul_nonneg (Real.sqrt_nonneg N)
    (integral_nonneg fun t => div_nonneg (norm_nonneg _) (by positivity))

/-- Lemma 29.5 at the canonical reflected length `T^(1+epsilon)/N`.
The constants are uniform in `T,U,N,g`, including every positive `N`. -/
theorem lemma295ApproximateFunctionalEquationExactM :
    Lemma295ApproximateFunctionalEquationExactM := by
  intro delta epsilon A hdelta hepsilon hA
  obtain ⟨Cr,hCr,hresAll⟩ := exists_norm_lemma295PoleResidue_le_exactM
    (delta := delta) (epsilon := epsilon) (A := A) hdelta
  obtain ⟨Cd,hCd,hdeepAll⟩ := deepLeftTail_exactM_power_saving
    (epsilon := epsilon) (A := A) hepsilon
  obtain ⟨Cc,hCc,hcriticalAll⟩ := exists_norm_integral_reflectedFinite_critical_exactM_le
    (epsilon := epsilon) (A := A) hepsilon
  let c : ℝ := 1 / (2 * Real.pi)
  let b : ℝ := sourceMellinDecayConstant (1/2)
  let C : ℝ := 1 + |Cr| + |c*b| + |c*Cc| + |c*Cd|
  refine ⟨C,2,?_,by norm_num,?_⟩
  · dsimp [C]
    positivity
  intro T U N g hT hN hNcap hgap hg hUT
  have hTone : 1 ≤ T := by linarith
  have hUone : 1 ≤ U :=
    ((Real.one_le_rpow hTone hdelta.le).trans hgap).trans hg
  have hres := hresAll (T := T) (N := N) (g := g) hTone hN hNcap hgap
  have hdeep := hdeepAll (T := T) (N := N) (U := U) (g := g)
    hT hN hNcap hUone hUT hg
  have hcritical := hcriticalAll (T := T) (N := N) (g := g) hTone hN hNcap
  dsimp only at hcritical
  have hnorm := norm_sourceHPlusSum_le_residue_add_critical_add_tail hN g
    ⌊reflectedLength29_40 T epsilon N⌋₊ (lemma295TailDepthStrong epsilon A)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmajor : 0 ≤ lemma295CentralMajorant N
      (reflectedLength29_40 T epsilon N) g (Real.rpow T epsilon) :=
    lemma295CentralMajorant_nonneg _ _ _ _
  have hpow : 0 ≤ Real.rpow T (-A) := Real.rpow_nonneg (by linarith) _
  have hCb : c*b ≤ C := by
    dsimp [C]
    linarith [le_abs_self (c*b), abs_nonneg Cr, abs_nonneg (c*Cc), abs_nonneg (c*Cd)]
  have hCe : Cr+c*Cc+c*Cd ≤ C := by
    dsimp [C]
    linarith [le_abs_self Cr, le_abs_self (c*Cc), le_abs_self (c*Cd), abs_nonneg (c*b)]
  calc
    ‖sourceHPlusSum N g‖ ≤
        Cr * Real.rpow T (-A) +
        c * (b * lemma295CentralMajorant N (reflectedLength29_40 T epsilon N)
          g (Real.rpow T epsilon) + Cc * Real.rpow T (-A)) +
        c * (Cd * Real.rpow T (-A)) := by
      exact hnorm.trans (add_le_add
        (add_le_add hres (mul_le_mul_of_nonneg_left hcritical hc))
        (mul_le_mul_of_nonneg_left hdeep hc))
    _ = (c*b) * lemma295CentralMajorant N (reflectedLength29_40 T epsilon N)
          g (Real.rpow T epsilon) +
        (Cr+c*Cc+c*Cd) * Real.rpow T (-A) := by ring
    _ ≤ C * lemma295CentralMajorant N (reflectedLength29_40 T epsilon N)
          g (Real.rpow T epsilon) + C * Real.rpow T (-A) :=
      add_le_add (mul_le_mul_of_nonneg_right hCb hmajor)
        (mul_le_mul_of_nonneg_right hCe hpow)

end
end GuthMaynardLemma295ExactMAFE

#print axioms GuthMaynardLemma295ExactMAFE.lemma295ApproximateFunctionalEquationExactM
