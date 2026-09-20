import MRTProposition61TypeD1FirstInequality
import MRTLemma210DyadicMeanSquare

/-!
# MRT Proposition 6.1, Type II: deterministic Cauchy--Fubini layer

The Type-II proof on MRT pp. 59--60 uses only Cauchy--Schwarz, Fubini, and
two applications of Lemma 2.10.  This file certifies the first two operations
and records the exact two mean-square hypotheses.  The premise-free dyadic
Lemma 2.10 theorem is imported for the source-facing instantiation.
-/

namespace MRTProposition61TypeIIFirstInequalityV3

open scoped BigOperators
open MeasureTheory
open MAPFarAnnulusSourceToModel
open MAPMRTProposition61TypeD1FirstInequality

noncomputable section

/-- The moving two-factor character mass in the Type-II proof. -/
def factoredTypeIIMass {Chi : Type*} [Fintype Chi]
    (alpha beta : Chi → ℝ → ℝ) (U t : ℝ) : ℝ :=
  ∑ chi : Chi, ∫ s in (t - U)..(t + U), alpha chi s * beta chi s

/-- Local character mean square for either Type-II factor. -/
def typeIILocalSquareMass {Chi : Type*} [Fintype Chi]
    (F : Chi → ℝ → ℝ) (U t : ℝ) : ℝ :=
  ∑ chi : Chi, ∫ s in (t - U)..(t + U), (F chi s) ^ 2

/-- Pointwise Cauchy--Schwarz over the character family and moving interval,
exactly the first display in the source Type-II proof. -/
theorem factoredTypeIIMass_sq_le
    {Chi : Type*} [Fintype Chi]
    {alpha beta : Chi → ℝ → ℝ}
    (halpha : ∀ chi, Continuous (alpha chi))
    (hbeta : ∀ chi, Continuous (beta chi))
    (halpha0 : ∀ chi t, 0 ≤ alpha chi t)
    (hbeta0 : ∀ chi t, 0 ≤ beta chi t)
    {U t : ℝ} (hU : 0 ≤ U) :
    (factoredTypeIIMass alpha beta U t) ^ 2 ≤
      typeIILocalSquareMass alpha U t *
        typeIILocalSquareMass beta U t := by
  let oneField : Chi → ℝ → ℝ := fun _ _ ↦ 1
  have hsource := factoredTypeD12Mass_sq_le (beta2 := oneField)
    halpha hbeta (fun _ ↦ continuous_const)
    halpha0 hbeta0 (fun _ _ ↦ zero_le_one) hU (t := t)
  simpa [factoredTypeIIMass, typeIILocalSquareMass,
    factoredTypeD12Mass, alphaLocalSquareMass,
    betaLocalProductSquareMass, oneField] using hsource

/-- Fubini gives overlap multiplicity at most `2U` for the long-factor local
mean square. -/
theorem integral_typeIILocalSquareMass_le
    {Chi : Type*} [Fintype Chi]
    {F : Chi → ℝ → ℝ}
    (hF : ∀ chi, Continuous (F chi))
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    (∫ t in a..b, typeIILocalSquareMass F U t) ≤
      2 * U * ∫ s in (a - U)..(b + U),
        ∑ chi : Chi, (F chi s) ^ 2 := by
  let oneField : Chi → ℝ → ℝ := fun _ _ ↦ 1
  have hsource := integral_betaLocalProductSquareMass_le (beta2 := oneField)
    hF (fun _ ↦ continuous_const) hab hU
  simpa [typeIILocalSquareMass, betaLocalProductSquareMass, oneField]
    using hsource

/-- Complete deterministic Type-II bound.  Its two remaining hypotheses are
precisely the two uses of MRT Lemma 2.10 at source lines 3134--3149. -/
theorem typeII_outerMass_le_of_two_meanSquares
    {Chi : Type*} [Fintype Chi]
    {alpha beta : Chi → ℝ → ℝ}
    (halpha : ∀ chi, Continuous (alpha chi))
    (hbeta : ∀ chi, Continuous (beta chi))
    (halpha0 : ∀ chi t, 0 ≤ alpha chi t)
    (hbeta0 : ∀ chi t, 0 ≤ beta chi t)
    {a b U P Q : ℝ} (hab : a ≤ b) (hU : 0 ≤ U)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (halphaMean : ∀ t ∈ Set.uIcc a b,
      typeIILocalSquareMass alpha U t ≤ P)
    (hbetaMean :
      (∫ s in (a - U)..(b + U),
        ∑ chi : Chi, (beta chi s) ^ 2) ≤ Q) :
    (∫ t in a..b, (factoredTypeIIMass alpha beta U t) ^ 2) ≤
      2 * U * P * Q := by
  have hmassCont : Continuous (factoredTypeIIMass alpha beta U) := by
    unfold factoredTypeIIMass
    apply continuous_finset_sum
    intro chi hchi
    exact continuous_movingWindowIntegral ((halpha chi).mul (hbeta chi)) U
  have hbetaMassCont : Continuous (typeIILocalSquareMass beta U) := by
    unfold typeIILocalSquareMass
    apply continuous_finset_sum
    intro chi hchi
    exact continuous_movingWindowIntegral ((hbeta chi).pow 2) U
  have hfirst :
      (∫ t in a..b, (factoredTypeIIMass alpha beta U t) ^ 2) ≤
        P * ∫ t in a..b, typeIILocalSquareMass beta U t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
    · exact (hmassCont.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul hbetaMassCont).intervalIntegrable _ _
    · intro t ht
      have hcauchy := factoredTypeIIMass_sq_le
        halpha hbeta halpha0 hbeta0 hU (t := t)
      have hbetaMass0 : 0 ≤ typeIILocalSquareMass beta U t := by
        unfold typeIILocalSquareMass
        exact Finset.sum_nonneg fun chi hchi ↦
          intervalIntegral.integral_nonneg (by linarith)
            (fun s hs ↦ sq_nonneg _)
      exact hcauchy.trans <| mul_le_mul_of_nonneg_right
        (halphaMean t (Set.Icc_subset_uIcc ht)) hbetaMass0
  have hsweep := integral_typeIILocalSquareMass_le hbeta hab hU
  have hlocal0 : 0 ≤ ∫ t in a..b,
      typeIILocalSquareMass beta U t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    unfold typeIILocalSquareMass
    exact Finset.sum_nonneg fun chi hchi ↦
      intervalIntegral.integral_nonneg (by linarith)
        (fun s hs ↦ sq_nonneg _)
  calc
    (∫ t in a..b, (factoredTypeIIMass alpha beta U t) ^ 2) ≤
        P * ∫ t in a..b, typeIILocalSquareMass beta U t := hfirst
    _ ≤ P * (2 * U * ∫ s in (a - U)..(b + U),
        ∑ chi : Chi, (beta chi s) ^ 2) :=
      mul_le_mul_of_nonneg_left hsweep hP
    _ ≤ P * (2 * U * Q) := by gcongr
    _ = 2 * U * P * Q := by ring

/-- The exact p. 59 scale before the final absorption.  Constants and
coefficient-energy losses remain visible in `Calpha,Cbeta`. -/
theorem typeII_outerMass_le_sourceMomentShape
    {Chi : Type*} [Fintype Chi]
    {alpha beta : Chi → ℝ → ℝ}
    (halpha : ∀ chi, Continuous (alpha chi))
    (hbeta : ∀ chi, Continuous (beta chi))
    (halpha0 : ∀ chi t, 0 ≤ alpha chi t)
    (hbeta0 : ∀ chi t, 0 ≤ beta chi t)
    {a b U q N T M Calpha Cbeta : ℝ}
    (hab : a ≤ b) (hU : 0 ≤ U) (hq : 0 ≤ q)
    (hN : 0 ≤ N) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hCalpha : 0 ≤ Calpha) (hCbeta : 0 ≤ Cbeta)
    (halphaMean : ∀ t ∈ Set.uIcc a b,
      typeIILocalSquareMass alpha U t ≤ Calpha * (q * (2 * U) + N))
    (hbetaMean :
      (∫ s in (a - U)..(b + U),
        ∑ chi : Chi, (beta chi s) ^ 2) ≤ Cbeta * (q * T + M)) :
    (∫ t in a..b, (factoredTypeIIMass alpha beta U t) ^ 2) ≤
      2 * U * (Calpha * (q * (2 * U) + N)) *
        (Cbeta * (q * T + M)) := by
  exact typeII_outerMass_le_of_two_meanSquares
    halpha hbeta halpha0 hbeta0 hab hU (by positivity) (by positivity)
    halphaMean hbetaMean

end
end MRTProposition61TypeIIFirstInequalityV3

#print axioms MRTProposition61TypeIIFirstInequalityV3.factoredTypeIIMass_sq_le
#print axioms MRTProposition61TypeIIFirstInequalityV3.typeII_outerMass_le_of_two_meanSquares
#print axioms MRTProposition61TypeIIFirstInequalityV3.typeII_outerMass_le_sourceMomentShape
