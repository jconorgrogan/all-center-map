import MRTCorollary25TypeD1IntegratedWeld
import FarAnnulusSourceToModel

/-!
# MRT Proposition 6.1, Type-d1: the first source inequality

This file certifies the deterministic Cauchy--Fubini reduction on pp. 60--61
of MRT.  It stops before the two cited analytic inputs: the character mean
square of Lemma 2.10 and the integral fourth moment of Corollary 2.12.
-/

namespace MAPMRTProposition61TypeD1FirstInequality

open scoped BigOperators
open MeasureTheory
open MAPFarAnnulusSourceToModel

noncomputable section

/-! ## BHP Lemma 9: deterministic source terms

Baker--Harman--Pintz Lemma 9 is stated for a finite, well-spaced set of
pairs `(chi,t)` at one fixed modulus, with no primitive-character restriction.
Its standing convention (3.33), however, excludes the exceptional set `E_q`.
The proof below does not assert that analytic lemma.  It records deductions
from its literal right-hand side, supplied as a direct inequality hypothesis.
-/

/-- The literal discrete fourth-power mass denoted `||N||_4^4` in BHP. -/
def bhpSelectedFourthMass {q : ℕ} [NeZero q]
    (F : DirichletCharacter ℂ q → ℝ → ℝ)
    (S : Finset (DirichletCharacter ℂ q × ℝ)) : ℝ :=
  ∑ z ∈ S, (F z.1 z.2) ^ 4

/-- The continuum mass of finitely many source bins assigned to the selected
pair which maximizes that bin. -/
def bhpSampledPieceMass {q : ℕ} [NeZero q]
    (F : DirichletCharacter ℂ q → ℝ → ℝ)
    (S : Finset (DirichletCharacter ℂ q × ℝ))
    (left right : DirichletCharacter ℂ q × ℝ → ℝ) : ℝ :=
  ∑ z ∈ S, ∫ t in left z..right z, (F z.1 t) ^ 4

/-- Exact local discretization used in Corollary 2.12.  Every clipped source
piece has length at most one and is charged to one selected maximizer.  Using
clipped pieces, rather than full bins crossing `T/2`, preserves the annular
lower bound needed for the principal-character residue term. -/
theorem bhpSampledPieceMass_le_selectedFourthMass
    {q : ℕ} [NeZero q]
    {F : DirichletCharacter ℂ q → ℝ → ℝ}
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {left right : DirichletCharacter ℂ q × ℝ → ℝ}
    (hF : ∀ chi, Continuous (F chi))
    (hlength : ∀ z ∈ S, 0 ≤ right z - left z ∧ right z - left z ≤ 1)
    (hmax : ∀ z ∈ S, ∀ t ∈ Set.Icc (left z) (right z),
      (F z.1 t) ^ 4 ≤ (F z.1 z.2) ^ 4) :
    bhpSampledPieceMass F S left right ≤ bhpSelectedFourthMass F S := by
  unfold bhpSampledPieceMass bhpSelectedFourthMass
  apply Finset.sum_le_sum
  intro z hz
  have hlr : left z ≤ right z := sub_nonneg.mp (hlength z hz).1
  calc
    (∫ t in left z..right z, (F z.1 t) ^ 4) ≤
        ∫ _t in left z..right z, (F z.1 z.2) ^ 4 := by
      apply intervalIntegral.integral_mono_on hlr
      · exact ((hF z.1).pow 4).intervalIntegrable _ _
      · exact intervalIntegrable_const
      · intro t ht
        exact hmax z hz t ht
    _ = (right z - left z) * (F z.1 z.2) ^ 4 := by simp
    _ ≤ (F z.1 z.2) ^ 4 := by
      have hpow : 0 ≤ (F z.1 z.2) ^ 4 := by positivity
      nlinarith [(hlength z hz).2]

/-- The separate principal-character residue term in BHP Lemma 9. -/
def bhpPrincipalDecayMass {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q × ℝ)) : ℝ := by
  classical
  exact ∑ z ∈ S, if z.1 = 1 then 1 / (1 + |z.2|) ^ 4 else 0

theorem bhpPrincipalDecayMass_nonneg {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q × ℝ)) :
    0 ≤ bhpPrincipalDecayMass S := by
  classical
  unfold bhpPrincipalDecayMass
  apply Finset.sum_nonneg
  intro z hz
  split_ifs
  · positivity
  · exact le_rfl

/-- On the MRT annulus `T/2 <= |t| <= T`, every summand in BHP's
principal-character residue term is at most `16/T^4`. -/
theorem bhpPrincipalDecayMass_le_card_mul_sixteen_div
    {q : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T : ℝ} (hT : 0 < T)
    (hannulus : ∀ z ∈ S, T / 2 ≤ |z.2|) :
    bhpPrincipalDecayMass S ≤ (S.card : ℝ) * (16 / T ^ 4) := by
  classical
  unfold bhpPrincipalDecayMass
  calc
    (∑ z ∈ S, if z.1 = 1 then 1 / (1 + |z.2|) ^ 4 else 0) ≤
        ∑ _z ∈ S, 16 / T ^ 4 := by
      apply Finset.sum_le_sum
      intro z hz
      split_ifs
      · have hscale : T ≤ 2 * (1 + |z.2|) := by
          nlinarith [hannulus z hz, abs_nonneg z.2]
        have hp := pow_le_pow_left₀ hT.le hscale 4
        rw [div_le_div_iff₀ (pow_pos (by positivity) 4) (pow_pos hT 4)]
        norm_num
        nlinarith
      · positivity
    _ = (S.card : ℝ) * (16 / T ^ 4) := by simp

/-- Deterministic substitution into the literal BHP Lemma 9 right-hand side.

`hBHP` is a direct inequality rather than a named `Prop` wrapper.  Supplying
it with BHP's standing `chi ∉ E_q` convention, or proving separately that the
published proof is uniform in that character, is the remaining analytic leaf.
-/
theorem bhpLemma9_rhs_annulus_reduction
    {q : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {raw T N L C A : ℝ} {B : ℕ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hannulus : ∀ z ∈ S, T / 2 ≤ |z.2|)
    (hcard : (S.card : ℝ) ≤ A * (q : ℝ) * T)
    (hBHP : raw ≤ C *
      ((q : ℝ) * T * L ^ B +
        L ^ 4 * (S.card : ℝ) *
          ((q : ℝ) ^ 2 / T ^ 2 + N ^ 2 / T ^ 4) +
        N ^ 2 * bhpPrincipalDecayMass S)) :
    raw ≤ C *
      ((q : ℝ) * T * L ^ B +
        L ^ 4 * (A * (q : ℝ) * T) *
          ((q : ℝ) ^ 2 / T ^ 2 + N ^ 2 / T ^ 4) +
        N ^ 2 * ((A * (q : ℝ) * T) * (16 / T ^ 4))) := by
  have hshape0 : 0 ≤ (q : ℝ) ^ 2 / T ^ 2 + N ^ 2 / T ^ 4 := by positivity
  have htail := bhpPrincipalDecayMass_le_card_mul_sixteen_div hT hannulus
  have hsixteen0 : 0 ≤ 16 / T ^ 4 := by positivity
  have htail' : bhpPrincipalDecayMass S ≤
      (A * (q : ℝ) * T) * (16 / T ^ 4) := by
    exact htail.trans (mul_le_mul_of_nonneg_right hcard hsixteen0)
  refine hBHP.trans (mul_le_mul_of_nonneg_left ?_ hC)
  gcongr

/-- Source-faithful restricted Corollary 2.12 assembly for one collection of
clipped bins.  The analytic premise is callable only after both printed BHP
conditions have been supplied: same-character one-spacing and membership in
the admissible complement of `E_q`.  This prevents the deterministic adapter
from silently promoting BHP Lemma 9 to an unrestricted all-character theorem.
-/
theorem bhpRestrictedSampledPieces_to_annulus_rhs
    {q : ℕ} [NeZero q]
    {F : DirichletCharacter ℂ q → ℝ → ℝ}
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {left right : DirichletCharacter ℂ q × ℝ → ℝ}
    {Admissible : DirichletCharacter ℂ q → Prop}
    {T N L C A : ℝ} {B : ℕ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hF : ∀ chi, Continuous (F chi))
    (hlength : ∀ z ∈ S, 0 ≤ right z - left z ∧ right z - left z ≤ 1)
    (hmax : ∀ z ∈ S, ∀ t ∈ Set.Icc (left z) (right z),
      (F z.1 t) ^ 4 ≤ (F z.1 z.2) ^ 4)
    (hannulus : ∀ z ∈ S, T / 2 ≤ |z.2|)
    (hcard : (S.card : ℝ) ≤ A * (q : ℝ) * T)
    (hadmissible : ∀ z ∈ S, Admissible z.1)
    (hspacing : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → z.1 = w.1 →
      1 ≤ |z.2 - w.2|)
    (hBHP :
      (∀ z ∈ S, Admissible z.1) →
      (∀ z ∈ S, ∀ w ∈ S, z ≠ w → z.1 = w.1 →
        1 ≤ |z.2 - w.2|) →
      bhpSelectedFourthMass F S ≤ C *
        ((q : ℝ) * T * L ^ B +
          L ^ 4 * (S.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + N ^ 2 / T ^ 4) +
          N ^ 2 * bhpPrincipalDecayMass S)) :
    bhpSampledPieceMass F S left right ≤ C *
      ((q : ℝ) * T * L ^ B +
        L ^ 4 * (A * (q : ℝ) * T) *
          ((q : ℝ) ^ 2 / T ^ 2 + N ^ 2 / T ^ 4) +
        N ^ 2 * ((A * (q : ℝ) * T) * (16 / T ^ 4))) := by
  have hdisc := bhpSampledPieceMass_le_selectedFourthMass
    hF hlength hmax
  have hanalytic := hBHP hadmissible hspacing
  have hreduced := bhpLemma9_rhs_annulus_reduction
    hT hC hannulus hcard hanalytic
  exact hdisc.trans hreduced

/-- The Corollary 2.12 bracket is harmless in MRT Proposition 6.1's range:
`q <= T`, `N <= T`, and `1 <= T` imply the literal bound by `3`. -/
theorem corollary212_bracket_le_three
    {q N T : ℝ} (hq : 0 ≤ q) (hN : 0 ≤ N)
    (hT : 1 ≤ T) (hqT : q ≤ T) (hNT : N ≤ T) :
    1 + q ^ 2 / T ^ 2 + N ^ 2 / T ^ 4 ≤ 3 := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hq2 : q ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hq hqT 2
  have hN2 : N ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hN hNT 2
  have hqratio : q ^ 2 / T ^ 2 ≤ 1 := by
    rw [div_le_one (pow_pos hT0 2)]
    exact hq2
  have hNratio : N ^ 2 / T ^ 4 ≤ 1 := by
    rw [div_le_one (pow_pos hT0 4)]
    calc
      N ^ 2 ≤ T ^ 2 := hN2
      _ ≤ T ^ 4 := by nlinarith [sq_nonneg (T ^ 2 - 1)]
  linarith

/-- The literal factored moving-window mass occurring after
`D[alpha * beta1 * beta2] = D[alpha] D[beta1] D[beta2]`.  The fields are
nonnegative norms in applications. -/
def factoredTypeD12Mass {Chi : Type*} [Fintype Chi]
    (alpha beta1 beta2 : Chi → ℝ → ℝ) (U t : ℝ) : ℝ :=
  ∑ chi : Chi, ∫ s in (t - U)..(t + U),
    alpha chi s * (beta1 chi s * beta2 chi s)

/-- The local character mean square for the short `alpha` factor. -/
def alphaLocalSquareMass {Chi : Type*} [Fintype Chi]
    (alpha : Chi → ℝ → ℝ) (U t : ℝ) : ℝ :=
  ∑ chi : Chi, ∫ s in (t - U)..(t + U), (alpha chi s) ^ 2

/-- The local mixed fourth-degree mass of the two long factors. -/
def betaLocalProductSquareMass {Chi : Type*} [Fintype Chi]
    (beta1 beta2 : Chi → ℝ → ℝ) (U t : ℝ) : ℝ :=
  ∑ chi : Chi, ∫ s in (t - U)..(t + U),
    (beta1 chi s) ^ 2 * (beta2 chi s) ^ 2

/-- Cauchy--Schwarz simultaneously over the character family and the moving
interval.  This is the first displayed inequality in the Type-d1/d2 proof. -/
theorem factoredTypeD12Mass_sq_le
    {Chi : Type*} [Fintype Chi]
    {alpha beta1 beta2 : Chi → ℝ → ℝ}
    (halpha : ∀ chi, Continuous (alpha chi))
    (hbeta1 : ∀ chi, Continuous (beta1 chi))
    (hbeta2 : ∀ chi, Continuous (beta2 chi))
    (halpha0 : ∀ chi t, 0 ≤ alpha chi t)
    (hbeta10 : ∀ chi t, 0 ≤ beta1 chi t)
    (hbeta20 : ∀ chi t, 0 ≤ beta2 chi t)
    {U t : ℝ} (hU : 0 ≤ U) :
    (factoredTypeD12Mass alpha beta1 beta2 U t) ^ 2 ≤
      alphaLocalSquareMass alpha U t *
        betaLocalProductSquareMass beta1 beta2 U t := by
  let I : Chi → ℝ := fun chi ↦
    ∫ s in (t - U)..(t + U),
      alpha chi s * (beta1 chi s * beta2 chi s)
  let A : Chi → ℝ := fun chi ↦
    ∫ s in (t - U)..(t + U), (alpha chi s) ^ 2
  let B : Chi → ℝ := fun chi ↦
    ∫ s in (t - U)..(t + U),
      (beta1 chi s) ^ 2 * (beta2 chi s) ^ 2
  have hA0 (chi : Chi) : 0 ≤ A chi := by
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun s hs ↦ sq_nonneg _)
  have hB0 (chi : Chi) : 0 ≤ B chi := by
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun s hs ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hI0 (chi : Chi) : 0 ≤ I chi := by
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun s hs ↦ mul_nonneg (halpha0 chi s)
        (mul_nonneg (hbeta10 chi s) (hbeta20 chi s)))
  have hterm (chi : Chi) :
      I chi ≤ Real.sqrt (A chi) * Real.sqrt (B chi) := by
    have hsq := intervalIntegral_mul_sq_le
      (halpha chi) ((hbeta1 chi).mul (hbeta2 chi))
      (halpha0 chi) (fun s ↦ mul_nonneg (hbeta10 chi s) (hbeta20 chi s))
      (by linarith : t - U ≤ t + U)
    have hsq' : (I chi) ^ 2 ≤ A chi * B chi := by
      simpa only [I, A, B, Pi.mul_apply, mul_pow] using hsq
    have hsqrt := Real.le_sqrt_of_sq_le hsq'
    change I chi ≤ Real.sqrt (A chi * B chi) at hsqrt
    rw [Real.sqrt_mul (hA0 chi)] at hsqrt
    exact hsqrt
  have hsum1 : (∑ chi, I chi) ≤
      ∑ chi, Real.sqrt (A chi) * Real.sqrt (B chi) :=
    Finset.sum_le_sum fun chi hchi ↦ hterm chi
  have hsum2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun chi ↦ Real.sqrt (A chi)) (fun chi ↦ Real.sqrt (B chi))
  have hAsq : (∑ chi, Real.sqrt (A chi) ^ 2) = ∑ chi, A chi := by
    apply Finset.sum_congr rfl
    intro chi hchi
    exact Real.sq_sqrt (hA0 chi)
  have hBsq : (∑ chi, Real.sqrt (B chi) ^ 2) = ∑ chi, B chi := by
    apply Finset.sum_congr rfl
    intro chi hchi
    exact Real.sq_sqrt (hB0 chi)
  rw [hAsq, hBsq] at hsum2
  have hsum : (∑ chi, I chi) ≤
      Real.sqrt (∑ chi, A chi) * Real.sqrt (∑ chi, B chi) :=
    hsum1.trans hsum2
  have hsumI0 : 0 ≤ ∑ chi, I chi :=
    Finset.sum_nonneg fun chi hchi ↦ hI0 chi
  have hsumA0 : 0 ≤ ∑ chi, A chi :=
    Finset.sum_nonneg fun chi hchi ↦ hA0 chi
  have hsumB0 : 0 ≤ ∑ chi, B chi :=
    Finset.sum_nonneg fun chi hchi ↦ hB0 chi
  change (∑ chi, I chi) ^ 2 ≤ (∑ chi, A chi) * ∑ chi, B chi
  nlinarith [Real.sq_sqrt hsumA0, Real.sq_sqrt hsumB0]

/-- Integrating the first Cauchy inequality and inserting the pointwise
character mean-square estimate for `alpha`. -/
theorem outer_factoredTypeD12Mass_sq_le_of_alphaMean
    {Chi : Type*} [Fintype Chi]
    {alpha beta1 beta2 : Chi → ℝ → ℝ}
    (halpha : ∀ chi, Continuous (alpha chi))
    (hbeta1 : ∀ chi, Continuous (beta1 chi))
    (hbeta2 : ∀ chi, Continuous (beta2 chi))
    (halpha0 : ∀ chi t, 0 ≤ alpha chi t)
    (hbeta10 : ∀ chi t, 0 ≤ beta1 chi t)
    (hbeta20 : ∀ chi t, 0 ≤ beta2 chi t)
    {a b U P : ℝ} (hab : a ≤ b) (hU : 0 ≤ U)
    (halphaMean : ∀ t ∈ Set.uIcc a b,
      alphaLocalSquareMass alpha U t ≤ P) :
    (∫ t in a..b, (factoredTypeD12Mass alpha beta1 beta2 U t) ^ 2) ≤
      P * ∫ t in a..b, betaLocalProductSquareMass beta1 beta2 U t := by
  have hfactCont : Continuous (factoredTypeD12Mass alpha beta1 beta2 U) := by
    unfold factoredTypeD12Mass
    apply continuous_finset_sum
    intro chi hchi
    exact continuous_movingWindowIntegral
      ((halpha chi).mul ((hbeta1 chi).mul (hbeta2 chi))) U
  have hbetaCont : Continuous
      (betaLocalProductSquareMass beta1 beta2 U) := by
    unfold betaLocalProductSquareMass
    apply continuous_finset_sum
    intro chi hchi
    exact continuous_movingWindowIntegral
      (((hbeta1 chi).pow 2).mul ((hbeta2 chi).pow 2)) U
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab
  · exact (hfactCont.pow 2).intervalIntegrable _ _
  · exact (continuous_const.mul hbetaCont).intervalIntegrable _ _
  · intro t ht
    have hfirst := factoredTypeD12Mass_sq_le halpha hbeta1 hbeta2
      halpha0 hbeta10 hbeta20 hU (t := t)
    have hbeta0 : 0 ≤ betaLocalProductSquareMass beta1 beta2 U t := by
      unfold betaLocalProductSquareMass
      exact Finset.sum_nonneg fun chi hchi ↦
        intervalIntegral.integral_nonneg (by linarith)
          (fun s hs ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
    exact hfirst.trans <| mul_le_mul_of_nonneg_right
      (halphaMean t (Set.Icc_subset_uIcc ht)) hbeta0

/-- Compact Fubini and interval enlargement: the moving mixed fourth-degree
mass has overlap multiplicity at most `2U`. -/
theorem integral_betaLocalProductSquareMass_le
    {Chi : Type*} [Fintype Chi]
    {beta1 beta2 : Chi → ℝ → ℝ}
    (hbeta1 : ∀ chi, Continuous (beta1 chi))
    (hbeta2 : ∀ chi, Continuous (beta2 chi))
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    (∫ t in a..b, betaLocalProductSquareMass beta1 beta2 U t) ≤
      2 * U * ∫ s in (a - U)..(b + U),
        ∑ chi : Chi, (beta1 chi s) ^ 2 * (beta2 chi s) ^ 2 := by
  unfold betaLocalProductSquareMass
  rw [intervalIntegral.integral_finset_sum]
  calc
    (∑ chi : Chi,
        ∫ t in a..b, ∫ s in (t - U)..(t + U),
          beta1 chi s ^ 2 * beta2 chi s ^ 2) ≤
        ∑ chi : Chi, 2 * U * ∫ s in (a - U)..(b + U),
          beta1 chi s ^ 2 * beta2 chi s ^ 2 := by
      apply Finset.sum_le_sum
      intro chi hchi
      exact movingWindowSweep_le_two_mul
        ((hbeta1 chi).pow 2 |>.mul ((hbeta2 chi).pow 2))
        (fun s ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hab hU
    _ = 2 * U * ∫ s in (a - U)..(b + U),
        ∑ chi : Chi, beta1 chi s ^ 2 * beta2 chi s ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      symm
      apply intervalIntegral.integral_finset_sum
      intro chi hchi
      exact (((hbeta1 chi).pow 2).mul ((hbeta2 chi).pow 2)).intervalIntegrable _ _
  · intro chi hchi
    exact (continuous_movingWindowIntegral
      (((hbeta1 chi).pow 2).mul ((hbeta2 chi).pow 2)) U).intervalIntegrable _ _

/-- The beta-product integral is bounded by the geometric mean of the two
fourth moments, exactly as on MRT p. 61. -/
theorem betaProductSquareIntegral_le_fourthMoments
    {Chi : Type*} [Fintype Chi]
    {beta1 beta2 : Chi → ℝ → ℝ}
    (hbeta1 : ∀ chi, Continuous (beta1 chi))
    (hbeta2 : ∀ chi, Continuous (beta2 chi))
    {a b Q1 Q2 : ℝ} (hab : a ≤ b) (hQ1 : 0 ≤ Q1)
    (hfourth1 : (∫ s in a..b, ∑ chi : Chi, (beta1 chi s) ^ 4) ≤ Q1)
    (hfourth2 : (∫ s in a..b, ∑ chi : Chi, (beta2 chi s) ^ 4) ≤ Q2) :
    (∫ s in a..b,
      ∑ chi : Chi, (beta1 chi s) ^ 2 * (beta2 chi s) ^ 2) ≤
        Real.sqrt Q1 * Real.sqrt Q2 := by
  let F : ℝ → ℝ := fun s ↦ Real.sqrt (∑ chi : Chi, (beta1 chi s) ^ 4)
  let G : ℝ → ℝ := fun s ↦ Real.sqrt (∑ chi : Chi, (beta2 chi s) ^ 4)
  have hsum10 (s : ℝ) : 0 ≤ ∑ chi : Chi, (beta1 chi s) ^ 4 :=
    Finset.sum_nonneg fun chi hchi ↦ by positivity
  have hsum20 (s : ℝ) : 0 ≤ ∑ chi : Chi, (beta2 chi s) ^ 4 :=
    Finset.sum_nonneg fun chi hchi ↦ by positivity
  have hF : Continuous F := by
    exact Real.continuous_sqrt.comp (continuous_finset_sum Finset.univ
      fun chi hchi ↦ (hbeta1 chi).pow 4)
  have hG : Continuous G := by
    exact Real.continuous_sqrt.comp (continuous_finset_sum Finset.univ
      fun chi hchi ↦ (hbeta2 chi).pow 4)
  have hpoint (s : ℝ) :
      (∑ chi : Chi, beta1 chi s ^ 2 * beta2 chi s ^ 2) ≤ F s * G s := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun chi ↦ beta1 chi s ^ 2) (fun chi ↦ beta2 chi s ^ 2)
    have hpow1 : (∑ chi : Chi, (beta1 chi s ^ 2) ^ 2) =
        ∑ chi : Chi, beta1 chi s ^ 4 := by
      apply Finset.sum_congr rfl
      intro chi hchi
      ring
    have hpow2 : (∑ chi : Chi, (beta2 chi s ^ 2) ^ 2) =
        ∑ chi : Chi, beta2 chi s ^ 4 := by
      apply Finset.sum_congr rfl
      intro chi hchi
      ring
    rw [hpow1, hpow2] at hcs
    exact hcs
  have hint :
      (∫ s in a..b,
        ∑ chi : Chi, beta1 chi s ^ 2 * beta2 chi s ^ 2) ≤
          ∫ s in a..b, F s * G s := by
    apply intervalIntegral.integral_mono_on hab
    · exact (continuous_finset_sum Finset.univ fun chi hchi ↦
        ((hbeta1 chi).pow 2).mul ((hbeta2 chi).pow 2)).intervalIntegrable _ _
    · exact (hF.mul hG).intervalIntegrable _ _
    · intro s hs
      exact hpoint s
  have hcsInt := intervalIntegral_mul_sq_le hF hG
    (fun s ↦ Real.sqrt_nonneg _) (fun s ↦ Real.sqrt_nonneg _) hab
  have hF2 : (∫ s in a..b, (F s) ^ 2) =
      ∫ s in a..b, ∑ chi : Chi, (beta1 chi s) ^ 4 := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact Real.sq_sqrt (hsum10 s)
  have hG2 : (∫ s in a..b, (G s) ^ 2) =
      ∫ s in a..b, ∑ chi : Chi, (beta2 chi s) ^ 4 := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact Real.sq_sqrt (hsum20 s)
  rw [hF2, hG2] at hcsInt
  have hprod :
      (∫ s in a..b, F s * G s) ^ 2 ≤ Q1 * Q2 :=
    hcsInt.trans <| mul_le_mul hfourth1 hfourth2
      (intervalIntegral.integral_nonneg hab fun s hs ↦ by positivity) hQ1
  have hint0 : 0 ≤ ∫ s in a..b, F s * G s :=
    intervalIntegral.integral_nonneg hab fun s hs ↦
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsqrt := Real.le_sqrt_of_sq_le hprod
  rw [Real.sqrt_mul hQ1] at hsqrt
  exact hint.trans hsqrt

/-- Complete deterministic p. 60--61 reduction.  The remaining hypotheses are
exactly the two analytic estimates cited by the source: Lemma 2.10 for the
short factor and Corollary 2.12 for the long factors. -/
theorem typeD12_outerMass_le_of_meanValue_and_fourthMoments
    {Chi : Type*} [Fintype Chi]
    {alpha beta1 beta2 : Chi → ℝ → ℝ}
    (halpha : ∀ chi, Continuous (alpha chi))
    (hbeta1 : ∀ chi, Continuous (beta1 chi))
    (hbeta2 : ∀ chi, Continuous (beta2 chi))
    (halpha0 : ∀ chi t, 0 ≤ alpha chi t)
    (hbeta10 : ∀ chi t, 0 ≤ beta1 chi t)
    (hbeta20 : ∀ chi t, 0 ≤ beta2 chi t)
    {a b U P Q1 Q2 : ℝ} (hab : a ≤ b) (hU : 0 ≤ U)
    (hP : 0 ≤ P) (hQ1 : 0 ≤ Q1)
    (halphaMean : ∀ t ∈ Set.uIcc a b,
      alphaLocalSquareMass alpha U t ≤ P)
    (hfourth1 :
      (∫ s in (a - U)..(b + U),
        ∑ chi : Chi, (beta1 chi s) ^ 4) ≤ Q1)
    (hfourth2 :
      (∫ s in (a - U)..(b + U),
        ∑ chi : Chi, (beta2 chi s) ^ 4) ≤ Q2) :
    (∫ t in a..b, (factoredTypeD12Mass alpha beta1 beta2 U t) ^ 2) ≤
      2 * U * P * (Real.sqrt Q1 * Real.sqrt Q2) := by
  have hfirst := outer_factoredTypeD12Mass_sq_le_of_alphaMean
    halpha hbeta1 hbeta2 halpha0 hbeta10 hbeta20 hab hU halphaMean
  have hsweep := integral_betaLocalProductSquareMass_le
    hbeta1 hbeta2 hab hU
  have hfourth := betaProductSquareIntegral_le_fourthMoments
    hbeta1 hbeta2 (by linarith : a - U ≤ b + U) hQ1 hfourth1 hfourth2
  have hbeta0 : 0 ≤ ∫ t in a..b,
      betaLocalProductSquareMass beta1 beta2 U t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    unfold betaLocalProductSquareMass
    exact Finset.sum_nonneg fun chi hchi ↦
      intervalIntegral.integral_nonneg (by linarith)
        (fun s hs ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
  calc
    (∫ t in a..b, (factoredTypeD12Mass alpha beta1 beta2 U t) ^ 2) ≤
        P * ∫ t in a..b, betaLocalProductSquareMass beta1 beta2 U t := hfirst
    _ ≤ P * (2 * U * ∫ s in (a - U)..(b + U),
        ∑ chi : Chi, beta1 chi s ^ 2 * beta2 chi s ^ 2) :=
      mul_le_mul_of_nonneg_left hsweep hP
    _ ≤ P * (2 * U * (Real.sqrt Q1 * Real.sqrt Q2)) := by
      gcongr
    _ = 2 * U * P * (Real.sqrt Q1 * Real.sqrt Q2) := by ring

/-- Source-shaped specialization of the preceding theorem.  `Lalpha` and
`Lbeta` retain the harmless logarithmic losses rather than hiding them in
Vinogradov notation.  The two hypotheses are exactly the bounds obtained from
MRT Lemma 2.10 and Corollary 2.12, respectively. -/
theorem typeD12_outerMass_le_sourceMomentShape
    {Chi : Type*} [Fintype Chi]
    {alpha beta1 beta2 : Chi → ℝ → ℝ}
    (halpha : ∀ chi, Continuous (alpha chi))
    (hbeta1 : ∀ chi, Continuous (beta1 chi))
    (hbeta2 : ∀ chi, Continuous (beta2 chi))
    (halpha0 : ∀ chi t, 0 ≤ alpha chi t)
    (hbeta10 : ∀ chi t, 0 ≤ beta1 chi t)
    (hbeta20 : ∀ chi t, 0 ≤ beta2 chi t)
    {a b U q N T Calpha Cbeta Lalpha Lbeta : ℝ}
    (hab : a ≤ b) (hU : 0 ≤ U) (hq : 0 ≤ q) (hN : 0 ≤ N)
    (hT : 0 ≤ T) (hCalpha : 0 ≤ Calpha) (hCbeta : 0 ≤ Cbeta)
    (hLalpha : 0 ≤ Lalpha) (hLbeta : 0 ≤ Lbeta)
    (halphaMean : ∀ t ∈ Set.uIcc a b,
      alphaLocalSquareMass alpha U t ≤
        Calpha * (q * U + N) * Lalpha)
    (hfourth1 :
      (∫ s in (a - U)..(b + U),
        ∑ chi : Chi, (beta1 chi s) ^ 4) ≤ Cbeta * q * T * Lbeta)
    (hfourth2 :
      (∫ s in (a - U)..(b + U),
        ∑ chi : Chi, (beta2 chi s) ^ 4) ≤ Cbeta * q * T * Lbeta) :
    (∫ t in a..b, (factoredTypeD12Mass alpha beta1 beta2 U t) ^ 2) ≤
      2 * U * (Calpha * (q * U + N) * Lalpha) *
        (Cbeta * q * T * Lbeta) := by
  have hP : 0 ≤ Calpha * (q * U + N) * Lalpha := by positivity
  have hQ : 0 ≤ Cbeta * q * T * Lbeta := by positivity
  have hraw := typeD12_outerMass_le_of_meanValue_and_fourthMoments
    halpha hbeta1 hbeta2 halpha0 hbeta10 hbeta20 hab hU
    hP hQ halphaMean hfourth1 hfourth2
  have hsqrt : Real.sqrt (Cbeta * q * T * Lbeta) *
      Real.sqrt (Cbeta * q * T * Lbeta) = Cbeta * q * T * Lbeta := by
    simpa only [pow_two] using Real.sq_sqrt hQ
  rw [hsqrt] at hraw
  exact hraw

/-- The exact scale algebra after the dyadic fourth-moment bound and the upper
choice in (101).  This isolates the only remaining absorption task: make
`q*sqrt(Q)*lambda` and `N*sqrt(Q)/H` logarithmically small using (88)--(100). -/
theorem typeD12_sourceCore_le_scaleEnvelope
    {raw C q U N T lambda H Q X : ℝ}
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hU : 0 ≤ U) (hN : 0 ≤ N)
    (hUeq : U = lambda * H)
    (hT : T ≤ Real.sqrt Q * lambda * X)
    (hraw : raw ≤ C * (q * U + N) * U * q * T) :
    raw ≤ C * q * (q * Real.sqrt Q * lambda * H + N * Real.sqrt Q) *
      lambda ^ 2 * H * X := by
  have hfac : 0 ≤ C * (q * U + N) * U * q := by positivity
  calc
    raw ≤ C * (q * U + N) * U * q * T := hraw
    _ ≤ C * (q * U + N) * U * q *
        (Real.sqrt Q * lambda * X) :=
      mul_le_mul_of_nonneg_left hT hfac
    _ = C * q * (q * Real.sqrt Q * lambda * H + N * Real.sqrt Q) *
        lambda ^ 2 * H * X := by
      rw [hUeq]
      ring

end
end MAPMRTProposition61TypeD1FirstInequality

#print axioms MAPMRTProposition61TypeD1FirstInequality.factoredTypeD12Mass_sq_le
#print axioms MAPMRTProposition61TypeD1FirstInequality.bhpPrincipalDecayMass_nonneg
#print axioms MAPMRTProposition61TypeD1FirstInequality.bhpSampledPieceMass_le_selectedFourthMass
#print axioms MAPMRTProposition61TypeD1FirstInequality.bhpPrincipalDecayMass_le_card_mul_sixteen_div
#print axioms MAPMRTProposition61TypeD1FirstInequality.bhpLemma9_rhs_annulus_reduction
#print axioms MAPMRTProposition61TypeD1FirstInequality.bhpRestrictedSampledPieces_to_annulus_rhs
#print axioms MAPMRTProposition61TypeD1FirstInequality.corollary212_bracket_le_three
#print axioms MAPMRTProposition61TypeD1FirstInequality.integral_betaLocalProductSquareMass_le
#print axioms MAPMRTProposition61TypeD1FirstInequality.betaProductSquareIntegral_le_fourthMoments
#print axioms MAPMRTProposition61TypeD1FirstInequality.typeD12_outerMass_le_of_meanValue_and_fourthMoments
#print axioms MAPMRTProposition61TypeD1FirstInequality.typeD12_outerMass_le_sourceMomentShape
#print axioms MAPMRTProposition61TypeD1FirstInequality.typeD12_sourceCore_le_scaleEnvelope
