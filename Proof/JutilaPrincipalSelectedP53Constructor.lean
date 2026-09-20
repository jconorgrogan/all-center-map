import JutilaPrincipalFiniteHalasz
import JutilaPrincipalLowHeightCharge
import JutilaGappedCollarSelectedP53Adapter
import JutilaLemma6DirectTail
import JutilaPseudocharacterHarmonicLower
import JutilaLemma6GenericTailAbsorption

/-!
# Principal selected-P53 constructor

The constructor is epsilon agnostic.  Its only contour obligation is the
literal eventual smallness of the principal direct series on the high set.
Low-height zeros are charged by one-separated packing.
-/

namespace MAPJutilaPrincipalSelectedP53Constructor

open scoped BigOperators
open Complex Real Filter DirichletZeros
open CGLProofDAG
open MAPJutilaPrincipalFiniteHalasz
open MAPJutilaPrincipalLowHeightCharge
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPJutilaGappedCollarFiniteAggregation
open MAPJutilaCollarSourceParameters
open MAPJutilaLemma6DirectTail
open MAPJutilaPseudocharacterHarmonicLower
open MAPJutilaLemma6GenericTailAbsorption
open MAPJutilaCollarMeshCutoff
open MAPJutilaCollarA5Budget

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

theorem jutilaGappedSelectedPrincipalP53Eventually
    (hseriesInput :
      ∀ᶠ D : ℝ in atTop, ∀ (T omega : ℝ) (rho : ℂ),
        1 ≤ T → T = D → 0 ≤ omega →
        (279 / 280 : ℝ) ≤ rho.re → rho.re ≤ 1 - omega →
        |rho.im| ≤ T → 12 * Real.log D ≤ |rho.im| →
        MAPPrincipalZetaFixedStrip.principalRegularized rho = 0 →
        ‖∑' n : ℕ, jutilaLemmaSixDirectTerm (1 : DirichletCharacter ℂ 1)
          (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
          (jutilaPrimedRSet 1 (sourceR (1 / 280) D)) rho
          (lemmaSixSmoothScale (1 / 280) D) n‖ < 1) :
    JutilaGappedSelectedPrincipalP53Eventually := by
  obtain ⟨C, hC, hhigh⟩ := exists_eventually_principal_high_card_le_of_directSeries hseriesInput
  obtain ⟨D0, hD0⟩ := Filter.eventually_atTop.mp hhigh
  refine ⟨C + 25, max 6 (max D0 (Real.exp 1)), 10, by positivity,
    le_max_left _ _, by norm_num, ?_⟩
  intro q _inst chi T sigma omega W hprim hchi hT hsigmaLow hsigmaHigh
    homega hgap hscale hregularGap hWsub hWsep hWcard
  have hq : q = 1 := by
    have hcond : chi.conductor = q := hprim
    rw [hchi, DirichletCharacter.conductor_one] at hcond
    exact hcond.symm
  subst q
  have hchiOne : chi = chiOne := hchi
  subst chi
  simp only [Nat.cast_one, one_mul] at hscale ⊢
  let D : ℝ := T
  have hDT : T = D := rfl
  have hRle : max 6 (max D0 (Real.exp 1)) ≤ D := hscale
  have hD0le : D0 ≤ D :=
    (le_max_left D0 (Real.exp 1)).trans ((le_max_right (6 : ℝ) _).trans hRle)
  have hDe' : Real.exp 1 ≤ D :=
    (le_max_right D0 (Real.exp 1)).trans ((le_max_right (6 : ℝ) _).trans hRle)
  let Wlow := W.filter (fun rho : ℂ => |rho.im| < 12 * Real.log D)
  let Whigh := W.filter (fun rho : ℂ => 12 * Real.log D ≤ |rho.im|)
  have hdj : Disjoint Wlow Whigh := by
    refine Finset.disjoint_left.mpr ?_
    intro rho hlow hhigh
    have hlt := (Finset.mem_filter.mp hlow).2
    have hge := (Finset.mem_filter.mp hhigh).2
    exact (lt_irrefl _ (hlt.trans_le hge))
  have hunion : Wlow ∪ Whigh = W := by
    ext rho
    simp only [Wlow, Whigh, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases ht : |rho.im| < 12 * Real.log D
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr ⟨h, le_of_not_gt ht⟩
  have hcardAdd : (W.card : ℝ) = (Wlow.card : ℝ) + (Whigh.card : ℝ) := by
    have := Finset.card_union_of_disjoint hdj
    rw [hunion] at this
    exact_mod_cast this
  have hlow : (Wlow.card : ℝ) ≤ 24 * Real.log D + 1 := by
    have hsub : Wlow ⊆ W := Finset.filter_subset _ _
    have hsep' := oneSeparated_subset hWsep (image_im_subset hsub)
    have hcard' := card_image_im_eq_of_parent hWcard hsub
    have hWlow : ∀ rho ∈ Wlow, |rho.im| ≤ 12 * Real.log D := by
      intro rho hr
      exact le_of_lt (Finset.mem_filter.mp hr).2
    exact lowHeight_source_card_le hDe' hsep' hcard' hWlow
  have hhigh : (Whigh.card : ℝ) ≤
      C * Real.rpow (Real.log D) 10 *
        Real.rpow D ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
          (1 - sigma)) := by
    have hsub : Whigh ⊆ W := Finset.filter_subset _ _
    have hsep' := oneSeparated_subset hWsep (image_im_subset hsub)
    have hcard' := card_image_im_eq_of_parent hWcard hsub
    have hW' : ∀ rho ∈ Whigh,
        rho ∈ regularCollarSupport chiOne sigma T ∧
          rho.re ≤ 1 - omega ∧ 12 * Real.log D ≤ |rho.im| := by
      intro rho hr
      have hmem := (Finset.mem_filter.mp hr).1
      exact ⟨hWsub hmem, hregularGap rho (hWsub hmem),
        (Finset.mem_filter.mp hr).2⟩
    exact hD0 D hD0le T sigma omega Whigh hT hDT hsigmaLow hsigmaHigh
      homega hgap hW' hsep' hcard'
  have hcoeff :
      0 ≤ 2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget := by
    norm_num [collarDelta, detectorLogBudget]
  have hpow0 : 0 ≤ Real.rpow D
      ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) * (1 - sigma)) :=
    Real.rpow_nonneg (zero_le_one.trans hT) _
  have h1log : 1 ≤ Real.log D := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hDe'
  have hlog10 : 1 ≤ Real.rpow (Real.log D) 10 :=
    Real.one_le_rpow h1log (by norm_num)
  have hDpow1 : 1 ≤ Real.rpow D
      ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) * (1 - sigma)) :=
    Real.one_le_rpow (hT : 1 ≤ D)
      (mul_nonneg hcoeff (sub_nonneg.mpr hsigmaHigh))
  have hlow' : (Wlow.card : ℝ) ≤
      25 * Real.rpow (Real.log D) 10 *
        Real.rpow D ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
          (1 - sigma)) := by
    have hlin : 24 * Real.log D + 1 ≤ 25 * Real.rpow (Real.log D) 10 := by
      have hlogLe : Real.log D ≤ Real.rpow (Real.log D) 10 := by
        calc
          Real.log D = Real.rpow (Real.log D) 1 := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h1log (by norm_num)
      nlinarith [Real.rpow_nonneg (zero_le_one.trans h1log) (10 : ℝ)]
    have hmul : 25 * Real.rpow (Real.log D) 10 ≤
        25 * Real.rpow (Real.log D) 10 *
          Real.rpow D
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - sigma)) := by
      nlinarith [hlog10, hDpow1, hpow0,
        Real.rpow_nonneg (zero_le_one.trans h1log) (10 : ℝ)]
    exact (hlow.trans hlin).trans hmul
  calc
    (W.card : ℝ) = (Wlow.card : ℝ) + (Whigh.card : ℝ) := hcardAdd
    _ ≤ 25 * Real.rpow (Real.log D) 10 *
          Real.rpow D ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
            (1 - sigma)) +
        C * Real.rpow (Real.log D) 10 *
          Real.rpow D ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
            (1 - sigma)) := add_le_add hlow' hhigh
    _ = (C + 25) * Real.rpow (Real.log D) 10 *
          Real.rpow D ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
            (1 - sigma)) := by ring
    _ = (C + 25) * Real.rpow (Real.log T) 10 *
          Real.rpow T ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
            (1 - sigma)) := by rfl



end

end MAPJutilaPrincipalSelectedP53Constructor

#print axioms MAPJutilaPrincipalSelectedP53Constructor.jutilaGappedSelectedPrincipalP53Eventually
