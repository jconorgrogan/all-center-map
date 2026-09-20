import JutilaP53CanonicalHalaszSource
import JutilaCanonicalQuadraticAbsorption
import JutilaSourceFVBudget
import JutilaSourceQEBudget
import JutilaGappedFixedModulusAggregateP53Adapter
import JutilaGappedCollarSelectedP53Adapter
import JutilaLemma6GenericTailAbsorption
import JutilaCollarNoLogBudget
import JutilaCollarSourceParameters
import JutilaLemma6DirectTail

/-!
# Principal finite Halasz/cardinality step

The contour lane supplies only the literal eventual smallness of the
principal canonical direct series.  This module applies the already proved
finite canonical Halasz quadratic estimate to the actual principal rows,
then converts the source FV/QE budgets to the selected cardinality bound.

The nonprincipal series-smallness theorem is not used: it requires `χ ≠ 1`.
-/

namespace MAPJutilaPrincipalFiniteHalasz

open scoped BigOperators
open Complex Real Filter DirichletZeros
open CGLProofDAG
open MAPJutilaP53CanonicalHalaszSource
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaCanonicalQuadraticAbsorption
open MAPJutilaSourceFVBudget
open MAPJutilaSourceQEBudget
open MAPJutilaCollarSourceParameters
open MAPJutilaLemma6GenericTailAbsorption
open MAPJutilaLemma6DirectTail
open MAPJutilaPseudocharacterHarmonicLower
open MAPJutilaGappedFixedModulusAggregateP53Adapter
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPJutilaGappedCollarFiniteAggregation
open MAPJutilaCollarA5Budget
open MAPJutilaCollarMeshCutoff
open MAPJutilaCollarNoLogBudget
open MAPJutilaP53SourceScaleEnvelopes
open MAPPrincipalZetaFixedStrip

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

set_option maxHeartbeats 1600000

theorem oneSeparated_subset {A B : Finset ℝ}
    (hB : OneSeparated B) (hsub : A ⊆ B) : OneSeparated A :=
  fun t ht u hu hne => hB t (hsub ht) u (hsub hu) hne

theorem image_im_subset {W S : Finset ℂ} (h : S ⊆ W) :
    S.image Complex.im ⊆ W.image Complex.im := by
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨rho, hrho, rfl⟩
  exact Finset.mem_image.mpr ⟨rho, h hrho, rfl⟩

theorem card_image_im_eq_of_parent
    {W S : Finset ℂ}
    (hcard : (W.image Complex.im).card = W.card)
    (hsub : S ⊆ W) :
    (S.image Complex.im).card = S.card := by
  have hinj : Set.InjOn Complex.im (W : Set ℂ) :=
    (Finset.card_image_iff.mp hcard)
  have hinjS : Set.InjOn Complex.im (S : Set ℂ) :=
    hinj.mono hsub
  exact Finset.card_image_of_injOn hinjS

theorem principalRegularized_eq_zero_of_mem_regularCollar
    {sigma T : ℝ} {rho : ℂ}
    (h : rho ∈ regularCollarSupport chiOne sigma T) :
    principalF rho = 0 := by
  have hsupp : rho ∈ zeroSupport chiOne sigma T :=
    (Finset.mem_filter.mp h).1
  have hreg := regularizedLFunction_eq_zero_of_mem_zeroSupport
    chiOne sigma T hsupp
  simpa [regularizedLFunction, principalRegularized] using hreg

private theorem sourceF_nonneg {δ D : ℝ} (hδ : 0 ≤ δ) (_hδhi : δ ≤ 1)
    (hgeo : SourceGeometry δ D) :
    0 ≤ sourceSharpResidueBudget (sourceR δ D) δ (sourceZ1 δ D)
      (lemmaSixDirectCutoff δ D : ℝ) := by
  have hz := hgeo.z1_one
  have hx : sourceZ1 δ D < (lemmaSixDirectCutoff δ D : ℝ) := by
    linarith [hgeo.separation]
  have hlogz : 0 ≤ Real.log (sourceZ1 δ D) := Real.log_nonneg hz.le
  have hlogx : Real.log (sourceZ1 δ D) ≤
      Real.log (lemmaSixDirectCutoff δ D : ℝ) :=
    Real.log_le_log (zero_lt_one.trans hz) hx.le
  have hmass := MAPJutilaSourceFVBudget.integerExponentialMass_nonneg
  unfold sourceSharpResidueBudget
  apply mul_nonneg
  · have hgap : 0 ≤
        (1 + δ) * Real.log (lemmaSixDirectCutoff δ D : ℝ) -
          (1 - δ) * Real.log (sourceZ1 δ D) := by
      nlinarith [mul_nonneg hδ hlogz, mul_nonneg hδ (hlogz.trans hlogx)]
    positivity
  · unfold harmonic
    positivity

/-- `collarLogCost` at `δ = 1/280` is a `P = 10` polylog times the selected
interface power.  The factor `64` is kept in the constant. -/
theorem collarLogCost_le_principal_selected_polylog
    {D sigma : ℝ} (hD : 1 ≤ D) (hlog : 1 ≤ Real.log D)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ 1) :
    collarLogCost D (1 / 280) sigma ≤
      64 * Real.rpow (Real.log D) 10 *
        Real.rpow D
          ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
            (1 - sigma)) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hlog0 : 0 ≤ Real.log D := zero_le_one.trans hlog
  have hgap0 : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigma
  have hexp :
      Real.rpow D (2 * (1 + 12 * (1 / 280 : ℝ)) * (1 - sigma)) ≤
        Real.rpow D
          ((2 * (1 + 12 * (1 / 280 : ℝ)) + 4 * (1 / 560 : ℝ)) *
            (1 - sigma)) :=
    Real.rpow_le_rpow_of_exponent_le hD
      (mul_le_mul_of_nonneg_right (by norm_num) hgap0)
  have hlog4 :
      Real.rpow (Real.log D) (4 * (1 - sigma)) ≤
        Real.rpow (Real.log D) 4 :=
      Real.rpow_le_rpow_of_exponent_le hlog (by nlinarith)
  have h16 : (1 + Real.log D) ^ 6 ≤ 64 * (Real.log D) ^ 6 := by
    calc
      _ ≤ (2 * Real.log D) ^ 6 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 6
      _ = 64 * (Real.log D) ^ 6 := by ring
  have hcomb :
      Real.rpow (Real.log D) 4 * (1 + Real.log D) ^ 6 ≤
        64 * Real.rpow (Real.log D) 10 := by
    have hpow6 : (Real.log D) ^ 6 = Real.rpow (Real.log D) 6 :=
      (Real.rpow_natCast _ 6).symm
    calc
      Real.rpow (Real.log D) 4 * (1 + Real.log D) ^ 6 ≤
          Real.rpow (Real.log D) 4 * (64 * (Real.log D) ^ 6) :=
        mul_le_mul_of_nonneg_left h16 (Real.rpow_nonneg hlog0 _)
      _ = 64 * Real.rpow (Real.log D) 4 * Real.rpow (Real.log D) 6 := by
        rw [hpow6]; ring
      _ = 64 * (Real.rpow (Real.log D) 4 *
          Real.rpow (Real.log D) 6) := by ring
      _ = 64 * Real.rpow (Real.log D) (4 + 6) := by
        have h4 : Real.rpow (Real.log D) 4 = (Real.log D) ^ (4 : ℕ) :=
          Real.rpow_natCast _ 4
        have h6 : Real.rpow (Real.log D) 6 = (Real.log D) ^ (6 : ℕ) :=
          Real.rpow_natCast _ 6
        have h10 : Real.rpow (Real.log D) 10 = (Real.log D) ^ (10 : ℕ) :=
          Real.rpow_natCast _ 10
        norm_num only [show (4 : ℝ) + 6 = 10 by norm_num]
        rw [h4, h6, h10]
        ring
      _ = 64 * Real.rpow (Real.log D) 10 := by norm_num
  have hpow0 :
      0 ≤ Real.rpow D (2 * (1 + 12 * (1 / 280 : ℝ)) * (1 - sigma)) :=
    Real.rpow_nonneg hDp.le _
  unfold collarLogCost
  calc
    Real.rpow D (2 * (1 + 12 * (1 / 280 : ℝ)) * (1 - sigma)) *
          Real.rpow (Real.log D) (4 * (1 - sigma)) *
          (1 + Real.log D) ^ 6 ≤
        Real.rpow D (2 * (1 + 12 * (1 / 280 : ℝ)) * (1 - sigma)) *
          Real.rpow (Real.log D) 4 * (1 + Real.log D) ^ 6 := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hlog4 hpow0
      · exact pow_nonneg (by linarith) 6
    _ ≤ Real.rpow D
          ((2 * (1 + 12 * (1 / 280 : ℝ)) + 4 * (1 / 560 : ℝ)) *
            (1 - sigma)) *
          (64 * Real.rpow (Real.log D) 10) := by
      calc
        _ = Real.rpow D
              (2 * (1 + 12 * (1 / 280 : ℝ)) * (1 - sigma)) *
              (Real.rpow (Real.log D) 4 * (1 + Real.log D) ^ 6) := by ring
        _ ≤ Real.rpow D
              ((2 * (1 + 12 * (1 / 280 : ℝ)) + 4 * (1 / 560 : ℝ)) *
                (1 - sigma)) *
              (Real.rpow (Real.log D) 4 * (1 + Real.log D) ^ 6) :=
          mul_le_mul_of_nonneg_right hexp
            (mul_nonneg (Real.rpow_nonneg hlog0 _)
              (pow_nonneg (by linarith) 6))
        _ ≤ _ := mul_le_mul_of_nonneg_left hcomb
          (Real.rpow_nonneg hDp.le _)
    _ = 64 * Real.rpow (Real.log D) 10 *
          Real.rpow D
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - sigma)) := by
      simp only [collarDelta, detectorLogBudget]
      ring

/-- High-ordinate principal selected count from Halasz plus the epsilon remainder. -/
theorem exists_eventually_principal_high_card_le_of_directSeries
    (hseriesInput :
      ∀ᶠ D : ℝ in atTop, ∀ (T omega : ℝ) (rho : ℂ),
        1 ≤ T → T = D → 0 ≤ omega →
        (279 / 280 : ℝ) ≤ rho.re → rho.re ≤ 1 - omega →
        |rho.im| ≤ T → 12 * Real.log D ≤ |rho.im| →
        principalF rho = 0 →
        ‖∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne
          (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
          (jutilaPrimedRSet 1 (sourceR (1 / 280) D)) rho
          (lemmaSixSmoothScale (1 / 280) D) n‖ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ D : ℝ in atTop,
      ∀ (T sigma omega : ℝ) (W : Finset ℂ),
        1 ≤ T → T = D →
        (279 / 280 : ℝ) ≤ sigma → sigma ≤ 1 →
        0 ≤ omega → omega ≤ 1 - sigma →
        (∀ rho ∈ W, rho ∈ regularCollarSupport chiOne sigma T ∧
          rho.re ≤ 1 - omega ∧ 12 * Real.log D ≤ |rho.im|) →
        OneSeparated (W.image Complex.im) →
        (W.image Complex.im).card = W.card →
        (W.card : ℝ) ≤ C * Real.rpow (Real.log D) 10 *
          Real.rpow D ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
            (1 - sigma)) := by
  classical
  have hδlo : (1 / 560 : ℝ) ≤ 1 / 280 := by norm_num
  have hδhi : (1 / 280 : ℝ) ≤ 1 / 280 := le_rfl
  obtain ⟨K, hK, hquad⟩ :=
    exists_canonical_halasz_source_quadratic
      (epsilon := (1 / 280 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨Cfv, hCfv, hFV⟩ := exists_eventually_sourceFVBudget hδlo hδhi
  refine ⟨64 * Cfv, by positivity, ?_⟩
  filter_upwards [hFV, eventually_sourceQE_le_one hδlo hδhi K hK.le,
    eventually_sourceParameters hδlo hδhi,
    hseriesInput,
    eventually_canonical_directTail_lt_one (δ := (1 / 280 : ℝ)) (by norm_num),
    eventually_ge_atTop (Real.exp 1)] with
    D hFV hQE hparams hseries htail hDe
  intro T sigma omega W hT hDT hslo hshi homega hgap hW hsep hcard
  have hgeo := hparams.1
  have hDp : 0 < D := (Real.exp_pos 1).trans_le hDe
  have hD1 : 1 ≤ D := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hDe
  have hlog : 1 ≤ Real.log D := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hDe
  let rows : Finset (JutilaP53Row 1) := fixedCharacterRows chiOne W
  have hrowsT : ∀ row ∈ rows, |row.zero.im| ≤ T := by
    intro row hr
    rcases Finset.mem_map.mp hr with ⟨rho, hrho, heq⟩
    have hmem := (hW rho hrho).1
    have hrect : rho ∈ zeroRectangle sigma T :=
      (zeroDivisor chiOne sigma T).supportWithinDomain
        ((zeroSupport_mem_iff chiOne sigma T rho).mp
          (Finset.mem_filter.mp hmem).1)
    have hrow : row.zero = rho := by
      calc
        row.zero = (fixedCharacterRowEmbedding chiOne rho).zero :=
          (congrArg JutilaP53Row.zero heq).symm
        _ = rho := rfl
    have hrect' : -T ≤ rho.im ∧ rho.im ≤ T := by
      simpa only [Set.mem_preimage, Set.mem_Icc] using hrect.2
    simpa [hrow] using (abs_le.mpr hrect')
  have hgeometry : ∀ row ∈ rows,
      sigma ≤ row.zero.re ∧ row.zero.re ≤ sigma + (1 / 280 : ℝ) := by
    intro row hr
    rcases Finset.mem_map.mp hr with ⟨rho, hrho, heq⟩
    have hmem := (hW rho hrho).1
    have hrect : rho ∈ zeroRectangle sigma T :=
      (zeroDivisor chiOne sigma T).supportWithinDomain
        ((zeroSupport_mem_iff chiOne sigma T rho).mp
          (Finset.mem_filter.mp hmem).1)
    have hre : rho.re ∈ Set.Icc sigma 1 := hrect.1
    have hrow : row.zero = rho := by
      calc
        row.zero = (fixedCharacterRowEmbedding chiOne rho).zero :=
          (congrArg JutilaP53Row.zero heq).symm
        _ = rho := rfl
    rw [hrow]
    exact ⟨hre.1, by linarith [hre.2, hslo]⟩
  have hsize := hparams.2 1 (by exact Nat.succ_pos 0) (by simpa using hD1)
  have hseries' : ∀ row ∈ rows,
      ‖∑' n : ℕ, jutilaLemmaSixDirectTerm row.character
        (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
        (jutilaPrimedRSet 1 (sourceR (1 / 280) D)) row.zero
        (lemmaSixSmoothScale (1 / 280) D) n‖ ≤ 1 := by
    intro row hr
    rcases Finset.mem_map.mp hr with ⟨rho, hrho, heq⟩
    have hdat := hW rho hrho
    have hF := principalRegularized_eq_zero_of_mem_regularCollar hdat.1
    have him : |rho.im| ≤ T := by
      have hrect : rho ∈ zeroRectangle sigma T :=
        (zeroDivisor chiOne sigma T).supportWithinDomain
          ((zeroSupport_mem_iff chiOne sigma T rho).mp
            (Finset.mem_filter.mp hdat.1).1)
      exact abs_le.mpr hrect.2
    have hrow : row.zero = rho := by
      calc
        row.zero = (fixedCharacterRowEmbedding chiOne rho).zero :=
          (congrArg JutilaP53Row.zero heq).symm
        _ = rho := rfl
    have hchar : row.character = chiOne := by
      calc
        row.character = (fixedCharacterRowEmbedding chiOne rho).character :=
          (congrArg JutilaP53Row.character heq).symm
        _ = chiOne := rfl
    have hgeomrow : sigma ≤ rho.re := by
      have hgeomrow' := (hgeometry row hr).1
      rw [hrow] at hgeomrow'
      exact hgeomrow'
    have hreLo : (279 / 280 : ℝ) ≤ rho.re := hslo.trans hgeomrow
    rw [hchar, hrow]
    exact
      (hseries T omega rho hT hDT homega hreLo hdat.2.1 him
        hdat.2.2 hF).le
  have htail' : ∀ row ∈ rows,
      ‖∑' k : ℕ, jutilaLemmaSixDirectTerm row.character
        (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
        (jutilaPrimedRSet 1 (sourceR (1 / 280) D)) row.zero
        (lemmaSixSmoothScale (1 / 280) D)
        (k + (lemmaSixDirectCutoff (1 / 280) D + 1))‖ ≤ 1 := by
    intro row hr
    have hre0 : 0 ≤ row.zero.re := by
      have := (hgeometry row hr).1
      linarith
    exact (htail 1 row.character (sourceZ1 (1 / 280) D)
      (sourceZ2 (1 / 280) D) row.zero hgeo.z1_one hgeo.z12 hre0).le
  have hfiberSep : ∀ chi : DirichletCharacter ℂ 1,
      OneSeparated
        ((rows.filter (fun row => row.character = chi)).image
          (fun row => row.zero.im)) := by
    intro psi
    by_cases hpsi : chiOne = psi
    · subst psi
      have hfilter : rows.filter (fun row => row.character = chiOne) = rows := by
        apply Finset.filter_eq_self.mpr
        intro row hr
        rcases Finset.mem_map.mp hr with ⟨rho, hrho, heq⟩
        calc
          row.character = (fixedCharacterRowEmbedding chiOne rho).character :=
            (congrArg JutilaP53Row.character heq).symm
          _ = chiOne := rfl
      rw [hfilter]
      rw [show rows.image (fun row => row.zero.im) = W.image Complex.im by
        simpa [rows] using image_im_fixedCharacterRows chiOne W]
      exact hsep
    · have hempty : rows.filter (fun row => row.character = psi) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro row hr hrowchar
        rcases Finset.mem_map.mp hr with ⟨rho, hrho, heq⟩
        apply hpsi
        calc
          chiOne = (fixedCharacterRowEmbedding chiOne rho).character := rfl
          _ = row.character := congrArg JutilaP53Row.character heq
          _ = psi := hrowchar
      rw [hempty]
      simp [OneSeparated]
  have hfiberCard : ∀ chi : DirichletCharacter ℂ 1,
      ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)).card =
      (rows.filter (fun row => row.character = chi)).card := by
    intro psi
    by_cases hpsi : chiOne = psi
    · subst psi
      have hfilter : rows.filter (fun row => row.character = chiOne) = rows := by
        apply Finset.filter_eq_self.mpr
        intro row hr
        rcases Finset.mem_map.mp hr with ⟨rho, hrho, heq⟩
        calc
          row.character = (fixedCharacterRowEmbedding chiOne rho).character :=
            (congrArg JutilaP53Row.character heq).symm
          _ = chiOne := rfl
      rw [hfilter]
      rw [show rows.image (fun row => row.zero.im) = W.image Complex.im by
        simpa [rows] using image_im_fixedCharacterRows chiOne W]
      rw [show rows.card = W.card by
        simpa [rows] using card_fixedCharacterRows chiOne W]
      exact hcard
    · have hempty : rows.filter (fun row => row.character = psi) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro row hr hrowchar
        rcases Finset.mem_map.mp hr with ⟨rho, hrho, heq⟩
        apply hpsi
        calc
          chiOne = (fixedCharacterRowEmbedding chiOne rho).character := rfl
          _ = row.character := congrArg JutilaP53Row.character heq
          _ = psi := hrowchar
      rw [hempty]
      simp
  have hquad' :=
    hquad 1 (sourceR (1 / 280) D) (lemmaSixDirectCutoff (1 / 280) D) rows
      (sourceZ1 (1 / 280) D) (sourceZ2 (1 / 280) D)
      (lemmaSixSmoothScale (1 / 280) D) sigma T
      hgeo.R_one hgeo.x_one hgeo.z1_one hgeo.z12 hgeo.X_two hgeo.separation
      (by linarith) hshi (zero_le_one.trans hT)
      hrowsT hgeometry hfiberSep hfiberCard hsize hseries' htail'
  let Q := sourceQ (1 / 280) D sigma
  let F := sourceSharpResidueBudget (sourceR (1 / 280) D) (1 / 280)
    (sourceZ1 (1 / 280) D) (lemmaSixDirectCutoff (1 / 280) D : ℝ)
  let V := (1 / 16 : ℝ) * ((Nat.totient 1 : ℝ) / (1 : ℝ)) *
    Real.log (sourceR (1 / 280) D : ℝ)
  let E := sourceE K (1 / 280) D 1 T
  have hV : 2 ≤ V := by
    have h := hsize
    dsimp [V] at ⊢
    norm_num [Nat.totient] at h ⊢
    linarith
  have hQ : 0 ≤ Q := by
    dsimp [Q, sourceQ]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (pow_nonneg (by
        linarith [Real.log_nonneg
          (show (1 : ℝ) ≤ lemmaSixDirectCutoff (1 / 280) D by
            exact_mod_cast hgeo.x_one)]) _)
  have hF0 : 0 ≤ F := sourceF_nonneg (by norm_num) (by norm_num) hgeo
  have hquadAbs :
      V ^ 2 * (rows.card : ℝ) ^ 2 ≤
        Q * (F * (rows.card : ℝ) + E * (rows.card : ℝ) ^ 2) := by
    simpa [V, Q, F, E, sourceQ, sourceE, Real.sqrt_eq_rpow, mul_assoc]
      using hquad'
  have hcount := card_le_two_linear_div_detector_sq
    (Nat.cast_nonneg rows.card) hV (mul_nonneg hQ hF0)
    (hQE 1 T sigma hT (by simpa using hDT)
      (by linarith : (1 - (1 / 280 : ℝ)) ≤ sigma)) hquadAbs
  have hfv := hFV 1 (by exact Nat.succ_pos 0) (by simpa using hD1) sigma hshi
  have hcut := cutoffPower_logCost_le hDp (Real.log_nonneg hD1) hshi hgeo
  have hcost := collarLogCost_le_principal_selected_polylog hD1 hlog
    (by linarith [hslo] : (0 : ℝ) ≤ sigma) hshi
  have hrowsCard : (rows.card : ℝ) = (W.card : ℝ) := by
    simp [rows, card_fixedCharacterRows]
  rw [← hrowsCard]
  calc
    (rows.card : ℝ) ≤ 2 * Q * F / V ^ 2 := hcount
    _ ≤ Cfv * Real.rpow (lemmaSixDirectCutoff (1 / 280) D : ℝ)
          (2 - 2 * sigma) * (1 + Real.log D) ^ 6 := by
      simpa [Q, F, V, sourceQ] using hfv
    _ ≤ Cfv * collarLogCost D (1 / 280) sigma := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hcut hCfv.le
    _ ≤ Cfv * (64 * Real.rpow (Real.log D) 10 *
          Real.rpow D
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - sigma))) :=
      mul_le_mul_of_nonneg_left hcost hCfv.le
    _ = (64 * Cfv) * Real.rpow (Real.log D) 10 *
          Real.rpow D
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - sigma)) := by ring



end

end MAPJutilaPrincipalFiniteHalasz

#print axioms MAPJutilaPrincipalFiniteHalasz.exists_eventually_principal_high_card_le_of_directSeries
