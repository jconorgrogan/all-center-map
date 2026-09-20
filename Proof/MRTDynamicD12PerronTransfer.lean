import MRTDynamicD12PolynomialFactorization
import MRTLemma215OpenIntervalCutoffV3
import MRTCorollary25CertifiedMAPWeld
import MRTCorollary25TypeD1IntegratedWeld

/-! # Globally constant cutoff removal for literal dynamic d1/d2 components -/
namespace MRTDynamicD12PerronTransfer

set_option maxHeartbeats 1500000

open scoped BigOperators
open MeasureTheory MixedMeanFrontend
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25CertifiedMAPWeld MAPMRTCorollary25Minkowski
open MAPMRTCorollary25TypeD1IntegratedWeld
open MAPMRTCorollary53Source MAPHBPerronSourceData MAPMRTProposition51Source
open MRTLemma215OpenIntervalCutoffV3

noncomputable section

/-- Exact comparison of the source and Perron carriers. The source cutoff
still ends at `2X`; no endpoint coefficient is added. -/
theorem criticalDirichletPolynomial_cutoff_eq_halfLine
    {X L Y C : ℝ} {q : ℕ} {f : ℕ → ℂ}
    (hsupp : ∀ n : ℕ, C * Y < (n : ℝ) → f n = 0)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    criticalDirichletPolynomial X 1 q (intervalCutoff L (2 * X) f) chi t =
      halfLineDirichletPolynomial Y C
        (intervalCutoff L (2 * X) (characterTwist (fun n => chi n) f)) t := by
  let A := Finset.Icc 1 ⌊2 * X⌋₊
  let B := Finset.Icc 1 (Nat.ceil (C * Y))
  let S := A ∪ B
  unfold criticalDirichletPolynomial halfLineDirichletPolynomial
  simp only [one_mul]
  let left : ℕ → ℂ := fun n ↦
    intervalCutoff L (2 * X) f n * chi n *
      (Real.sqrt n : ℂ)⁻¹ * mellinPhase n t
  let right : ℕ → ℂ := fun n ↦
    (intervalCutoff L (2 * X)
      (characterTwist (fun n ↦ chi n) f) n /
      (Real.sqrt (n : ℝ) : ℂ)) * mellinPhase n t
  change (∑ n ∈ A, left n) = ∑ n ∈ B, right n
  have hAS : (∑ n ∈ A, left n) = ∑ n ∈ S, left n := by
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_union_left B hn
    · intro n hnS hnA
      have hnB : n ∈ B := (Finset.mem_union.mp hnS).resolve_left hnA
      have hnB' := Finset.mem_Icc.mp hnB
      have hnFloor : ⌊2 * X⌋₊ < n := by
        by_contra h
        apply hnA
        exact Finset.mem_Icc.mpr ⟨hnB'.1, Nat.le_of_not_gt h⟩
      have hnAbove : 2 * X < (n : ℝ) := by
        by_cases h2X : 0 ≤ 2 * X
        · exact (Nat.floor_lt h2X).mp hnFloor
        · have hnpos : (0 : ℝ) < n := by exact_mod_cast hnB'.1
          linarith
      have hnot : ¬ (n : ℝ) ≤ 2 * X := not_le_of_gt hnAbove
      simp [left, intervalCutoff, hnot]
  have hBS : (∑ n ∈ B, right n) = ∑ n ∈ S, right n := by
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_union_right A hn
    · intro n hnS hnB
      have hnA : n ∈ A := (Finset.mem_union.mp hnS).resolve_right hnB
      have hnA' := Finset.mem_Icc.mp hnA
      have hnCeil : Nat.ceil (C * Y) < n := by
        by_contra h
        apply hnB
        exact Finset.mem_Icc.mpr ⟨hnA'.1, Nat.le_of_not_gt h⟩
      have hnAbove : C * Y < (n : ℝ) := by
        have hc : C * Y ≤
            (Nat.ceil (C * Y) : ℝ) := Nat.le_ceil _
        have hnCeilR : (Nat.ceil (C * Y) : ℝ) < n := by
          exact_mod_cast hnCeil
        nlinarith
      have hzero : f n = 0 := hsupp n hnAbove
      simp [right, intervalCutoff, characterTwist, hzero]
  rw [hAS, hBS]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [left, right]
  unfold intervalCutoff characterTwist
  split_ifs <;> ring

/-- One fixed support dilation gives a single Perron constant before every
source parameter, coefficient, character, component and truncation height. -/
theorem exists_component_cutoff_transfer (C : ℝ) (hC : 1 < C) :
    ∃ κ : ℝ, 0 < κ ∧
    ∀ {X H beta eta Y P B : ℝ} {q : ℕ} {f : ℕ → ℂ},
      0 ≤ X → 0 ≤ H → 0 < eta → eta ≤ 1 →
      1 ≤ Y → 1 ≤ P → 0 ≤ B → SupportedNear Y C f →
      (∀ n, ‖f n‖ ≤ B) → ∀ component : OuterComponent,
      let a := (componentEndpoints X beta eta component).1
      let b := (componentEndpoints X beta eta component).2
      let U := stationaryWidth beta H
      componentIntegral X H 1 q
          (intervalCutoff (openSourceLeft X) (2 * X) f) beta eta component ≤
        2 * κ ^ 2 *
          ((∫ u in (-P)..P, perronWeight u) ^ 2 *
            (∫ s in (a-P)..(b+P),
              (characterMovingMass
                (fun chi : DirichletCharacter ℂ q => fun t =>
                  ‖halfLineDirichletPolynomial Y C
                    (characterTwist (fun n => chi n) f) t‖) U s) ^ 2) +
            (b-a) * (2*U*(Fintype.card (DirichletCharacter ℂ q) : ℝ) *
              (B * Real.sqrt Y * Real.log (2+P) / P)) ^ 2) := by
  obtain ⟨κ,hκ,hcut⟩ := cutoffRemoval_characterTwist_certified hC
  refine ⟨κ,hκ,?_⟩
  intro X H beta eta Y P B q f hX hH heta hetaOne hY hP hB hsupp hcoeff component
  dsimp only
  let a := (componentEndpoints X beta eta component).1
  let b := (componentEndpoints X beta eta component).2
  let U := stationaryWidth beta H
  let full : DirichletCharacter ℂ q → ℝ → ℝ := fun chi t =>
    ‖halfLineDirichletPolynomial Y C (characterTwist (fun n => chi n) f) t‖
  let clip : DirichletCharacter ℂ q → ℝ → ℝ := fun chi t =>
    ‖halfLineDirichletPolynomial Y C
      (intervalCutoff (openSourceLeft X) (2*X) (characterTwist (fun n => chi n) f)) t‖
  let E : ℝ := B * Real.sqrt Y * Real.log (2+P) / P
  have hfull : ∀ chi, Continuous (full chi) := fun chi =>
    continuous_norm_halfLineDirichletPolynomial _ _ _
  have hclip : ∀ chi, Continuous (clip chi) := fun chi =>
    continuous_norm_halfLineDirichletPolynomial _ _ _
  have hE : 0 ≤ E := by
    dsimp [E]
    have hlog : 0 ≤ Real.log (2+P) := Real.log_nonneg (by linarith)
    positivity
  have hU : 0 ≤ U := by dsimp [U, stationaryWidth]; positivity
  have hab : a ≤ b := componentEndpoints_mono hX heta hetaOne component
  have hpoint : ∀ chi t, clip chi t ≤ κ * (perronConvolution (full chi) P t + E) := by
    intro chi t
    have h := hcut Y P (openSourceLeft X) (2*X) t B
      (fun n => chi n) f hY hP hB hsupp
      (fun n => DirichletCharacter.norm_le_one chi n) hcoeff
    have hperron : perronConvolution (full chi) P t =
        ∫ u in (-P)..P, ‖halfLineDirichletPolynomial Y C
          (characterTwist (fun n => chi n) f) (t+u)‖ / (1+|u|) := by
      unfold perronConvolution
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp [full, perronWeight]
      ring
    simpa only [clip,E,hperron] using h
  have htransfer := character_component_square_cutoff_transfer hclip hfull
    (fun chi t => norm_nonneg _) (fun chi t => norm_nonneg _)
    hab hU (by linarith : 0 < P) hκ.le hE hpoint
  have hsource : componentIntegral X H 1 q
      (intervalCutoff (openSourceLeft X) (2*X) f) beta eta component =
      ∫ t in a..b, (characterMovingMass clip U t)^2 := by
    unfold componentIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    apply congrArg (fun x : ℝ => x ^ 2)
    unfold characterWindow characterMovingMass movingIntegral
    apply Finset.sum_congr rfl
    intro chi hchi
    apply intervalIntegral.integral_congr
    intro s hs
    exact congrArg norm (criticalDirichletPolynomial_cutoff_eq_halfLine
      (X := X) (L := openSourceLeft X) (Y := Y) (C := C)
      (fun n hn => hsupp n (Or.inr hn)) chi s)
  rw [hsource]
  exact htransfer

end
end MRTDynamicD12PerronTransfer

#print axioms MRTDynamicD12PerronTransfer.criticalDirichletPolynomial_cutoff_eq_halfLine
#print axioms MRTDynamicD12PerronTransfer.exists_component_cutoff_transfer
