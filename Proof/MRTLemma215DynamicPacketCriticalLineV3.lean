import MRTLemma215DynamicHighPacketFlattenV3

/-!
# Critical-line realization of literal dynamic high packets

The exact open-left packet coefficients are rewritten as the clipped
Dirichlet polynomials consumed by certified Perron removal.  The selected
short factor is kept as the second factor and the dyadic complement as the
first, matching the existing mixed-mean interface.
-/

namespace MRTLemma215DynamicPacketCriticalLineV3

set_option maxHeartbeats 800000

open scoped ArithmeticFunction BigOperators
open MeasureTheory ArithmeticFunction
open MixedMeanFrontend DeterminantCountWeld
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25Minkowski MAPMRTCorollary25TypeD1IntegratedWeld
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketAggregateV3
open MRTLemma215DynamicHighPacketFlattenV3

noncomputable section

theorem branchHighPacketConvolution_apply_eq_literal_long_short
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} {branch : Fin K}
    (packet : DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch)
    (n : ℕ) :
    branchHighPacketConvolutionV3 packet n =
      literalDirichletConvolution
        (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
        (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet)) n := by
  unfold branchHighPacketConvolutionV3 highPacketConvolutionV3
  rw [mul_comm, ArithmeticFunction.mul_apply]
  rfl

/-- The critical polynomial of a clipped dyadic convolution equals the
finite half-line polynomial used in Corollary 2.5.  The lower endpoint is
arbitrary; the upper endpoint remains the exact source endpoint `2X`. -/
theorem criticalDirichletPolynomial_intervalConvolution_eq_clipped_open
    {X L : ℝ} {q N M : ℕ} {alpha beta : ℕ → ℂ}
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    criticalDirichletPolynomial X 1 q
        (intervalCutoff L (2 * X)
          (literalDirichletConvolution alpha beta)) chi t =
      halfLineDirichletPolynomial ((N : ℝ) * M) 4
        (intervalCutoff L (2 * X)
          (characterTwist (fun n ↦ chi n)
            (literalDirichletConvolution alpha beta))) t := by
  let f := literalDirichletConvolution alpha beta
  let A := Finset.Icc 1 ⌊2 * X⌋₊
  let B := Finset.Icc 1 (Nat.ceil (4 * ((N : ℝ) * M)))
  let S := A ∪ B
  have hsupp : ∀ n : ℕ, ¬ ((N : ℝ) * M ≤ (n : ℝ) ∧
      (n : ℝ) ≤ 4 * (N : ℝ) * M) → f n = 0 :=
    fun n hn ↦ literalDirichletConvolution_eq_zero_off_productBlock
      (by exact_mod_cast Nat.zero_le N) (by exact_mod_cast Nat.zero_le M)
      (supportedDyadic_coe_of_supportedNatDyadic halpha)
      (supportedDyadic_coe_of_supportedNatDyadic hbeta) hn
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
      have hnCeil : Nat.ceil (4 * ((N : ℝ) * M)) < n := by
        by_contra h
        apply hnB
        exact Finset.mem_Icc.mpr ⟨hnA'.1, Nat.le_of_not_gt h⟩
      have hnAbove : 4 * (N : ℝ) * M < (n : ℝ) := by
        have hc : 4 * ((N : ℝ) * M) ≤
            (Nat.ceil (4 * ((N : ℝ) * M)) : ℝ) := Nat.le_ceil _
        have hnCeilR : (Nat.ceil (4 * ((N : ℝ) * M)) : ℝ) < n := by
          exact_mod_cast hnCeil
        nlinarith
      have hzero : f n = 0 := hsupp n (by
        intro hblock
        nlinarith [hblock.2])
      simp [right, intervalCutoff, characterTwist, hzero]
  rw [hAS, hBS]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [left, right]
  unfold intervalCutoff characterTwist
  split_ifs <;> ring

/-- Packet specialization of the critical-line clipped identity. -/
theorem criticalDirichletPolynomial_branchHighPacket_eq_clipped
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K q : ℕ} {branch : Fin K}
    (packet : DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch)
    (L : ℝ) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    criticalDirichletPolynomial X 1 q
        (intervalCutoff L (2 * X) (branchHighPacketConvolutionV3 packet))
        chi t =
      halfLineDirichletPolynomial
        ((highPacketLongLengthV3 (branchHighPacketToGlobalV3 packet) : ℝ) *
          highPacketShortLengthV3 (branchHighPacketToGlobalV3 packet)) 4
        (intervalCutoff L (2 * X)
          (characterTwist (fun n ↦ chi n)
            (literalDirichletConvolution
              (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
              (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet))))) t := by
  let gp := branchHighPacketToGlobalV3 packet
  have hgeom := highPacket_geometryV3 gp
  have hsupp := highPacket_supportV3 gp
  rw [show intervalCutoff L (2 * X) (branchHighPacketConvolutionV3 packet) =
      intervalCutoff L (2 * X)
        (literalDirichletConvolution (highPacketLongCoeffV3 gp)
          (highPacketShortCoeffV3 gp)) by
    funext n
    unfold intervalCutoff
    split_ifs
    · exact branchHighPacketConvolution_apply_eq_literal_long_short packet n
    · rfl]
  exact criticalDirichletPolynomial_intervalConvolution_eq_clipped_open
    (by omega) (by omega) hsupp.2 hsupp.1 chi t

end
end MRTLemma215DynamicPacketCriticalLineV3

#print axioms MRTLemma215DynamicPacketCriticalLineV3.criticalDirichletPolynomial_intervalConvolution_eq_clipped_open
#print axioms MRTLemma215DynamicPacketCriticalLineV3.criticalDirichletPolynomial_branchHighPacket_eq_clipped
