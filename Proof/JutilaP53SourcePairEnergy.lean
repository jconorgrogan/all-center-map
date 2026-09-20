import JutilaP53SourceKernelBound
import JutilaP53SourceScaleEnvelopes

/-! Full source-line row-pair energy estimate with signed residue cancellation. -/
namespace MAPJutilaP53SourcePairEnergy
open scoped BigOperators ComplexConjugate
open Complex
open MAPJutilaP53SourceKernelBound MAPJutilaP53SourceDivisorMass
open MAPJutilaP53AggregateCorrelationLeaf MAPJutilaP53KernelExpansion MAPJutilaP53KernelSourceForm
open MAPJutilaP53PrincipalRResidueAggregation MAPJutilaOneSeparatedExponentialPacking
open MAPJutilaP53SourceScaleEnvelopes MAPJutilaP53SharpResidueAggregation
noncomputable section

theorem exists_sourcePair_energy_le
    {epsilon : ℝ} (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q R : ℕ) [NeZero q]
      (rows : Finset (JutilaP53Row q)) (S : Finset ℕ) (alpha M N T : ℝ),
      S ⊆ Finset.Icc 1 R → (∀ r ∈ S, Squarefree r) → (∀ r ∈ S, r.Coprime q) →
      1 ≤ M → M < N → 0 ≤ T →
      (∀ row ∈ rows, |row.zero.im| ≤ T) →
      (∀ row ∈ rows, alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha + epsilon) →
      (∀ chi : DirichletCharacter ℂ q, CGLProofDAG.OneSeparated
        ((rows.filter (fun row => row.character = chi)).image (fun row => row.zero.im))) →
      (∀ chi : DirichletCharacter ℂ q,
        ((rows.filter (fun row => row.character = chi)).image (fun row => row.zero.im)).card =
        (rows.filter (fun row => row.character = chi)).card) →
      ∀ eta : JutilaP53Row q → ℂ, (∀ row ∈ rows, ‖eta row‖ = 1) →
      jutilaP53CorrelationEnergy rows S alpha M N eta ≤
        (K * Real.rpow ((q : ℝ) * (1 + 2 * T)) (1 / 2) *
          sourceEndpoint N M epsilon * p53NormalizedEulerMass S) * (rows.card : ℝ) ^ 2 +
        (rows.card : ℝ) * ((12 * (Real.log N - Real.log M) +
          48 * Real.exp 1 * integerExponentialMass) * (harmonic R : ℝ)) := by
  classical
  obtain ⟨K, hK, hKernel⟩ := exists_norm_sourceB_le heps hepsHi
  refine ⟨K, hK, ?_⟩
  intro q R _inst rows S alpha M N T hS hSq hcop hM hMN hT hrowsT hrows hsep hcard eta heta
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  let B := K * Real.rpow ((q : ℝ) * (1 + 2 * T)) (1 / 2) *
    sourceEndpoint N M epsilon * p53NormalizedEulerMass S
  have hpair : ∀ i ∈ rows, ∀ j ∈ rows,
      ‖jutilaP53Kernel S alpha M N i j‖ ≤ B +
        (if i.character = j.character then
          ‖p53PrincipalRResidue q S (jutilaP53PairShift alpha i j) M N‖ else 0) := by
    intro i hi j hj
    have hs := pairShift_re_mem_Icc (hrows i hi).1 (hrows i hi).2 (hrows j hj).1 (hrows j hj).2
    have hraw := hKernel q R (jutilaP53PairCharacter i j) S M N
      (jutilaP53PairShift alpha i j) hS hSq hMpos hMN hs.1 hs.2
    rw [← jutilaP53Kernel_eq_sourceB] at hraw
    simp only [pairCharacter_eq_one_iff] at hraw
    apply hraw.trans
    apply add_le_add _ (le_refl _)
    dsimp [B]
    apply mul_le_mul_of_nonneg_right _ (p53NormalizedEulerMass_nonneg S)
    apply mul_le_mul_of_nonneg_right _ (sourceEndpoint_nonneg (hMpos.trans hMN) hMpos epsilon)
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
    have him := abs_pairShift_im_le_two_mul (alpha := alpha) (hrowsT i hi) (hrowsT j hj)
    linarith
  have henergy0 : 0 ≤ jutilaP53CorrelationEnergy rows S alpha M N eta := by
    unfold jutilaP53CorrelationEnergy
    exact tsum_nonneg fun n => mul_nonneg (jutilaP53CorrelationWeight_nonneg S hMpos hMN n) (sq_nonneg _)
  have hexpand := jutilaP53CorrelationEnergy_eq_doubleSum rows hS hMpos hMN eta
    (fun row hr => (hrows row hr).1) heta
  calc
    _ = ‖(jutilaP53CorrelationEnergy rows S alpha M N eta : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg henergy0]
    _ = ‖∑ i ∈ rows, ∑ j ∈ rows, conj (eta i) * eta j * jutilaP53Kernel S alpha M N i j‖ := by rw [hexpand]
    _ ≤ ∑ i ∈ rows, ∑ j ∈ rows, ‖conj (eta i) * eta j * jutilaP53Kernel S alpha M N i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => norm_sum_le _ _)
    _ = ∑ i ∈ rows, ∑ j ∈ rows, ‖jutilaP53Kernel S alpha M N i j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [heta i hi, heta j hj]
    _ ≤ ∑ i ∈ rows, ∑ j ∈ rows, (B + if i.character = j.character then
        ‖p53PrincipalRResidue q S (jutilaP53PairShift alpha i j) M N‖ else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum (hpair i hi)
    _ = B * (rows.card : ℝ) ^ 2 +
        (∑ i ∈ rows, ∑ j ∈ rows, if i.character = j.character then
          ‖p53PrincipalRResidue q S (jutilaP53PairShift alpha i j) M N‖ else 0) := by
      simp only [Finset.sum_add_distrib]
      simp
      ring
    _ ≤ _ := add_le_add (le_refl _)
      (sum_sameCharacter_norm_p53PrincipalRResidue_le_harmonic q rows hS hSq hcop hM hMN.le
        (by linarith) hrows hsep hcard)

end
end MAPJutilaP53SourcePairEnergy
#print axioms MAPJutilaP53SourcePairEnergy.exists_sourcePair_energy_le
