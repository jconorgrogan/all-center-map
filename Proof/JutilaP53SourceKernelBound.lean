import JutilaP53SourceContourMass
import JutilaP53AllSourceLineIntegral
import JutilaP53PrincipalRResidueAggregation

/-! Full ambient source-line kernel bound, retaining the exact principal residue. -/
namespace MAPJutilaP53SourceKernelBound
open scoped BigOperators
open Complex MeasureTheory
open MAPJutilaP53SourcePairContours MAPJutilaP53SourceContourMass MAPJutilaP53SourceDivisorMass
open MAPJutilaP53PairRExpansion MAPJutilaP53KernelSourceForm
open MAPJutilaP53PrincipalRResidueAggregation MAPJutilaP53PrincipalDivisorResidueBound
noncomputable section

def sourceBranch {q : ℕ} [NeZero q] (S : Finset ℕ) (M N epsilon : ℝ)
    (s : ℂ) (chi : DirichletCharacter ℂ q) : ℂ :=
  ∑ r ∈ S, ∑ r' ∈ S, (((r * r' : ℕ) : ℂ)⁻¹) *
    ∑ d ∈ (r.lcm r').divisors, sourceContourTerm chi s M N epsilon r r' d

theorem sourceB_eq_sourceBranch_add_residue
    {q R : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R) (hSq : ∀ r ∈ S, Squarefree r)
    {M N epsilon : ℝ} (hM : 0 < M) (hMN : M < N)
    (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8)
    {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 2 * epsilon) :
    jutilaP53SourceB S M N s chi = sourceBranch S M N epsilon s chi +
      (if chi = 1 then p53PrincipalRResidue q S s M N else 0) := by
  classical
  rw [jutilaP53SourceB_eq_pairR_doubleSum hS hM hMN hsLo]
  by_cases hc : chi = 1
  · subst chi
    rw [if_pos rfl]
    unfold sourceBranch p53PrincipalRResidue
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro r' hr'
    exact pairRB_eq_sourceContours_principal_add_residue hM hMN hsLo hsHi
      heps hepsHi (hSq r hr) (hSq r' hr')
  · rw [if_neg hc, add_zero]
    unfold sourceBranch
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro r' hr'
    exact pairRB_eq_sourceContours_nonprincipal chi hc hM hMN heps hepsHi
      hsLo hsHi (hSq r hr) (hSq r' hr')

theorem exists_norm_sourceB_le
    {epsilon : ℝ} (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q R : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (S : Finset ℕ) (M N : ℝ) (s : ℂ),
      S ⊆ Finset.Icc 1 R → (∀ r ∈ S, Squarefree r) →
      0 < M → M < N → 0 ≤ s.re → s.re ≤ 2 * epsilon →
      ‖jutilaP53SourceB S M N s chi‖ ≤
        K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) *
          sourceEndpoint N M epsilon * p53NormalizedEulerMass S +
        (if chi = 1 then ‖p53PrincipalRResidue q S s M N‖ else 0) := by
  classical
  obtain ⟨K, hK, hAll⟩ := MAPJutilaP53AllSourceLineIntegral.exists_all_sourceLine_integrable_and_norm_integral_le heps hepsHi
  refine ⟨K, hK, ?_⟩
  intro q R _inst chi S M N s hS hSq hM hMN hsLo hsHi
  have hbranch : ‖sourceBranch S M N epsilon s chi‖ ≤
      K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) *
        sourceEndpoint N M epsilon * p53NormalizedEulerMass S := by
    unfold sourceBranch
    calc
      _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
          ‖(((r * r' : ℕ) : ℂ)⁻¹) * ∑ d ∈ (r.lcm r').divisors,
            sourceContourTerm chi s M N epsilon r r' d‖ := by
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => norm_sum_le _ _)
      _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
          (((r * r' : ℕ) : ℝ)⁻¹) *
            ((K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) * sourceEndpoint N M epsilon) *
              (MAPJutilaLemma3AbsoluteMass.lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ)) := by
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro r' hr'
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply norm_sum_sourceContourTerm_le chi hM (hM.trans hMN) heps.le hsLo hK.le (hSq r hr) (hSq r' hr')
        intro d hd
        have hdPos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hd)
        exact (hAll q chi s (N / d) (M / d) (div_pos (hM.trans hMN) hdPos)
          (div_pos hM hdPos) hsLo hsHi).2
      _ = _ := by
        unfold p53NormalizedEulerMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r' hr'
        ring
  rw [sourceB_eq_sourceBranch_add_residue chi hS hSq hM hMN heps hepsHi hsLo hsHi]
  calc
    _ ≤ ‖sourceBranch S M N epsilon s chi‖ +
      ‖if chi = 1 then p53PrincipalRResidue q S s M N else 0‖ := norm_add_le _ _
    _ ≤ _ := by
      by_cases hc : chi = 1
      · simpa only [if_pos hc] using add_le_add hbranch (le_refl ‖p53PrincipalRResidue q S s M N‖)
      · simpa only [if_neg hc, norm_zero, add_zero] using hbranch

end
end MAPJutilaP53SourceKernelBound
#print axioms MAPJutilaP53SourceKernelBound.sourceB_eq_sourceBranch_add_residue
#print axioms MAPJutilaP53SourceKernelBound.exists_norm_sourceB_le
