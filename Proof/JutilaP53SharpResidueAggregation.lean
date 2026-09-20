import JutilaP53PrincipalResidueScaling
import JutilaP53PairSectorAggregation

/-! # Harmonic residue budget after exact signed divisor cancellation -/
namespace MAPJutilaP53SharpResidueAggregation
open scoped BigOperators
open CGLProofDAG
open MAPJutilaP53AggregateCorrelationLeaf MAPJutilaP53KernelSourceForm
open MAPJutilaP53PrincipalRResidueAggregation MAPJutilaP53PrincipalResidueScaling
open MAPJutilaP53PairSectorAggregation MAPJutilaOneSeparatedExponentialPacking
open MAPJutilaP53SignedDivisorMass
noncomputable section

/-- Reuse the established fiber packing with the singleton arithmetic system;
exact signed cancellation extracts the full system's scalar diagonal mass. -/
theorem sum_sameCharacter_norm_p53PrincipalRResidue_le_harmonic
    (q : ℕ) [NeZero q] (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} {R : ℕ} {alpha epsilon M N : ℝ}
    (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r) (hcop : ∀ r ∈ S, r.Coprime q)
    (hM : 1 ≤ M) (hMN : M ≤ N) (heps : 2 * epsilon ≤ 1 / 2)
    (hrows : ∀ row ∈ rows,
      alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha + epsilon)
    (hfiberSep : ∀ chi : DirichletCharacter ℂ q,
      OneSeparated ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)))
    (hfiberCard : ∀ chi : DirichletCharacter ℂ q,
      ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)).card =
      (rows.filter (fun row => row.character = chi)).card) :
    (∑ i ∈ rows, ∑ j ∈ rows,
      if i.character = j.character then
        ‖p53PrincipalRResidue q S (jutilaP53PairShift alpha i j) M N‖
      else 0) ≤
      (rows.card : ℝ) *
        ((12 * (Real.log N - Real.log M) +
            48 * Real.exp 1 * integerExponentialMass) * (harmonic R : ℝ)) := by
  classical
  let D : ℝ := ∑ r ∈ S, (Nat.totient r : ℝ) / (r : ℝ)^2
  let K : ℝ := 12 * (Real.log N - Real.log M) +
    48 * Real.exp 1 * integerExponentialMass
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDle : D ≤ (harmonic R : ℝ) := sum_totient_div_sq_le_harmonic hS
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hNp : 0 < N := hMp.trans_le hMN
  have hK : 0 ≤ K := by
    have hlog : 0 ≤ Real.log N - Real.log M := sub_nonneg.mpr
      (Real.log_le_log hMp hMN)
    have hm : 0 ≤ integerExponentialMass := tsum_nonneg fun k => (Real.exp_pos _).le
    dsimp [K]
    positivity
  have hOneSq : ∀ r ∈ ({1} : Finset ℕ), Squarefree r := by simp
  have hOneCop : ∀ r ∈ ({1} : Finset ℕ), r.Coprime q := by simp
  have hOneScale : ∀ r ∈ ({1} : Finset ℕ), ∀ r' ∈ ({1} : Finset ℕ),
      ((r.lcm r' : ℕ) : ℝ) ≤ M := by simpa using hM
  have hmass : p53NormalizedEulerMass ({1} : Finset ℕ) = 1 := by
    simp [p53NormalizedEulerMass, MAPJutilaLemma3AbsoluteMass.lemmaThreeAbsoluteMass,
      MAPJutilaPseudocharacterAlgebra.exclusivePrimes]
  have hbase := sum_sameCharacter_norm_p53PrincipalRResidue_le q rows
    hOneSq hOneScale hMN heps hrows hfiberSep hfiberCard
  rw [hmass, mul_one] at hbase
  have hnorm (s : ℂ) : ‖p53PrincipalRResidue q S s M N‖ =
      D * ‖p53PrincipalRResidue q ({1} : Finset ℕ) s M N‖ := by
    rw [principalRResidue_eq_diagonalMass q hNp hMp S hSq hcop,
      principalRResidue_eq_diagonalMass q hNp hMp {1} hOneSq hOneCop]
    simp only [Finset.sum_singleton, Nat.totient_one, Nat.cast_one, one_pow,
      div_one, one_mul, norm_mul]
    have hcast : (∑ r ∈ S, (r.totient : ℂ) / (r : ℂ)^2) = (D : ℂ) := by
      dsimp [D]
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD]
  calc
    _ = D * (∑ i ∈ rows, ∑ j ∈ rows,
        if i.character = j.character then
          ‖p53PrincipalRResidue q {1} (jutilaP53PairShift alpha i j) M N‖
        else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp [hnorm]
    _ ≤ D * ((rows.card : ℝ) * K) :=
      mul_le_mul_of_nonneg_left hbase hD
    _ ≤ (harmonic R : ℝ) * ((rows.card : ℝ) * K) :=
      mul_le_mul_of_nonneg_right hDle (mul_nonneg (Nat.cast_nonneg _) hK)
    _ = _ := by dsimp [K]; ring
end
end MAPJutilaP53SharpResidueAggregation
#print axioms MAPJutilaP53SharpResidueAggregation.sum_sameCharacter_norm_p53PrincipalRResidue_le_harmonic
