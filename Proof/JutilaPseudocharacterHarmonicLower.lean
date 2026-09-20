import SelbergDenominatorLower

/-!
# A uniform replacement for Jutila's pseudocharacter Lemma 5

Jutila uses an asymptotic for the primed harmonic sum over squarefree
`r ≤ R` coprime to the modulus.  The detector only needs a fixed positive
multiple of `(φ(q)/q) log R`.  The elementary squarefree-coprime harmonic
lower bound already certified for the Selberg denominator supplies this
directly, uniformly in both parameters and without an `o(1)` term.
-/

namespace MAPJutilaPseudocharacterHarmonicLower

open scoped BigOperators
open ShiuSelbergDenominatorLower

noncomputable section

/-- The literal finite set denoted by the prime on Jutila's `r`-sum. -/
def jutilaPrimedRSet (q R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter (fun r => Squarefree r ∧ r.Coprime q)

theorem jutilaPrimedRSet_subset_Icc (q R : ℕ) :
    jutilaPrimedRSet q R ⊆ Finset.Icc 1 R := by
  intro r hr
  exact (Finset.mem_filter.mp hr).1

theorem squarefree_of_mem_jutilaPrimedRSet
    {q R r : ℕ} (hr : r ∈ jutilaPrimedRSet q R) : Squarefree r :=
  (Finset.mem_filter.mp hr).2.1

theorem coprime_of_mem_jutilaPrimedRSet
    {q R r : ℕ} (hr : r ∈ jutilaPrimedRSet q R) : r.Coprime q :=
  (Finset.mem_filter.mp hr).2.2

/-- The literal primed `r`-sum in Jutila: the prime means squarefree and
coprime to the ambient modulus. -/
def jutilaPrimedHarmonic (q R : ℕ) : ℝ :=
  ∑ r ∈ jutilaPrimedRSet q R,
    (r : ℝ)⁻¹

theorem jutilaPrimedHarmonic_eq_squarefreeCoprimeHarmonic
    (q R : ℕ) :
    jutilaPrimedHarmonic q R = squarefreeCoprimeHarmonic q R := by
  simp only [jutilaPrimedHarmonic, jutilaPrimedRSet,
    squarefreeCoprimeHarmonic, one_div]

/-- A source-strong uniform substitute for the lower-bound half of Jutila's
Lemma 5.  Its absolute constant is weaker than `6/π²`, but no asymptotic or
parameter-dependent threshold remains. -/
theorem quarter_totientRatio_log_le_jutilaPrimedHarmonic
    {q R : ℕ} (hq : 0 < q) :
    (1 / 4 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
        Real.log (R : ℝ) ≤ jutilaPrimedHarmonic q R := by
  simpa [jutilaPrimedHarmonic, jutilaPrimedRSet,
    squarefreeCoprimeHarmonic,
    one_div] using
    (quarter_eulerRatio_log_le_squarefreeCoprimeHarmonic
      (modulus := q) (z := R) hq)

/-- Detector-friendly association of the same explicit lower bound. -/
theorem totientRatio_mul_quarterLog_le_jutilaPrimedHarmonic
    {q R : ℕ} (hq : 0 < q) :
    ((Nat.totient q : ℝ) / (q : ℝ)) *
        ((1 / 4 : ℝ) * Real.log (R : ℝ)) ≤
      jutilaPrimedHarmonic q R := by
  convert quarter_totientRatio_log_le_jutilaPrimedHarmonic
    (q := q) (R := R) hq using 1 <;> ring

end

end MAPJutilaPseudocharacterHarmonicLower

#print axioms MAPJutilaPseudocharacterHarmonicLower.quarter_totientRatio_log_le_jutilaPrimedHarmonic
