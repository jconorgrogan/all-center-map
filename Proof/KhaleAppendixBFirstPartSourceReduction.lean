import KhaleAppendixB1FirstPartReduction

/-!
# Source reduction for Khale Appendix B display `(firstpart)`

The previously exposed `AppendixBFirstPartEstimate` bundled two logically
separate facts: the displayed upper inequality and `beta < 1`.  The latter is
already a theorem of Mathlib (`LFunction_ne_zero_of_one_le_re`) once the
ordinate is nonzero.  This file removes it from the source-facing analytic
leaf.  The only remaining proposition is now exactly the upper inequality
obtained by applying Khale Lemma 4.1, the trigonometric polynomial, and Lemma
5.1.
-/

namespace MAPKhaleAppendixBFirstPartSourceReduction

open MAPKhaleAppendixBSource MAPKhaleAppendixBEtaAlgebra
open MAPKhaleAppendixB1ZetaReduction
open MAPKhaleAppendixB1FirstPartReduction

noncomputable section

/-- The final upper inequality in `(firstpart)`, without the already-certified
closed-right-half-plane nonvanishing fact.  Its exponentially tiny parity
correction is the uniform `b₅ e⁻¹⁹³⁷` repair rather than the source's
odd-character-only `(b₂+b₄)e⁻¹⁹³⁷`; all later constants are unchanged. -/
abbrev AppendixBFirstPartUpperEstimate : Prop :=
  ∀ (A B T₀ : ℝ),
    0 < A → 0 < B → B ≤ 4.45 →
    FordHurwitzEquation12 A B →
    Real.exp 10650 ≤ T₀ →
    5110.6 / B ≤ Real.log T₀ / Real.log (Real.log T₀) →
    183 / B ^ 2 ≤ Real.log (Real.log T₀) →
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (gamma beta : ℝ),
      3 ≤ q → T₀ ≤ gamma →
      Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ gamma →
      1 - beta ≤ 1 /
        (18 * Real.log q + appendixBHeightCoefficient A T₀ *
          Real.rpow B (2 / 3 : ℝ) *
          Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) →
      DirichletCharacter.LFunction chi
          ((beta : ℂ) + (gamma : ℂ) * Complex.I) = 0 →
      let eta := khaleEta B gamma
      let sigmaAux := 1 + 3.238 * (1 - beta)
      let y := (sigmaAux - beta) / eta
      0 ≤
        -17.145 * (1 / eta) *
            ((Real.pi / 2) * Real.cot ((Real.pi / 2) * y)) +
        (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
            Real.log (A + 1)) +
        10.01055 / (sigmaAux - 1) +
        (10.01055 / 2) * (1 / eta) * zetaLog eta +
        (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937)

/-- A nonreal zero of a Dirichlet L-function cannot lie on or to the right of
`Re(s)=1`.  This is already available in Mathlib and does not belong in the
Khale analytic source leaf. -/
theorem beta_lt_one_of_nonzero_ordinate_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {gamma beta : ℝ} (hgamma : 0 < gamma)
    (hzero : DirichletCharacter.LFunction chi
      ((beta : ℂ) + (gamma : ℂ) * Complex.I) = 0) :
    beta < 1 := by
  by_contra hnot
  have hbeta : (1 : ℝ) ≤ beta := le_of_not_gt hnot
  let s : ℂ := (beta : ℂ) + (gamma : ℂ) * Complex.I
  have hsre : s.re = beta := by simp [s]
  have hsne : s ≠ 1 := by
    intro hs
    have him : s.im = 0 := by rw [hs]; simp
    simp [s] at him
    exact hgamma.ne' him
  have hnz := DirichletCharacter.LFunction_ne_zero_of_one_le_re chi
    (Or.inr hsne) (by simpa [hsre] using hbeta)
  exact hnz (by simpa [s] using hzero)

/-- The literal upper estimate plus Mathlib's closed-half-plane nonvanishing
inhabits the older bundled interface. -/
theorem firstPartEstimate_of_upper
    (hUpper : AppendixBFirstPartUpperEstimate) :
    AppendixBFirstPartEstimate := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  have hgammaPos : 0 < gamma :=
    (Real.exp_pos 10650).trans_le (hT₀.trans hgamma)
  refine ⟨beta_lt_one_of_nonzero_ordinate_zero chi hgammaPos hzero, ?_⟩
  exact hUpper A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero

end
end MAPKhaleAppendixBFirstPartSourceReduction

#print axioms MAPKhaleAppendixBFirstPartSourceReduction.beta_lt_one_of_nonzero_ordinate_zero
#print axioms MAPKhaleAppendixBFirstPartSourceReduction.firstPartEstimate_of_upper
