import MRTLemma29Counterexample

/-!
# Source-faithful corrected interface for MRT Lemma 2.9

MRT, *Correlations of the von Mangoldt and higher divisor functions I: Long
shift ranges*, Lemma 2.9 (printed pp. 22--23, equations (33)--(35)), assumes
that `f` is finitely supported and uses the complete Dirichlet series.  A
finite truncation is therefore valid only after the cutoff contains the
support (or after the rescaled sums are cut off at `q₀ * n ≤ N`).

`MRTLemma29Supported` is the minimal correction of the rejected proposition
certified in `MRTLemma29Counterexample`.  No theorem in this module asserts the
published character expansion; its inhabitant is the remaining finite
harmonic-analysis proof obligation.
-/

namespace MAPMRTLemma29Corrected

open scoped BigOperators
open MAPMRTProposition51Source MAPMRTCorollary53Source
open PrimePairEndpoints MAPAllCenterNearFarTransfer

noncomputable section

/-- Correct finite form of MRT Lemma 2.9: `N` contains the support of `f`. -/
def MRTLemma29Supported : Prop :=
  ∀ (N q a : ℕ) (f : ℕ → ℂ) (t : ℝ),
    1 ≤ q → a.Coprime q →
    (∀ n : ℕ, N < n → f n = 0) →
    ‖finiteCriticalPolynomial N (additiveTwist q a f) t‖ ≤
      (divisorCount q : ℝ) / Real.sqrt q *
        ∑ z ∈ modulusFactorizations q,
          ∑ chi : DirichletCharacter ℂ z.2,
            ‖∑ n ∈ Finset.Icc 1 N,
              f (z.1 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
                MixedMeanFrontend.mellinPhase n t‖

/-- The exact source-polynomial specialization consumed by the stationary
phase chain, with the missing support premise made visible. -/
theorem lemma29_specialize_to_source_supported
    (hL29 : MRTLemma29Supported) {X : ℝ} {q a : ℕ} {f : ℕ → ℂ} {t : ℝ}
    (hq : 1 ≤ q) (haq : a.Coprime q)
    (hsupport : ∀ n : ℕ, ⌊2 * X⌋₊ < n → f n = 0) :
    ‖finiteCriticalPolynomial ⌊2 * X⌋₊ (additiveTwist q a f) t‖ ≤
      (divisorCount q : ℝ) / Real.sqrt q *
        ∑ z ∈ modulusFactorizations q,
          ∑ chi : DirichletCharacter ℂ z.2,
            ‖criticalDirichletPolynomial X z.1 z.2 f chi t‖ := by
  simpa [criticalDirichletPolynomial] using
    hL29 ⌊2 * X⌋₊ q a f t hq haq hsupport

/-- The support condition already present in Proposition 5.1/Corollary 5.3
implies that the cutoff `⌊2X⌋₊` contains the support. -/
theorem cutoff_support_of_dyadic_support
    {X : ℝ} {f : ℕ → ℂ} (hX : 0 ≤ X)
    (hsupport : ∀ n : ℕ,
      ¬(X < (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) → f n = 0) :
    ∀ n : ℕ, ⌊2 * X⌋₊ < n → f n = 0 := by
  intro n hn
  apply hsupport n
  intro hinside
  have h2Xlt : 2 * X < (n : ℝ) :=
    (Nat.floor_lt (by positivity : 0 ≤ 2 * X)).mp hn
  exact (not_lt_of_ge hinside.2) h2Xlt

/-- Direct adapter from a literal admissible Corollary 5.3 input to the
support premise required by the corrected finite lemma. -/
theorem cutoff_support_of_corollary53Admissible
    {cBetaEta cEta : ℝ} {p : Corollary53Input}
    (hp : Corollary53Admissible cBetaEta cEta p) :
    ∀ n : ℕ, ⌊2 * p.X⌋₊ < n → p.f n = 0 := by
  rcases hp with
    ⟨hH, hHX, hq, haq, heta, hetaOne, hbetaEta, hetaCap, hbeta, hsupport⟩
  have hX : 0 ≤ p.X := by linarith
  exact cutoff_support_of_dyadic_support hX hsupport

end
end MAPMRTLemma29Corrected

#print axioms MAPMRTLemma29Corrected.lemma29_specialize_to_source_supported
#print axioms MAPMRTLemma29Corrected.cutoff_support_of_dyadic_support
#print axioms MAPMRTLemma29Corrected.cutoff_support_of_corollary53Admissible
