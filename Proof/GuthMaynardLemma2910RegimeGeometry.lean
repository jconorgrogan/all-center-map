import GuthMaynardJutilaLemma29NineKTwo
import GuthMaynardLemma2910HighRangeFromAFE

/-!
# Exact two-step regime geometry in Jutila Lemma 29.10

Write `A = T^(1+epsilon)`, `M = A/N`, and `P = 4 M^2`.  If the
direct-feedback condition at `N` fails, then `N < P`.  More importantly, the
same identity `A = N M` shows that the transformed pair `(A/P,P)` satisfies
the direct condition automatically.  Thus the middle-range argument is a
finite two-step bootstrap, not an appeal to an unformalized infinite descent.
-/

namespace GuthMaynardLemma2910RegimeGeometry

open GuthMaynardJutilaLemma29NineKTwo
open GuthMaynardJutilaReflection2941

noncomputable section

/-- Failure of direct feedback says exactly that the four-square comparison
length is larger than the current length. -/
theorem lt_four_square_of_primeScale_lt_one
    {N M : ℝ} (hM : 0 < M)
    (hfail : kTwoPrimeLower M N < 1) :
    N < 4 * M ^ 2 := by
  unfold kTwoPrimeLower at hfail
  have hden : 0 < 4 * M ^ 2 := by positivity
  exact (div_lt_one hden).mp hfail

/-- At the bootstrap target `P=4M^2`, the reflected scale `A/P` is in the
direct-feedback regime as soon as `A=NM` and `N≤P`. -/
theorem transformed_primeScale_one_le
    {A N M P : ℝ} (hN : 0 < N) (hM : 0 < M)
    (hA : A = N * M) (hP : P = 4 * M ^ 2) (hNP : N ≤ P) :
    1 ≤ kTwoPrimeLower (A / P) P := by
  have hPpos : 0 < P := by rw [hP]; positivity
  have hApos : 0 < A := by rw [hA]; positivity
  have hAPpos : 0 < A / P := div_pos hApos hPpos
  unfold kTwoPrimeLower
  rw [hA, hP]
  field_simp
  have hMsq : 0 < M ^ 2 := sq_pos_of_pos hM
  have hNP' : N ≤ 4 * M ^ 2 := by simpa [hP] using hNP
  nlinarith [mul_self_le_mul_self (le_of_lt hN) hNP']

/-- The reflected length identity used in every invocation of the two-step
geometry. -/
theorem sourceNumerator_eq_length_mul_reflection
    {T epsilon N : ℝ} (hN : 0 < N) :
    sourceReflectionNumerator29_40 T epsilon =
      N * reflectedLength29_40 T epsilon N := by
  unfold reflectedLength29_40
  field_simp

/-- The source numerator dominates the aperture for positive epsilon. -/
theorem aperture_le_sourceNumerator
    {T epsilon : ℝ} (hT : 1 ≤ T) (hepsilon : 0 ≤ epsilon) :
    T ≤ sourceReflectionNumerator29_40 T epsilon := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  unfold sourceReflectionNumerator29_40
  calc
    T = Real.rpow T 1 := (Real.rpow_one T).symm
    _ ≤ Real.rpow T (1 + epsilon) :=
      Real.rpow_le_rpow_of_exponent_le hT (by linarith)

/-- Exact middle-range dichotomy used by the final constructor.  In the
bootstrap branch the target either lies above the aperture, where the
unconditional real-length mean square applies, or remains inside the legal
AFE range and is already in the direct-feedback regime. -/
theorem direct_or_bootstrap_target
    {T epsilon N : ℝ} (hT : 1 ≤ T) (hepsilon : 0 ≤ epsilon)
    (hN : 0 < N) :
    let A := sourceReflectionNumerator29_40 T epsilon
    let M := reflectedLength29_40 T epsilon N
    let P := 4 * M ^ 2
    1 ≤ kTwoPrimeLower M N ∨
      (N < P ∧ (T ≤ P ∨
        (P < T ∧ P ≤ A ∧ 1 ≤ kTwoPrimeLower (A / P) P))) := by
  dsimp only
  let A := sourceReflectionNumerator29_40 T epsilon
  let M := reflectedLength29_40 T epsilon N
  let P := 4 * M ^ 2
  have hApos : 0 < A := by
    dsimp [A, sourceReflectionNumerator29_40]
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) _
  have hMpos : 0 < M := by
    dsimp [M, reflectedLength29_40]
    positivity
  by_cases hdirect : 1 ≤ kTwoPrimeLower M N
  · exact Or.inl hdirect
  · right
    have hfail : kTwoPrimeLower M N < 1 := lt_of_not_ge hdirect
    have hNP : N < P := by
      dsimp [P]
      exact lt_four_square_of_primeScale_lt_one hMpos hfail
    refine ⟨hNP, ?_⟩
    by_cases hhigh : T ≤ P
    · exact Or.inl hhigh
    · right
      have hPT : P < T := lt_of_not_ge hhigh
      have hTA : T ≤ A := by
        dsimp [A]
        exact aperture_le_sourceNumerator hT hepsilon
      have hPA : P ≤ A := hPT.le.trans hTA
      refine ⟨hPT, hPA, ?_⟩
      apply transformed_primeScale_one_le hN hMpos
      · dsimp [A, M]
        exact sourceNumerator_eq_length_mul_reflection hN
      · rfl
      · exact hNP.le

end
end GuthMaynardLemma2910RegimeGeometry

#print axioms GuthMaynardLemma2910RegimeGeometry.lt_four_square_of_primeScale_lt_one
#print axioms GuthMaynardLemma2910RegimeGeometry.transformed_primeScale_one_le
#print axioms GuthMaynardLemma2910RegimeGeometry.sourceNumerator_eq_length_mul_reflection
#print axioms GuthMaynardLemma2910RegimeGeometry.aperture_le_sourceNumerator
#print axioms GuthMaynardLemma2910RegimeGeometry.direct_or_bootstrap_target
