import KTwoPrimeArithmeticLogBudgetLargeScale

/-!
# Source-exact interface and weld for equation (29.41)

Equation (29.41) in the third-volume source is obtained from Lemma 29.5
(the zeta functional-equation reflection), coefficient majorization in
Lemma 29.6, a dyadic split, the prime transference Lemma 29.7, and the
length comparison Lemma 29.8.  This file records the exact finite moments,
keeps the Lemma 29.5 remainder explicit, and proves the algebraic weld to
the recurrence.

No large-sieve or Halasz theorem occurs in this derivation.  The analytic
source leaf is Lemma 29.5, printed pp. 261--263; the other nontrivial
number-theoretic input is the reciprocal-prime estimate (29.32), printed
pp. 264--265.
-/

namespace GuthMaynardJutilaReflection2941

open scoped BigOperators
open GuthMaynardHeathBrownMajorant
open GuthMaynardJutilaTransference
open GuthMaynardLengthComparison
open GuthMaynardJutilaLemma29NineKTwo
open GuthMaynardPoweringKTwo

noncomputable section

/-! ## Exact source moments and ranges -/

/-- The source's reflected prefix after Lemma 29.5: coefficient one,
inverse-square-root normalization, and the literal range `0 < m <= M`. -/
def jutilaReflectedPrefixMoment (M : ℝ) (G : Finset ℝ) : ℝ :=
  sourceQuadratic (fun _ => (1 : ℂ)) 0 M (1 / 2) G

/-- A `T^delta`-separated finite set, matching Lemma 29.10 rather than the
weaker one-separated convention used elsewhere in the project. -/
def TPowerSeparated (G : Finset ℝ) (T delta : ℝ) : Prop :=
  ∀ g₁ ∈ G, ∀ g₂ ∈ G, g₁ ≠ g₂ → Real.rpow T delta ≤ |g₁ - g₂|

/-- Literal source range `G subset (0,T]`. -/
def InOpenClosedZeroT (G : Finset ℝ) (T : ℝ) : Prop :=
  ∀ g ∈ G, 0 < g ∧ g ≤ T

/-- Equation (29.40), with no rounding of the reflected length. -/
def sourceReflectionNumerator29_40 (T epsilon : ℝ) : ℝ :=
  Real.rpow T (1 + epsilon)

def reflectedLength29_40 (T epsilon N : ℝ) : ℝ :=
  sourceReflectionNumerator29_40 T epsilon / N

/-- A literal dyadic block in Lemmas 29.7--29.8 is exactly Jutila's
coefficient-one moment.  This theorem fixes both the sign convention and
the inverse-square-root normalization. -/
theorem sourceQuadratic_one_dyadic_eq_jutilaSecondMoment
    (X : ℝ) (G : Finset ℝ) :
    sourceQuadratic (fun _ => (1 : ℂ)) X (2 * X) (1 / 2) G =
      jutilaSecondMoment X G := by
  unfold sourceQuadratic sigmaCoefficient
  simp only [one_mul]
  change negativeJutilaSecondMoment X G = jutilaSecondMoment X G
  exact negativeJutilaSecondMoment_eq_jutilaSecondMoment X G

theorem jutilaReflectedPrefixMoment_nonneg (M : ℝ) (G : Finset ℝ) :
    0 ≤ jutilaReflectedPrefixMoment M G := by
  unfold jutilaReflectedPrefixMoment sourceQuadratic realGramQuadratic
  positivity

/-! ## The two source leaves before (29.41) -/

/-- The source's smooth step `Theta`. -/
def sourceTheta (x : ℝ) : ℝ :=
  if 0 < x then Real.exp (-x⁻¹) else 0

/-- The source's smooth transition `Upsilon`. -/
def sourceUpsilon (x : ℝ) : ℝ :=
  sourceTheta x / (sourceTheta x + sourceTheta (1 - x))

/-- The literal four-endpoint cutoff `w₀(α;a,b,c,d)` from p. 256. -/
def sourceWZero (alpha a b c d : ℝ) : ℝ :=
  sourceUpsilon ((alpha - a) / (b - a)) *
    sourceUpsilon ((d - alpha) / (d - c))

/-- The majorizing profile `h_g^+` from equation (29.18), including the
source endpoints `(1/2,1,2,5/2)`. -/
def sourceHPlus (g alpha : ℝ) : ℂ :=
  (sourceWZero alpha (1 / 2) 1 2 (5 / 2) : ℂ) *
    Complex.exp (Complex.I * (g * Real.log alpha))

/-- The finite form of `sum_n h_g^+(n/N)`; compact support restricts the
integer range to `N/2 < n <= 5N/2`. -/
def sourceHPlusSum (N g : ℝ) : ℂ :=
  ∑ n ∈ natRealIoc (N / 2) (5 * N / 2),
    sourceHPlus g ((n : ℝ) / N)

/-- The exact coefficient-one reflected Dirichlet prefix in Lemma 29.5. -/
def lemma295ReflectedPolynomial (M tau : ℝ) : ℂ :=
  ∑ m ∈ natRealIoc 0 M,
    (Real.rpow (m : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
      dirichletPhase m tau

/-- The literal truncated integral on the right of Lemma 29.5. -/
def lemma295CentralMajorant (N M g R : ℝ) : ℝ :=
  Real.sqrt N *
    ∫ t : ℝ in Set.Icc (-R) R,
      ‖lemma295ReflectedPolynomial M (g + t)‖ / (1 + t ^ 2)

/-- Lemma 29.5 exactly at its printed line on p. 261, with the implicit
constant and `O_A(T^{-A})` made explicit.  This is the first genuinely
analytic leaf behind (29.41): its proof is the contour shift and zeta
functional equation on pp. 261--263. -/
def Lemma295ApproximateFunctionalEquationExact : Prop :=
  ∀ delta epsilon A : ℝ, 0 < delta → 0 < epsilon → 0 < A →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T U N M g : ℝ),
        T₀ ≤ T → 0 < N → Real.rpow T delta ≤ |g| →
        |g| ≤ U → U ≤ T →
        U * Real.rpow T epsilon / N ≤ M →
        ‖sourceHPlusSum N g‖ ≤
          C * lemma295CentralMajorant N M g (Real.rpow T epsilon) +
            C * Real.rpow T (-A)

/-- Source-corrected form of Lemma 29.5 at the only truncation and length
range used in equation (29.40), namely `M = T^(1+epsilon)/N` and
`N ≤ T^(1+epsilon)`.  The latter is a specialization of the chapter-wide
polynomial length hypothesis (29.2).  The printed proof's residue and final
critical-line tail estimates are uniform at this scale.  Its printed statement
locally allows every larger `M`, but the displayed bound
`(MN)^(1/2) * ∫_{T^epsilon}^∞ t^{-j} dt` does not justify that stronger
quantifier.  The overbroad interface above is retained for audit history and
must not be used by the certified chain. -/
def Lemma295ApproximateFunctionalEquationExactM : Prop :=
  ∀ delta epsilon A : ℝ, 0 < delta → 0 < epsilon → 0 < A →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T U N g : ℝ),
        T₀ ≤ T → 0 < N →
        N ≤ sourceReflectionNumerator29_40 T epsilon →
        Real.rpow T delta ≤ |g| →
        |g| ≤ U → U ≤ T →
        ‖sourceHPlusSum N g‖ ≤
          C * lemma295CentralMajorant N
              (reflectedLength29_40 T epsilon N) g
              (Real.rpow T epsilon) +
            C * Real.rpow T (-A)

/-- Exact inequality extracted from Lemma 29.5 followed by the displayed
Cauchy/Lemma-29.6 step on p. 267.  The power-saving remainder is retained as
`C*T^(-A)`.  The conditions are the literal ones used in Lemma 29.10.

This is a separately named passage from
`Lemma295ApproximateFunctionalEquationExact`; it also includes the finite
majorization and Cauchy steps, so those steps are not silently identified
with the analytic lemma itself. -/
def Lemma295ReflectedPairMoment : Prop :=
  ∀ delta epsilon A : ℝ, 0 < delta → 0 < epsilon → 0 < A →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → N ≤ sourceReflectionNumerator29_40 T epsilon →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        jutilaSecondMoment N G ≤
          C * ((G.card : ℝ) * N +
            jutilaReflectedPrefixMoment
              (reflectedLength29_40 T epsilon N) G) +
          C * Real.rpow T (-A)

/-- Exact dyadic/transference conclusion used between Lemma 29.5 and
(29.41).  Its only analytic-number-theory parameter is the already isolated
reciprocal-prime statement (29.32).  All moments use coefficient one.

The printed proof divides `0 < m <= M` into the literal ranges
`M*2^(-j) < m <= M*2^(1-j)`, applies Lemma 29.7 with
`J=2^(j-1), J'=2^j`, and ends with Lemma 29.8.  An added `1+log M`
is unnecessary because the interface exposes the source's large-scale
threshold `M₀ >= 2`; hence the conclusion retains the printed `(log M)^3`
exactly. -/
def PrefixDyadicTransference29_41 : Prop :=
  DyadicPrimeReciprocalLower29_32 →
    ∃ C M₀ : ℝ, 0 < C ∧ 2 ≤ M₀ ∧
      ∀ (M : ℝ) (G : Finset ℝ), M₀ ≤ M →
        jutilaReflectedPrefixMoment M G ≤
          C * (Real.log M) ^ 3 * jutilaSecondMoment M G

/-! ## Certified recurrence weld with explicit error -/

/-- Equation (29.41) with every constant and the Lemma-29.5 remainder
visible.  Nothing from the final Heath--Brown theorem is assumed.

The proof below is only monotonicity and ring normalization: after the two
source leaves are supplied, there is no further analytic estimate hidden in
the passage to the recurrence. -/
theorem jutila_reflection_recurrence_29_41_explicit
    (h295 : Lemma295ReflectedPairMoment)
    {hprime : DyadicPrimeReciprocalLower29_32}
    (hdyadic : PrefixDyadicTransference29_41)
    {delta epsilon A : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (hA : 0 < A) :
    ∃ C₁ C₂ T₀ M₀ : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧ 2 ≤ T₀ ∧ 2 ≤ M₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → N ≤ sourceReflectionNumerator29_40 T epsilon →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        let M := reflectedLength29_40 T epsilon N
        M₀ ≤ M →
        jutilaSecondMoment N G ≤
          C₁ * (G.card : ℝ) * N +
          C₁ * C₂ * (Real.log M) ^ 3 *
            jutilaSecondMoment M G +
          C₁ * Real.rpow T (-A) := by
  obtain ⟨C₁, T₁, hC₁, hT₁, hafe⟩ :=
    h295 delta epsilon A hdelta hepsilon hA
  obtain ⟨C₂, M₀, hC₂, hM₀, hprefix⟩ := hdyadic hprime
  refine ⟨C₁, C₂, T₁, M₀, hC₁, hC₂, hT₁, hM₀, ?_⟩
  intro T N G hT hN hNupper hsep hheight
  dsimp only
  intro hM
  have hbase := hafe T N G hT hN hNupper hsep hheight
  have hpref := hprefix (reflectedLength29_40 T epsilon N) G hM
  have hmul := mul_le_mul_of_nonneg_left hpref hC₁.le
  calc
    jutilaSecondMoment N G ≤
        C₁ * ((G.card : ℝ) * N +
          jutilaReflectedPrefixMoment
            (reflectedLength29_40 T epsilon N) G) +
          C₁ * Real.rpow T (-A) := hbase
    _ ≤ C₁ * ((G.card : ℝ) * N +
          C₂ * (Real.log (reflectedLength29_40 T epsilon N)) ^ 3 *
            jutilaSecondMoment
              (reflectedLength29_40 T epsilon N) G) +
          C₁ * Real.rpow T (-A) := by
      gcongr
    _ = C₁ * (G.card : ℝ) * N +
          C₁ * C₂ *
            (Real.log (reflectedLength29_40 T epsilon N)) ^ 3 *
              jutilaSecondMoment
                (reflectedLength29_40 T epsilon N) G +
          C₁ * Real.rpow T (-A) := by ring

/-! ## Exact `k=2` companion used immediately after (29.41) -/

/-- The corrected large-scale `k=2` theorem, obtained directly from the
source prime estimate (29.32).  Its prime interval is literally

`[P/(4N^2), 2P/(4N^2)]`,

through `kTwoPrimeRange`; the premises `2 <= P/(4N^2)` and `2 <= P`
prevent the false small-scale formulation previously detected. -/
theorem jutila_kTwo_powering_of_29_32
    (h29_32 : DyadicPrimeReciprocalLower29_32) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N P : ℝ) (G : Finset ℝ), 0 < N →
        2 ≤ kTwoPrimeLower N P → 2 ≤ P →
        (kTwoPrimeRange N P).Nonempty →
        jutilaSecondMoment N G ^ 2 ≤
          C * (G.card : ℝ) ^ 2 * (Real.log P) ^ 3 *
            (maxProductMultiplicity N : ℝ) ^ 2 *
              jutilaSecondMoment P G := by
  exact jutila_lemma29Nine_kTwo_of_primeArithmeticLogBudgetLargeScale
    (kTwoPrimeArithmeticLogBudgetLargeScale_of_dyadicPrimeReciprocal
      (dyadicPrimeReciprocalInverseLogBound_of_29_32 h29_32))

end

end GuthMaynardJutilaReflection2941

#print axioms GuthMaynardJutilaReflection2941.sourceQuadratic_one_dyadic_eq_jutilaSecondMoment
#print axioms GuthMaynardJutilaReflection2941.jutila_reflection_recurrence_29_41_explicit
#print axioms GuthMaynardJutilaReflection2941.jutila_kTwo_powering_of_29_32
