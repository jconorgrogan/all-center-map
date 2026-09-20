import APWeightedZeroMassIntegrationScaffold

/-!
# CGL v2 at polylogarithmic conductor

This file is the deterministic adapter from the literal fixed-modulus family
estimate in `CGLMeshFormalization.CGLv2Theorem12AllCases` to the exact
primitive-inducer density proposition consumed by the MAP compact mesh.

There is no new analytic hypothesis here.  A primitive character is extracted
as one summand of the CGL ambient family at its actual conductor.  The three
conductor powers are absorbed by fixed powers of `log T`, and the already
certified primitive-inducer aggregation absorbs the resulting `Q^2` loss.
-/

namespace CGLMeshFormalization

open scoped BigOperators ENNReal
open Filter Asymptotics
open DirichletZeros ZeroDensityInterface
open MAPAPZeroDensityCert MAPGuthMaynard

noncomputable section

/-- Source-formula arithmetic at a general height.  This is the fixed-height
counterpart of `cgl_source_formula_to_map_height`: after separately bounding
the three conductor powers by `T^lambda`, both literal CGL terms fit under the
`30/13` curve. -/
theorem cgl_source_formula_to_fixed_thirty_thirteen
    {q : ℕ} [NeZero q]
    {T sigma sourceEta lambda targetEta C zeroCount : ℝ}
    (hT : 1 ≤ T) (hC : 0 ≤ C)
    (hsigma_high : sigma ≤ 1)
    (hqEta : Real.rpow (q : ℝ) sourceEta ≤ Real.rpow T lambda)
    (hqFirst : Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) ≤
      Real.rpow T lambda)
    (hqSecond : Real.rpow (q : ℝ)
        (densityCoeff * (1 - sigma)) ≤ Real.rpow T lambda)
    (hloss : sourceEta + 2 * lambda ≤ targetEta)
    (hdensity : zeroCount ≤
      C * Real.rpow ((q : ℝ) * T) sourceEta *
        (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow T (2 * (1 - sigma)) +
          Real.rpow ((q : ℝ) * T)
            (densityCoeff * (1 - sigma)))) :
    zeroCount ≤ (2 * C) * Real.rpow T
      (densityCoeff * (1 - sigma) + targetEta) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hmulEta :
      Real.rpow ((q : ℝ) * T) sourceEta =
        Real.rpow (q : ℝ) sourceEta * Real.rpow T sourceEta :=
    Real.mul_rpow hq0 hTpos.le
  have hmulSecond :
      Real.rpow ((q : ℝ) * T) (densityCoeff * (1 - sigma)) =
        Real.rpow (q : ℝ) (densityCoeff * (1 - sigma)) *
          Real.rpow T (densityCoeff * (1 - sigma)) :=
    Real.mul_rpow hq0 hTpos.le
  have honeMinus : 0 ≤ 1 - sigma := by linarith
  have hfirstCurve :
      2 * (1 - sigma) ≤ densityCoeff * (1 - sigma) := by
    unfold densityCoeff
    nlinarith
  have hfirst :
      Real.rpow ((q : ℝ) * T) sourceEta *
          (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow T (2 * (1 - sigma))) ≤
        Real.rpow T (densityCoeff * (1 - sigma) + targetEta) := by
    calc
      Real.rpow ((q : ℝ) * T) sourceEta *
          (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow T (2 * (1 - sigma))) =
        (Real.rpow (q : ℝ) sourceEta * Real.rpow T sourceEta) *
          (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow T (2 * (1 - sigma))) := by rw [hmulEta]
      _ ≤ (Real.rpow T lambda * Real.rpow T sourceEta) *
          (Real.rpow T lambda *
            Real.rpow T (densityCoeff * (1 - sigma))) := by
        have hleft := mul_le_mul_of_nonneg_right hqEta
          (Real.rpow_nonneg hTpos.le sourceEta)
        have hheight : Real.rpow T (2 * (1 - sigma)) ≤
            Real.rpow T (densityCoeff * (1 - sigma)) :=
          Real.rpow_le_rpow_of_exponent_le hT hfirstCurve
        have hright := mul_le_mul hqFirst hheight
          (Real.rpow_nonneg hTpos.le _)
          (Real.rpow_nonneg hTpos.le _)
        exact mul_le_mul hleft hright
          (mul_nonneg (Real.rpow_nonneg hq0 _)
            (Real.rpow_nonneg hTpos.le _))
          (mul_nonneg (Real.rpow_nonneg hTpos.le _)
            (Real.rpow_nonneg hTpos.le _))
      _ = Real.rpow T
          (densityCoeff * (1 - sigma) + (sourceEta + 2 * lambda)) := by
        rw [four_rpow_mul hTpos]
        congr 1
        ring
      _ ≤ Real.rpow T
          (densityCoeff * (1 - sigma) + targetEta) := by
        apply Real.rpow_le_rpow_of_exponent_le hT
        linarith
  have hsecond :
      Real.rpow ((q : ℝ) * T) sourceEta *
          Real.rpow ((q : ℝ) * T)
            (densityCoeff * (1 - sigma)) ≤
        Real.rpow T (densityCoeff * (1 - sigma) + targetEta) := by
    calc
      Real.rpow ((q : ℝ) * T) sourceEta *
          Real.rpow ((q : ℝ) * T)
            (densityCoeff * (1 - sigma)) =
        (Real.rpow (q : ℝ) sourceEta * Real.rpow T sourceEta) *
          (Real.rpow (q : ℝ) (densityCoeff * (1 - sigma)) *
            Real.rpow T (densityCoeff * (1 - sigma))) := by
        rw [hmulEta, hmulSecond]
      _ ≤ (Real.rpow T lambda * Real.rpow T sourceEta) *
          (Real.rpow T lambda *
            Real.rpow T (densityCoeff * (1 - sigma))) := by
        have hleft := mul_le_mul_of_nonneg_right hqEta
          (Real.rpow_nonneg hTpos.le sourceEta)
        have hright :
            Real.rpow (q : ℝ) (densityCoeff * (1 - sigma)) *
                Real.rpow T (densityCoeff * (1 - sigma)) ≤
              Real.rpow T lambda *
                Real.rpow T (densityCoeff * (1 - sigma)) :=
          mul_le_mul_of_nonneg_right hqSecond
            (Real.rpow_nonneg hTpos.le (densityCoeff * (1 - sigma)))
        exact mul_le_mul hleft hright
          (mul_nonneg (Real.rpow_nonneg hq0 _)
            (Real.rpow_nonneg hTpos.le _))
          (mul_nonneg (Real.rpow_nonneg hTpos.le _)
            (Real.rpow_nonneg hTpos.le _))
      _ = Real.rpow T
          (densityCoeff * (1 - sigma) + (sourceEta + 2 * lambda)) := by
        rw [four_rpow_mul hTpos]
        congr 1
        ring
      _ ≤ Real.rpow T
          (densityCoeff * (1 - sigma) + targetEta) := by
        apply Real.rpow_le_rpow_of_exponent_le hT
        linarith
  calc
    zeroCount ≤ C * Real.rpow ((q : ℝ) * T) sourceEta *
        (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow T (2 * (1 - sigma)) +
          Real.rpow ((q : ℝ) * T)
            (densityCoeff * (1 - sigma))) := hdensity
    _ = C *
        (Real.rpow ((q : ℝ) * T) sourceEta *
            (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
              Real.rpow T (2 * (1 - sigma))) +
          Real.rpow ((q : ℝ) * T) sourceEta *
            Real.rpow ((q : ℝ) * T)
              (densityCoeff * (1 - sigma))) := by ring
    _ ≤ C *
        (Real.rpow T (densityCoeff * (1 - sigma) + targetEta) +
          Real.rpow T (densityCoeff * (1 - sigma) + targetEta)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC
    _ = (2 * C) * Real.rpow T
        (densityCoeff * (1 - sigma) + targetEta) := by ring

/-! ## One source-faithful level below the all-cases line

The source obtains the all-cases assertion from equation (12.6), after taking
`q₁ = q`.  The specialization has four terms.  The first is exactly the
`q^(7/3(1-σ)) T^(2(1-σ))` term in the all-cases statement; the other
three have `qT` coefficients `9/4`, `B(1)`, and `30/13`.

The paper does not spell out the three elementary comparisons at this final
step.  They are certified below.  Thus `CGLv2Equation126AtQ` is a strictly
lower, named source boundary than `CGLv2Theorem12AllCases`, rather than a
renaming of its conclusion.
-/

/-- The coefficient `B` from CGL equation (12.6), specialized to
`β = log(qT)/log(qT) = 1` by the source choice `q₁ = q`. -/
def equation126BAtOne : ℝ :=
  (40 - Real.sqrt 160) / 12

/-- Exact `q₁=q` specialization of CGL v2 equation (12.6), with its four
literal source terms and a uniform epsilon-form expansion of `(qT)^{o(1)}`.

This is an explicit source leaf.  No inhabitant is asserted in this file.
-/
def CGLv2Equation126AtQ : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ C R0 : ℝ, 0 < C ∧ 2 ≤ R0 ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        1 ≤ T → 1 / 2 < sigma → sigma < 1 →
        R0 ≤ (q : ℝ) * T →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T) eta *
            (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
                Real.rpow T (2 * (1 - sigma)) +
              Real.rpow ((q : ℝ) * T)
                ((9 / 4) * (1 - sigma)) +
              Real.rpow ((q : ℝ) * T)
                (equation126BAtOne * (1 - sigma)) +
              Real.rpow ((q : ℝ) * T)
                (densityCoeff * (1 - sigma)))

/-- The radical coefficient in (12.6) at `q₁=q` is already below
`30/13`. -/
theorem equation126BAtOne_le_densityCoeff :
    equation126BAtOne ≤ densityCoeff := by
  have hsqrt0 : 0 ≤ Real.sqrt 160 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 160) ^ 2 = (160 : ℝ) := by
    norm_num
  have hrat0 : (0 : ℝ) ≤ 160 / 13 := by norm_num
  have hratSq : (160 / 13 : ℝ) ^ 2 < 160 := by norm_num
  have hsqrtLower : (160 / 13 : ℝ) ≤ Real.sqrt 160 := by
    by_contra h
    have hlt : Real.sqrt 160 < (160 / 13 : ℝ) := lt_of_not_ge h
    nlinarith
  unfold equation126BAtOne densityCoeff
  nlinarith

/-- The first deterministic source reduction below CGL v2 Theorem 1.2:
equation (12.6) at `q₁=q` implies the displayed all-cases line.

The factor `3` is the exact finite cost of putting the `9/4`, `B(1)`, and
`30/13` terms under one copy of the final `30/13` envelope. -/
theorem cgl_v2_all_cases_of_equation126_at_q
    (h126 : CGLv2Equation126AtQ) :
    CGLv2Theorem12AllCases := by
  intro eta heta
  obtain ⟨C, R0, hC, hR0, hsource⟩ := h126 eta heta
  refine ⟨3 * C, R0, by positivity, hR0, ?_⟩
  intro q _inst T sigma hT hsigmaLow hsigmaHigh hscale
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hRone : 1 ≤ (q : ℝ) * T := by
    nlinarith [mul_le_mul hqone hT zero_le_one (by norm_num : (0 : ℝ) ≤ q)]
  have honeMinus : 0 ≤ 1 - sigma := by linarith
  have hNine : (9 / 4 : ℝ) * (1 - sigma) ≤
      densityCoeff * (1 - sigma) := by
    unfold densityCoeff
    nlinarith
  have hB : equation126BAtOne * (1 - sigma) ≤
      densityCoeff * (1 - sigma) :=
    mul_le_mul_of_nonneg_right equation126BAtOne_le_densityCoeff honeMinus
  have hNinePow :
      Real.rpow ((q : ℝ) * T) ((9 / 4) * (1 - sigma)) ≤
        Real.rpow ((q : ℝ) * T)
          (densityCoeff * (1 - sigma)) :=
    Real.rpow_le_rpow_of_exponent_le hRone hNine
  have hBPow :
      Real.rpow ((q : ℝ) * T) (equation126BAtOne * (1 - sigma)) ≤
        Real.rpow ((q : ℝ) * T)
          (densityCoeff * (1 - sigma)) :=
    Real.rpow_le_rpow_of_exponent_le hRone hB
  let P := Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
    Real.rpow T (2 * (1 - sigma))
  let S := Real.rpow ((q : ℝ) * T)
    (densityCoeff * (1 - sigma))
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _)
      (Real.rpow_nonneg (zero_le_one.trans hT) _)
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg q)
      (zero_le_one.trans hT)) _
  have hterms :
      P + Real.rpow ((q : ℝ) * T) ((9 / 4) * (1 - sigma)) +
          Real.rpow ((q : ℝ) * T)
            (equation126BAtOne * (1 - sigma)) + S ≤
        3 * (P + S) := by
    dsimp [S] at hNinePow hBPow ⊢
    nlinarith
  have hraw := hsource q T sigma hT hsigmaLow hsigmaHigh hscale
  calc
    (ambientZeroCountAtLevel q sigma T : ℝ) ≤
        C * Real.rpow ((q : ℝ) * T) eta *
          (P + Real.rpow ((q : ℝ) * T) ((9 / 4) * (1 - sigma)) +
            Real.rpow ((q : ℝ) * T)
              (equation126BAtOne * (1 - sigma)) + S) := by
      simpa only [P, S] using hraw
    _ ≤ C * Real.rpow ((q : ℝ) * T) eta * (3 * (P + S)) := by
      exact mul_le_mul_of_nonneg_left hterms
        (mul_nonneg hC.le (Real.rpow_nonneg
          (mul_nonneg (Nat.cast_nonneg q) (zero_le_one.trans hT)) _))
    _ = (3 * C) * Real.rpow ((q : ℝ) * T) eta *
        (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow T (2 * (1 - sigma)) +
          Real.rpow ((q : ℝ) * T)
            (densityCoeff * (1 - sigma))) := by
      dsimp [P, S]
      ring

/-! ## Section 12 analytic leaves and deterministic assembly

The source proof of (12.6) first forms the general density estimate in
Section 12.4 from three independently named inputs: equation (12.4), Lemma
12.1, and the class-II fourth-moment estimate.  We expose those inputs below
using two real-valued class cardinalities.  They are the first genuinely
analytic leaves in this descent; all following assembly is finite inequality
and exponent arithmetic.
-/

/-- The four terms in the general Section 12.4 density estimate after the
source choice `q₁=q`.  They are written with the products expanded into
separate `q` and `T` powers, which is the form needed for the first
Ingham-intersection calculation. -/
def section124GeneralTermsAtQ (q : ℕ) (T sigma : ℝ) : ℝ :=
  Real.rpow (q : ℝ) ((4 / (1 + sigma)) * (1 - sigma)) *
      Real.rpow T ((3 / (1 + sigma)) * (1 - sigma)) +
    Real.rpow ((q : ℝ) * T)
      ((3 / (2 * sigma)) * (1 - sigma)) +
    Real.rpow ((q : ℝ) * T) ((18 - 20 * sigma) / 6) +
    Real.rpow ((q : ℝ) * T)
      ((15 / (3 + 5 * sigma)) * (1 - sigma))

/-- Equation (12.4): the ambient zero count is recovered, up to a uniform
subpower loss, from the two well-spaced class cardinalities. -/
def CGLv2Equation124
    (classI classII : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ C R0 : ℝ, 0 < C ∧ 2 ≤ R0 ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        1 ≤ T → 7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        R0 ≤ (q : ℝ) * T →
        0 ≤ classI q T sigma → 0 ≤ classII q T sigma →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T) eta *
            (classI q T sigma + classII q T sigma + 1)

/-- Lemma 12.1, specialized to `q₁=q`, as used for the class-I zeros in
Section 12.4. -/
def CGLv2Lemma121AtQ
    (classI : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ C R0 : ℝ, 0 < C ∧ 2 ≤ R0 ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        1 ≤ T → 7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        R0 ≤ (q : ℝ) * T →
        classI q T sigma ≤
          C * Real.rpow ((q : ℝ) * T) eta *
            section124GeneralTermsAtQ q T sigma

/-- The class-II conclusion of source lines 2162--2173, whose analytic input
is Montgomery's discrete fourth moment (Theorem 10.3). -/
def CGLv2ClassIIFourthMomentBound
    (classII : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ C R0 : ℝ, 0 < C ∧ 2 ≤ R0 ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        1 ≤ T → 7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        R0 ≤ (q : ℝ) * T →
        classII q T sigma ≤
          C * Real.rpow ((q : ℝ) * T) eta *
            Real.rpow ((q : ℝ) * T) (2 * (1 - sigma))

/-- The assembled general estimate displayed at source lines 2358--2370,
specialized to `q₁=q`. -/
def CGLv2Section124GeneralAtQ : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ C R0 : ℝ, 0 < C ∧ 2 ≤ R0 ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        1 ≤ T → 7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        R0 ≤ (q : ℝ) * T →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T) eta *
            section124GeneralTermsAtQ q T sigma

/-- On the central strip the class-II exponent `2(1-σ)` and the constant
term are both absorbed by the last term of Lemma 12.1. -/
theorem classII_and_one_le_two_mul_last_general_term
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 1 ≤ T) (hsigmaLow : 7 / 10 ≤ sigma)
    (hsigmaHigh : sigma ≤ 4 / 5) :
    Real.rpow ((q : ℝ) * T) (2 * (1 - sigma)) + 1 ≤
      2 * Real.rpow ((q : ℝ) * T)
        ((15 / (3 + 5 * sigma)) * (1 - sigma)) := by
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hRone : 1 ≤ (q : ℝ) * T := by
    nlinarith [mul_le_mul hqone hT zero_le_one (by norm_num : (0 : ℝ) ≤ q)]
  have hdenom : 0 < 3 + 5 * sigma := by linarith
  have honeMinus : 0 ≤ 1 - sigma := by linarith
  have hcoeff : (2 : ℝ) ≤ 15 / (3 + 5 * sigma) := by
    rw [le_div_iff₀ hdenom]
    linarith
  have hexp : 2 * (1 - sigma) ≤
      (15 / (3 + 5 * sigma)) * (1 - sigma) :=
    mul_le_mul_of_nonneg_right hcoeff honeMinus
  have hpow := Real.rpow_le_rpow_of_exponent_le hRone hexp
  have htargetOne : 1 ≤ Real.rpow ((q : ℝ) * T)
      ((15 / (3 + 5 * sigma)) * (1 - sigma)) := by
    apply Real.one_le_rpow hRone
    exact mul_nonneg (by positivity) honeMinus
  calc
    Real.rpow ((q : ℝ) * T) (2 * (1 - sigma)) + 1 ≤
        Real.rpow ((q : ℝ) * T)
            ((15 / (3 + 5 * sigma)) * (1 - sigma)) +
          Real.rpow ((q : ℝ) * T)
            ((15 / (3 + 5 * sigma)) * (1 - sigma)) :=
      add_le_add hpow htargetOne
    _ = 2 * Real.rpow ((q : ℝ) * T)
        ((15 / (3 + 5 * sigma)) * (1 - sigma)) := by ring

/-- Fully deterministic assembly of source equation (12.4), Lemma 12.1, and
the class-II fourth-moment conclusion.  The only hypotheses are the three
named analytic leaves above. -/
theorem section124_general_at_q_of_named_leaves
    (classI classII : ℕ → ℝ → ℝ → ℝ)
    (hI0 : ∀ q T sigma, 0 ≤ classI q T sigma)
    (hII0 : ∀ q T sigma, 0 ≤ classII q T sigma)
    (h124 : CGLv2Equation124 classI classII)
    (h121 : CGLv2Lemma121AtQ classI)
    (hII : CGLv2ClassIIFourthMomentBound classII) :
    CGLv2Section124GeneralAtQ := by
  intro eta heta
  have hethird : 0 < eta / 3 := by positivity
  obtain ⟨C0, R0, hC0, hR0, hzero⟩ := h124 (eta / 3) hethird
  obtain ⟨C1, R1, hC1, hR1, hclassI⟩ := h121 (eta / 3) hethird
  obtain ⟨C2, R2, hC2, hR2, hclassII⟩ := hII (eta / 3) hethird
  let M : ℝ := max C1 (max C2 1)
  let Rstar : ℝ := max R0 (max R1 R2)
  refine ⟨3 * C0 * M, Rstar, ?_, ?_, ?_⟩
  · dsimp [M]
    positivity
  · exact hR0.trans (le_max_left _ _)
  intro q _inst T sigma hT hsigmaLow hsigmaHigh hscale
  have hR0' : R0 ≤ (q : ℝ) * T :=
    (le_max_left _ _).trans hscale
  have hR1' : R1 ≤ (q : ℝ) * T :=
    ((le_max_left R1 R2).trans (le_max_right R0 (max R1 R2))).trans hscale
  have hR2' : R2 ≤ (q : ℝ) * T :=
    ((le_max_right R1 R2).trans (le_max_right R0 (max R1 R2))).trans hscale
  let R : ℝ := (q : ℝ) * T
  let G : ℝ := section124GeneralTermsAtQ q T sigma
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hR0nonneg : 0 ≤ R := by dsimp [R]; positivity
  have hRone : 1 ≤ R := by
    have hqone : (1 : ℝ) ≤ q := by
      exact_mod_cast (NeZero.one_le : 1 ≤ q)
    dsimp [R]
    nlinarith [mul_le_mul hqone hT zero_le_one hq0]
  have hepow : 1 ≤ Real.rpow R (eta / 3) :=
    Real.one_le_rpow hRone (by positivity)
  have hG0 : 0 ≤ G := by
    dsimp [G, section124GeneralTermsAtQ]
    positivity
  have hlast_le_G :
      Real.rpow R ((15 / (3 + 5 * sigma)) * (1 - sigma)) ≤ G := by
    have ha : 0 ≤ Real.rpow (q : ℝ)
        ((4 / (1 + sigma)) * (1 - sigma)) *
          Real.rpow T ((3 / (1 + sigma)) * (1 - sigma)) :=
      mul_nonneg (Real.rpow_nonneg hq0 _)
        (Real.rpow_nonneg (zero_le_one.trans hT) _)
    have hb : 0 ≤ Real.rpow ((q : ℝ) * T)
        ((3 / (2 * sigma)) * (1 - sigma)) :=
      Real.rpow_nonneg (mul_nonneg hq0 (zero_le_one.trans hT)) _
    have hc : 0 ≤ Real.rpow ((q : ℝ) * T)
        ((18 - 20 * sigma) / 6) :=
      Real.rpow_nonneg (mul_nonneg hq0 (zero_le_one.trans hT)) _
    dsimp [G, section124GeneralTermsAtQ, R]
    exact le_add_of_nonneg_left (add_nonneg (add_nonneg ha hb) hc)
  have hclassIIpow_le_G :
      Real.rpow R (2 * (1 - sigma)) ≤ G := by
    have hpair := classII_and_one_le_two_mul_last_general_term
      (q := q) (T := T) hT hsigmaLow hsigmaHigh
    have hlast0 : 0 ≤ Real.rpow R
        ((15 / (3 + 5 * sigma)) * (1 - sigma)) :=
      Real.rpow_nonneg hR0nonneg _
    have hpowLast : Real.rpow R (2 * (1 - sigma)) ≤
        Real.rpow R ((15 / (3 + 5 * sigma)) * (1 - sigma)) := by
      have hdenom : 0 < 3 + 5 * sigma := by linarith
      have honeMinus : 0 ≤ 1 - sigma := by linarith
      have hcoeff : (2 : ℝ) ≤ 15 / (3 + 5 * sigma) := by
        rw [le_div_iff₀ hdenom]
        linarith
      exact Real.rpow_le_rpow_of_exponent_le hRone
        (mul_le_mul_of_nonneg_right hcoeff honeMinus)
    exact hpowLast.trans hlast_le_G
  have hGone : 1 ≤ G := by
    have hlastOne : 1 ≤ Real.rpow R
        ((15 / (3 + 5 * sigma)) * (1 - sigma)) := by
      apply Real.one_le_rpow hRone
      have : 0 ≤ 1 - sigma := by linarith
      positivity
    exact hlastOne.trans hlast_le_G
  have hM1 : C1 ≤ M := le_max_left _ _
  have hM2 : C2 ≤ M :=
    (le_max_left C2 1).trans (le_max_right C1 (max C2 1))
  have hMone : 1 ≤ M :=
    (le_max_right C2 1).trans (le_max_right C1 (max C2 1))
  have hI := hclassI q T sigma hT hsigmaLow hsigmaHigh hR1'
  have hII' := hclassII q T sigma hT hsigmaLow hsigmaHigh hR2'
  have hIbound : classI q T sigma ≤ M * Real.rpow R (eta / 3) * G := by
    calc
      classI q T sigma ≤ C1 * Real.rpow R (eta / 3) * G := by
        simpa only [R, G] using hI
      _ ≤ M * Real.rpow R (eta / 3) * G := by
        gcongr
  have hIIbound : classII q T sigma ≤
      M * Real.rpow R (eta / 3) * G := by
    calc
      classII q T sigma ≤ C2 * Real.rpow R (eta / 3) *
          Real.rpow R (2 * (1 - sigma)) := by
        simpa only [R] using hII'
      _ ≤ C2 * Real.rpow R (eta / 3) * G := by
        exact mul_le_mul_of_nonneg_left hclassIIpow_le_G
          (mul_nonneg hC2.le (Real.rpow_nonneg hR0nonneg _))
      _ ≤ M * Real.rpow R (eta / 3) * G := by gcongr
  have honeBound : (1 : ℝ) ≤ M * Real.rpow R (eta / 3) * G := by
    nlinarith [mul_le_mul hMone hepow zero_le_one (by positivity : 0 ≤ M),
      mul_le_mul (mul_le_mul hMone hepow zero_le_one (by positivity : 0 ≤ M))
        hGone zero_le_one (by positivity : 0 ≤ M * Real.rpow R (eta / 3))]
  have hinner : classI q T sigma + classII q T sigma + 1 ≤
      3 * (M * Real.rpow R (eta / 3) * G) := by linarith
  have hzero' := hzero q T sigma hT hsigmaLow hsigmaHigh hR0'
    (hI0 q T sigma) (hII0 q T sigma)
  have htwoThird : 2 * (eta / 3) ≤ eta := by linarith
  have hpowLoss : Real.rpow R (2 * (eta / 3)) ≤ Real.rpow R eta :=
    Real.rpow_le_rpow_of_exponent_le hRone htwoThird
  have hpowEq : Real.rpow R (eta / 3) * Real.rpow R (eta / 3) =
      Real.rpow R (2 * (eta / 3)) := by
    calc
      Real.rpow R (eta / 3) * Real.rpow R (eta / 3) =
          Real.rpow R (eta / 3 + eta / 3) :=
        (Real.rpow_add (zero_lt_one.trans_le hRone) _ _).symm
      _ = Real.rpow R (2 * (eta / 3)) := by
        congr 1
        ring
  calc
    (ambientZeroCountAtLevel q sigma T : ℝ) ≤
        C0 * Real.rpow R (eta / 3) *
          (classI q T sigma + classII q T sigma + 1) := by
      simpa only [R] using hzero'
    _ ≤ C0 * Real.rpow R (eta / 3) *
        (3 * (M * Real.rpow R (eta / 3) * G)) := by
      gcongr
    _ = (3 * C0 * M) * Real.rpow R (2 * (eta / 3)) * G := by
      rw [← hpowEq]
      ring
    _ ≤ (3 * C0 * M) * Real.rpow R eta * G := by
      gcongr
    _ = (3 * C0 * M) * Real.rpow ((q : ℝ) * T) eta *
        section124GeneralTermsAtQ q T sigma := by rfl

/-! ## Ingham intersection: Section 12.4 to equation (12.6) -/

/-- The fixed-modulus family Ingham estimate quoted as equation (1.4) in the
CGL paper.  This is a published analytic source leaf, with the subpower term
expanded uniformly. -/
def CGLv2InghamEquation14 : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ C R0 : ℝ, 0 < C ∧ 2 ≤ R0 ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        1 ≤ T → 1 / 2 < sigma → sigma < 1 →
        R0 ≤ (q : ℝ) * T →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T) eta *
            Real.rpow ((q : ℝ) * T)
              ((3 / (2 - sigma)) * (1 - sigma))

/-- The fixed-modulus family Huxley estimate quoted as equation (1.5) in the
CGL paper. -/
def CGLv2HuxleyEquation15 : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ C R0 : ℝ, 0 < C ∧ 2 ≤ R0 ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        1 ≤ T → 1 / 2 < sigma → sigma < 1 →
        R0 ≤ (q : ℝ) * T →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T) eta *
            Real.rpow ((q : ℝ) * T)
              ((3 / (3 * sigma - 1)) * (1 - sigma))

/-- The minimum of two positive quantities is bounded by every weighted
geometric interpolation between them. -/
theorem min_le_weighted_geometric_mean
    {A B theta : ℝ} (hA : 0 < A) (hB : 0 < B)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    min A B ≤ Real.rpow A theta * Real.rpow B (1 - theta) := by
  by_cases hAB : A ≤ B
  · rw [min_eq_left hAB]
    calc
      A = Real.rpow A 1 := (Real.rpow_one A).symm
      _ = Real.rpow A (theta + (1 - theta)) := by
        congr 1
        ring
      _ = Real.rpow A theta * Real.rpow A (1 - theta) :=
        Real.rpow_add hA _ _
      _ ≤ Real.rpow A theta * Real.rpow B (1 - theta) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hA.le hAB (sub_nonneg.mpr htheta1))
          (Real.rpow_nonneg hA.le _)
  · have hBA : B ≤ A := le_of_not_ge hAB
    rw [min_eq_right hBA]
    calc
      B = Real.rpow B 1 := (Real.rpow_one B).symm
      _ = Real.rpow B (theta + (1 - theta)) := by
        congr 1
        ring
      _ = Real.rpow B theta * Real.rpow B (1 - theta) :=
        Real.rpow_add hB _ _
      _ ≤ Real.rpow A theta * Real.rpow B (1 - theta) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hB.le hBA htheta0)
          (Real.rpow_nonneg hB.le _)

/-- Four-term scalar form of the source's term-by-term intersection with
Ingham. -/
theorem min_four_sum_le_sum_mins
    {a b c d i : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hi : 0 ≤ i) :
    min (a + b + c + d) i ≤
      min a i + min b i + min c i + min d i := by
  by_cases hai : i ≤ a
  · have hisum : i ≤ a + b + c + d := by linarith
    rw [min_eq_right hisum, min_eq_right hai]
    have hmb : 0 ≤ min b i := le_min hb hi
    have hmc : 0 ≤ min c i := le_min hc hi
    have hmd : 0 ≤ min d i := le_min hd hi
    linarith
  by_cases hbi : i ≤ b
  · have hisum : i ≤ a + b + c + d := by linarith
    rw [min_eq_right hisum, min_eq_right hbi]
    have hma : 0 ≤ min a i := le_min ha hi
    have hmc : 0 ≤ min c i := le_min hc hi
    have hmd : 0 ≤ min d i := le_min hd hi
    linarith
  by_cases hci : i ≤ c
  · have hisum : i ≤ a + b + c + d := by linarith
    rw [min_eq_right hisum, min_eq_right hci]
    have hma : 0 ≤ min a i := le_min ha hi
    have hmb : 0 ≤ min b i := le_min hb hi
    have hmd : 0 ≤ min d i := le_min hd hi
    linarith
  by_cases hdi : i ≤ d
  · have hisum : i ≤ a + b + c + d := by linarith
    rw [min_eq_right hisum, min_eq_right hdi]
    have hma : 0 ≤ min a i := le_min ha hi
    have hmb : 0 ≤ min b i := le_min hb hi
    have hmc : 0 ≤ min c i := le_min hc hi
    linarith
  · have hai' : a ≤ i := le_of_not_ge hai
    have hbi' : b ≤ i := le_of_not_ge hbi
    have hci' : c ≤ i := le_of_not_ge hci
    have hdi' : d ≤ i := le_of_not_ge hdi
    rw [min_eq_left hai', min_eq_left hbi', min_eq_left hci',
      min_eq_left hdi']
    exact min_le_left _ _

/-- The first general-density term and Ingham interpolate exactly to the
`q^(7/3(1-σ)) T^(2(1-σ))` term.  The interpolation weight is
`theta=(1+σ)/3`; both exponent coordinates are exact identities. -/
theorem first_general_term_intersect_ingham_le
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 1 ≤ T) (hsigmaLow : 7 / 10 ≤ sigma)
    (hsigmaHigh : sigma ≤ 4 / 5) :
    min
      (Real.rpow (q : ℝ) ((4 / (1 + sigma)) * (1 - sigma)) *
        Real.rpow T ((3 / (1 + sigma)) * (1 - sigma)))
      (Real.rpow ((q : ℝ) * T)
        ((3 / (2 - sigma)) * (1 - sigma))) ≤
      Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
        Real.rpow T (2 * (1 - sigma)) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  let theta : ℝ := (1 + sigma) / 3
  have htheta0 : 0 ≤ theta := by dsimp [theta]; linarith
  have htheta1 : theta ≤ 1 := by dsimp [theta]; linarith
  let A := Real.rpow (q : ℝ) ((4 / (1 + sigma)) * (1 - sigma)) *
    Real.rpow T ((3 / (1 + sigma)) * (1 - sigma))
  let I := Real.rpow ((q : ℝ) * T)
    ((3 / (2 - sigma)) * (1 - sigma))
  have hA : 0 < A := by dsimp [A]; positivity
  have hI : 0 < I := by dsimp [I]; positivity
  have hden1 : 1 + sigma ≠ 0 := by linarith
  have hden2 : 2 - sigma ≠ 0 := by linarith
  have hqexp :
      ((4 / (1 + sigma)) * (1 - sigma)) * theta +
          ((3 / (2 - sigma)) * (1 - sigma)) * (1 - theta) =
        (7 / 3) * (1 - sigma) := by
    dsimp [theta]
    field_simp [hden1, hden2]
    ring
  have hTexp :
      ((3 / (1 + sigma)) * (1 - sigma)) * theta +
          ((3 / (2 - sigma)) * (1 - sigma)) * (1 - theta) =
        2 * (1 - sigma) := by
    dsimp [theta]
    field_simp [hden1, hden2]
    ring
  have hgeom : Real.rpow A theta * Real.rpow I (1 - theta) =
      Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
        Real.rpow T (2 * (1 - sigma)) := by
    have hq0 : 0 ≤ (q : ℝ) := hqpos.le
    have hT0 : 0 ≤ T := hTpos.le
    have hmul0 : 0 ≤ (q : ℝ) * T := mul_nonneg hq0 hT0
    dsimp [A, I]
    rw [Real.mul_rpow (Real.rpow_nonneg hq0 _)
      (Real.rpow_nonneg hT0 _)]
    rw [Real.mul_rpow hq0 hT0]
    rw [Real.mul_rpow (Real.rpow_nonneg hq0 _)
      (Real.rpow_nonneg hT0 _)]
    rw [← Real.rpow_mul hq0, ← Real.rpow_mul hT0,
      ← Real.rpow_mul hq0, ← Real.rpow_mul hT0]
    rw [mul_mul_mul_comm]
    rw [← Real.rpow_add hqpos, ← Real.rpow_add hTpos, hqexp, hTexp]
  exact (min_le_weighted_geometric_mean hA hI htheta0 htheta1).trans_eq hgeom

/-- At `β=1`, the equation-(12.6) radical coefficient lies above `9/4` as
well as below `30/13`. -/
theorem nine_fourths_le_equation126BAtOne :
    (9 / 4 : ℝ) ≤ equation126BAtOne := by
  have hsqrt0 : 0 ≤ Real.sqrt 160 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 160) ^ 2 = (160 : ℝ) := by norm_num
  have hsqrtUpper : Real.sqrt 160 ≤ 13 := by nlinarith
  unfold equation126BAtOne
  linarith

/-- The remaining three terms of the general estimate fit respectively below
the `9/4`, `B(1)`, and `30/13` terms of equation (12.6). -/
theorem remaining_general_terms_le_equation126_terms
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 1 ≤ T) (hsigmaLow : 7 / 10 ≤ sigma)
    (hsigmaHigh : sigma ≤ 4 / 5) :
    Real.rpow ((q : ℝ) * T)
        ((3 / (2 * sigma)) * (1 - sigma)) ≤
          Real.rpow ((q : ℝ) * T) ((9 / 4) * (1 - sigma)) ∧
    Real.rpow ((q : ℝ) * T) ((18 - 20 * sigma) / 6) ≤
          Real.rpow ((q : ℝ) * T)
            (equation126BAtOne * (1 - sigma)) ∧
    Real.rpow ((q : ℝ) * T)
        ((15 / (3 + 5 * sigma)) * (1 - sigma)) ≤
          Real.rpow ((q : ℝ) * T)
            (densityCoeff * (1 - sigma)) := by
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hRone : 1 ≤ (q : ℝ) * T := by
    nlinarith [mul_le_mul hqone hT zero_le_one (by norm_num : (0 : ℝ) ≤ q)]
  have honeMinus : 0 ≤ 1 - sigma := by linarith
  have hspos : 0 < sigma := by linarith
  have hdenlast : 0 < 3 + 5 * sigma := by linarith
  have h2exp : (3 / (2 * sigma)) * (1 - sigma) ≤
      (9 / 4) * (1 - sigma) := by
    apply mul_le_mul_of_nonneg_right _ honeMinus
    rw [div_le_iff₀ (by positivity : 0 < 2 * sigma)]
    nlinarith
  have h3toNine : (18 - 20 * sigma) / 6 ≤
      (9 / 4) * (1 - sigma) := by linarith
  have hNineToB : (9 / 4 : ℝ) * (1 - sigma) ≤
      equation126BAtOne * (1 - sigma) :=
    mul_le_mul_of_nonneg_right nine_fourths_le_equation126BAtOne honeMinus
  have h4exp : (15 / (3 + 5 * sigma)) * (1 - sigma) ≤
      densityCoeff * (1 - sigma) := by
    apply mul_le_mul_of_nonneg_right _ honeMinus
    unfold densityCoeff
    rw [div_le_iff₀ hdenlast]
    nlinarith
  exact ⟨Real.rpow_le_rpow_of_exponent_le hRone h2exp,
    Real.rpow_le_rpow_of_exponent_le hRone (h3toNine.trans hNineToB),
    Real.rpow_le_rpow_of_exponent_le hRone h4exp⟩

/-- Source equation (12.6), specialized to `q₁=q`, from the nearest named
source inputs.  The central strip uses the general Section 12.4 estimate and
the exact weighted interpolation with Ingham.  The two outer strips use the
quoted Ingham and Huxley equations directly, exactly as source line 2109 says.
-/
theorem equation126_at_q_of_section12_and_classical
    (hgeneral : CGLv2Section124GeneralAtQ)
    (hIngham : CGLv2InghamEquation14)
    (hHuxley : CGLv2HuxleyEquation15) :
    CGLv2Equation126AtQ := by
  intro eta heta
  have hhalf : 0 < eta / 2 := by positivity
  obtain ⟨CG, RG, hCG, hRG, hGsource⟩ := hgeneral (eta / 2) hhalf
  obtain ⟨CI, RI, hCI, hRI, hIsource⟩ := hIngham (eta / 2) hhalf
  obtain ⟨CH, RH, hCH, hRH, hHsource⟩ := hHuxley (eta / 2) hhalf
  let C : ℝ := max CG (max CI CH)
  let Rstar : ℝ := max RG (max RI RH)
  refine ⟨C, Rstar, ?_, ?_, ?_⟩
  · dsimp [C]
    positivity
  · exact hRG.trans (le_max_left _ _)
  intro q _inst T sigma hT hsigmaLow hsigmaHigh hscale
  have hRG' : RG ≤ (q : ℝ) * T := (le_max_left _ _).trans hscale
  have hRI' : RI ≤ (q : ℝ) * T :=
    ((le_max_left RI RH).trans (le_max_right RG (max RI RH))).trans hscale
  have hRH' : RH ≤ (q : ℝ) * T :=
    ((le_max_right RI RH).trans (le_max_right RG (max RI RH))).trans hscale
  let R : ℝ := (q : ℝ) * T
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hRone : 1 ≤ R := by
    dsimp [R]
    nlinarith [mul_le_mul hqone hT zero_le_one hq0]
  have hpowLoss : Real.rpow R (eta / 2) ≤ Real.rpow R eta :=
    Real.rpow_le_rpow_of_exponent_le hRone (by linarith)
  have hConeG : CG ≤ C := le_max_left _ _
  have hConeI : CI ≤ C :=
    (le_max_left CI CH).trans (le_max_right CG (max CI CH))
  have hConeH : CH ≤ C :=
    (le_max_right CI CH).trans (le_max_right CG (max CI CH))
  have hC0 : 0 ≤ C := hCG.le.trans hConeG
  have hRhalf0 : 0 ≤ Real.rpow R (eta / 2) :=
    Real.rpow_nonneg hR0 _
  have hReta0 : 0 ≤ Real.rpow R eta := Real.rpow_nonneg hR0 _
  let P := Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
    Real.rpow T (2 * (1 - sigma))
  let S9 := Real.rpow R ((9 / 4) * (1 - sigma))
  let SB := Real.rpow R (equation126BAtOne * (1 - sigma))
  let S30 := Real.rpow R (densityCoeff * (1 - sigma))
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hS90 : 0 ≤ S9 := Real.rpow_nonneg hR0 _
  have hSB0 : 0 ≤ SB := Real.rpow_nonneg hR0 _
  have hS300 : 0 ≤ S30 := Real.rpow_nonneg hR0 _
  have htarget0 : 0 ≤ P + S9 + SB + S30 := by positivity
  by_cases hlow : sigma < 7 / 10
  · have hdenom : 0 < 2 - sigma := by linarith
    have hcoeff : 3 / (2 - sigma) ≤ densityCoeff := by
      unfold densityCoeff
      rw [div_le_iff₀ hdenom]
      nlinarith
    have hexp : (3 / (2 - sigma)) * (1 - sigma) ≤
        densityCoeff * (1 - sigma) :=
      mul_le_mul_of_nonneg_right hcoeff (by linarith)
    have hIpow : Real.rpow R ((3 / (2 - sigma)) * (1 - sigma)) ≤ S30 := by
      dsimp [S30]
      exact Real.rpow_le_rpow_of_exponent_le hRone hexp
    have hraw := hIsource q T sigma hT hsigmaLow hsigmaHigh hRI'
    calc
      (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          CI * Real.rpow R (eta / 2) *
            Real.rpow R ((3 / (2 - sigma)) * (1 - sigma)) := by
        simpa only [R] using hraw
      _ ≤ C * Real.rpow R (eta / 2) * S30 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hConeI hRhalf0) hIpow
          (Real.rpow_nonneg hR0 _) (mul_nonneg hC0 hRhalf0)
      _ ≤ C * Real.rpow R eta * S30 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowLoss hC0) hS300
      _ ≤ C * Real.rpow R eta * (P + S9 + SB + S30) := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg hC0 hReta0)
      _ = C * Real.rpow ((q : ℝ) * T) eta *
          (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
              Real.rpow T (2 * (1 - sigma)) +
            Real.rpow ((q : ℝ) * T) ((9 / 4) * (1 - sigma)) +
            Real.rpow ((q : ℝ) * T)
              (equation126BAtOne * (1 - sigma)) +
            Real.rpow ((q : ℝ) * T)
              (densityCoeff * (1 - sigma))) := by rfl
  by_cases hhigh : 4 / 5 < sigma
  · have hdenom : 0 < 3 * sigma - 1 := by linarith
    have hcoeff : 3 / (3 * sigma - 1) ≤ densityCoeff := by
      unfold densityCoeff
      rw [div_le_iff₀ hdenom]
      nlinarith
    have hexp : (3 / (3 * sigma - 1)) * (1 - sigma) ≤
        densityCoeff * (1 - sigma) :=
      mul_le_mul_of_nonneg_right hcoeff (by linarith)
    have hHpow : Real.rpow R ((3 / (3 * sigma - 1)) * (1 - sigma)) ≤
        S30 := by
      dsimp [S30]
      exact Real.rpow_le_rpow_of_exponent_le hRone hexp
    have hraw := hHsource q T sigma hT hsigmaLow hsigmaHigh hRH'
    calc
      (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          CH * Real.rpow R (eta / 2) *
            Real.rpow R ((3 / (3 * sigma - 1)) * (1 - sigma)) := by
        simpa only [R] using hraw
      _ ≤ C * Real.rpow R (eta / 2) * S30 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hConeH hRhalf0) hHpow
          (Real.rpow_nonneg hR0 _) (mul_nonneg hC0 hRhalf0)
      _ ≤ C * Real.rpow R eta * S30 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowLoss hC0) hS300
      _ ≤ C * Real.rpow R eta * (P + S9 + SB + S30) := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg hC0 hReta0)
      _ = C * Real.rpow ((q : ℝ) * T) eta *
          (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
              Real.rpow T (2 * (1 - sigma)) +
            Real.rpow ((q : ℝ) * T) ((9 / 4) * (1 - sigma)) +
            Real.rpow ((q : ℝ) * T)
              (equation126BAtOne * (1 - sigma)) +
            Real.rpow ((q : ℝ) * T)
              (densityCoeff * (1 - sigma))) := by rfl
  · have hsigmaCentralLow : 7 / 10 ≤ sigma := le_of_not_gt hlow
    have hsigmaCentralHigh : sigma ≤ 4 / 5 := le_of_not_gt hhigh
    let a := Real.rpow (q : ℝ)
        ((4 / (1 + sigma)) * (1 - sigma)) *
      Real.rpow T ((3 / (1 + sigma)) * (1 - sigma))
    let b := Real.rpow R ((3 / (2 * sigma)) * (1 - sigma))
    let c := Real.rpow R ((18 - 20 * sigma) / 6)
    let d := Real.rpow R ((15 / (3 + 5 * sigma)) * (1 - sigma))
    let i := Real.rpow R ((3 / (2 - sigma)) * (1 - sigma))
    let G := a + b + c + d
    let F := C * Real.rpow R (eta / 2)
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have hb0 : 0 ≤ b := Real.rpow_nonneg hR0 _
    have hc0 : 0 ≤ c := Real.rpow_nonneg hR0 _
    have hd0 : 0 ≤ d := Real.rpow_nonneg hR0 _
    have hi0 : 0 ≤ i := Real.rpow_nonneg hR0 _
    have hF0 : 0 ≤ F := by dsimp [F]; positivity
    have hG0 : 0 ≤ G := by dsimp [G]; positivity
    have hrawG := hGsource q T sigma hT hsigmaCentralLow
      hsigmaCentralHigh hRG'
    have hrawI := hIsource q T sigma hT hsigmaLow hsigmaHigh hRI'
    have hZG : (ambientZeroCountAtLevel q sigma T : ℝ) ≤ F * G := by
      calc
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
            CG * Real.rpow R (eta / 2) * G := by
          simpa only [R, G, a, b, c, d, section124GeneralTermsAtQ] using hrawG
        _ ≤ C * Real.rpow R (eta / 2) * G := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hConeG hRhalf0) hG0
        _ = F * G := by rfl
    have hZI : (ambientZeroCountAtLevel q sigma T : ℝ) ≤ F * i := by
      calc
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
            CI * Real.rpow R (eta / 2) * i := by
          simpa only [R, i] using hrawI
        _ ≤ C * Real.rpow R (eta / 2) * i := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hConeI hRhalf0) hi0
        _ = F * i := by rfl
    have hZmin : (ambientZeroCountAtLevel q sigma T : ℝ) ≤
        F * min G i := by
      have := le_min hZG hZI
      rw [mul_min_of_nonneg G i hF0]
      exact this
    have hsplit : min G i ≤
        min a i + min b i + min c i + min d i := by
      dsimp [G]
      exact min_four_sum_le_sum_mins ha0 hb0 hc0 hd0 hi0
    have haP : min a i ≤ P := by
      dsimp [a, i, P, R]
      exact first_general_term_intersect_ingham_le hT
        hsigmaCentralLow hsigmaCentralHigh
    obtain ⟨hbS9, hcSB, hdS30⟩ :=
      remaining_general_terms_le_equation126_terms
        (q := q) (T := T) hT hsigmaCentralLow hsigmaCentralHigh
    have hb' : min b i ≤ S9 := (min_le_left _ _).trans (by
      simpa only [b, S9, R] using hbS9)
    have hc' : min c i ≤ SB := (min_le_left _ _).trans (by
      simpa only [c, SB, R] using hcSB)
    have hd' : min d i ≤ S30 := (min_le_left _ _).trans (by
      simpa only [d, S30, R] using hdS30)
    have hminTarget : min G i ≤ P + S9 + SB + S30 :=
      hsplit.trans (add_le_add (add_le_add (add_le_add haP hb') hc') hd')
    calc
      (ambientZeroCountAtLevel q sigma T : ℝ) ≤ F * min G i := hZmin
      _ ≤ F * (P + S9 + SB + S30) :=
        mul_le_mul_of_nonneg_left hminTarget hF0
      _ ≤ C * Real.rpow R eta * (P + S9 + SB + S30) := by
        dsimp [F]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowLoss hC0) htarget0
      _ = C * Real.rpow ((q : ℝ) * T) eta *
          (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
              Real.rpow T (2 * (1 - sigma)) +
            Real.rpow ((q : ℝ) * T) ((9 / 4) * (1 - sigma)) +
            Real.rpow ((q : ℝ) * T)
              (equation126BAtOne * (1 - sigma)) +
            Real.rpow ((q : ℝ) * T)
              (densityCoeff * (1 - sigma))) := by rfl

/-- Full deterministic descent from the named Section 12 and classical source
leaves to the CGL v2 all-cases statement. -/
theorem cgl_v2_all_cases_of_section12_named_leaves
    (classI classII : ℕ → ℝ → ℝ → ℝ)
    (hI0 : ∀ q T sigma, 0 ≤ classI q T sigma)
    (hII0 : ∀ q T sigma, 0 ≤ classII q T sigma)
    (h124 : CGLv2Equation124 classI classII)
    (h121 : CGLv2Lemma121AtQ classI)
    (hII : CGLv2ClassIIFourthMomentBound classII)
    (hIngham : CGLv2InghamEquation14)
    (hHuxley : CGLv2HuxleyEquation15) :
    CGLv2Theorem12AllCases :=
  cgl_v2_all_cases_of_equation126_at_q
    (equation126_at_q_of_section12_and_classical
      (section124_general_at_q_of_named_leaves
        classI classII hI0 hII0 h124 h121 hII)
      hIngham hHuxley)

/-- Weak fixed-character compact-strip consequence of CGL v2.  This is the
smallest reusable analytic boundary needed before the finite primitive-inducer
aggregation: one primitive character, its actual conductor, and only
polylogarithmic conductor range. -/
theorem fixedPrimitivePolylogDensity_of_cgl_v2
    (hCGL : CGLv2Theorem12AllCases) :
    CGLPolylogBypass.FixedPrimitivePolylogDensity := by
  intro K delta eta hK hdelta heta
  let sourceEta : ℝ := eta / 4
  let lambda : ℝ := eta / 8
  have hsourceEta : 0 < sourceEta := by dsimp [sourceEta]; positivity
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  obtain ⟨C, Rsource, hC, hRsource, hsource⟩ :=
    hCGL sourceEta hsourceEta
  have hpoly := fixed_polylog_envelopes_eventually_absorbed
    K sourceEta lambda hlambda
  obtain ⟨Rpoly, hRpoly⟩ := Filter.eventually_atTop.1 hpoly
  let T₀ : ℝ := max (Real.exp 1) (max Rsource Rpoly)
  refine ⟨2 * C, T₀, by positivity, ?_, ?_⟩
  · dsimp [T₀]
    exact hRsource.trans
      ((le_max_left Rsource Rpoly).trans
        (le_max_right (Real.exp 1) (max Rsource Rpoly)))
  · intro T Q sigma hT hQ hsigmaLow hsigmaHigh r _inst chi _hprim hrQ
    have hTexp : Real.exp 1 ≤ T := (le_max_left _ _).trans hT
    have hTsource : Rsource ≤ T :=
      ((le_max_left Rsource Rpoly).trans
        (le_max_right (Real.exp 1) (max Rsource Rpoly))).trans hT
    have hTpoly : Rpoly ≤ T :=
      ((le_max_right Rsource Rpoly).trans
        (le_max_right (Real.exp 1) (max Rsource Rpoly))).trans hT
    have hTone : 1 ≤ T := by
      have : (1 : ℝ) ≤ Real.exp 1 := (Real.one_le_exp zero_le_one)
      exact this.trans hTexp
    have hlog : 1 ≤ Real.log T := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hTexp
    have hsigmaHalf : 1 / 2 ≤ sigma := by linarith
    have hsigmaOne : sigma ≤ 1 := hsigmaHigh.trans (by norm_num)
    have hrpoly : (r : ℝ) ≤ Real.rpow (Real.log T) K := by
      exact (by exact_mod_cast hrQ : (r : ℝ) ≤ Q) |>.trans hQ
    obtain ⟨hEtaAbsorb, hFirstAbsorb, hSecondAbsorb⟩ := hRpoly T hTpoly
    obtain ⟨hqEta, hqFirst, hqSecond⟩ :=
      polylog_conductor_powers_fit hK.le hsourceEta.le hlog hrpoly
        hsigmaHalf hsigmaOne hEtaAbsorb hFirstAbsorb hSecondAbsorb
    have hrone : (1 : ℝ) ≤ r := by
      exact_mod_cast (NeZero.one_le : 1 ≤ r)
    have hscale : Rsource ≤ (r : ℝ) * T := by
      calc
        Rsource ≤ T := hTsource
        _ = 1 * T := by ring
        _ ≤ (r : ℝ) * T :=
          mul_le_mul_of_nonneg_right hrone (zero_le_one.trans hTone)
    have hraw := hsource r T sigma hTone (by linarith) (by linarith) hscale
    have hsingleNat :=
      MAPAPWeightedZeroMassIntegration.dirichletZeroCount_le_ambientZeroCountAtLevel
        chi sigma T
    have hsingle : (dirichletZeroCount chi sigma T : ℝ) ≤
        (ambientZeroCountAtLevel r sigma T : ℝ) := by
      exact_mod_cast hsingleNat
    apply cgl_source_formula_to_fixed_thirty_thirteen
      hTone hC.le hsigmaOne hqEta hqFirst hqSecond
      (targetEta := eta)
    · dsimp [sourceEta, lambda]
      linarith
    · exact hsingle.trans hraw

/-- Canonical project-facing deterministic adapter.  The only nonlocal
analytic premise is the literal CGL v2 all-cases theorem; the remaining arrows
are fixed-character extraction, logarithmic conductor absorption, and the
finite primitive-inducer aggregation already certified in
`FixedCharacterReduction`. -/
theorem polylogConductorDensity_of_cgl_v2
    (hCGL : CGLv2Theorem12AllCases) :
    MAPAPZeroDensityCert.PolylogConductorDensity :=
  CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target
    (fixedPrimitivePolylogDensity_of_cgl_v2 hCGL)

end
end CGLMeshFormalization

#print axioms CGLMeshFormalization.cgl_source_formula_to_fixed_thirty_thirteen
#print axioms CGLMeshFormalization.equation126BAtOne_le_densityCoeff
#print axioms CGLMeshFormalization.cgl_v2_all_cases_of_equation126_at_q
#print axioms CGLMeshFormalization.classII_and_one_le_two_mul_last_general_term
#print axioms CGLMeshFormalization.section124_general_at_q_of_named_leaves
#print axioms CGLMeshFormalization.min_le_weighted_geometric_mean
#print axioms CGLMeshFormalization.first_general_term_intersect_ingham_le
#print axioms CGLMeshFormalization.remaining_general_terms_le_equation126_terms
#print axioms CGLMeshFormalization.equation126_at_q_of_section12_and_classical
#print axioms CGLMeshFormalization.cgl_v2_all_cases_of_section12_named_leaves
#print axioms CGLMeshFormalization.fixedPrimitivePolylogDensity_of_cgl_v2
#print axioms CGLMeshFormalization.polylogConductorDensity_of_cgl_v2
