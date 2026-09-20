import LowBetaMeshClosure
import APZeroDensityCertificate
import AllCenterNearFarTransfer

/-!
# Chen--Gupta--Li v2: exact source boundary and MAP-local deductions

This file does **not** certify the research proof of Chen--Gupta--Li v2,
Theorem 1.2.  `CGLv2Theorem12AllCases` is a proposition spelling out the
``in all cases'' line of that source in the divisor-backed language used by
the MAP development.  Every theorem below is conditional on an explicit
inhabitant of that proposition, or is elementary arithmetic/finite geometry.

The source paper is arXiv:2507.08296v2 (27 July 2026), Theorem 1.2.  Its
notation `(q T)^{o(1)}` is expanded here as the usual uniform
`for every eta > 0, there are C and R0` quantifiers.  The source itself says
``number of zeros'' but does not separately state the multiplicity convention
in the theorem statement.  Consequently, identifying its `N` with
`ambientZeroCountAtLevel` (analytic multiplicity) is deliberately visible in
this import contract.
-/

namespace CGLMeshFormalization

open scoped BigOperators ENNReal
open Filter Asymptotics
open ZeroDensityArithmetic DirichletZeros ZeroDensityInterface
open MAPAPZeroDensityCert MAPGuthMaynard MAPLowBetaMeshClosure
open MAPAllCenterApertureTransfer MAPAllCenterNearFarTransfer

noncomputable section

/-! ## The one deep imported source statement -/

/--
The exact MAP-used line of Chen--Gupta--Li v2, Theorem 1.2:

`sum_{chi mod q} N(sigma,T,chi) <= (qT)^{o(1)}
  (q^{(7/3)(1-sigma)} T^{2(1-sigma)}
    + (qT)^{(30/13)(1-sigma)})`.

No constant may depend on `q`, `T`, or `sigma`.  This is only a `Prop`
interface and is not a Lean proof of the source theorem.
-/
def CGLv2Theorem12AllCases : Prop :=
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
                ((30 / 13) * (1 - sigma)))

/-- Merely unpack the source contract.  The theorem keeps the research input
as an explicit hypothesis; it introduces no global declaration. -/
theorem CGLv2Theorem12AllCases.apply
    (hCGL : CGLv2Theorem12AllCases) (eta : ℝ) (heta : 0 < eta) :
    ∃ C R0 : ℝ, 0 < C ∧ 2 ≤ R0 ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        1 ≤ T → 1 / 2 < sigma → sigma < 1 →
        R0 ≤ (q : ℝ) * T →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T) eta *
            (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
                Real.rpow T (2 * (1 - sigma)) +
              Real.rpow ((q : ℝ) * T)
                ((30 / 13) * (1 - sigma))) :=
  hCGL eta heta

/-! ## Exact source exponent arithmetic at the MAP height -/

/-- The first CGL term has a fixed height reserve at the MAP truncation. -/
theorem cgl_first_height_reserve (epsilon : ℝ) :
    2 - 2 * tau epsilon = 4 / 15 + epsilon := by
  unfold tau
  ring

/-- The `30/13` CGL term has the sharp reserve that fixes `2/15`. -/
theorem cgl_second_height_reserve (epsilon : ℝ) :
    2 - densityCoeff * tau epsilon = 15 * epsilon / 13 := by
  unfold densityCoeff tau
  ring

/-- The first CGL term remains far below the required cell exponent on the
whole compact strip.  The source `o(1)`, conductor powers, and fixed log
losses have all been allocated the same literal allowance `etaZD` used by the
manuscript. -/
theorem cgl_first_cell_exponent_bound
    {epsilon sigma Delta : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : sigma ≤ 4 / 5)
    (hDelta : Delta ≤ 3 * epsilon / 52) :
    tau epsilon * (2 * (1 - sigma) + etaZD epsilon) +
        2 * (sigma + Delta - 1) ≤
      -(3 * epsilon / 52) := by
  have htau : 0 < tau epsilon := tau_pos hepsilon_le
  have heta : tau epsilon * etaZD epsilon = 3 * epsilon / 52 := by
    unfold etaZD
    field_simp
  have hgap := cgl_first_height_reserve epsilon
  rw [mul_add, heta]
  nlinarith

/-- The second CGL term is exactly the compact-cell calculation already
certified in `PaperMeshExponent`. -/
theorem cgl_second_cell_exponent_bound
    {epsilon sigma Delta : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : sigma ≤ 4 / 5)
    (hDelta : Delta ≤ 3 * epsilon / 52) :
    tau epsilon * (densityCoeff * (1 - sigma) + etaZD epsilon) +
        2 * (sigma + Delta - 1) ≤
      -(3 * epsilon / 52) := by
  exact paper_cell_exponent_bound hepsilon hepsilon_le hsigma_high hDelta

theorem four_rpow_mul
    {X a b c d : ℝ} (hX : 0 < X) :
    (Real.rpow X a * Real.rpow X b) *
        (Real.rpow X c * Real.rpow X d) =
      Real.rpow X ((a + b) + (c + d)) := by
  calc
    (Real.rpow X a * Real.rpow X b) *
        (Real.rpow X c * Real.rpow X d) =
      Real.rpow X (a + b) * Real.rpow X (c + d) := by
        exact congrArg₂ (fun x y : ℝ => x * y)
          (Real.rpow_add hX a b).symm
          (Real.rpow_add hX c d).symm
    _ = Real.rpow X ((a + b) + (c + d)) :=
      (Real.rpow_add hX _ _).symm

/-- Every conductor power occurring in the CGL all-cases line is absorbed by
one common `X^lambda`, provided the corresponding three fixed log powers are.
This is the exact uniform-in-`sigma` comparison used for
`q <= (log X)^K` on `1/2 <= sigma <= 1`. -/
theorem polylog_conductor_powers_fit
    {q : ℕ} [NeZero q]
    {K eta lambda X sigma : ℝ}
    (hK : 0 ≤ K) (heta : 0 ≤ eta)
    (hlog : 1 ≤ Real.log X)
    (hq : (q : ℝ) ≤ Real.rpow (Real.log X) K)
    (hsigma_low : 1 / 2 ≤ sigma) (hsigma_high : sigma ≤ 1)
    (hEtaAbsorb : Real.rpow (Real.log X) (K * eta) ≤
      Real.rpow X lambda)
    (hFirstAbsorb : Real.rpow (Real.log X) ((7 / 6) * K) ≤
      Real.rpow X lambda)
    (hSecondAbsorb : Real.rpow (Real.log X) ((15 / 13) * K) ≤
      Real.rpow X lambda) :
    Real.rpow (q : ℝ) eta ≤ Real.rpow X lambda ∧
    Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) ≤
      Real.rpow X lambda ∧
    Real.rpow (q : ℝ) (densityCoeff * (1 - sigma)) ≤
      Real.rpow X lambda := by
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hlog0 : 0 ≤ Real.log X := zero_le_one.trans hlog
  have hqEta :
      Real.rpow (q : ℝ) eta ≤
        Real.rpow (Real.rpow (Real.log X) K) eta :=
    Real.rpow_le_rpow hq0 hq heta
  have hEtaEq :
      Real.rpow (Real.rpow (Real.log X) K) eta =
        Real.rpow (Real.log X) (K * eta) :=
    (Real.rpow_mul hlog0 K eta).symm
  have hfirstExp0 : 0 ≤ (7 / 3) * (1 - sigma) := by
    positivity
  have hfirstExp : (7 / 3) * (1 - sigma) ≤ (7 / 6 : ℝ) := by
    nlinarith
  have hqFirstBase :
      Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) ≤
        Real.rpow (Real.rpow (Real.log X) K)
          ((7 / 3) * (1 - sigma)) :=
    Real.rpow_le_rpow hq0 hq hfirstExp0
  have hFirstNested :
      Real.rpow (Real.rpow (Real.log X) K)
          ((7 / 3) * (1 - sigma)) =
        Real.rpow (Real.log X)
          (K * ((7 / 3) * (1 - sigma))) :=
    (Real.rpow_mul hlog0 K _).symm
  have hFirstPower :
      Real.rpow (Real.log X)
          (K * ((7 / 3) * (1 - sigma))) ≤
        Real.rpow (Real.log X) ((7 / 6) * K) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    nlinarith
  have hsecondExp0 : 0 ≤ densityCoeff * (1 - sigma) := by
    unfold densityCoeff
    positivity
  have hsecondExp :
      densityCoeff * (1 - sigma) ≤ (15 / 13 : ℝ) := by
    unfold densityCoeff
    nlinarith
  have hqSecondBase :
      Real.rpow (q : ℝ) (densityCoeff * (1 - sigma)) ≤
        Real.rpow (Real.rpow (Real.log X) K)
          (densityCoeff * (1 - sigma)) :=
    Real.rpow_le_rpow hq0 hq hsecondExp0
  have hSecondNested :
      Real.rpow (Real.rpow (Real.log X) K)
          (densityCoeff * (1 - sigma)) =
        Real.rpow (Real.log X)
          (K * (densityCoeff * (1 - sigma))) :=
    (Real.rpow_mul hlog0 K _).symm
  have hSecondPower :
      Real.rpow (Real.log X)
          (K * (densityCoeff * (1 - sigma))) ≤
        Real.rpow (Real.log X) ((15 / 13) * K) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    nlinarith
  constructor
  · exact hqEta.trans_eq hEtaEq |>.trans hEtaAbsorb
  constructor
  · exact hqFirstBase.trans_eq hFirstNested |>.trans
      (hFirstPower.trans hFirstAbsorb)
  · exact hqSecondBase.trans_eq hSecondNested |>.trans
      (hSecondPower.trans hSecondAbsorb)

/-- The three fixed logarithmic envelopes in
`polylog_conductor_powers_fit` are simultaneously absorbed by `X^lambda`.
The theorem is eventual because that is the literal content of the standard
polylog-to-power comparison. -/
theorem fixed_polylog_envelopes_eventually_absorbed
    (K eta lambda : ℝ) (hlambda : 0 < lambda) :
    ∀ᶠ X : ℝ in atTop,
      Real.rpow (Real.log X) (K * eta) ≤ Real.rpow X lambda ∧
      Real.rpow (Real.log X) ((7 / 6) * K) ≤ Real.rpow X lambda ∧
      Real.rpow (Real.log X) ((15 / 13) * K) ≤ Real.rpow X lambda := by
  filter_upwards
    [polylog_absorption (K * eta) lambda hlambda,
      polylog_absorption ((7 / 6) * K) lambda hlambda,
      polylog_absorption ((15 / 13) * K) lambda hlambda] with X h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- Convert the literal two terms in CGL v2, Theorem 1.2, to the two MAP
height exponents at `T = X^(tau epsilon)`.

`lambda` is a completely explicit envelope for each conductor power.  Thus
the three premises `hqEta`, `hqFirst`, and `hqSecond` are precisely the place
where `q <= (log X)^K` and polylogarithmic absorption enter.  The final
premise `hloss` says that the source subpower loss and both conductor losses
fit in the manuscript's allotted `etaZD epsilon`.
-/
theorem cgl_source_formula_to_map_height
    {q : ℕ} [NeZero q]
    {epsilon sigma eta lambda X C zeroCount : ℝ}
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hqEta : Real.rpow (q : ℝ) eta ≤ Real.rpow X lambda)
    (hqFirst : Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) ≤
      Real.rpow X lambda)
    (hqSecond : Real.rpow (q : ℝ)
        (densityCoeff * (1 - sigma)) ≤ Real.rpow X lambda)
    (hloss : tau epsilon * eta + 2 * lambda ≤
      tau epsilon * etaZD epsilon)
    (hdensity : zeroCount ≤
      C * Real.rpow
          ((q : ℝ) * Real.rpow X (tau epsilon)) eta *
        (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow (Real.rpow X (tau epsilon))
              (2 * (1 - sigma)) +
          Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon))
            (densityCoeff * (1 - sigma)))) :
    zeroCount ≤ C *
      (Real.rpow X
          (tau epsilon * (2 * (1 - sigma) + etaZD epsilon)) +
       Real.rpow X
          (tau epsilon *
            (densityCoeff * (1 - sigma) + etaZD epsilon))) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hT0 : 0 ≤ Real.rpow X (tau epsilon) :=
    Real.rpow_nonneg hXpos.le _
  have hTeta :
      Real.rpow (Real.rpow X (tau epsilon)) eta =
        Real.rpow X (tau epsilon * eta) :=
    (Real.rpow_mul hXpos.le _ _).symm
  have hTfirst :
      Real.rpow (Real.rpow X (tau epsilon)) (2 * (1 - sigma)) =
        Real.rpow X (tau epsilon * (2 * (1 - sigma))) :=
    (Real.rpow_mul hXpos.le _ _).symm
  have hTsecond :
      Real.rpow (Real.rpow X (tau epsilon))
          (densityCoeff * (1 - sigma)) =
        Real.rpow X
          (tau epsilon * (densityCoeff * (1 - sigma))) :=
    (Real.rpow_mul hXpos.le _ _).symm
  have hmulEta :
      Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon)) eta =
        Real.rpow (q : ℝ) eta *
          Real.rpow (Real.rpow X (tau epsilon)) eta :=
    Real.mul_rpow hq0 hT0
  have hmulSecond :
      Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon))
          (densityCoeff * (1 - sigma)) =
        Real.rpow (q : ℝ) (densityCoeff * (1 - sigma)) *
          Real.rpow (Real.rpow X (tau epsilon))
            (densityCoeff * (1 - sigma)) :=
    Real.mul_rpow hq0 hT0
  have hfirst :
      Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon)) eta *
          (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow (Real.rpow X (tau epsilon))
              (2 * (1 - sigma))) ≤
        Real.rpow X
          (tau epsilon * (2 * (1 - sigma) + etaZD epsilon)) := by
    calc
      Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon)) eta *
          (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow (Real.rpow X (tau epsilon))
              (2 * (1 - sigma))) =
        (Real.rpow (q : ℝ) eta * Real.rpow X (tau epsilon * eta)) *
          (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow X (tau epsilon * (2 * (1 - sigma))) ) := by
        rw [hmulEta, hTeta, hTfirst]
      _ ≤ (Real.rpow X lambda * Real.rpow X (tau epsilon * eta)) *
          (Real.rpow X lambda *
            Real.rpow X (tau epsilon * (2 * (1 - sigma)))) := by
        have hab :
            Real.rpow (q : ℝ) eta *
                Real.rpow X (tau epsilon * eta) ≤
              Real.rpow X lambda *
                Real.rpow X (tau epsilon * eta) :=
          mul_le_mul_of_nonneg_right hqEta
            (Real.rpow_nonneg hXpos.le _)
        have hcd :
            Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
                Real.rpow X (tau epsilon * (2 * (1 - sigma))) ≤
              Real.rpow X lambda *
                Real.rpow X (tau epsilon * (2 * (1 - sigma))) :=
          mul_le_mul_of_nonneg_right hqFirst
            (Real.rpow_nonneg hXpos.le _)
        exact mul_le_mul hab hcd
          (mul_nonneg (Real.rpow_nonneg hq0 _)
            (Real.rpow_nonneg hXpos.le _))
          (mul_nonneg (Real.rpow_nonneg hXpos.le _)
            (Real.rpow_nonneg hXpos.le _))
      _ = Real.rpow X
          (tau epsilon * (2 * (1 - sigma)) +
            (tau epsilon * eta + 2 * lambda)) := by
        calc
          (Real.rpow X lambda * Real.rpow X (tau epsilon * eta)) *
              (Real.rpow X lambda *
                Real.rpow X (tau epsilon * (2 * (1 - sigma)))) =
            Real.rpow X
              ((lambda + tau epsilon * eta) +
                (lambda + tau epsilon * (2 * (1 - sigma)))) :=
            four_rpow_mul hXpos
          _ = Real.rpow X
              (tau epsilon * (2 * (1 - sigma)) +
                (tau epsilon * eta + 2 * lambda)) := by
            congr 1
            ring
      _ ≤ Real.rpow X
          (tau epsilon * (2 * (1 - sigma) + etaZD epsilon)) := by
        apply Real.rpow_le_rpow_of_exponent_le hX
        nlinarith
  have hsecond :
      Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon)) eta *
          Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon))
            (densityCoeff * (1 - sigma)) ≤
        Real.rpow X
          (tau epsilon *
            (densityCoeff * (1 - sigma) + etaZD epsilon)) := by
    calc
      Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon)) eta *
          Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon))
            (densityCoeff * (1 - sigma)) =
        (Real.rpow (q : ℝ) eta * Real.rpow X (tau epsilon * eta)) *
          (Real.rpow (q : ℝ) (densityCoeff * (1 - sigma)) *
            Real.rpow X
              (tau epsilon * (densityCoeff * (1 - sigma)))) := by
        rw [hmulEta, hmulSecond, hTeta, hTsecond]
      _ ≤ (Real.rpow X lambda * Real.rpow X (tau epsilon * eta)) *
          (Real.rpow X lambda *
            Real.rpow X
              (tau epsilon * (densityCoeff * (1 - sigma)))) := by
        have hab :
            Real.rpow (q : ℝ) eta *
                Real.rpow X (tau epsilon * eta) ≤
              Real.rpow X lambda *
                Real.rpow X (tau epsilon * eta) :=
          mul_le_mul_of_nonneg_right hqEta
            (Real.rpow_nonneg hXpos.le _)
        have hcd :
            Real.rpow (q : ℝ) (densityCoeff * (1 - sigma)) *
                Real.rpow X
                  (tau epsilon * (densityCoeff * (1 - sigma))) ≤
              Real.rpow X lambda *
                Real.rpow X
                  (tau epsilon * (densityCoeff * (1 - sigma))) :=
          mul_le_mul_of_nonneg_right hqSecond
            (Real.rpow_nonneg hXpos.le _)
        exact mul_le_mul hab hcd
          (mul_nonneg (Real.rpow_nonneg hq0 _)
            (Real.rpow_nonneg hXpos.le _))
          (mul_nonneg (Real.rpow_nonneg hXpos.le _)
            (Real.rpow_nonneg hXpos.le _))
      _ = Real.rpow X
          (tau epsilon * (densityCoeff * (1 - sigma)) +
            (tau epsilon * eta + 2 * lambda)) := by
        calc
          (Real.rpow X lambda * Real.rpow X (tau epsilon * eta)) *
              (Real.rpow X lambda *
                Real.rpow X
                  (tau epsilon * (densityCoeff * (1 - sigma)))) =
            Real.rpow X
              ((lambda + tau epsilon * eta) +
                (lambda +
                  tau epsilon * (densityCoeff * (1 - sigma)))) :=
            four_rpow_mul hXpos
          _ = Real.rpow X
              (tau epsilon * (densityCoeff * (1 - sigma)) +
                (tau epsilon * eta + 2 * lambda)) := by
            congr 1
            ring
      _ ≤ Real.rpow X
          (tau epsilon *
            (densityCoeff * (1 - sigma) + etaZD epsilon)) := by
        apply Real.rpow_le_rpow_of_exponent_le hX
        nlinarith
  calc
    zeroCount ≤ C *
        Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon)) eta *
          (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
              Real.rpow (Real.rpow X (tau epsilon))
                (2 * (1 - sigma)) +
            Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon))
              (densityCoeff * (1 - sigma))) := hdensity
    _ = C *
        (Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon)) eta *
            (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
              Real.rpow (Real.rpow X (tau epsilon))
                (2 * (1 - sigma))) +
          Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon)) eta *
            Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon))
              (densityCoeff * (1 - sigma))) := by ring
    _ ≤ C *
      (Real.rpow X
          (tau epsilon * (2 * (1 - sigma) + etaZD epsilon)) +
       Real.rpow X
          (tau epsilon *
            (densityCoeff * (1 - sigma) + etaZD epsilon))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC

/-- Weighted-mass conversion for both literal terms in the CGL all-cases
bound.  This is the exact exponent ledger after all polylogarithmic losses
have been placed inside `etaZD epsilon`.

The theorem is deliberately abstract in `zeroCount`: the only analytic
premise is `hdensity`; every multiplication and exponent comparison is local
and kernel checked.
-/
theorem cgl_two_term_count_mul_weight_le
    {epsilon sigma Delta X C zeroCount : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : sigma ≤ 4 / 5)
    (hDelta : Delta ≤ 3 * epsilon / 52)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : zeroCount ≤ C *
      (Real.rpow X
          (tau epsilon * (2 * (1 - sigma) + etaZD epsilon)) +
       Real.rpow X
          (tau epsilon *
            (densityCoeff * (1 - sigma) + etaZD epsilon)))) :
    zeroCount * Real.rpow X (2 * (sigma + Delta - 1)) ≤
      (2 * C) * Real.rpow X (-(3 * epsilon / 52)) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  let W := Real.rpow X (2 * (sigma + Delta - 1))
  have hW : 0 ≤ W := Real.rpow_nonneg hXpos.le _
  have hfirst :
      Real.rpow X
          (tau epsilon * (2 * (1 - sigma) + etaZD epsilon)) * W ≤
        Real.rpow X (-(3 * epsilon / 52)) := by
    change Real.rpow X
        (tau epsilon * (2 * (1 - sigma) + etaZD epsilon)) *
          Real.rpow X (2 * (sigma + Delta - 1)) ≤
      Real.rpow X (-(3 * epsilon / 52))
    calc
      Real.rpow X
          (tau epsilon * (2 * (1 - sigma) + etaZD epsilon)) *
          Real.rpow X (2 * (sigma + Delta - 1)) =
        Real.rpow X
          (tau epsilon * (2 * (1 - sigma) + etaZD epsilon) +
            2 * (sigma + Delta - 1)) :=
        (Real.rpow_add hXpos _ _).symm
      _ ≤ Real.rpow X (-(3 * epsilon / 52)) := by
        apply Real.rpow_le_rpow_of_exponent_le hX
        exact cgl_first_cell_exponent_bound hepsilon hepsilon_le hsigma_high
          hDelta
  have hsecond :
      Real.rpow X
          (tau epsilon *
            (densityCoeff * (1 - sigma) + etaZD epsilon)) * W ≤
        Real.rpow X (-(3 * epsilon / 52)) := by
    change Real.rpow X
        (tau epsilon *
          (densityCoeff * (1 - sigma) + etaZD epsilon)) *
          Real.rpow X (2 * (sigma + Delta - 1)) ≤
      Real.rpow X (-(3 * epsilon / 52))
    calc
      Real.rpow X
          (tau epsilon *
            (densityCoeff * (1 - sigma) + etaZD epsilon)) *
          Real.rpow X (2 * (sigma + Delta - 1)) =
        Real.rpow X
          (tau epsilon *
            (densityCoeff * (1 - sigma) + etaZD epsilon) +
              2 * (sigma + Delta - 1)) :=
        (Real.rpow_add hXpos _ _).symm
      _ ≤ Real.rpow X (-(3 * epsilon / 52)) := by
        apply Real.rpow_le_rpow_of_exponent_le hX
        exact cgl_second_cell_exponent_bound hepsilon hepsilon_le
          hsigma_high hDelta
  calc
    zeroCount * W ≤
        (C *
          (Real.rpow X
              (tau epsilon * (2 * (1 - sigma) + etaZD epsilon)) +
           Real.rpow X
              (tau epsilon *
                (densityCoeff * (1 - sigma) + etaZD epsilon)))) * W :=
      mul_le_mul_of_nonneg_right hdensity hW
    _ = C *
        (Real.rpow X
            (tau epsilon * (2 * (1 - sigma) + etaZD epsilon)) * W +
         Real.rpow X
            (tau epsilon *
              (densityCoeff * (1 - sigma) + etaZD epsilon)) * W) := by
      ring
    _ ≤ C *
        (Real.rpow X (-(3 * epsilon / 52)) +
         Real.rpow X (-(3 * epsilon / 52))) := by
      gcongr
    _ = (2 * C) * Real.rpow X (-(3 * epsilon / 52)) := by ring

/-! ### Literal divisor-backed family cell mass -/

variable {q : ℕ} [NeZero q]

/-- Actual zeros of one ambient Dirichlet L-function in one half-open paper
mesh cell. -/
def cglCellSupport (chi : DirichletCharacter ℂ q)
    (T delta0 Delta : ℝ) (j : ℕ) : Finset ℂ :=
  (zeroSupport chi (meshPoint delta0 Delta j) T).filter fun rho =>
    rho.re < meshPoint delta0 Delta j + Delta

/-- Literal `X^(2(beta-1))` mass, with analytic multiplicity, in one paper
mesh cell. -/
def cglCellMass (chi : DirichletCharacter ℂ q)
    (X T delta0 Delta : ℝ) (j : ℕ) : ℝ :=
  ∑ rho ∈ cglCellSupport chi T delta0 Delta j,
    (zeroMultiplicity chi (meshPoint delta0 Delta j) T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- Sum the literal cell mass over every ambient character modulo `q`,
matching the family on the left side of CGL Theorem 1.2. -/
def cglAmbientCellMass
    (X T delta0 Delta : ℝ) (j : ℕ) : ℝ :=
  ∑ chi : DirichletCharacter ℂ q,
    cglCellMass chi X T delta0 Delta j

/-- Every actual zero in a cell is bounded by the zero count at the left
endpoint times the largest cell weight. -/
theorem cglCellMass_le_count_weight
    (chi : DirichletCharacter ℂ q)
    {X T delta0 Delta : ℝ} (j : ℕ) (hX : 1 ≤ X) :
    cglCellMass chi X T delta0 Delta j ≤
      (dirichletZeroCount chi (meshPoint delta0 Delta j) T : ℝ) *
        Real.rpow X (2 * (meshPoint delta0 Delta j + Delta - 1)) := by
  let S := cglCellSupport chi T delta0 Delta j
  let W := Real.rpow X (2 * (meshPoint delta0 Delta j + Delta - 1))
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hsum :
      (∑ rho ∈ S,
          zeroMultiplicity chi (meshPoint delta0 Delta j) T rho) ≤
        dirichletZeroCount chi (meshPoint delta0 Delta j) T := by
    unfold dirichletZeroCount
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro rho hrho
      exact (Finset.mem_filter.mp hrho).1
    · intro rho _ _
      exact Nat.zero_le _
  calc
    cglCellMass chi X T delta0 Delta j ≤
        ∑ rho ∈ S,
          (zeroMultiplicity chi (meshPoint delta0 Delta j) T rho : ℝ) * W := by
      unfold cglCellMass
      apply Finset.sum_le_sum
      intro rho hrho
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le hX
      have hupper := (Finset.mem_filter.mp hrho).2
      linarith
    _ = ((∑ rho ∈ S,
          zeroMultiplicity chi (meshPoint delta0 Delta j) T rho : ℕ) : ℝ) * W := by
      push_cast
      rw [Finset.sum_mul]
    _ ≤ (dirichletZeroCount chi (meshPoint delta0 Delta j) T : ℝ) * W := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hsum
      · exact Real.rpow_nonneg hXpos.le _

/-- The fixed-modulus actual family mass is controlled by the exact
`ambientZeroCountAtLevel` used in the source contract. -/
theorem cglAmbientCellMass_le_family_count_weight
    {X T delta0 Delta : ℝ} (j : ℕ) (hX : 1 ≤ X) :
    cglAmbientCellMass (q := q) X T delta0 Delta j ≤
      (ambientZeroCountAtLevel q (meshPoint delta0 Delta j) T : ℝ) *
        Real.rpow X (2 * (meshPoint delta0 Delta j + Delta - 1)) := by
  let W := Real.rpow X (2 * (meshPoint delta0 Delta j + Delta - 1))
  calc
    cglAmbientCellMass (q := q) X T delta0 Delta j ≤
        ∑ chi : DirichletCharacter ℂ q,
          (dirichletZeroCount chi (meshPoint delta0 Delta j) T : ℝ) * W := by
      unfold cglAmbientCellMass
      apply Finset.sum_le_sum
      intro chi _
      exact cglCellMass_le_count_weight chi j hX
    _ = ((∑ chi : DirichletCharacter ℂ q,
          dirichletZeroCount chi (meshPoint delta0 Delta j) T : ℕ) : ℝ) * W := by
      push_cast
      rw [Finset.sum_mul]
    _ = (ambientZeroCountAtLevel q (meshPoint delta0 Delta j) T : ℝ) * W := by
      simp [ambientZeroCountAtLevel, NeZero.ne q]

/-- End-to-end local deduction from the literal CGL source formula at
`T = X^(tau epsilon)` to the weighted contribution of one compact mesh cell.
Only `hdensity` is analytic; the conductor absorption, source exponent
conversion, and zero weight are explicit premises or proved calculations.
-/
theorem cgl_source_formula_cell_mass_bound
    {q : ℕ} [NeZero q]
    {epsilon sigma Delta eta lambda X C zeroCount : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : sigma ≤ 4 / 5)
    (hDelta : Delta ≤ 3 * epsilon / 52)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hqEta : Real.rpow (q : ℝ) eta ≤ Real.rpow X lambda)
    (hqFirst : Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) ≤
      Real.rpow X lambda)
    (hqSecond : Real.rpow (q : ℝ)
        (densityCoeff * (1 - sigma)) ≤ Real.rpow X lambda)
    (hloss : tau epsilon * eta + 2 * lambda ≤
      tau epsilon * etaZD epsilon)
    (hdensity : zeroCount ≤
      C * Real.rpow
          ((q : ℝ) * Real.rpow X (tau epsilon)) eta *
        (Real.rpow (q : ℝ) ((7 / 3) * (1 - sigma)) *
            Real.rpow (Real.rpow X (tau epsilon))
              (2 * (1 - sigma)) +
          Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon))
            (densityCoeff * (1 - sigma)))) :
    zeroCount * Real.rpow X (2 * (sigma + Delta - 1)) ≤
      (2 * C) * Real.rpow X (-(3 * epsilon / 52)) := by
  have hconverted := cgl_source_formula_to_map_height
    (q := q) (epsilon := epsilon) (sigma := sigma)
    (eta := eta) (lambda := lambda) (X := X) (C := C)
    (zeroCount := zeroCount) hX hC hqEta hqFirst hqSecond hloss hdensity
  exact cgl_two_term_count_mul_weight_le hepsilon hepsilon_le hsigma_high
    hDelta hX hC hconverted

/-- Concrete divisor-backed version of `cgl_source_formula_cell_mass_bound`.
It starts from the literal CGL family count at a paper-mesh left endpoint and
ends with the actual multiplicity-aware family zero mass in that cell. -/
theorem actual_cgl_ambient_cell_mass_bound
    {epsilon delta0 Delta eta lambda X C : ℝ} {j : ℕ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : meshPoint delta0 Delta j ≤ 4 / 5)
    (hDelta : Delta ≤ 3 * epsilon / 52)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hqEta : Real.rpow (q : ℝ) eta ≤ Real.rpow X lambda)
    (hqFirst : Real.rpow (q : ℝ)
        ((7 / 3) * (1 - meshPoint delta0 Delta j)) ≤
      Real.rpow X lambda)
    (hqSecond : Real.rpow (q : ℝ)
        (densityCoeff * (1 - meshPoint delta0 Delta j)) ≤
      Real.rpow X lambda)
    (hloss : tau epsilon * eta + 2 * lambda ≤
      tau epsilon * etaZD epsilon)
    (hdensity :
      (ambientZeroCountAtLevel q (meshPoint delta0 Delta j)
        (Real.rpow X (tau epsilon)) : ℝ) ≤
      C * Real.rpow
          ((q : ℝ) * Real.rpow X (tau epsilon)) eta *
        (Real.rpow (q : ℝ)
            ((7 / 3) * (1 - meshPoint delta0 Delta j)) *
            Real.rpow (Real.rpow X (tau epsilon))
              (2 * (1 - meshPoint delta0 Delta j)) +
          Real.rpow ((q : ℝ) * Real.rpow X (tau epsilon))
            (densityCoeff * (1 - meshPoint delta0 Delta j)))) :
    cglAmbientCellMass (q := q) X (Real.rpow X (tau epsilon))
        delta0 Delta j ≤
      (2 * C) * Real.rpow X (-(3 * epsilon / 52)) := by
  have hmass := cglAmbientCellMass_le_family_count_weight
    (q := q) (X := X) (T := Real.rpow X (tau epsilon))
    (delta0 := delta0) (Delta := Delta) j hX
  exact hmass.trans (cgl_source_formula_cell_mass_bound
    hepsilon hepsilon_le hsigma_high hDelta hX hC hqEta hqFirst hqSecond
      hloss hdensity)

/-! ## Low beta and exact mesh endpoints -/

/-- CGL is not used below the density cutoff.  The paper's elementary count
and the largest low-strip weight give a fixed `X^(-1/10)` saving. -/
theorem low_beta_local_deduction
    {iota : Type*} [DecidableEq iota]
    (s : Finset iota) (multiplicity : iota → ℕ) (beta : iota → ℝ)
    {epsilon X C xi : ℝ}
    (hepsilon : 0 < epsilon) (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hxi : xi ≤ 1 / 30)
    (hbeta : ∀ z ∈ s, beta z ≤ 1 / 2 + paperDelta0 epsilon)
    (hcount : ((∑ z ∈ s, multiplicity z : ℕ) : ℝ) ≤
      C * Real.rpow X (tau epsilon + xi)) :
    (∑ z ∈ s, (multiplicity z : ℝ) *
        Real.rpow X (2 * (beta z - 1))) ≤
      C * Real.rpow X (-(1 / 10)) := by
  exact low_beta_weighted_mass_power_saving s multiplicity beta
    hepsilon hX hC hxi hbeta hcount

/-- The lower density endpoint is assigned to cell zero, exactly once. -/
theorem lower_mesh_endpoint_closed
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 ∈ Finset.range
        (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)) ∧
      meshPoint (paperDelta0 epsilon) (paperDelta epsilon) 0 ≤
          1 / 2 + paperDelta0 epsilon ∧
      1 / 2 + paperDelta0 epsilon <
        meshPoint (paperDelta0 epsilon) (paperDelta epsilon) 0 +
          paperDelta epsilon :=
  lower_endpoint_mem_first_mesh_cell hepsilon

/-- The endpoint `4/5` is included in a legal half-open compact cell. -/
theorem upper_mesh_endpoint_covered
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ j ∈ Finset.range
        (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)),
      meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j ≤ 4 / 5 ∧
      (4 / 5 : ℝ) <
        meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j +
          paperDelta epsilon :=
  four_fifths_has_paper_mesh_cell hepsilon

/-- The low strip and compact mesh form a disjoint, endpoint-complete split
through `beta = 4/5`. -/
theorem low_or_unique_side_of_mesh
    {epsilon beta : ℝ} (hepsilon : 0 < epsilon)
    (hbeta_high : beta ≤ 4 / 5) :
    beta < 1 / 2 + paperDelta0 epsilon ∨
      ∃ j ∈ Finset.range
          (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)),
        meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j ≤ beta ∧
        beta < meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j +
          paperDelta epsilon :=
  low_or_exists_paper_mesh_cell hepsilon hbeta_high

/-! ## Exact compact/near-one split and high-strip arithmetic -/

/-- Assign the shared endpoint `4/5` to the compact branch. -/
theorem compact_or_near_one (beta : ℝ) :
    beta ≤ 4 / 5 ∨ 4 / 5 < beta := le_or_gt beta (4 / 5)

/-- The Jutila `2+1/10 = 21/10` high-strip exponent retains a `1/6`
weight gap once `log(qT)/log X` is at most `tau + 1/315`.

This is only the local exponent implication.  It neither imports Jutila's
research theorem nor a zero-free region.
-/
theorem near_one_weighted_exponent_bound
    {epsilon u sigma : ℝ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hsigma : sigma ≤ 1) :
    (21 / 10) * (tau epsilon + u) * (1 - sigma) +
        2 * (sigma - 1) ≤
      -(1 / 6) * (1 - sigma) := by
  have hgap : 1 / 6 ≤ 2 - (21 / 10) * (tau epsilon + u) := by
    simpa only [tau] using
      (nearOneExponent_bound (ε := epsilon) (u := u)
        hepsilon hu0 hu)
  have hone : 0 ≤ 1 - sigma := by linarith
  have hmul := mul_le_mul_of_nonneg_right hgap hone
  nlinarith

/-- A relative near-one cell width preserves half of the `1/6` high-strip
gap.  The condition `Delta <= (1-sigma)/24` is the precise geometric-mesh
requirement; it leaves a `1/12` exponent saving after paying the upper-cell
zero weight. -/
theorem near_one_cell_exponent_bound
    {epsilon u sigma Delta : ℝ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hsigma : sigma ≤ 1)
    (hDelta : Delta ≤ (1 - sigma) / 24) :
    (21 / 10) * (tau epsilon + u) * (1 - sigma) +
        2 * (sigma + Delta - 1) ≤
      -(1 / 12) * (1 - sigma) := by
  have hbase := near_one_weighted_exponent_bound
    hepsilon hu0 hu hsigma
  nlinarith

/-- The local near-one weighted-mass deduction from Jutila's published
`2+1/10` family density exponent, after the conductor has been included in
the explicit ratio allowance `u`.

As in the compact theorem, `zeroCount` is abstract and `hdensity` is the only
analytic premise.
-/
theorem near_one_density_mul_weight_le
    {epsilon u sigma Delta X C zeroCount : ℝ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hsigma : sigma ≤ 1)
    (hDelta : Delta ≤ (1 - sigma) / 24)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : zeroCount ≤ C * Real.rpow X
      ((21 / 10) * (tau epsilon + u) * (1 - sigma))) :
    zeroCount * Real.rpow X (2 * (sigma + Delta - 1)) ≤
      C * Real.rpow X (-(1 / 12) * (1 - sigma)) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hW : 0 ≤ Real.rpow X (2 * (sigma + Delta - 1)) :=
    Real.rpow_nonneg hXpos.le _
  calc
    zeroCount * Real.rpow X (2 * (sigma + Delta - 1)) ≤
        (C * Real.rpow X
          ((21 / 10) * (tau epsilon + u) * (1 - sigma))) *
            Real.rpow X (2 * (sigma + Delta - 1)) :=
      mul_le_mul_of_nonneg_right hdensity hW
    _ = C * Real.rpow X
        ((21 / 10) * (tau epsilon + u) * (1 - sigma) +
          2 * (sigma + Delta - 1)) := by
      rw [mul_assoc]
      congr 1
      exact (Real.rpow_add hXpos _ _).symm
    _ ≤ C * Real.rpow X (-(1 / 12) * (1 - sigma)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hX
      exact near_one_cell_exponent_bound hepsilon hu0 hu hsigma hDelta

/-- A quantitative zero-free gap converts the relative high-strip saving to
one common exponent. -/
theorem near_one_density_mul_weight_le_of_gap
    {epsilon u sigma Delta omega X C zeroCount : ℝ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hsigma : sigma ≤ 1) (homega : omega ≤ 1 - sigma)
    (hDelta : Delta ≤ (1 - sigma) / 24)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : zeroCount ≤ C * Real.rpow X
      ((21 / 10) * (tau epsilon + u) * (1 - sigma))) :
    zeroCount * Real.rpow X (2 * (sigma + Delta - 1)) ≤
      C * Real.rpow X (-(omega / 12)) := by
  have hnear := near_one_density_mul_weight_le hepsilon hu0 hu hsigma
    hDelta hX hC hdensity
  exact hnear.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX (by nlinarith)) hC)

/-! ## Finite mesh summation and three-range weld -/

/-- Summing the uniform CGL compact-cell saving pays exactly the finite mesh
cardinality and no additional power of `X`. -/
theorem compact_mesh_sum_le
    {epsilon X C : ℝ}
    (cellMass : ℕ → ℝ)
    (hcell : ∀ j,
      j < meshCellCount (paperDelta0 epsilon) (paperDelta epsilon) →
        0 ≤ cellMass j ∧
        cellMass j ≤
          (2 * C) * Real.rpow X (-(3 * epsilon / 52))) :
    (∑ j ∈ Finset.range
        (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)),
        cellMass j) ≤
      meshCellCount (paperDelta0 epsilon) (paperDelta epsilon) *
        ((2 * C) * Real.rpow X (-(3 * epsilon / 52))) := by
  exact sum_mesh_cells_le cellMass hcell

/-- Summing a uniform fixed-level CGL bound over every positive modulus
`q <= Q` costs exactly the number `Q` of levels.  For polylogarithmic `Q`
this is the final fixed log factor handled by
`fixed_polylog_envelopes_eventually_absorbed`. -/
theorem sum_positive_levels_le
    (Q : ℕ) (levelMass : ℕ → ℝ) {M : ℝ}
    (hlevel : ∀ q ∈ Finset.Icc 1 Q, levelMass q ≤ M) :
    (∑ q ∈ Finset.Icc 1 Q, levelMass q) ≤ (Q : ℝ) * M := by
  calc
    (∑ q ∈ Finset.Icc 1 Q, levelMass q) ≤
        ∑ _q ∈ Finset.Icc 1 Q, M := by
      apply Finset.sum_le_sum
      intro q hq
      exact hlevel q hq
    _ = ((Finset.Icc 1 Q).card : ℝ) * M := by simp
    _ = (Q : ℝ) * M := by simp

/-- The full finite cost of the compact branch: `Q` positive conductor
levels times the literal number of beta cells.  No unrecorded power of `X`
appears. -/
theorem compact_levels_and_mesh_sum_le
    {epsilon X C : ℝ} (Q : ℕ)
    (levelCellMass : ℕ → ℕ → ℝ)
    (hcell : ∀ q ∈ Finset.Icc 1 Q, ∀ j,
      j < meshCellCount (paperDelta0 epsilon) (paperDelta epsilon) →
        0 ≤ levelCellMass q j ∧
        levelCellMass q j ≤
          (2 * C) * Real.rpow X (-(3 * epsilon / 52))) :
    (∑ q ∈ Finset.Icc 1 Q,
        ∑ j ∈ Finset.range
          (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)),
          levelCellMass q j) ≤
      (Q : ℝ) *
        (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon) *
          ((2 * C) * Real.rpow X (-(3 * epsilon / 52)))) := by
  apply sum_positive_levels_le
  intro q hq
  exact compact_mesh_sum_le (levelCellMass q) (hcell q hq)

/-- The exact additive weld of the disjoint low, compact, and near-one
ranges.  This theorem makes the only three losses visible: a fixed low-strip
power, the finite compact mesh cardinality, and the zero-free gap `omega` in
the near-one strip. -/
theorem low_compact_near_one_weld
    {epsilon X C_low C_compact C_near omega : ℝ}
    {J : ℕ} {lowMass compactMass nearMass : ℝ}
    (hlow : lowMass ≤ C_low * Real.rpow X (-(1 / 10)))
    (hcompact : compactMass ≤
      J * ((2 * C_compact) *
        Real.rpow X (-(3 * epsilon / 52))))
    (hnear : nearMass ≤
      C_near * Real.rpow X (-(omega / 12))) :
    lowMass + compactMass + nearMass ≤
      C_low * Real.rpow X (-(1 / 10)) +
      J * ((2 * C_compact) *
        Real.rpow X (-(3 * epsilon / 52))) +
      C_near * Real.rpow X (-(omega / 12)) := by
  linarith

/-! ## Simultaneous short-interval AP parameter balance -/

/-- The AP aperture reserve used after the near/far parameter selection. -/
def apEpsilon (epsilon : ℝ) : ℝ := apertureReserve epsilon / 2

theorem apEpsilon_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < apEpsilon epsilon := by
  unfold apEpsilon
  exact div_pos (apertureReserve_pos hepsilon) (by norm_num)

/-- The artificial cap in the Lean AP proposition is automatically legal. -/
theorem apEpsilon_le_cap (epsilon : ℝ) :
    apEpsilon epsilon ≤ 13 / 30 := by
  unfold apEpsilon apertureReserve
  have h := min_le_right (epsilon / 4) (1 / 1200)
  linarith

/-- The exact exponent margin between the base aperture and the AP length. -/
theorem base_minus_ap_exponent (epsilon : ℝ) :
    (2 / 15 + apertureReserve epsilon) -
        (2 / 15 + apEpsilon epsilon) = apEpsilon epsilon := by
  unfold apEpsilon
  ring

/-- The collar length `y = H_*/(32 R)` used in the manuscript. -/
def collarLength (epsilon X R : ℝ) : ℝ :=
  baseAperture epsilon X / (32 * R)

/-- If the fixed logarithmic collar factor is absorbed by the spare
`X^(rho/2)`, then the simultaneous AP theorem is legal at the literal collar
length.  This proves the manuscript step
`64 R <= X^(rho/2)  =>  y >= X^(2/15+rho/2)`.
-/
theorem collarLength_ge_ap_threshold
    {epsilon X R : ℝ} (hX : 1 ≤ X) (hR : 0 < R)
    (habsorb : 64 * R ≤ Real.rpow X (apEpsilon epsilon)) :
    Real.rpow X (2 / 15 + apEpsilon epsilon) ≤
      collarLength epsilon X R := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hden : 0 < 64 * R := mul_pos (by norm_num) hR
  have hsplit :
      Real.rpow X (2 / 15 + apertureReserve epsilon) =
        Real.rpow X (2 / 15 + apEpsilon epsilon) *
          Real.rpow X (apEpsilon epsilon) := by
    calc
      Real.rpow X (2 / 15 + apertureReserve epsilon) =
          Real.rpow X
            ((2 / 15 + apEpsilon epsilon) + apEpsilon epsilon) := by
        congr 1
        unfold apEpsilon
        ring
      _ = Real.rpow X (2 / 15 + apEpsilon epsilon) *
          Real.rpow X (apEpsilon epsilon) := Real.rpow_add hXpos _ _
  have hpow :
      Real.rpow X (2 / 15 + apEpsilon epsilon) * (64 * R) ≤
        Real.rpow X (2 / 15 + apertureReserve epsilon) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left habsorb
      (Real.rpow_nonneg hXpos.le _)
  have hdiv :
      Real.rpow X (2 / 15 + apEpsilon epsilon) ≤
        Real.rpow X (2 / 15 + apertureReserve epsilon) / (64 * R) :=
    (le_div_iff₀ hden).2 hpow
  calc
    Real.rpow X (2 / 15 + apEpsilon epsilon) ≤
        Real.rpow X (2 / 15 + apertureReserve epsilon) / (64 * R) := hdiv
    _ = collarLength epsilon X R := by
      unfold collarLength baseAperture
      field_simp
      <;> ring

/-- At `theta = 2/15 + epsilon`, the truncation height has the exact
`X^(-epsilon/2)` margin used in the explicit formula. -/
theorem simultaneous_ap_truncation_balance (epsilon : ℝ) :
    1 - tau epsilon - theta epsilon = -(epsilon / 2) :=
  truncation_exponent epsilon

/-- The two density terms and the explicit-formula truncation are all strict
for positive epsilon. -/
theorem simultaneous_ap_strict_margins
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < 2 - 2 * tau epsilon ∧
    0 < 2 - densityCoeff * tau epsilon ∧
    1 - tau epsilon - theta epsilon < 0 := by
  rw [cgl_first_height_reserve, cgl_second_height_reserve,
    simultaneous_ap_truncation_balance]
  constructor
  · linarith
  constructor <;> linarith

/-! ## Honest connector to the public MAP proposition -/

/-- All post-analytic geometry from the synchronized near/far estimates to
the public all-center statement is already Lean certified.  CGL alone does
not inhabit `CanonicalNearFarEstimates`: the explicit formula, zero-free
input, Gallagher/maximal estimates, and the far MRT branch remain separate
deep inputs. -/
theorem allCenterLocalMAP_of_synchronized_nearFar
    (hNF : CanonicalNearFarEstimates) :
    PrimePairEndpoints.AllCenterLocalMAP :=
  allCenterLocalMAP_of_nearFarEstimates hNF

end
end CGLMeshFormalization

#print axioms CGLMeshFormalization.CGLv2Theorem12AllCases.apply
#print axioms CGLMeshFormalization.cgl_first_height_reserve
#print axioms CGLMeshFormalization.cgl_second_height_reserve
#print axioms CGLMeshFormalization.cgl_first_cell_exponent_bound
#print axioms CGLMeshFormalization.cgl_second_cell_exponent_bound
#print axioms CGLMeshFormalization.cgl_two_term_count_mul_weight_le
#print axioms CGLMeshFormalization.low_beta_local_deduction
#print axioms CGLMeshFormalization.lower_mesh_endpoint_closed
#print axioms CGLMeshFormalization.upper_mesh_endpoint_covered
#print axioms CGLMeshFormalization.low_or_unique_side_of_mesh
#print axioms CGLMeshFormalization.compact_or_near_one
#print axioms CGLMeshFormalization.near_one_weighted_exponent_bound
#print axioms CGLMeshFormalization.apEpsilon_pos
#print axioms CGLMeshFormalization.apEpsilon_le_cap
#print axioms CGLMeshFormalization.base_minus_ap_exponent
#print axioms CGLMeshFormalization.collarLength_ge_ap_threshold
#print axioms CGLMeshFormalization.simultaneous_ap_truncation_balance
#print axioms CGLMeshFormalization.simultaneous_ap_strict_margins
#print axioms CGLMeshFormalization.allCenterLocalMAP_of_synchronized_nearFar
