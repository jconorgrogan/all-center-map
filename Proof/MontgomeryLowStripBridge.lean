import FixedCharacterReduction
import APWeightedZeroMassIntegrationScaffold
import CGLCompactStripDensityConstructor

/-!
# The fixed-character low strip from Montgomery's fixed-modulus family theorem

This staging file isolates the part of the classical low-strip argument which
does not depend on a zero detector or on Guth--Maynard large values.

The source input is written literally as Montgomery's fixed-modulus family
count: all characters modulo one positive modulus, the symmetric height box
`|Im rho| <= T`, and analytic multiplicity.  It is a theorem parameter rather
than a new axiom or a named proposition.  Everything after that published
input -- extraction of one primitive character, conductor bookkeeping,
polylogarithmic absorption, the Ingham exponent comparison, and the endpoint
`sigma = 7/10` -- is proved below.
-/

namespace MAPMontgomeryLowStrip

open Filter
open scoped BigOperators

noncomputable section

open DirichletZeros ZeroDensityArithmetic ZeroDensityInterface
open MAPAPZeroDensityCert MAPAPWeightedZeroMassIntegration

/-- The exponent in Montgomery, *Topics in Multiplicative Number Theory*,
Theorem 12.1, equation (A.14) in the MAP appendix. -/
def inghamExponent (sigma : ℝ) : ℝ :=
  inghamCoeff sigma * (1 - sigma)

theorem inghamExponent_eq (sigma : ℝ) :
    inghamExponent sigma = 3 * (1 - sigma) / (2 - sigma) := by
  unfold inghamExponent inghamCoeff
  ring

theorem inghamExponent_nonneg
    {sigma : ℝ} (_hsigmaLow : 1 / 2 ≤ sigma) (hsigmaHigh : sigma ≤ 7 / 10) :
    0 ≤ inghamExponent sigma := by
  rw [inghamExponent_eq]
  exact div_nonneg (by linarith) (by linarith)

theorem inghamExponent_le_one
    {sigma : ℝ} (hsigmaLow : 1 / 2 ≤ sigma) (hsigmaHigh : sigma ≤ 7 / 10) :
    inghamExponent sigma ≤ 1 := by
  rw [inghamExponent_eq]
  apply (div_le_one (by linarith : 0 < 2 - sigma)).2
  linarith

theorem inghamExponent_le_uniformExponent
    {sigma eta : ℝ} (hsigmaLow : 1 / 2 ≤ sigma)
    (hsigmaHigh : sigma ≤ 7 / 10) :
    inghamExponent sigma + eta ≤ uniformCoeff * (1 - sigma) + eta := by
  have hone : 0 ≤ 1 - sigma := by linarith
  have hcoeff := inghamCoeff_le_uniform hsigmaLow hsigmaHigh
  unfold inghamExponent
  exact add_le_add (mul_le_mul_of_nonneg_right hcoeff hone) le_rfl

/-- If the conductor is at most `(log T)^K`, its logarithm contributes at most
`K log log T`; for `log T >= 1` this is at most `K log T`.  This is the exact
uniform scale comparison needed for the ninth logarithmic power in the source
theorem. -/
theorem log_conductor_mul_height_le
    {K T : ℝ} (hK : 0 < K) (hT : Real.exp 1 ≤ T)
    {r : ℕ} [NeZero r]
    (hr : (r : ℝ) ≤ Real.rpow (Real.log T) K) :
    Real.log ((r : ℝ) * T) ≤ (K + 1) * Real.log T := by
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hT
  have hlogTpos : 0 < Real.log T := zero_lt_one.trans_le hlogT
  have hrpos : 0 < (r : ℝ) := by
    exact_mod_cast NeZero.pos r
  have hloglog : Real.log (Real.log T) ≤ Real.log T := by
    have h := Real.log_le_sub_one_of_pos hlogTpos
    linarith
  have hlogr : Real.log (r : ℝ) ≤ K * Real.log T := by
    calc
      Real.log (r : ℝ) ≤ Real.log (Real.rpow (Real.log T) K) :=
        Real.log_le_log hrpos hr
      _ = K * Real.log (Real.log T) := Real.log_rpow hlogTpos K
      _ ≤ K * Real.log T :=
        mul_le_mul_of_nonneg_left hloglog hK.le
  rw [Real.log_mul hrpos.ne' hTpos.ne']
  linarith

/-- At one set of legal parameters, the literal Montgomery family estimate
implies the required fixed-character `30/13` estimate.  The two hypotheses
`hconductorLoss` and `hlogLoss` display exactly where the two halves of `eta`
are spent. -/
theorem fixed_primitive_low_strip_at_scale
    {K eta C₀ T sigma : ℝ} {Q r : ℕ} [NeZero r]
    (chi : DirichletCharacter ℂ r)
    (hK : 0 < K) (_heta : 0 < eta) (hC₀ : 0 ≤ C₀)
    (hT : Real.exp 1 ≤ T)
    (hQ : (Q : ℝ) ≤ Real.rpow (Real.log T) K)
    (hrQ : r ≤ Q)
    (hsigmaLow : 1 / 2 ≤ sigma) (hsigmaHigh : sigma ≤ 7 / 10)
    (hconductorLoss : Real.rpow (Real.log T) K ≤
      Real.rpow T (eta / 2))
    (hlogLoss : Real.rpow (Real.log T) 9 ≤
      Real.rpow T (eta / 2))
    (hMontgomery : (ambientZeroCountAtLevel r sigma T : ℝ) ≤
      C₀ * Real.rpow ((r : ℝ) * T) (inghamExponent sigma) *
        (Real.log ((r : ℝ) * T)) ^ 9) :
    (dirichletZeroCount chi sigma T : ℝ) ≤
      (C₀ * (K + 1) ^ 9) *
        Real.rpow T (uniformCoeff * (1 - sigma) + eta) := by
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hTone : 1 ≤ T := (by
    have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith)
  have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast NeZero.pos r
  have hrnonneg : 0 ≤ (r : ℝ) := hrOne.trans' zero_le_one
  have hTnonneg : 0 ≤ T := hTpos.le
  have he0 : 0 ≤ inghamExponent sigma :=
    inghamExponent_nonneg hsigmaLow hsigmaHigh
  have he1 : inghamExponent sigma ≤ 1 :=
    inghamExponent_le_one hsigmaLow hsigmaHigh
  have hrlog : (r : ℝ) ≤ Real.rpow (Real.log T) K := by
    exact (by exact_mod_cast hrQ : (r : ℝ) ≤ (Q : ℝ)).trans hQ
  have hrLoss : (r : ℝ) ≤ Real.rpow T (eta / 2) :=
    hrlog.trans hconductorLoss
  have hscalePow :
      Real.rpow ((r : ℝ) * T) (inghamExponent sigma) ≤
        Real.rpow T (inghamExponent sigma + eta / 2) := by
    calc
      Real.rpow ((r : ℝ) * T) (inghamExponent sigma) =
          Real.rpow (r : ℝ) (inghamExponent sigma) *
            Real.rpow T (inghamExponent sigma) :=
        Real.mul_rpow hrnonneg hTnonneg
      _ ≤ (r : ℝ) * Real.rpow T (inghamExponent sigma) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le hrOne he1)
          (Real.rpow_nonneg hTnonneg _)
      _ ≤ Real.rpow T (eta / 2) *
            Real.rpow T (inghamExponent sigma) := by
        exact mul_le_mul_of_nonneg_right hrLoss
          (Real.rpow_nonneg hTnonneg _)
      _ = Real.rpow T (inghamExponent sigma + eta / 2) := by
        rw [mul_comm]
        exact (Real.rpow_add hTpos _ _).symm
  have hlogScaleNonneg : 0 ≤ Real.log ((r : ℝ) * T) := by
    have hprod : (1 : ℝ) ≤ (r : ℝ) * T := by
      simpa only [one_mul] using
        (mul_le_mul hrOne hTone zero_le_one hrnonneg)
    exact Real.log_nonneg hprod
  have hKone : 0 ≤ K + 1 := by linarith
  have hlogTnonneg : 0 ≤ Real.log T := Real.log_nonneg hTone
  have hlogScale := log_conductor_mul_height_le hK hT hrlog
  have hlogPow :
      (Real.log ((r : ℝ) * T)) ^ 9 ≤
        (K + 1) ^ 9 * Real.rpow T (eta / 2) := by
    calc
      (Real.log ((r : ℝ) * T)) ^ 9 ≤
          ((K + 1) * Real.log T) ^ 9 := by
        gcongr
      _ = (K + 1) ^ 9 * (Real.log T) ^ 9 := by rw [mul_pow]
      _ = (K + 1) ^ 9 * Real.rpow (Real.log T) 9 := by
        congr 1
        exact (Real.rpow_natCast (Real.log T) 9).symm
      _ ≤ (K + 1) ^ 9 * Real.rpow T (eta / 2) := by
        exact mul_le_mul_of_nonneg_left hlogLoss (by positivity)
  have hsingleNat :=
    dirichletZeroCount_le_ambientZeroCountAtLevel chi sigma T
  have hsingle : (dirichletZeroCount chi sigma T : ℝ) ≤
      (ambientZeroCountAtLevel r sigma T : ℝ) := by
    exact_mod_cast hsingleNat
  have hraw := hsingle.trans hMontgomery
  have hscaleNonneg :
      0 ≤ Real.rpow ((r : ℝ) * T) (inghamExponent sigma) :=
    Real.rpow_nonneg (mul_nonneg hrnonneg hTnonneg) _
  have hpowNonneg :
      0 ≤ Real.rpow T (inghamExponent sigma + eta / 2) :=
    Real.rpow_nonneg hTnonneg _
  have hlogPowNonneg : 0 ≤ (Real.log ((r : ℝ) * T)) ^ 9 := by
    positivity
  have hcombine :
      Real.rpow T (inghamExponent sigma + eta / 2) *
          Real.rpow T (eta / 2) =
        Real.rpow T (inghamExponent sigma + eta) := by
    calc
      Real.rpow T (inghamExponent sigma + eta / 2) *
          Real.rpow T (eta / 2) =
          Real.rpow T ((inghamExponent sigma + eta / 2) + eta / 2) :=
        (Real.rpow_add hTpos _ _).symm
      _ = Real.rpow T (inghamExponent sigma + eta) := by
        congr 1
        ring
  calc
    (dirichletZeroCount chi sigma T : ℝ) ≤
        C₀ * Real.rpow ((r : ℝ) * T) (inghamExponent sigma) *
          (Real.log ((r : ℝ) * T)) ^ 9 := hraw
    _ ≤ C₀ * Real.rpow T (inghamExponent sigma + eta / 2) *
          ((K + 1) ^ 9 * Real.rpow T (eta / 2)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hscalePow hC₀)
        hlogPow hlogPowNonneg
        (mul_nonneg hC₀ hpowNonneg)
    _ = (C₀ * (K + 1) ^ 9) *
          Real.rpow T (inghamExponent sigma + eta) := by
      calc
        C₀ * Real.rpow T (inghamExponent sigma + eta / 2) *
            ((K + 1) ^ 9 * Real.rpow T (eta / 2)) =
            (C₀ * (K + 1) ^ 9) *
              (Real.rpow T (inghamExponent sigma + eta / 2) *
                Real.rpow T (eta / 2)) := by ring
        _ = (C₀ * (K + 1) ^ 9) *
              Real.rpow T (inghamExponent sigma + eta) := by
          rw [hcombine]
    _ ≤ (C₀ * (K + 1) ^ 9) *
          Real.rpow T (uniformCoeff * (1 - sigma) + eta) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le hTone
          (inghamExponent_le_uniformExponent hsigmaLow hsigmaHigh)
      · exact mul_nonneg hC₀ (by positivity)

/-- Full quantifier adapter for the low strip.  The sole analytic premise is
the literal fixed-modulus family theorem with one absolute source constant.
It is deliberately not packaged as a new `Prop`: downstream users can see the
published statement at the call site. -/
theorem montgomery_family_source_to_fixed_primitive_low_strip
    (hMontgomery : ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (r : ℕ) [NeZero r] (T sigma : ℝ),
        2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 4 / 5 →
          (ambientZeroCountAtLevel r sigma T : ℝ) ≤
            C₀ * Real.rpow ((r : ℝ) * T) (inghamExponent sigma) *
              (Real.log ((r : ℝ) * T)) ^ 9) :
    ∀ K delta eta : ℝ, 0 < K → 0 < delta → 0 < eta →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
          (Q : ℝ) ≤ Real.rpow (Real.log T) K →
          1 / 2 + delta ≤ sigma → sigma ≤ 7 / 10 →
          ∀ (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r),
            chi.IsPrimitive → r ≤ Q →
              (dirichletZeroCount chi sigma T : ℝ) ≤
                C * Real.rpow T
                  (uniformCoeff * (1 - sigma) + eta) := by
  intro K delta eta hK hdelta heta
  obtain ⟨C₀, hC₀, hsource⟩ := hMontgomery
  have hcondEvent := polylog_absorption K (eta / 2) (half_pos heta)
  have hlogEvent := polylog_absorption 9 (eta / 2) (half_pos heta)
  obtain ⟨Tcond, hTcond⟩ := Filter.eventually_atTop.1 hcondEvent
  obtain ⟨Tlog, hTlog⟩ := Filter.eventually_atTop.1 hlogEvent
  let T₀ : ℝ := max (Real.exp 1) (max 2 (max Tcond Tlog))
  let C : ℝ := C₀ * (K + 1) ^ 9
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, T₀, hC, ?_, ?_⟩
  · dsimp [T₀]
    exact (le_max_left 2 (max Tcond Tlog)).trans
      (le_max_right (Real.exp 1) (max 2 (max Tcond Tlog)))
  intro T Q sigma hT hQ hsigmaLow hsigmaHigh r _inst chi _hprim hrQ
  have hTexp : Real.exp 1 ≤ T := (le_max_left _ _).trans hT
  have hTtwo : 2 ≤ T :=
    ((le_max_left 2 (max Tcond Tlog)).trans
      (le_max_right (Real.exp 1) (max 2 (max Tcond Tlog)))).trans hT
  have hTcond' : Tcond ≤ T :=
    ((le_max_left Tcond Tlog).trans
      (le_max_right 2 (max Tcond Tlog)) |>.trans
      (le_max_right (Real.exp 1) (max 2 (max Tcond Tlog)))).trans hT
  have hTlog' : Tlog ≤ T :=
    ((le_max_right Tcond Tlog).trans
      (le_max_right 2 (max Tcond Tlog)) |>.trans
      (le_max_right (Real.exp 1) (max 2 (max Tcond Tlog)))).trans hT
  have hsigmaHalf : 1 / 2 ≤ sigma := by linarith
  have hraw := hsource r T sigma hTtwo hsigmaHalf
    (hsigmaHigh.trans (by norm_num))
  simpa only [C] using
    fixed_primitive_low_strip_at_scale chi hK heta hC₀.le hTexp hQ hrQ
      hsigmaHalf hsigmaHigh (hTcond T hTcond') (hTlog T hTlog') hraw

/-- Endpoint-complete weld with the independently formalized high-strip
route.  Equality at `sigma = 7/10` is assigned to the Montgomery branch.  The
high-strip hypothesis is left in expanded theorem form so that no new
proposition-valued analytic placeholder is introduced. -/
theorem fixedPrimitivePolylogDensity_of_montgomery_and_high_strip
    (hMontgomery : ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (r : ℕ) [NeZero r] (T sigma : ℝ),
        2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 4 / 5 →
          (ambientZeroCountAtLevel r sigma T : ℝ) ≤
            C₀ * Real.rpow ((r : ℝ) * T) (inghamExponent sigma) *
              (Real.log ((r : ℝ) * T)) ^ 9)
    (hHigh : ∀ K eta : ℝ, 0 < K → 0 < eta →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
          (Q : ℝ) ≤ Real.rpow (Real.log T) K →
          7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
          ∀ (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r),
            chi.IsPrimitive → r ≤ Q →
              (dirichletZeroCount chi sigma T : ℝ) ≤
                C * Real.rpow T
                  (uniformCoeff * (1 - sigma) + eta)) :
    CGLPolylogBypass.FixedPrimitivePolylogDensity := by
  intro K delta eta hK hdelta heta
  obtain ⟨Clow, Tlow, hClow, hTlow, hlow⟩ :=
    montgomery_family_source_to_fixed_primitive_low_strip hMontgomery
      K delta eta hK hdelta heta
  obtain ⟨Chigh, Thigh, hChigh, hThigh, hhigh⟩ :=
    hHigh K eta hK heta
  let C : ℝ := max Clow Chigh
  let T₀ : ℝ := max Tlow Thigh
  have hC : 0 < C := hClow.trans_le (le_max_left _ _)
  refine ⟨C, T₀, hC, hTlow.trans (le_max_left _ _), ?_⟩
  intro T Q sigma hT hQ hsigmaLow hsigmaHigh r _inst chi hprim hrQ
  have hTnonneg : 0 ≤ T := by
    have : 2 ≤ T := hTlow.trans ((le_max_left Tlow Thigh).trans hT)
    linarith
  have hpow : 0 ≤ Real.rpow T (uniformCoeff * (1 - sigma) + eta) :=
    Real.rpow_nonneg hTnonneg _
  by_cases hsplit : sigma ≤ 7 / 10
  · have hraw := hlow T Q sigma ((le_max_left _ _).trans hT) hQ
      hsigmaLow hsplit r chi hprim hrQ
    exact hraw.trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  · have hsigmaJunction : 7 / 10 ≤ sigma := le_of_not_ge hsplit
    have hraw := hhigh T Q sigma ((le_max_right _ _).trans hT) hQ
      hsigmaJunction hsigmaHigh r chi hprim hrQ
    exact hraw.trans <| mul_le_mul_of_nonneg_right (le_max_right _ _) hpow

/-- Exact inhabitant of the canonical low-strip/principal field.  Montgomery
supplies every character through the junction.  The only additional input is
the conductor-one zeta estimate above the junction, stated directly on the
divisor-backed principal character rather than hidden in a general density
proposition. -/
theorem fixedPrimitiveLowStripOrPrincipalDensity_of_montgomery_and_zeta
    (hMontgomery : ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (r : ℕ) [NeZero r] (T sigma : ℝ),
        2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 4 / 5 →
          (ambientZeroCountAtLevel r sigma T : ℝ) ≤
            C₀ * Real.rpow ((r : ℝ) * T) (inghamExponent sigma) *
              (Real.log ((r : ℝ) * T)) ^ 9)
    (hZeta : ∀ eta : ℝ, 0 < eta →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T sigma : ℝ), T₀ ≤ T →
          7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
            (dirichletZeroCount
                (1 : DirichletCharacter ℂ 1) sigma T : ℝ) ≤
              C * Real.rpow T
                (MAPGuthMaynard.densityCoeff * (1 - sigma) + eta)) :
    CGLCompactStripDensityConstructor.FixedPrimitiveLowStripOrPrincipalDensity := by
  intro K delta eta hK hdelta heta
  obtain ⟨Clow, Tlow, hClow, hTlow, hlow⟩ :=
    montgomery_family_source_to_fixed_primitive_low_strip hMontgomery
      K delta eta hK hdelta heta
  obtain ⟨Czeta, Tzeta, hCzeta, hTzeta, hzeta⟩ := hZeta eta heta
  let C : ℝ := max Clow Czeta
  let T₀ : ℝ := max Tlow Tzeta
  have hC : 0 < C := hClow.trans_le (le_max_left _ _)
  refine ⟨C, T₀, hC, hTlow.trans (le_max_left _ _), ?_⟩
  intro T Q sigma hT hQ hsigmaLow hsigmaHigh r _inst chi hprim hrQ hcase
  have hTlow' : Tlow ≤ T := (le_max_left _ _).trans hT
  have hTzeta' : Tzeta ≤ T := (le_max_right _ _).trans hT
  have hTnonneg : 0 ≤ T := by linarith [hTlow.trans hTlow']
  have hpow :
      0 ≤ Real.rpow T
        (MAPGuthMaynard.densityCoeff * (1 - sigma) + eta) :=
    Real.rpow_nonneg hTnonneg _
  by_cases hsplit : sigma ≤ 7 / 10
  · have hraw := hlow T Q sigma hTlow' hQ hsigmaLow hsplit
      r chi hprim hrQ
    simpa only [ZeroDensityArithmetic.uniformCoeff,
      MAPGuthMaynard.densityCoeff] using
      hraw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
  · have hchi : chi = 1 := hcase.resolve_left hsplit
    have hr : r = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hchi,
        DirichletCharacter.conductor_one] at hprim
      exact hprim.symm
    subst r
    have hchi' : chi = (1 : DirichletCharacter ℂ 1) := hchi
    subst chi
    have hsigmaJunction : 7 / 10 ≤ sigma := le_of_not_ge hsplit
    have hraw := hzeta T sigma hTzeta' hsigmaJunction hsigmaHigh
    exact hraw.trans <| mul_le_mul_of_nonneg_right (le_max_right _ _) hpow

end
end MAPMontgomeryLowStrip

#print axioms MAPMontgomeryLowStrip.inghamExponent_nonneg
#print axioms MAPMontgomeryLowStrip.inghamExponent_le_one
#print axioms MAPMontgomeryLowStrip.log_conductor_mul_height_le
#print axioms MAPMontgomeryLowStrip.fixed_primitive_low_strip_at_scale
#print axioms MAPMontgomeryLowStrip.montgomery_family_source_to_fixed_primitive_low_strip
#print axioms MAPMontgomeryLowStrip.fixedPrimitivePolylogDensity_of_montgomery_and_high_strip
#print axioms MAPMontgomeryLowStrip.fixedPrimitiveLowStripOrPrincipalDensity_of_montgomery_and_zeta
