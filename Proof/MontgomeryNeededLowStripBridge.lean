import APZeroDensityCertificate
import FixedCharacterReduction
import CGLCompactStripDensityConstructor

/-!
# The exact Montgomery low-strip source actually consumed by MAP

The MAP compact-density splice uses Montgomery's family theorem only through
`7/10`.  This file records precisely that restricted analytic source and proves
all subsequent conductor absorption and principal/nonprincipal splicing.

This module intentionally avoids the much larger AP integration import graph:
the fact that one character count is a summand of the ambient family is proved
locally from the definition.
-/

namespace MAPMontgomeryNeededLowStrip

open Filter
open DirichletZeros ZeroDensityArithmetic ZeroDensityInterface
open MAPAPZeroDensityCert CGLPolylogBypass

noncomputable section

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

/-- One character zero count is a literal nonnegative summand of the ambient
fixed-modulus family count. -/
theorem dirichletZeroCount_le_ambientZeroCountAtLevel
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma T : ℝ) :
    dirichletZeroCount chi sigma T ≤
      ambientZeroCountAtLevel q sigma T := by
  simp only [ambientZeroCountAtLevel, NeZero.ne q, dite_false]
  exact Finset.single_le_sum
    (f := fun psi : DirichletCharacter ℂ q =>
      dirichletZeroCount psi sigma T)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ chi)

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


/-- Weakest closed Montgomery family estimate used by the MAP splice. -/
def MontgomeryNeededLowStripSource : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (r : ℕ) [NeZero r] (T sigma : ℝ),
      2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 7 / 10 →
        (ambientZeroCountAtLevel r sigma T : ℝ) ≤
          C₀ * Real.rpow ((r : ℝ) * T) (inghamExponent sigma) *
            (Real.log ((r : ℝ) * T)) ^ 9

/-- The former source surface, stated through `4/5`, restricts to the exact
range needed here.  This preserves backward compatibility while allowing new
callers to certify only the weaker statement. -/
theorem neededLowStripSource_of_closed
    (h : ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (r : ℕ) [NeZero r] (T sigma : ℝ),
        2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 4 / 5 →
          (ambientZeroCountAtLevel r sigma T : ℝ) ≤
            C₀ * Real.rpow ((r : ℝ) * T) (inghamExponent sigma) *
              (Real.log ((r : ℝ) * T)) ^ 9) :
    MontgomeryNeededLowStripSource := by
  obtain ⟨C₀, hC₀, hbound⟩ := h
  refine ⟨C₀, hC₀, ?_⟩
  intro r _inst T sigma hT hsigmaLow hsigmaHigh
  exact hbound r T sigma hT hsigmaLow
    (hsigmaHigh.trans (by norm_num))

/-- The restricted family source gives exactly the fixed-primitive low strip.
The proof spends half of `eta` on the conductor and half on the ninth
logarithmic power, exactly as in the larger-strip adapter. -/
theorem needed_montgomery_to_fixed_primitive_low_strip
    (hMontgomery : MontgomeryNeededLowStripSource) :
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
  have hraw := hsource r T sigma hTtwo hsigmaHalf hsigmaHigh
  simpa only [C] using
    fixed_primitive_low_strip_at_scale chi hK heta hC₀.le hTexp hQ hrQ
      hsigmaHalf hsigmaHigh (hTcond T hTcond') (hTlog T hTlog') hraw

/-- Exact low/principal compact-density base from the restricted Montgomery
source and a conductor-one high-strip theorem.  Equality at `7/10` stays in
the Montgomery branch. -/
theorem fixedPrimitiveLowStripOrPrincipalDensity_of_needed_montgomery_and_zeta
    (hMontgomery : MontgomeryNeededLowStripSource)
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
    needed_montgomery_to_fixed_primitive_low_strip hMontgomery
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
end MAPMontgomeryNeededLowStrip

#print axioms MAPMontgomeryNeededLowStrip.dirichletZeroCount_le_ambientZeroCountAtLevel
#print axioms MAPMontgomeryNeededLowStrip.needed_montgomery_to_fixed_primitive_low_strip
#print axioms MAPMontgomeryNeededLowStrip.fixedPrimitiveLowStripOrPrincipalDensity_of_needed_montgomery_and_zeta
#print axioms MAPMontgomeryNeededLowStrip.neededLowStripSource_of_closed
