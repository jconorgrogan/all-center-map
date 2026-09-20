import JutilaGappedCollarSelectedP53Adapter
import HuxleyCompactGapExponent

/-!
# Huxley 1972, equation (1.9), to the principal MAP collar

The source is M. N. Huxley, *On the Difference between Consecutive
Primes*, Invent. Math. **15** (1972), 164--170.  On printed p.164,
equations (1.4) and (1.9), `N(alpha,T)` counts zeta zeros in
`alpha <= beta <= 1`, `-T <= gamma <= T`, and

`N(alpha,T) << T^(3*(1-alpha)/(3*alpha-1)) (log T)^44`.

The sentence continuing at the top of printed p.165 states that (1.9) is
uniform for `3/4 <= alpha <= 1`.  This module records exactly that explicit
logarithmic source and proves the complete deterministic bridge to the
separate conductor-one selected-system leaf.  No `T^o(1)` interface is used.
-/

namespace MAPPrincipalZetaHuxley1972Theorem19Adapter

open DirichletZeros
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPHuxleyCompactGapExponent
open MAPJutilaCollarMeshCutoff MAPJutilaCollarA5Budget
open MAPJutilaGappedCollarFiniteAggregation

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- Literal explicit-log source surface of Huxley 1972, equations (1.4) and
(1.9), including the uniformity statement at the top of printed p.165.

This is the first genuinely analytic source theorem in the principal-collar
route. -/
def Huxley1972Theorem19ExactLogDensity : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ T sigma : ℝ, T₀ ≤ T →
      3 / 4 ≤ sigma → sigma ≤ 1 →
      ((zeroSupport chiOne sigma T).card : ℝ) ≤
        C * Real.rpow (Real.log T) 44 *
          Real.rpow T (huxleyDensityExponent sigma)

/-- Exact source-facing closure of the principal selected-system p.53 leaf
from Huxley 1972 (1.9). -/
theorem principalSelectedP53_of_huxley1972
    (hsource : Huxley1972Theorem19ExactLogDensity) :
    JutilaGappedSelectedPrincipalP53Eventually := by
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := hsource
  let R₀ : ℝ := max T₀ 6
  refine ⟨C, R₀, 44, hC, le_max_right _ _, by norm_num, ?_⟩
  intro q _inst chi T sigma omega W hprim hchi hT hsigmaLow hsigmaHigh
    _homega _hgap hscale _hregularGap hWsub _hWsep _hWcard
  have hq : q = 1 := by
    have hcond : chi.conductor = q := hprim
    rw [hchi, DirichletCharacter.conductor_one] at hcond
    exact hcond.symm
  subst q
  have hchiOne : chi = (1 : DirichletCharacter ℂ 1) := hchi
  subst chi
  simp only [Nat.cast_one, one_mul] at hscale ⊢
  have hTzero : T₀ ≤ T := by
    exact (le_max_left T₀ 6).trans hscale
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hWsupport : W ⊆ zeroSupport chiOne sigma T := by
    intro rho hrho
    exact (Finset.mem_filter.mp (hWsub hrho)).1
  have hcard : (W.card : ℝ) ≤ ((zeroSupport chiOne sigma T).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hWsupport
  have hsourceBound := hbound T sigma hTzero
    ((by norm_num : (3 / 4 : ℝ) ≤ 279 / 280).trans hsigmaLow)
    hsigmaHigh
  have hden : 0 < 3 * sigma - 1 := by linarith
  have hgap0 : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigmaHigh
  have hcoeff : 3 / (3 * sigma - 1) ≤
      2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget := by
    apply (div_le_iff₀ hden).2
    norm_num [collarDelta, detectorLogBudget]
    nlinarith
  have hexp : huxleyDensityExponent sigma ≤
      (2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
        (1 - sigma) := by
    rw [show huxleyDensityExponent sigma =
      (3 / (3 * sigma - 1)) * (1 - sigma) by
        unfold huxleyDensityExponent
        field_simp]
    exact mul_le_mul_of_nonneg_right hcoeff hgap0
  have hpower := Real.rpow_le_rpow_of_exponent_le hTone hexp
  have hlog0 : 0 ≤ Real.rpow (Real.log T) (44 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg hTone) _
  calc
    (W.card : ℝ) ≤ ((zeroSupport chiOne sigma T).card : ℝ) := hcard
    _ ≤ C * Real.rpow (Real.log T) 44 *
          Real.rpow T (huxleyDensityExponent sigma) := hsourceBound
    _ ≤ C * Real.rpow (Real.log T) 44 *
          Real.rpow T
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - sigma)) := by
      exact mul_le_mul_of_nonneg_left hpower
        (mul_nonneg hC.le hlog0)

end

end MAPPrincipalZetaHuxley1972Theorem19Adapter

#print axioms MAPPrincipalZetaHuxley1972Theorem19Adapter.principalSelectedP53_of_huxley1972
