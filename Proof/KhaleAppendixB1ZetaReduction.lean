import KhaleAppendixB1LazyKeyReduction
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The `(lazyzeta)` insertion in Khale Appendix B.1

This separates equation `(lazykey)` from the elementary zeta estimate used in
the next line.  The combination is fully certified; the two propositions are
literal analytic source leaves rather than zero-free-region restatements.
-/

namespace MAPKhaleAppendixB1ZetaReduction

open MAPKhaleAppendixBSource MAPKhaleAppendixBEtaAlgebra
open MAPKhaleAppendixB1LazyKeyReduction

noncomputable section

/-- Real logarithm of zeta on the positive real axis, in the exact form used
by Khale. -/
def zetaLog (eta : ℝ) : ℝ :=
  Real.log (Complex.re (riemannZeta (((1 + eta : ℝ) : ℂ))))

/-- Equation `(lazykey)` before applying `(lazyzeta)`. -/
abbrev AppendixBLazyKeyBeforeZetaEstimate : Prop :=
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
      beta < 1 ∧
      let eta := khaleEta B gamma
      0.953 / (1 - beta) ≤
        (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
            Real.log (A + 1)) +
        (10.01055 / 2) * (1 / eta) * zetaLog eta +
        (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937)

/-- The literal estimate `(lazyzeta)`, restricted to the source eta values
and startup range actually consumed by B.1. -/
abbrev AppendixBLazyZetaBound : Prop :=
  ∀ eta : ℝ, 0 < eta → eta ≤ 0.06 →
    (10.01055 / 2) * (1 / eta) * zetaLog eta ≤
      (10.01055 / 2) * (1 / eta) * Real.log (1 / eta) +
        0.3 * 10.01055

/-- The exact part of Khale's elementary `zetabound` lemma used here. -/
abbrev AppendixBZetaPointwise06 : Prop :=
  ∀ eta : ℝ, 0 < eta → eta ≤ 0.06 →
    0 < Complex.re (riemannZeta (((1 + eta : ℝ) : ℂ))) ∧
      Complex.re (riemannZeta (((1 + eta : ℝ) : ℂ))) ≤ 0.6 + 1 / eta

/-- The pointwise zeta bound implies the displayed `(lazyzeta)` inequality;
the `0.3 b0` is exactly `(b0/(2 eta)) * (0.6 eta)`. -/
theorem lazyZetaBound_of_pointwise06
    (hPointwise : AppendixBZetaPointwise06) :
    AppendixBLazyZetaBound := by
  intro eta heta hetaTop
  have hz := hPointwise eta heta hetaTop
  have honeEta : 0 < 1 / eta := one_div_pos.mpr heta
  have hupperPos : 0 < 0.6 + 1 / eta := by positivity
  have hlogmono : zetaLog eta ≤ Real.log (0.6 + 1 / eta) := by
    unfold zetaLog
    exact Real.log_le_log hz.1 hz.2
  have honePlus : 0 < 1 + 0.6 * eta := by positivity
  have hfactor : 0.6 + 1 / eta = (1 / eta) * (1 + 0.6 * eta) := by
    field_simp [heta.ne']
    ring
  have hlogUpper : Real.log (0.6 + 1 / eta) ≤
      Real.log (1 / eta) + 0.6 * eta := by
    rw [hfactor, Real.log_mul honeEta.ne' honePlus.ne']
    have h := Real.log_le_sub_one_of_pos honePlus
    nlinarith
  have hlog : zetaLog eta ≤ Real.log (1 / eta) + 0.6 * eta :=
    hlogmono.trans hlogUpper
  have hcoef : 0 ≤ (10.01055 / 2) * (1 / eta) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog hcoef
  nlinarith [show eta * (1 / eta) = 1 by field_simp]

/-- Certified insertion of `(lazyzeta)` into `(lazykey)`. -/
theorem lazyKeyAfterZeta_of_beforeZeta_and_zetaBound
    (hKey : AppendixBLazyKeyBeforeZetaEstimate)
    (hZeta : AppendixBLazyZetaBound) :
    AppendixBLazyKeyAfterZetaEstimate := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  have hkey := hKey A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero
  refine ⟨hkey.1, ?_⟩
  let eta := khaleEta B gamma
  have hgamma0 : Real.exp 10650 ≤ gamma := hT₀.trans hgamma
  have hLlower : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma0
  have hL : 0 < Real.log gamma := by linarith
  have hell : 0 < Real.log (Real.log gamma) :=
    Real.log_pos (by linarith [hLlower])
  have hratioGamma : 5110.6 / B ≤
      Real.log gamma / Real.log (Real.log gamma) :=
    hratio.trans (log_ratio_mono_from_exp10650 hT₀ hgamma)
  have hetaPos : 0 < eta := khaleEta_pos hB hL hell
  have hetaTop : eta ≤ 0.06 :=
    khaleEta_le_point_zero_six_of_ratio hB hL hell hratioGamma
  have hzeta := hZeta eta hetaPos hetaTop
  have hkey' : 0.953 / (1 - beta) ≤
      (33.3275 / 2) * (1 / eta) *
          ((2 / 3 : ℝ) * Real.log (Real.log gamma) +
            B * Real.rpow eta (3 / 2 : ℝ) * Real.log gamma +
            Real.log (A + 1)) +
        (10.01055 / 2) * (1 / eta) * zetaLog eta +
        (33.3275 / 2) * Real.log q +
        33.3275 * Real.exp (-1937) := by
    simpa only [eta] using hkey.2
  dsimp only
  exact hkey'.trans (by linarith)

end
end MAPKhaleAppendixB1ZetaReduction

#print axioms MAPKhaleAppendixB1ZetaReduction.lazyKeyAfterZeta_of_beforeZeta_and_zetaBound
