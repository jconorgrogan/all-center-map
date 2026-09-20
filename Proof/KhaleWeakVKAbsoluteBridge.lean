import KhaleWeakVKDeterministicBridge

/-!
# Sign-symmetric Khale bridge for equation (2.7)

Khale's published high-ordinate region is stated in terms of `|t|`.  The
earlier deterministic MAP bridge used a positive variable `t`, which is not
by itself sufficient for the zero rectangle `|Im rho| <= T`.  This file makes
the absolute-value convention literal and proves the same weak-gap and
near-factor deductions for both signs of the ordinate.

No zero-free theorem is asserted here.  The source nonvanishing conclusion is
a local higher-order hypothesis of the final theorem.
-/

namespace MAPKhaleWeakVKApplication

open Filter Asymptotics

noncomputable section

/-- Khale's weak denominator with the source's literal `|t|` convention. -/
def khaleWeakDenominatorAbs (q : ℕ) (t : ℝ) : ℝ :=
  khaleWeakDenominator q |t|

theorem khaleWeakDenominatorAbs_pos
    {q : ℕ} {t : ℝ} (hq : 1 ≤ q) (ht : 3 ≤ |t|) :
    0 < khaleWeakDenominatorAbs q t := by
  exact khaleWeakDenominator_pos hq ht

/-- A zero outside the sign-symmetric Khale region has the literal reciprocal
gap.  The L-function is evaluated at the original signed ordinate. -/
theorem one_div_khaleWeakDenominatorAbs_le_one_sub_sigma_of_zero
    {q : ℕ} [NeZero q] {t sigma : ℝ} (chi : DirichletCharacter ℂ q)
    (hq : 1 ≤ q) (ht : 3 ≤ |t|)
    (hnonzero :
      1 - 1 / khaleWeakDenominatorAbs q t ≤ sigma →
        DirichletCharacter.LFunction chi
          ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hzero : DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (t : ℂ) * Complex.I) = 0) :
    1 / khaleWeakDenominatorAbs q t ≤ 1 - sigma := by
  have hden := khaleWeakDenominatorAbs_pos hq ht
  by_contra hgap
  have hboundary : 1 - 1 / khaleWeakDenominatorAbs q t ≤ sigma := by
    linarith
  exact (hnonzero hboundary) hzero

/-- The reciprocal denominator supplies the same uniform weak-VK gap for
both signs of the ordinate. -/
theorem weakGap_le_of_one_div_khaleWeakDenominatorAbs_le
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) (t sigma : ℝ),
      1 ≤ q →
      (q : ℝ) ≤ Real.rpow (Real.log X) K →
      3 ≤ |t| → |t| ≤ X →
      1 / khaleWeakDenominatorAbs q t ≤ 1 - sigma →
      (1 / (18 * K + 104)) *
          Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ 1 - sigma := by
  filter_upwards
      [weakGap_le_of_one_div_khaleWeakDenominator_le K hK] with
      X hgap q t sigma hq hqX ht htX hrecip
  exact hgap q |t| sigma hq hqX ht htX hrecip

/-- Complete sign-symmetric deterministic consequence needed when summing
the full multiplicity-weighted rectangle in equation (2.7). -/
theorem khaleWeakRegionAbs_nearFactor_beats_polylog
    (K P A : ℝ) (hK : 0 ≤ K) (hP : 0 ≤ P) (hA : 0 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (t sigma : ℝ)
        (chi : DirichletCharacter ℂ q),
      1 ≤ q →
      (q : ℝ) ≤ Real.rpow (Real.log X) K →
      3 ≤ |t| → |t| ≤ X →
      (1 - 1 / khaleWeakDenominatorAbs q t ≤ sigma →
        DirichletCharacter.LFunction chi
          ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0) →
      DirichletCharacter.LFunction chi
          ((sigma : ℂ) + (t : ℂ) * Complex.I) = 0 →
      Real.rpow (Real.log X) P *
          Real.rpow X (-((1 - sigma) / 12)) ≤
        Real.rpow (Real.log X) (-A) := by
  have hc : 0 < 1 / (18 * K + 104) := by
    positivity
  filter_upwards
      [weakGap_le_of_one_div_khaleWeakDenominatorAbs_le K hK,
        WeakVKNear.weakGap_nearFactor_beats_polylog
          (3 / 4 : ℝ) (1 / (18 * K + 104)) P A
          (by norm_num) hc hP hA] with
      X hgap hdecay q _inst t sigma chi hq hqX ht htX hnonzero hzero
  have hrecip :=
    one_div_khaleWeakDenominatorAbs_le_one_sub_sigma_of_zero
      chi hq ht hnonzero hzero
  have homega := hgap q t sigma hq hqX ht htX hrecip
  exact hdecay (1 - sigma) homega

end

end MAPKhaleWeakVKApplication

#print axioms MAPKhaleWeakVKApplication.khaleWeakDenominatorAbs_pos
#print axioms MAPKhaleWeakVKApplication.one_div_khaleWeakDenominatorAbs_le_one_sub_sigma_of_zero
#print axioms MAPKhaleWeakVKApplication.weakGap_le_of_one_div_khaleWeakDenominatorAbs_le
#print axioms MAPKhaleWeakVKApplication.khaleWeakRegionAbs_nearFactor_beats_polylog
