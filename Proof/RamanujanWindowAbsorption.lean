import RamanujanTailWeighted
import ZeroDeterminantSectorClosure
import MajorArcFinalAnalyticWeld
import SupportBoundaryQuantitative

/-!
# Translated-window absorption of the certified Ramanujan tail

This module removes the remaining finite-window bookkeeping between the
pointwise certified Ramanujan tail and an all-center square estimate.  The
zero shift is deleted explicitly, while positive and negative shifts are
handled as two injective `natAbs` fibers.
-/

namespace MAPRamanujanWindowAbsorption

open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction MixedMellinCert
open PrimePairEndpoints MAPHarmonicEndpoint
open MAPRamanujanTailWeighted MAPMixedMeanZeroClose MAPMixedMean

noncomputable section

/-- The order-two convolution power of zeta is the ordinary divisor-counting
function away from zero. -/
theorem tauAF_two_eq_card_divisors {n : ℕ} (hn : n ≠ 0) :
    tauAF 2 n = n.divisors.card := by
  rw [show 2 = 1 + 1 by omega, tauAF_succ_apply]
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := fun h => hn (by simpa [h] using hdvd)
  simp [tauAF, ArithmeticFunction.zeta_apply, hd0]

/-- Squaring the divisor count is absorbed by the order-four divisor
function. -/
theorem card_divisors_sq_le_tauAF_four {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ^ 2 ≤ tauAF 4 n := by
  rw [← tauAF_two_eq_card_divisors hn]
  simpa using tauAF_sq_le_tauAF_mul 2 n

/-- Any finite set of signed nonzero shifts contributes at most two copies of
the corresponding positive `natAbs` moment.  This is the exact `±h` weld. -/
theorem sum_int_natAbs_nonzero_le_two_sum_Icc
    (s : Finset ℤ) (R : ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hR : ∀ z ∈ s, z ≠ 0 → z.natAbs ≤ R) :
    (∑ z ∈ s, if z = 0 then 0 else f z.natAbs) ≤
      2 * ∑ n ∈ Finset.Icc 1 R, f n := by
  classical
  let s0 : Finset ℤ := s.filter (fun z => z ≠ 0)
  let sp : Finset ℤ := s0.filter (fun z => 0 < z)
  let sn : Finset ℤ := s0.filter (fun z => ¬ 0 < z)
  have hzero :
      (∑ z ∈ s, if z = 0 then 0 else f z.natAbs) =
        ∑ z ∈ s0, f z.natAbs := by
    simp only [s0, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hz0 : z = 0 <;> simp [hz0]
  have hsplit :
      (∑ z ∈ s0, f z.natAbs) =
        (∑ z ∈ sp, f z.natAbs) + ∑ z ∈ sn, f z.natAbs := by
    simpa [sp, sn] using
      (Finset.sum_filter_add_sum_filter_not s0 (fun z : ℤ => 0 < z)
        (fun z => f z.natAbs)).symm
  have hposinj : Set.InjOn Int.natAbs (sp : Set ℤ) := by
    intro a ha b hb hab
    have ha' : a ∈ s0 ∧ 0 < a := by simpa [sp] using ha
    have hb' : b ∈ s0 ∧ 0 < b := by simpa [sp] using hb
    exact (Int.natAbs_inj_of_nonneg_of_nonneg ha'.2.le hb'.2.le).mp hab
  have hneginj : Set.InjOn Int.natAbs (sn : Set ℤ) := by
    intro a ha b hb hab
    have ha' : a ∈ s0 ∧ ¬ 0 < a := by simpa [sn] using ha
    have hb' : b ∈ s0 ∧ ¬ 0 < b := by simpa [sn] using hb
    exact (Int.natAbs_inj_of_nonpos_of_nonpos
      (le_of_not_gt ha'.2) (le_of_not_gt hb'.2)).mp hab
  have hpossub : sp.image Int.natAbs ⊆ Finset.Icc 1 R := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    have hz' : z ∈ s0 ∧ 0 < z := by simpa [sp] using hz
    have hzs : z ∈ s ∧ z ≠ 0 := by simpa [s0] using hz'.1
    rw [Finset.mem_Icc]
    exact ⟨Int.natAbs_pos.mpr hzs.2, hR z hzs.1 hzs.2⟩
  have hnegsub : sn.image Int.natAbs ⊆ Finset.Icc 1 R := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    have hz' : z ∈ s0 ∧ ¬ 0 < z := by simpa [sn] using hz
    have hzs : z ∈ s ∧ z ≠ 0 := by simpa [s0] using hz'.1
    rw [Finset.mem_Icc]
    exact ⟨Int.natAbs_pos.mpr hzs.2, hR z hzs.1 hzs.2⟩
  have hpos : (∑ z ∈ sp, f z.natAbs) ≤
      ∑ n ∈ Finset.Icc 1 R, f n := by
    rw [← Finset.sum_image hposinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpossub
      (fun n hn hnot => hf n)
  have hneg : (∑ z ∈ sn, f z.natAbs) ≤
      ∑ n ∈ Finset.Icc 1 R, f n := by
    rw [← Finset.sum_image hneginj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hnegsub
      (fun n hn hnot => hf n)
  rw [hzero, hsplit]
  linarith

/-- Squared pointwise Ramanujan discrepancy, with the fourth divisor moment
made explicit. -/
theorem norm_truncatedSingularCoefficient_sub_singular_sq_le_tauAF_four
    {h : ℤ} (hh : h ≠ 0) (Q : ℕ) :
    ‖MAPMajorArcWeld.truncatedSingularCoefficient Q h -
        ((singularSeriesTotal h : ℝ) : ℂ)‖ ^ 2 ≤
      basePrimeMassConstant ^ 2 * (tauAF 4 h.natAbs : ℝ) ^ 2 /
        (Q + 1 : ℕ) := by
  have htail :=
    norm_truncatedSingularCoefficient_sub_singular_le_divisors hh Q
  have hnat : h.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hh
  have hdivNat := card_divisors_sq_le_tauAF_four hnat
  have hdiv : (h.natAbs.divisors.card : ℝ) ^ 2 ≤
      (tauAF 4 h.natAbs : ℝ) := by exact_mod_cast hdivNat
  have hbase0 : 0 ≤ basePrimeMassConstant := basePrimeMassConstant_nonneg
  have hden0 : 0 ≤ Real.sqrt ((Q : ℝ) + 1) := Real.sqrt_nonneg _
  have hdenpos : 0 < Real.sqrt ((Q : ℝ) + 1) := by positivity
  have hright0 : 0 ≤
      (basePrimeMassConstant * (h.natAbs.divisors.card : ℝ) ^ 2) /
        Real.sqrt (Q + 1) := div_nonneg (mul_nonneg hbase0 (sq_nonneg _)) hden0
  have hsquare :
      ‖MAPMajorArcWeld.truncatedSingularCoefficient Q h -
          ((singularSeriesTotal h : ℝ) : ℂ)‖ ^ 2 ≤
        ((basePrimeMassConstant * (h.natAbs.divisors.card : ℝ) ^ 2) /
          Real.sqrt (Q + 1)) ^ 2 := by
    nlinarith [norm_nonneg
      (MAPMajorArcWeld.truncatedSingularCoefficient Q h -
        ((singularSeriesTotal h : ℝ) : ℂ))]
  have hfour : (h.natAbs.divisors.card : ℝ) ^ 4 ≤
      (tauAF 4 h.natAbs : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (h.natAbs.divisors.card : ℝ),
      sq_nonneg (tauAF 4 h.natAbs : ℝ)]
  calc
    ‖MAPMajorArcWeld.truncatedSingularCoefficient Q h -
        ((singularSeriesTotal h : ℝ) : ℂ)‖ ^ 2 ≤
      ((basePrimeMassConstant * (h.natAbs.divisors.card : ℝ) ^ 2) /
        Real.sqrt (Q + 1)) ^ 2 := hsquare
    _ = basePrimeMassConstant ^ 2 *
        (h.natAbs.divisors.card : ℝ) ^ 4 / (Q + 1 : ℕ) := by
      rw [div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Q : ℝ) + 1)]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ basePrimeMassConstant ^ 2 * (tauAF 4 h.natAbs : ℝ) ^ 2 /
        (Q + 1 : ℕ) := by
      gcongr

end
end MAPRamanujanWindowAbsorption

namespace MAPRamanujanWindowAbsorption

open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction MixedMellinCert
open PrimePairEndpoints MAPHarmonicEndpoint
open MAPRamanujanTailWeighted MAPMixedMeanZeroClose MAPMixedMean

noncomputable section

/-- The exact translated-window square energy of the Ramanujan truncation
error.  The singular series is undefined at zero, so that shift is explicitly
deleted rather than fed to the pointwise theorem. -/
def ramanujanTailEnergy (H h₀ : ℝ) (Q : ℕ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀,
    if h = 0 then 0 else
      ‖MAPMajorArcWeld.truncatedSingularCoefficient Q h -
        ((singularSeriesTotal h : ℝ) : ℂ)‖ ^ 2

/-- Uniform finite-window fourth-divisor bound before inserting the harmonic
moment estimate.  A positive integer can occur at most once on each of the
positive and negative signed fibers. -/
theorem ramanujanTailEnergy_le_zeroSecondMoment
    {H h₀ : ℝ} (Q R : ℕ)
    (hR : ∀ h ∈ translatedWindow H h₀, h ≠ 0 → h.natAbs ≤ R) :
    ramanujanTailEnergy H h₀ Q ≤
      (basePrimeMassConstant ^ 2 / (Q + 1 : ℕ)) *
        (2 * (zeroSecondMoment 4 R : ℝ)) := by
  let c : ℝ := basePrimeMassConstant ^ 2 / (Q + 1 : ℕ)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hpoint :
      ramanujanTailEnergy H h₀ Q ≤
        ∑ h ∈ translatedWindow H h₀,
          if h = 0 then 0 else c * (tauAF 4 h.natAbs : ℝ) ^ 2 := by
    unfold ramanujanTailEnergy
    apply Finset.sum_le_sum
    intro h hhwin
    by_cases hh : h = 0
    · simp [hh]
    · rw [if_neg hh, if_neg hh]
      have ht :=
        norm_truncatedSingularCoefficient_sub_singular_sq_le_tauAF_four hh Q
      simpa [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using ht
  have hsigned := sum_int_natAbs_nonzero_le_two_sum_Icc
    (translatedWindow H h₀) R (fun n => (tauAF 4 n : ℝ) ^ 2)
    (fun n => sq_nonneg _) hR
  have hmomentIdentity :
      (∑ n ∈ Finset.Icc 1 R, (tauAF 4 n : ℝ) ^ 2) =
        (zeroSecondMoment 4 R : ℝ) := by
    unfold zeroSecondMoment
    push_cast
    rfl
  calc
    ramanujanTailEnergy H h₀ Q ≤
        ∑ h ∈ translatedWindow H h₀,
          if h = 0 then 0 else c * (tauAF 4 h.natAbs : ℝ) ^ 2 := hpoint
    _ = c * (∑ h ∈ translatedWindow H h₀,
          if h = 0 then 0 else (tauAF 4 h.natAbs : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hz : h = 0 <;> simp [hz]
    _ ≤ c * (2 * ∑ n ∈ Finset.Icc 1 R, (tauAF 4 n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsigned hc0
    _ = c * (2 * (zeroSecondMoment 4 R : ℝ)) := by rw [hmomentIdentity]
    _ = (basePrimeMassConstant ^ 2 / (Q + 1 : ℕ)) *
        (2 * (zeroSecondMoment 4 R : ℝ)) := by rfl

/-- Harmonic-moment absorption of the complete translated Ramanujan-tail
energy.  The exponent `15 = 4^2-1` is certified by the existing zero-sector
moment theorem, not assumed as a divisor-moment axiom. -/
theorem ramanujanTailEnergy_le_harmonic
    {H h₀ : ℝ} (Q R : ℕ)
    (hR : ∀ h ∈ translatedWindow H h₀, h ≠ 0 → h.natAbs ≤ R) :
    ramanujanTailEnergy H h₀ Q ≤
      (2 * basePrimeMassConstant ^ 2 * (R : ℝ) *
          (((harmonic R : ℚ) : ℝ) ^ 15)) /
        (Q + 1 : ℕ) := by
  have hfinite := ramanujanTailEnergy_le_zeroSecondMoment Q R hR
  have hmomentQ := zeroSecondMoment_cast_le_harmonic 4 R (by norm_num)
  have hmomentR : (zeroSecondMoment 4 R : ℝ) ≤
      (R : ℝ) * (((harmonic R : ℚ) : ℝ) ^ 15) := by
    norm_num at hmomentQ
    exact_mod_cast hmomentQ
  have hfac0 : 0 ≤ basePrimeMassConstant ^ 2 / (Q + 1 : ℕ) := by positivity
  calc
    ramanujanTailEnergy H h₀ Q ≤
      (basePrimeMassConstant ^ 2 / (Q + 1 : ℕ)) *
        (2 * (zeroSecondMoment 4 R : ℝ)) := hfinite
    _ ≤ (basePrimeMassConstant ^ 2 / (Q + 1 : ℕ)) *
        (2 * ((R : ℝ) * (((harmonic R : ℚ) : ℝ) ^ 15))) := by
      gcongr
    _ = (2 * basePrimeMassConstant ^ 2 * (R : ℝ) *
          (((harmonic R : ℚ) : ℝ) ^ 15)) /
        (Q + 1 : ℕ) := by ring

end
end MAPRamanujanWindowAbsorption

namespace MAPRamanujanWindowAbsorption

open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction MixedMellinCert
open PrimePairEndpoints MAPHarmonicEndpoint
open MAPRamanujanTailWeighted MAPMixedMeanZeroClose MAPMixedMean

noncomputable section

/-- A natural prefix radius containing every shift in a legal all-center
window. -/
def legalRamanujanRadius (X ε : ℝ) : ℕ :=
  ⌈2 * Real.rpow X (1 - ε)⌉₊

theorem natAbs_le_legalRamanujanRadius
    {X H h₀ ε : ℝ}
    (hlegal : LegalParameters ε X H h₀)
    {h : ℤ} (hh : h ∈ translatedWindow H h₀) :
    h.natAbs ≤ legalRamanujanRadius X ε := by
  have hreal := SupportBoundaryQuantitative.natAbs_shift_le_two_rpow hlegal hh
  have hceil : 2 * Real.rpow X (1 - ε) ≤
      (legalRamanujanRadius X ε : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hreal.trans hceil

/-- Source-faithful all-center specialization of the global fourth-moment
bound.  Its numerator contains the *shift radius* rather than the aperture;
this distinction is mathematically essential for the downstream audit. -/
theorem legal_ramanujanTailEnergy_le_global_harmonic
    {X H h₀ ε : ℝ} (Q : ℕ)
    (hlegal : LegalParameters ε X H h₀) :
    ramanujanTailEnergy H h₀ Q ≤
      (2 * basePrimeMassConstant ^ 2 *
          (legalRamanujanRadius X ε : ℝ) *
          (((harmonic (legalRamanujanRadius X ε) : ℚ) : ℝ) ^ 15)) /
        (Q + 1 : ℕ) := by
  apply ramanujanTailEnergy_le_harmonic Q (legalRamanujanRadius X ε)
  intro h hh hne
  exact natAbs_le_legalRamanujanRadius hlegal hh

/-- Direct insertion of the now-certified Ramanujan tail into the pointwise
major-arc weld.  No independent `hRamanujan` premise remains; zero is still
excluded because the literal coefficient has a different zero-shift value. -/
theorem norm_majorCoefficient_sub_overlapSingular_le_ramanujan_divisors
    {X E : ℝ} {B D : ℕ} {h : ℤ}
    (hX : 1 < X) (hE : 0 ≤ E)
    (hh0 : h ≠ 0) (hhX : |(h : ℝ)| ≤ X)
    (hR : 0 < MAPMajorArcWeld.paperArcRadius X D)
    (hRhalf : MAPMajorArcWeld.paperArcRadius X D < (1 : ℝ) / 2)
    (hgrowth : 2 * (Real.log X) ^ (D + 2 * B) < X)
    (hpointwise : ∀ q a : ℕ, ∀ β : ℝ,
      1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
      a < q → a.Coprime q →
      |β| ≤ MAPMajorArcWeld.paperArcRadius X D →
      ‖primeExponentialSum X
          (MAPMajorArcWeld.rationalCenter q a + (β : UnitAddCircle)) -
        MAPMajorArcWeld.primeMajorCoefficient q *
          MAPContinuousOverlap.dyadicAmplitude X β‖ ≤ E) :
    ‖majorCoefficient X B D h -
        (((X - |(h : ℝ)|) * singularSeriesTotal h : ℝ) : ℂ)‖ ≤
      ((MAPMajorArcWeld.paperDenominatorCutoff X B : ℕ) : ℝ) ^ 2 *
          (2 * MAPMajorArcWeld.paperArcRadius X D * (E * (2 * X + E))) +
        (‖((singularSeriesTotal h : ℝ) : ℂ)‖ +
            (basePrimeMassConstant * (h.natAbs.divisors.card : ℝ) ^ 2) /
              Real.sqrt (MAPMajorArcWeld.paperDenominatorCutoff X B + 1)) *
          (2 / (Real.pi ^ 2 * MAPMajorArcWeld.paperArcRadius X D)) +
        ((basePrimeMassConstant * (h.natAbs.divisors.card : ℝ) ^ 2) /
            Real.sqrt (MAPMajorArcWeld.paperDenominatorCutoff X B + 1)) * X := by
  let T : ℝ :=
    (basePrimeMassConstant * (h.natAbs.divisors.card : ℝ) ^ 2) /
      Real.sqrt (MAPMajorArcWeld.paperDenominatorCutoff X B + 1)
  have hT : 0 ≤ T := by
    dsimp [T]
    exact div_nonneg
      (mul_nonneg basePrimeMassConstant_nonneg (sq_nonneg _))
      (Real.sqrt_nonneg _)
  have htail :
      ‖MAPMajorArcWeld.truncatedSingularCoefficient
          (MAPMajorArcWeld.paperDenominatorCutoff X B) h -
        ((singularSeriesTotal h : ℝ) : ℂ)‖ ≤ T := by
    exact norm_truncatedSingularCoefficient_sub_singular_le_divisors
      hh0 (MAPMajorArcWeld.paperDenominatorCutoff X B)
  simpa [T] using
    MAPMajorArcFinalAnalyticWeld.norm_majorCoefficient_sub_overlapSingular_le
      hX hE hT hhX hR hRhalf hgrowth hpointwise htail

end
end MAPRamanujanWindowAbsorption
