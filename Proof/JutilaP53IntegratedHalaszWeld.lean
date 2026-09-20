import JutilaP53EnergyContinuity

/-!
# Integrated Halasz weld for Jutila p.53

This module carries the common Halasz phase through the literal double
smoothing average (3.4)--(3.6).  It leaves the coefficient quotient bound and
the integrated character-labelled kernel estimate as explicit premises.
-/

namespace MAPJutilaP53IntegratedHalaszWeld

open scoped BigOperators
open Set MeasureTheory
open MAPJutilaDeterministicCore
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53InfiniteHalaszWeld
open MAPJutilaP53EnergyContinuity
open MAPMontgomeryInfiniteHalasz

noncomputable section

private def selectedPhase {q : ℕ}
    (rows : Finset (JutilaP53Row q)) (alpha : ℝ)
    (row : JutilaP53Row q) (n : ℕ) : ℂ :=
  if row ∈ rows then jutilaP53Phase alpha row n else 0

set_option maxHeartbeats 1200000 in
/-- Exact deterministic implication obtained by applying source Lemma 7 at
each smoothing scale and integrating.  The phase is chosen once, before both
integrals. -/
theorem exists_common_phase_integrated_halasz
    {q R : ℕ} (rows : Finset (JutilaP53Row q))
    (cols : Finset ℕ) (a : ℕ → ℂ)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {alpha xiLo xiHi upsLo upsHi V Q : ℝ}
    (hxiOrder : xiLo ≤ xiHi) (hupsOrder : upsLo ≤ upsHi)
    (hcross : xiHi < upsLo)
    (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hrow : ∀ row ∈ rows, alpha ≤ row.zero.re)
    (hlarge : ∀ row ∈ rows,
      V ≤ ‖finitePolynomial cols a (jutilaP53Phase alpha) row‖)
    (hcolsPos : ∀ n ∈ cols, 0 < n)
    (hpseudo : ∀ n ∈ cols, jutilaP53PseudoReal S n ≠ 0)
    (hquotient : ∀ xi ∈ Icc xiLo xiHi, ∀ upsilon ∈ Icc upsLo upsHi,
      (∑ n ∈ cols,
        ‖a n‖ ^ 2 /
          jutilaP53CorrelationWeight S
            (Real.exp xi) (Real.exp upsilon) n) ≤ Q) :
    ∃ eta : JutilaP53Row q → ℂ,
      (∀ row ∈ rows, ‖eta row‖ = 1) ∧
      ((xiHi - xiLo) * (upsHi - upsLo)) *
          ((rows.card : ℝ) * V) ^ 2 ≤
        Q * (∫ xi in xiLo..xiHi,
          ∫ upsilon in upsLo..upsHi,
            jutilaP53CorrelationEnergy rows S alpha
              (Real.exp xi) (Real.exp upsilon) eta) := by
  let K : Set (ℝ × ℝ) := Icc xiLo xiHi ×ˢ Icc upsLo upsHi
  let P := {p : ℝ × ℝ // p ∈ K}
  let v : JutilaP53Row q → ℕ → ℂ := selectedPhase rows alpha
  let weight : P → ℕ → ℝ := fun p n =>
    jutilaP53CorrelationWeight S
      (Real.exp p.1.1) (Real.exp p.1.2) n
  have hpCross (p : P) : p.1.1 < p.1.2 := by
    have hp := p.2
    change p.1 ∈ Icc xiLo xiHi ×ˢ Icc upsLo upsHi at hp
    exact hp.1.2.trans_lt (hcross.trans_le hp.2.1)
  have hweightPos : ∀ p n, n ∈ cols → 0 < weight p n := by
    intro p n hn
    exact MAPJutilaHalaszLargeValueFront.jutilaCorrelationWeight_pos
      (Real.exp_pos _) (Real.exp_lt_exp.mpr (hpCross p))
      (hcolsPos n hn) (hpseudo n hn)
  have hweight0 : ∀ p n, 0 ≤ weight p n := by
    intro p n
    exact jutilaP53CorrelationWeight_nonneg S
      (Real.exp_pos _) (Real.exp_lt_exp.mpr (hpCross p)) n
  have hweightSummable : ∀ p, Summable (weight p) := by
    intro p
    exact summable_jutilaP53CorrelationWeight hS
      (Real.exp_pos _) (Real.exp_lt_exp.mpr (hpCross p))
  have hv : ∀ row n, ‖v row n‖ ≤ 1 := by
    intro row n
    by_cases hr : row ∈ rows
    · simpa [v, selectedPhase, hr] using
        norm_jutilaP53Phase_le_one (hrow row hr) n
    · simp [v, selectedPhase, hr]
  have hlargeV : ∀ row ∈ rows,
      V ≤ ‖finitePolynomial cols a v row‖ := by
    intro row hr
    simpa [finitePolynomial, v, selectedPhase, hr] using hlarge row hr
  have hquotientP : ∀ p : P,
      (∑ n ∈ cols, ‖a n‖ ^ 2 / weight p n) ≤ Q := by
    intro p
    have hp := p.2
    change p.1 ∈ Icc xiLo xiHi ×ˢ Icc upsLo upsHi at hp
    exact hquotient p.1.1 hp.1 p.1.2 hp.2
  obtain ⟨eta, heta, hpointGeneric⟩ :=
    finite_halasz_common_phase_to_infinite rows cols a v weight V Q
      hV hQ hlargeV hweightPos hweight0 hweightSummable hv hquotientP
  refine ⟨eta, heta, ?_⟩
  let A : ℝ := ((rows.card : ℝ) * V) ^ 2
  let energy : ℝ → ℝ → ℝ := fun xi upsilon =>
    jutilaP53CorrelationEnergy rows S alpha
      (Real.exp xi) (Real.exp upsilon) eta
  have hpoint : ∀ xi ∈ Icc xiLo xiHi, ∀ upsilon ∈ Icc upsLo upsHi,
      A ≤ Q * energy xi upsilon := by
    intro xi hxi upsilon hups
    let p : P := ⟨(xi, upsilon), by
      change (xi, upsilon) ∈ Icc xiLo xiHi ×ˢ Icc upsLo upsHi
      exact ⟨hxi, hups⟩⟩
    have hp := hpointGeneric p
    have henergy :
        infiniteCorrelationEnergy rows (weight p) eta v =
          energy xi upsilon := by
      unfold infiniteCorrelationEnergy energy
      apply tsum_congr
      intro n
      congr 2
      apply congrArg (fun z : ℂ => ‖z‖)
      apply Finset.sum_congr rfl
      intro row hr
      simp [v, selectedPhase, hr]
    simpa [A, p, weight, henergy] using hp
  have hinnerIntegrable : ∀ xi ∈ Icc xiLo xiHi,
      IntervalIntegrable (energy xi) volume upsLo upsHi := by
    intro xi hxi
    exact intervalIntegrable_jutilaP53CorrelationEnergy_inner
      rows hS hupsOrder hcross hxi eta hrow heta
  have hinner : ∀ xi ∈ Icc xiLo xiHi,
      (upsHi - upsLo) * A ≤
        Q * (∫ upsilon in upsLo..upsHi, energy xi upsilon) := by
    intro xi hxi
    have hconst : IntervalIntegrable (fun _upsilon : ℝ => A)
        volume upsLo upsHi := continuous_const.intervalIntegrable _ _
    have hright : IntervalIntegrable (fun upsilon : ℝ =>
        Q * energy xi upsilon) volume upsLo upsHi :=
      (hinnerIntegrable xi hxi).const_mul Q
    have hmono := intervalIntegral.integral_mono_on hupsOrder
      hconst hright (fun upsilon hups => hpoint xi hxi upsilon hups)
    simpa [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      mul_assoc] using hmono
  have houterEnergy : IntervalIntegrable
      (fun xi : ℝ => ∫ upsilon in upsLo..upsHi, energy xi upsilon)
      volume xiLo xiHi := by
    exact intervalIntegrable_jutilaP53IntegratedCorrelationEnergy_outer
      rows hS hxiOrder hupsOrder hcross eta hrow heta
  have hleftOuter : IntervalIntegrable
      (fun _xi : ℝ => (upsHi - upsLo) * A) volume xiLo xiHi :=
    continuous_const.intervalIntegrable _ _
  have hrightOuter : IntervalIntegrable
      (fun xi : ℝ => Q *
        (∫ upsilon in upsLo..upsHi, energy xi upsilon))
      volume xiLo xiHi := houterEnergy.const_mul Q
  have hmonoOuter := intervalIntegral.integral_mono_on hxiOrder
    hleftOuter hrightOuter hinner
  simpa [A, energy, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, mul_assoc, mul_left_comm, mul_comm]
    using hmonoOuter

end

end MAPJutilaP53IntegratedHalaszWeld

#print axioms MAPJutilaP53IntegratedHalaszWeld.exists_common_phase_integrated_halasz
