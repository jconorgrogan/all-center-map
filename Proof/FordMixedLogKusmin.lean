import FordMixedLogAntitone
import FordUnitPhaseLipschitz
import GuthMaynardDiscreteFullPeriodVariation

open scoped BigOperators
noncomputable section
namespace FordMixedLogKusmin

open FordMixedReciprocalIntegral FordMixedLogAntitone
open FordUnitPhaseLipschitz
open GuthMaynardDiscreteFullPeriodVariation

def phaseArgument (hs : List ℝ) (t y : ℝ) : ℝ :=
  (-1 : ℝ) ^ hs.length * t * mixedDiff hs Real.log y

def phaseSequence (hs : List ℝ) (t x : ℝ) (n : ℕ) : ℂ :=
  unitPhase (phaseArgument hs t (x + n))

def incrementSequence (hs : List ℝ) (t x : ℝ) (n : ℕ) : ℝ :=
  t * signedMixedDiff (1 :: hs) (x + n)

lemma phase_increment (hs : List ℝ) (t x : ℝ) (n : ℕ) :
    phaseArgument hs t (x + (n + 1)) -
        phaseArgument hs t (x + n) =
      incrementSequence hs t x n := by
  dsimp [phaseArgument, incrementSequence, signedMixedDiff]
  have hpow : (-1 : ℝ) ^ (hs.length + 2) =
      (-1 : ℝ) ^ hs.length := by
    rw [show hs.length + 2 = hs.length + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  rw [hpow]
  ring_nf

lemma phase_recurrence (hs : List ℝ) (t x : ℝ) (n : ℕ) :
    phaseSequence hs t x (n + 1) =
      phaseSequence hs t x n *
        Complex.exp (Complex.I *
          (incrementSequence hs t x n : ℂ)) := by
  have hd := phase_increment hs t x n
  dsimp [phaseSequence]
  unfold unitPhase
  have hd' : phaseArgument hs t (x + ((n + 1 : ℕ) : ℝ)) -
      phaseArgument hs t (x + (n : ℝ)) =
        incrementSequence hs t x n := by
    simpa using hd
  rw [show phaseArgument hs t (x + ((n + 1 : ℕ) : ℝ)) =
      phaseArgument hs t (x + (n : ℝ)) + incrementSequence hs t x n by
      linarith]
  rw [show Complex.I *
      ((phaseArgument hs t (x + n) + incrementSequence hs t x n : ℝ) : ℂ) =
      Complex.I * (phaseArgument hs t (x + n) : ℂ) +
        Complex.I * (incrementSequence hs t x n : ℂ) by
      push_cast
      ring, Complex.exp_add]

theorem norm_sum_phase_le
    (hs : List ℝ) (hsteps : ∀ h ∈ hs, 0 ≤ h)
    {t x δ : ℝ} (ht : 0 ≤ t) (hx : 0 < x) (hδ : 0 < δ)
    (H : ℕ)
    (hlower : δ ≤ incrementSequence hs t x H)
    (hupper : incrementSequence hs t x 0 ≤ 2 * Real.pi - δ) :
    ‖∑ n ∈ Finset.range H, phaseSequence hs t x n‖ ≤
      3 * Real.pi / δ := by
  by_cases hH : H = 0
  · subst H
    simp only [Finset.sum_range_zero, norm_zero]
    positivity
  · obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hH
    let d : ℕ → ℝ := incrementSequence hs t x
    let z : ℕ → ℂ := phaseSequence hs t x
    have hdanti : Antitone d := by
      intro n m hnm
      dsimp [d]
      have hnmR : x + (n : ℝ) ≤ x + (m : ℝ) := by
        have hnmR' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
        linarith
      have hnpos : 0 < x + (n : ℝ) := by positivity
      have hmpos : 0 < x + (m : ℝ) := by positivity
      have hsm := signedMixedDiff_antitone (1 :: hs) (by
        intro h hh
        simp only [List.mem_cons] at hh
        rcases hh with rfl | hh
        · positivity
        · exact hsteps h hh) hnpos hmpos hnmR
      exact mul_le_mul_of_nonneg_left hsm ht
    have hdlo : ∀ n ≤ K, δ ≤ d n := by
      intro n hn
      have hnh : n ≤ K + 1 := by omega
      have hmon : d (K + 1) ≤ d n :=
        hdanti (a := n) (b := K + 1) hnh
      dsimp [d] at hmon ⊢
      exact hlower.trans hmon
    have hdhi : ∀ n ≤ K, d n ≤ 2 * Real.pi - δ := by
      intro n hn
      have h0n : d n ≤ d 0 :=
        hdanti (a := 0) (b := n) (by omega)
      dsimp [d] at h0n ⊢
      exact h0n.trans hupper
    have hrec : ∀ n < K + 1,
        z (n + 1) = z n * Complex.exp (Complex.I * (d n : ℂ)) := by
      intro n hn
      dsimp [z, d]
      exact phase_recurrence hs t x n
    have hz : ∀ n ≤ K + 1, ‖z n‖ = 1 := by
      intro n hn
      dsimp [z]
      exact unitPhase_norm _
    exact norm_sum_le_margin_finite K d z hδ hdlo hdhi
      (by
        intro n hn m hm hnm
        exact hdanti hnm) hrec hz

end FordMixedLogKusmin

#print axioms FordMixedLogKusmin.phase_increment
#print axioms FordMixedLogKusmin.norm_sum_phase_le
