import FordPhaseTreeRecurrence
import FordGoodShiftError
import FordGoodShiftsNonempty

noncomputable section
namespace FordPhaseScaleIteration

open FordPhaseTreeRecurrence FordGoodShiftError FordGoodShiftsNonempty
open FordDiscretePairCount FordScaleFloor

/-- Scale-selected phase iteration.  The terminal good-prefix estimate remains
an explicit hypothesis; this theorem supplies the finite recurrence and scale
algebra only. -/
theorem phaseSize_scale_iterated_le
    {N H r : ℕ} {q eps : ℝ} (hN : 1 ≤ N) (hH : H ≤ N)
    (heps : 0 ≤ eps) (heq : eps ≤ q)
    (hq1 : q ≤ 1) (hsmall :
      16 * (N : ℝ) ^ (-eps) ≤ 1)
    (f : ℝ → ℝ) (x : ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hleaf : ∀ hs : List ℕ,
      (∀ g ∈ hs, g ∈ goodShifts (FordScaleFloor.scale N q)
        ((N : ℝ) ^ (-eps))) →
      hs.length = r →
      phaseSize N H f x hs ≤ B) :
    phaseSize N H f x [] ^ (2 ^ r) ≤
      16 ^ (2 ^ r) * (16 * (N : ℝ) ^ (-eps) + B) := by
  let Q : ℕ := FordScaleFloor.scale N q
  let A : ℝ := (N : ℝ) ^ (-eps)
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hq0 : 0 ≤ q := heps.trans heq
  have hscale := FordScaleFloor.scale_comparable hN hq0
  have hpow_eps : (0 : ℝ) < (N : ℝ) ^ eps :=
    Real.rpow_pos_of_pos hn0 _
  have hpow_eps_ge : (16 : ℝ) ≤ (N : ℝ) ^ eps := by
    have hs : 16 * ((N : ℝ) ^ eps)⁻¹ ≤ 1 := by
      simpa [A, Real.rpow_neg hn0.le] using hsmall
    have hsdiv : (16 : ℝ) / ((N : ℝ) ^ eps) ≤ 1 := by
      simpa [div_eq_mul_inv] using hs
    simpa using (div_le_iff₀ hpow_eps).mp hsdiv
  have hpow_q : (N : ℝ) ^ eps ≤ (N : ℝ) ^ q :=
    Real.rpow_le_rpow_of_exponent_le hn heq
  have hQ2 : 2 ≤ Q := by
    have hQr : (2 : ℝ) ≤ (Q : ℝ) := by
      dsimp [Q]
      nlinarith [hscale.2.2, hpow_eps_ge, hpow_q]
    exact_mod_cast hQr
  have hQ1 : 1 ≤ Q := by omega
  have hQN : Q ≤ N := by
    dsimp [Q]
    exact FordScaleFloor.scale_le_base hN hq0 hq1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hAhalf : A ≤ (1 : ℝ) / 2 := by
    have hsA : 16 * A ≤ 1 := by simpa [A] using hsmall
    linarith
  have hG : (goodShifts Q A).Nonempty := by
    apply goodShifts_nonempty hQ2 hAhalf
  have hGsub : goodShifts Q A ⊆ positiveRange Q := by
    intro h hh
    exact (Finset.mem_filter.mp hh).1
  have herror :
      2 / (Q : ℝ) +
          4 * ((positiveRange Q \ goodShifts Q A).card : ℝ) / Q ≤
        16 * A := by
    simpa [Q, A] using (error_scale_le hN heps heq)
  have hA1 : 16 * A ≤ 1 := by simpa [A] using hsmall
  have h16A0 : 0 ≤ 16 * A := mul_nonneg (by norm_num) hA0
  have hmain := phaseSize_iterated_le
    (N := N) (H := H) (Q := Q) (r := r)
    (a := 16 * A) (B := B) hH hQ1 hQN f x
    (goodShifts Q A) hGsub hG h16A0 hA1 hB herror
    (by simpa [Q, A] using hleaf)
  simpa [A] using hmain

end FordPhaseScaleIteration

#print axioms FordPhaseScaleIteration.phaseSize_scale_iterated_le
