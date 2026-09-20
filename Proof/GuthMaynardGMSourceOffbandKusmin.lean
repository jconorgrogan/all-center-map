import GuthMaynardGMPointwiseHighTPartition
import GuthMaynardDiscreteFullPeriodVariation
import GuthMaynardGMSourceKusminActual

namespace GuthMaynardGMSourceOffbandKusmin

open scoped BigOperators
open GuthMaynardSectionFourTrace
open GuthMaynardGMPointwiseHighTPartition
open GuthMaynardDiscreteFullPeriodVariation
open GuthMaynardGMSourceKusminActual

noncomputable section

private theorem exp_shift_by_two_pi_int
    (x : ℝ) (ell : ℤ) :
    Complex.exp (Complex.I * ((x - 2 * Real.pi * (ell : ℝ) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (x : ℂ)) := by
  have hper :
      Complex.exp (Complex.I * ((-(2 * Real.pi * (ell : ℝ)) : ℝ) : ℂ)) = 1 := by
    have h := Complex.exp_int_mul_two_pi_mul_I (-ell)
    convert h using 1 <;> push_cast <;> ring
  calc
    Complex.exp (Complex.I * ((x - 2 * Real.pi * (ell : ℝ) : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (x : ℂ) +
          Complex.I * ((-(2 * Real.pi * (ell : ℝ)) : ℝ) : ℂ)) := by
            congr 1
            push_cast
            ring
    _ = Complex.exp (Complex.I * (x : ℂ)) *
          Complex.exp (Complex.I * ((-(2 * Real.pi * (ell : ℝ)) : ℝ) : ℂ)) :=
        Complex.exp_add _ _
    _ = Complex.exp (Complex.I * (x : ℂ)) := by rw [hper, mul_one]

theorem norm_sum_sourcePhase_shift_offband
    (base k : ℕ) (t : ℝ) (ell : ℤ) {δ : ℝ}
    (hbase : 0 < base) (hδ : 0 < δ)
    (hdlo : ∀ n ≤ k,
      δ ≤ gmIncrement t (base + n) - 2 * Real.pi * (ell : ℝ))
    (hdhi : ∀ n ≤ k,
      gmIncrement t (base + n) - 2 * Real.pi * (ell : ℝ) ≤ 2 * Real.pi - δ)
    (hanti : AntitoneOn (fun n => gmIncrement t (base + n)) (Set.Iic k)) :
    ‖∑ n ∈ Finset.range (k + 1), sourcePhase (base + n) t‖ ≤
      3 * Real.pi / δ := by
  let d : ℕ → ℝ := fun n =>
    gmIncrement t (base + n) - 2 * Real.pi * (ell : ℝ)
  let z : ℕ → ℂ := fun n => sourcePhase (base + n) t
  have hdlo' : ∀ n ≤ k, δ ≤ d n := by
    intro n hn
    exact hdlo n hn
  have hdhi' : ∀ n ≤ k, d n ≤ 2 * Real.pi - δ := by
    intro n hn
    exact hdhi n hn
  have hdanti : AntitoneOn d (Set.Iic k) := by
    intro n hn m hm hnm
    dsimp [d]
    exact sub_le_sub_right (hanti hn hm hnm) _
  have hrec : ∀ n < k + 1,
      z (n + 1) = z n * Complex.exp (Complex.I * (d n : ℂ)) := by
    intro n hn
    have hpos : 0 < base + n := by omega
    have hs := sourcePhase_succ_eq_mul_gmStepPhase (t := t)
      (n := base + n) hpos
    rw [show z (n + 1) = sourcePhase (base + n + 1) t by
      simp [z, Nat.add_assoc]]
    rw [show base + n + 1 = (base + n) + 1 by omega, hs]
    rw [show gmStepPhase t (base + n) =
      Complex.exp (Complex.I * (gmIncrement t (base + n) : ℂ)) by rfl]
    rw [exp_shift_by_two_pi_int (gmIncrement t (base + n)) ell]
  have hz : ∀ n ≤ k + 1, ‖z n‖ = 1 := by
    intro n hn
    dsimp [z, sourcePhase]
    simpa [mul_comm] using
      Complex.norm_exp_ofReal_mul_I (t * Real.log (base + n))
  exact norm_sum_le_margin_finite k d z hδ hdlo' hdhi' hdanti hrec hz

theorem norm_sum_sourcePhase_shift_offband_of_pos
    (base k : ℕ) (t : ℝ) (ell : ℤ) {δ : ℝ}
    (hbase : 0 < base) (ht : 0 < t) (hδ : 0 < δ)
    (hdlo : ∀ n ≤ k,
      δ ≤ gmIncrement t (base + n) - 2 * Real.pi * (ell : ℝ))
    (hdhi : ∀ n ≤ k,
      gmIncrement t (base + n) - 2 * Real.pi * (ell : ℝ) ≤ 2 * Real.pi - δ) :
    ‖∑ n ∈ Finset.range (k + 1), sourcePhase (base + n) t‖ ≤
      3 * Real.pi / δ := by
  have hanti : AntitoneOn (fun n => gmIncrement t (base + n)) (Set.Iic k) := by
    intro n hn m hm hnm
    exact gmIncrement_shift_antitone ht hbase hnm
  exact norm_sum_sourcePhase_shift_offband base k t ell hbase hδ hdlo hdhi
    hanti

end
end GuthMaynardGMSourceOffbandKusmin

#print axioms GuthMaynardGMSourceOffbandKusmin.norm_sum_sourcePhase_shift_offband
