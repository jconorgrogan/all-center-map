import JutilaReflectionKernelInterchange
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Dirichlet-series form of Jutila's initial contour identity

Jutila's proof of Lemma 1 (Acta Arith. 32 (1977), p. 58) begins from a
vertical integral for the smoothed Dirichlet series `H(s,chi)`.  This file
certifies the countable Fubini step and rewrites the termwise sum as the
literal `L`-series on the source line `Re w = 2`.

The contour shift to `Re(s+w)=-1/2`, the functional equation, and the split
of the dual series at `M` are not used here.
-/

namespace JutilaReflectionDirichletIdentity

open Complex Real MeasureTheory Filter
open scoped BigOperators LSeries.notation
open JutilaReflectionKernelInterchange

noncomputable section

abbrev PositiveNat := {n : ℕ // 0 < n}

def dirichletCoefficient {q : ℕ} (chi : DirichletCharacter ℂ q)
    (s : ℂ) (n : PositiveNat) : ℂ :=
  chi (n : ℕ) / ((n : ℕ) : ℂ) ^ s

def dirichletRatio (U : ℝ) (n : PositiveNat) : ℝ := (n : ℝ) / U

theorem dirichletRatio_pos {U : ℝ} (hU : 0 < U) (n : PositiveNat) :
    0 < dirichletRatio U n :=
  div_pos (Nat.cast_pos.mpr n.property) hU

theorem weighted_dirichletCoefficient_eq
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ} {U : ℝ}
    (hU : 0 < U) (n : PositiveNat) :
    ‖dirichletCoefficient chi s n‖ *
        Real.rpow (dirichletRatio U n) (-2) =
      ‖chi (n : ℕ)‖ * U ^ 2 * Real.rpow (n : ℝ) (-s.re - 2) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr n.property
  unfold dirichletCoefficient dirichletRatio
  simp only [Real.rpow_eq_pow]
  rw [norm_div, Complex.norm_natCast_cpow_of_pos n.property]
  rw [Real.div_rpow hn.le hU.le, show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg hU.le, Real.rpow_two, div_inv_eq_mul]
  rw [div_eq_mul_inv, ← Real.rpow_neg hn.le]
  rw [show -s.re - 2 = -s.re + (-2) by ring, Real.rpow_add hn]
  ring

theorem summable_weighted_dirichletCoefficient
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ} {U : ℝ}
    (hs : -1 < s.re) (hU : 0 < U) :
    Summable fun n : PositiveNat =>
      ‖dirichletCoefficient chi s n‖ *
        Real.rpow (dirichletRatio U n) (-2) := by
  let p : ℝ := -s.re - 2
  have hp : p < -1 := by dsimp [p]; linarith
  have hnat : Summable fun n : ℕ => Real.rpow (n : ℝ) p :=
    Real.summable_nat_rpow.mpr hp
  have hsub : Summable fun n : PositiveNat => Real.rpow (n : ℝ) p := by
    simpa only [Function.comp_apply] using! hnat.subtype {n : ℕ | 0 < n}
  have hmajor : Summable fun n : PositiveNat =>
      U ^ 2 * Real.rpow (n : ℝ) p := hsub.mul_left (U ^ 2)
  refine Summable.of_nonneg_of_le
    (f := fun n : PositiveNat => U ^ 2 * Real.rpow (n : ℝ) p) ?_ ?_ hmajor
  · intro n
    exact mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (dirichletRatio_pos hU n).le _)
  · intro n
    rw [weighted_dirichletCoefficient_eq chi hU]
    have hchi : ‖chi (n : ℕ)‖ ≤ 1 := chi.norm_le_one (n : ZMod q)
    have hpow : 0 ≤ Real.rpow (n : ℝ) p := Real.rpow_nonneg (by positivity) _
    have hU2 : 0 ≤ U ^ 2 := sq_nonneg U
    calc
      ‖chi (n : ℕ)‖ * U ^ 2 * Real.rpow (n : ℝ) (-s.re - 2) =
          (‖chi (n : ℕ)‖ * U ^ 2) * Real.rpow (n : ℝ) p := by rfl
      _ ≤ (1 * U ^ 2) * Real.rpow (n : ℝ) p := by gcongr
      _ = U ^ 2 * Real.rpow (n : ℝ) p := by ring

theorem ratio_cpow_neg
    {U : ℝ} (hU : 0 < U) (n : PositiveNat) (w : ℂ) :
    (((dirichletRatio U n : ℝ) : ℂ) ^ (-w)) =
      (((n : ℕ) : ℂ) ^ (-w)) * ((U : ℂ) ^ w) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr n.property
  have hr : 0 < dirichletRatio U n := dirichletRatio_pos hU n
  have hUC : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU.ne'
  rw [show (((n : ℕ) : ℂ)) = (((n : ℝ) : ℂ)) by norm_cast]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'),
    Complex.cpow_def_of_ne_zero hUC]
  rw [← Complex.ofReal_log hr.le, ← Complex.ofReal_log hn.le,
    ← Complex.ofReal_log hU.le]
  unfold dirichletRatio
  rw [Real.log_div hn.ne' hU.ne']
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

theorem coefficient_ratio_eq_LSeriesTerm
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ} {U : ℝ}
    (hU : 0 < U) (n : PositiveNat) (w : ℂ) :
    dirichletCoefficient chi s n *
        (((dirichletRatio U n : ℝ) : ℂ) ^ (-w)) =
      (U : ℂ) ^ w * LSeries.term (fun m : ℕ => chi m) (s + w) n := by
  have hnC : (((n : ℕ) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr n.property.ne'
  have hns : (((n : ℕ) : ℂ) ^ s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  have hnw : (((n : ℕ) : ℂ) ^ w) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  unfold dirichletCoefficient
  rw [ratio_cpow_neg hU n w, LSeries.term_of_ne_zero n.property.ne']
  rw [Complex.cpow_neg, Complex.cpow_add s w hnC]
  field_simp [hns, hnw]

theorem positiveNat_tsum_LSeries
    {q : ℕ} (chi : DirichletCharacter ℂ q) (z : ℂ) :
    (∑' n : PositiveNat, LSeries.term (fun m : ℕ => chi m) z n) =
      LSeries (fun m : ℕ => chi m) z := by
  rw [show (∑' n : {n : ℕ // 0 < n},
      LSeries.term (fun m : ℕ => chi m) z n) =
      ∑' n : ℕ, {n : ℕ | 0 < n}.indicator
        (fun n => LSeries.term (fun m : ℕ => chi m) z n) n by
      exact tsum_subtype {n : ℕ | 0 < n}
        (fun n => LSeries.term (fun m : ℕ => chi m) z n)]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : 0 < n
  · rw [Set.indicator_of_mem (show n ∈ {n : ℕ | 0 < n} from hn)]
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [Set.indicator_of_notMem (show (0 : ℕ) ∉ {n : ℕ | 0 < n} by simp)]
    simp [LSeries.term_zero]

theorem positiveNat_integrand_eq_LSeries
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ} {U c : ℝ}
    (hs : 1 - c < s.re) (hU : 0 < U) (r : ℝ) :
    (∑' n : PositiveNat, dirichletCoefficient chi s n *
      (((dirichletRatio U n : ℝ) : ℂ) ^ (-verticalPoint c r) *
        jutilaKernel c 1 r)) =
      jutilaKernel c 1 r * (U : ℂ) ^ (verticalPoint c r) *
        LSeries (fun m : ℕ => chi m) (s + verticalPoint c r) := by
  let w : ℂ := verticalPoint c r
  have hz : 1 < (s + w).re := by
    dsimp [w, verticalPoint]
    norm_num
    linarith
  calc
    (∑' n : PositiveNat, dirichletCoefficient chi s n *
      (((dirichletRatio U n : ℝ) : ℂ) ^ (-w) * jutilaKernel c 1 r)) =
      ∑' n : PositiveNat,
        jutilaKernel c 1 r * (U : ℂ) ^ w *
          LSeries.term (fun m : ℕ => chi m) (s + w) n := by
            apply tsum_congr
            intro n
            calc
              dirichletCoefficient chi s n *
                  (((dirichletRatio U n : ℝ) : ℂ) ^ (-w) *
                    jutilaKernel c 1 r) =
                (dirichletCoefficient chi s n *
                  ((dirichletRatio U n : ℝ) : ℂ) ^ (-w)) *
                    jutilaKernel c 1 r := by ring
              _ = ((U : ℂ) ^ w *
                  LSeries.term (fun m : ℕ => chi m) (s + w) n) *
                    jutilaKernel c 1 r := by
                rw [coefficient_ratio_eq_LSeriesTerm chi hU n w]
              _ = jutilaKernel c 1 r * (U : ℂ) ^ w *
                  LSeries.term (fun m : ℕ => chi m) (s + w) n := by ring
    _ = jutilaKernel c 1 r * (U : ℂ) ^ w *
        (∑' n : PositiveNat,
          LSeries.term (fun m : ℕ => chi m) (s + w) n) := by
            rw [tsum_mul_left]
    _ = jutilaKernel c 1 r * (U : ℂ) ^ w *
        LSeries (fun m : ℕ => chi m) (s + w) := by
          rw [positiveNat_tsum_LSeries chi (s + w)]

/-- One-scale version of the exact identity printed at the start of Jutila's
proof.  Taking the `U=2N` minus `U=N` difference gives his displayed
smoothed coefficient `b(n)` and factor `(2N)^w-N^w`. -/
theorem literal_dirichlet_exp_smoothing_identity
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ} {U h : ℝ}
    (hs : -1 < s.re) (hU : 0 < U) (hh : 0 < h) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ,
          jutilaKernel 2 h r * (U : ℂ) ^ (verticalPoint 2 r) *
            LSeries (fun m : ℕ => chi m) (s + verticalPoint 2 r)) =
      ∑' n : PositiveNat, dirichletCoefficient chi s n *
        (Real.exp (-Real.rpow (dirichletRatio U n) h) : ℂ) := by
  have hInter := countable_jutilaKernel_interchange_of_weighted_summable
    (c := 2) (h := h) (by norm_num) hh
    (dirichletCoefficient chi s) (dirichletRatio U)
    (dirichletRatio_pos hU)
    (summable_weighted_dirichletCoefficient chi hs hU)
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ,
          jutilaKernel 2 h r * (U : ℂ) ^ (verticalPoint 2 r) *
            LSeries (fun m : ℕ => chi m) (s + verticalPoint 2 r)) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, ∑' n : PositiveNat,
          dirichletCoefficient chi s n *
            (((dirichletRatio U n : ℝ) : ℂ) ^ (-verticalPoint 2 r) *
              jutilaKernel 2 h r)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with r
        have hsum : (∑' n : PositiveNat,
          dirichletCoefficient chi s n *
            (((dirichletRatio U n : ℝ) : ℂ) ^ (-verticalPoint 2 r) *
              jutilaKernel 2 h r)) =
          jutilaKernel 2 h r * (U : ℂ) ^ (verticalPoint 2 r) *
            LSeries (fun m : ℕ => chi m) (s + verticalPoint 2 r) := by
              -- The same algebra as `positiveNat_integrand_eq_LSeries`,
              -- with arbitrary positive `h` in the common kernel.
              let w : ℂ := verticalPoint 2 r
              calc
                (∑' n : PositiveNat, dirichletCoefficient chi s n *
                  (((dirichletRatio U n : ℝ) : ℂ) ^ (-w) *
                    jutilaKernel 2 h r)) =
                  ∑' n : PositiveNat,
                    jutilaKernel 2 h r * (U : ℂ) ^ w *
                      LSeries.term (fun m : ℕ => chi m) (s + w) n := by
                        apply tsum_congr
                        intro n
                        calc
                          dirichletCoefficient chi s n *
                              (((dirichletRatio U n : ℝ) : ℂ) ^ (-w) *
                                jutilaKernel 2 h r) =
                            (dirichletCoefficient chi s n *
                              ((dirichletRatio U n : ℝ) : ℂ) ^ (-w)) *
                                jutilaKernel 2 h r := by ring
                          _ = ((U : ℂ) ^ w *
                              LSeries.term (fun m : ℕ => chi m) (s + w) n) *
                                jutilaKernel 2 h r := by
                            rw [coefficient_ratio_eq_LSeriesTerm chi hU n w]
                          _ = jutilaKernel 2 h r * (U : ℂ) ^ w *
                              LSeries.term (fun m : ℕ => chi m) (s + w) n := by ring
                _ = jutilaKernel 2 h r * (U : ℂ) ^ w *
                    (∑' n : PositiveNat,
                      LSeries.term (fun m : ℕ => chi m) (s + w) n) := by
                        rw [tsum_mul_left]
                _ = jutilaKernel 2 h r * (U : ℂ) ^ w *
                    LSeries (fun m : ℕ => chi m) (s + w) := by
                      rw [positiveNat_tsum_LSeries chi (s + w)]
        exact hsum.symm
    _ = _ := hInter

end

end JutilaReflectionDirichletIdentity

#print axioms JutilaReflectionDirichletIdentity.summable_weighted_dirichletCoefficient
#print axioms JutilaReflectionDirichletIdentity.literal_dirichlet_exp_smoothing_identity
