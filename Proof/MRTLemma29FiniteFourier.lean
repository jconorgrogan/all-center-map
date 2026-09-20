import MRTLemma29CorrectedInterface
import Mathlib.Analysis.Fourier.ZMod

namespace MAPMRTLemma29Proof
open scoped BigOperators ZMod ComplexConjugate
open Complex
noncomputable section

set_option maxHeartbeats 800000

lemma star_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  simpa using (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

lemma dft_energy_complex {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (∑ k : ZMod N, star (ZMod.dft f k) * ZMod.dft f k) =
      (N : ℂ) * ∑ x : ZMod N, star (f x) * f x := by
  simp_rw [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul, star_stdAddChar]
  simp_rw [Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, i]
    rw [Finset.sum_comm]
  have hchar (i j x : ZMod N) :
      ZMod.stdAddChar (- -(i * x)) * ZMod.stdAddChar (-(j * x)) =
        ZMod.stdAddChar (x * (i - j)) := by
    rw [← (ZMod.stdAddChar).map_add_eq_mul]
    congr 1
    ring
  simp_rw [show ∀ (i j x : ZMod N),
      star (f i) * ZMod.stdAddChar (- -(i * x)) *
          (ZMod.stdAddChar (-(j * x)) * f j) =
        (star (f i) * f j) *
          (ZMod.stdAddChar (- -(i * x)) * ZMod.stdAddChar (-(j * x))) by
      intro i j x; ring]
  simp_rw [hchar, ← Finset.mul_sum]
  have horth (i j : ZMod N) :
      (∑ x : ZMod N, ZMod.stdAddChar (x * (i - j))) =
        if i = j then (N : ℂ) else 0 := by
    simpa [sub_eq_zero] using
      (AddChar.sum_mulShift (i - j) (ZMod.isPrimitive_stdAddChar N))
  simp_rw [horth]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp
  ring

lemma dft_energy {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (∑ k : ZMod N, ‖ZMod.dft f k‖ ^ 2) =
      (N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 := by
  have h :
      (∑ k : ZMod N, conj (ZMod.dft f k) * ZMod.dft f k) =
        (N : ℂ) * ∑ x : ZMod N, conj (f x) * f x := by
    simpa only [RCLike.star_def] using dft_energy_complex f
  simp_rw [← Complex.normSq_eq_conj_mul_self] at h
  have hr := congrArg Complex.re h
  simpa [Complex.mul_re, Complex.sq_norm] using hr

lemma dirichletCharacter_energy {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) :
    (∑ x : ZMod N, ‖chi x‖ ^ 2) = (N.totient : ℝ) := by
  calc
    (∑ x : ZMod N, ‖chi x‖ ^ 2) =
        ∑ x : ZMod N, if IsUnit x then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hunit : IsUnit x
      · have hn : ‖chi x‖ = 1 := by
          rw [← hunit.unit_spec]
          exact chi.unit_norm_eq_one hunit.unit
        rw [if_pos hunit, hn]
        norm_num
      · rw [if_neg hunit, chi.map_nonunit hunit]
        simp
    _ = (((Finset.univ : Finset (ZMod N)).filter IsUnit).card : ℝ) := by
      rw [Finset.sum_boole]
    _ = (N.totient : ℝ) := by
      congr 1
      rw [show (Finset.univ : Finset (ZMod N)).filter IsUnit =
          Finset.univ.map ⟨((↑) : (ZMod N)ˣ → ZMod N), Units.val_injective⟩ by
        ext x
        simp [IsUnit]]
      rw [Finset.card_map, Finset.card_univ, ZMod.card_units_eq_totient]

lemma dft_unit_norm_eq_gaussSum {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    ‖ZMod.dft (chi : ZMod N → ℂ) (u : ZMod N)‖ =
      ‖gaussSum chi ZMod.stdAddChar‖ := by
  rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift]
  have h := congrArg norm
    (gaussSum_mulShift chi (ZMod.stdAddChar (N := N)) (-u))
  have hu : IsUnit (-(u : ZMod N)) := u.isUnit.neg
  have hn : ‖chi (-(u : ZMod N))‖ = 1 := by
    rw [← hu.unit_spec]
    exact chi.unit_norm_eq_one hu.unit
  simpa only [Units.val_neg, norm_mul, hn, one_mul] using h

lemma unit_dft_energy_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) :
    (N.totient : ℝ) * ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 ≤
      ∑ k : ZMod N, ‖ZMod.dft (chi : ZMod N → ℂ) k‖ ^ 2 := by
  let e : (ZMod N)ˣ ↪ ZMod N := ⟨((↑) : (ZMod N)ˣ → ZMod N), Units.val_injective⟩
  calc
    (N.totient : ℝ) * ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 =
        ∑ u : (ZMod N)ˣ, ‖ZMod.dft (chi : ZMod N → ℂ) (u : ZMod N)‖ ^ 2 := by
      simp_rw [dft_unit_norm_eq_gaussSum]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ZMod.card_units_eq_totient]
    _ = ∑ k ∈ Finset.univ.map e,
          ‖ZMod.dft (chi : ZMod N → ℂ) k‖ ^ 2 := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ k : ZMod N, ‖ZMod.dft (chi : ZMod N → ℂ) k‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro k hk hnot
      positivity

lemma gaussSum_norm_sq_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) :
    ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 ≤ (N : ℝ) := by
  have hlower := unit_dft_energy_le chi
  have hparseval := dft_energy (chi : ZMod N → ℂ)
  rw [dirichletCharacter_energy chi] at hparseval
  have hphi : 0 < (N.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [hparseval] at hlower
  nlinarith

lemma gaussSum_norm_le_sqrt {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) :
    ‖gaussSum chi ZMod.stdAddChar‖ ≤ Real.sqrt N := by
  have h := gaussSum_norm_sq_le chi
  rw [← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)] at h
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp h

end
end MAPMRTLemma29Proof
