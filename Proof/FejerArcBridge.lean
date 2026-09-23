import FejerWindowMass

/-!
# Spatial form of the shifted Fejér convolution

This file advances the open arc-mass bridge without assuming it.  The first
step keeps the real translated center through its integer modulation and
rewrites the finite Fourier convolution as an honest normalized-Haar spatial
integral.
-/

namespace MAPHarmonicEndpoint

open AddCircle MeasureTheory Metric Set
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The literal finite spatial kernel underlying `shiftedFejerConvolution`.
The sign convention agrees with `circleCoefficient`, hence with the paper's
`fourier (-h)` convention. -/
def shiftedFejerSpatialKernel (N : ℕ) (c : ℤ)
    (z : UnitAddCircle) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
    ((FejerLocalMass.pairMultiplicity N k : ℝ) / N : ℂ) *
      fourier (-(c + k)) z

/-- The unmodulated finite Fejér polynomial, with the negative-frequency
sign forced by the spatial convolution convention. -/
def finiteFejerPolynomial (N : ℕ) (z : UnitAddCircle) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
    ((FejerLocalMass.pairMultiplicity N k : ℝ) / N : ℂ) *
      fourier (-k) z

/-- Negating the circle argument is the same as negating the frequency. -/
theorem fourier_argument_neg (h : ℤ) (z : UnitAddCircle) :
    fourier h (-z) = fourier (-h) z := by
  rw [fourier_apply, smul_neg, toCircle_neg, Circle.coe_inv_eq_conj]
  rw [← fourier_apply, ← fourier_neg]

/-- The translated center is a norm-one modulation of the unmodulated
finite Fejér polynomial. -/
theorem shiftedFejerSpatialKernel_eq_modulation
    (N : ℕ) (c : ℤ) (z : UnitAddCircle) :
    shiftedFejerSpatialKernel N c z =
      fourier (-c) z * finiteFejerPolynomial N z := by
  classical
  simp only [shiftedFejerSpatialKernel, finiteFejerPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hf : fourier (-(c + k)) z =
      fourier (-c) z * fourier (-k) z := by
    rw [← fourier_add]
    congr 2
    omega
  rw [hf]
  ring

/-- Every difference arising from `[0,N)²` lies in the literal closed
frequency range used by the finite Fejér polynomial. -/
theorem pairDifference_mem_fejerRange
    {N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ Finset.range N ×ˢ Finset.range N) :
    (p.1 : ℤ) - (p.2 : ℤ) ∈
      Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1) := by
  simp only [Finset.mem_product, Finset.mem_range] at hp
  rw [Finset.mem_Icc]
  omega

/-- Regrouping the finite square by its exact integer difference.  This is
purely finite and includes both extreme endpoint differences. -/
theorem pairMultiplicity_weighted_sum
    (N : ℕ) (z : UnitAddCircle) :
    (∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
        (FejerLocalMass.pairMultiplicity N k : ℂ) * fourier (-k) z) =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N,
        fourier (-((p.1 : ℤ) - (p.2 : ℤ))) z := by
  classical
  let s : Finset (ℕ × ℕ) := Finset.range N ×ˢ Finset.range N
  let t : Finset ℤ := Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1)
  let g : ℕ × ℕ → ℤ := fun p ↦ (p.1 : ℤ) - (p.2 : ℤ)
  have hmap : ∀ p ∈ s, g p ∈ t := by
    intro p hp
    exact pairDifference_mem_fejerRange hp
  have hfiber := Finset.sum_fiberwise_of_maps_to'
    (M := ℂ) hmap (fun k : ℤ ↦ fourier (-k) z)
  change (∑ k ∈ t,
      (FejerLocalMass.pairMultiplicity N k : ℂ) * fourier (-k) z) =
    ∑ p ∈ s, fourier (-(g p)) z
  calc
    (∑ k ∈ t,
        (FejerLocalMass.pairMultiplicity N k : ℂ) * fourier (-k) z) =
      ∑ k ∈ t, ∑ p ∈ s with g p = k, fourier (-k) z := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [FejerLocalMass.pairMultiplicity, s, g]
        rw [Finset.sum_const]
        simp
    _ = ∑ p ∈ s, fourier (-(g p)) z := hfiber

/-- The finite polynomial is exactly the standard nonnegative Fejér kernel
at the negated circle argument. -/
theorem finiteFejerPolynomial_eq_fejerKernel_neg
    (N : ℕ) (z : UnitAddCircle) :
    finiteFejerPolynomial N z = FejerLocalMass.fejerKernel N (-z) := by
  classical
  rw [finiteFejerPolynomial, FejerLocalMass.fejerKernel_eq_doubleSum]
  calc
    (∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
        ((FejerLocalMass.pairMultiplicity N k : ℝ) / N : ℂ) *
          fourier (-k) z) =
      (N : ℂ)⁻¹ *
        ∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
          (FejerLocalMass.pairMultiplicity N k : ℂ) * fourier (-k) z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    _ = (N : ℂ)⁻¹ *
        ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          fourier (-((p.1 : ℤ) - (p.2 : ℤ))) z := by
      rw [pairMultiplicity_weighted_sum]
    _ = (N : ℂ)⁻¹ *
        ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          fourier ((j : ℤ) - (l : ℤ)) (-z) := by
      congr 1
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      simp only
      rw [fourier_argument_neg]

/-- Spatial kernel in the exact familiar form: modulation times the
nonnegative Fejér kernel. -/
theorem shiftedFejerSpatialKernel_eq_modulated_fejer
    (N : ℕ) (c : ℤ) (z : UnitAddCircle) :
    shiftedFejerSpatialKernel N c z =
      fourier (-c) z * FejerLocalMass.fejerKernel N (-z) := by
  rw [shiftedFejerSpatialKernel_eq_modulation,
    finiteFejerPolynomial_eq_fejerKernel_neg]

/-- Modulation does not change the spatial-kernel norm. -/
theorem norm_shiftedFejerSpatialKernel
    (N : ℕ) (c : ℤ) (z : UnitAddCircle) :
    ‖shiftedFejerSpatialKernel N c z‖ =
      ‖FejerLocalMass.fejerKernel N (-z)‖ := by
  rw [shiftedFejerSpatialKernel_eq_modulated_fejer, norm_mul,
    fourier_apply, Circle.norm_coe, one_mul]

/-- The chord of the basic character controls the intrinsic circle distance.
The endpoint `‖z‖ = 1/2` is included. -/
theorem four_mul_norm_le_norm_fourier_one_sub (z : UnitAddCircle) :
    4 * ‖z‖ ≤ ‖fourier 1 z - 1‖ := by
  induction z using QuotientAddGroup.induction_on with
  | _ x =>
      have ht : |x - (round x : ℝ)| ≤ (1 : ℝ) / 2 := abs_sub_round x
      have hu : |Real.pi * (x - (round x : ℝ))| ≤ Real.pi / 2 := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        nlinarith [Real.pi_pos]
      have hjordan := Real.mul_abs_le_abs_sin hu
      have hsin :
          |Real.sin (Real.pi * (x - (round x : ℝ)))| =
            |Real.sin (Real.pi * x)| := by
        rw [show Real.pi * (x - (round x : ℝ)) =
            Real.pi * x - (round x : ℝ) * Real.pi by ring,
          Real.sin_sub_int_mul_pi, abs_mul]
        have hone : |((-1 : ℝ) ^ (round x))| = 1 := by
          rw [abs_zpow]
          norm_num
        rw [hone, one_mul]
      have hlower : 2 * |x - (round x : ℝ)| ≤
          |Real.sin (Real.pi * x)| := by
        rw [← hsin]
        calc
          2 * |x - (round x : ℝ)| =
              2 / Real.pi * |Real.pi * (x - (round x : ℝ))| := by
            rw [abs_mul, abs_of_pos Real.pi_pos]
            field_simp [Real.pi_ne_zero]
          _ ≤ |Real.sin (Real.pi * (x - (round x : ℝ)))| := hjordan
      rw [UnitAddCircle.norm_eq]
      rw [fourier_coe_apply]
      have hexp :
          Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (x : ℂ) / (1 : ℝ)) =
            Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) := by
        congr 1
        push_cast
        ring
      rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
      norm_num [Real.norm_eq_abs, norm_mul]
      rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring]
      nlinarith

/-- Characters at natural frequencies are powers of the basic character. -/
theorem fourier_nat_eq_pow (j : ℕ) (z : UnitAddCircle) :
    fourier (j : ℤ) z = (fourier 1 z) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        fourier ((j + 1 : ℕ) : ℤ) z = fourier ((j : ℤ) + 1) z := by norm_num
        _ = fourier (j : ℤ) z * fourier 1 z := fourier_add
        _ = (fourier 1 z) ^ (j + 1) := by rw [ih, pow_succ]

/-- Exact geometric-series identity for the one-sided Dirichlet block. -/
theorem dirichletBlock_mul_chord
    (N : ℕ) (z : UnitAddCircle) :
    FejerLocalMass.dirichletBlock N z * (fourier 1 z - 1) =
      fourier (N : ℤ) z - 1 := by
  rw [FejerLocalMass.dirichletBlock]
  simp_rw [fourier_nat_eq_pow]
  exact geom_sum_mul (fourier 1 z) N

/-- Triangle-inequality bound for the one-sided block. -/
theorem norm_dirichletBlock_le (N : ℕ) (z : UnitAddCircle) :
    ‖FejerLocalMass.dirichletBlock N z‖ ≤ N := by
  rw [FejerLocalMass.dirichletBlock]
  calc
    ‖∑ j ∈ Finset.range N, fourier (j : ℤ) z‖ ≤
        ∑ j ∈ Finset.range N, ‖fourier (j : ℤ) z‖ := norm_sum_le _ _
    _ = N := by
      simp only [fourier_apply, Circle.norm_coe, Finset.sum_const,
        nsmul_eq_mul, mul_one, Finset.card_range]

/-- Exact norm formula for the nonnegative Fejér kernel. -/
theorem norm_fejerKernel_eq
    (N : ℕ) (z : UnitAddCircle) :
    ‖FejerLocalMass.fejerKernel N z‖ =
      (N : ℝ)⁻¹ * ‖FejerLocalMass.dirichletBlock N z‖ ^ 2 := by
  rw [FejerLocalMass.fejerKernel_eq_normSq]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg]
  positivity

/-- The global height bound `F_N ≤ N`, with the zero order totalized
correctly. -/
theorem norm_fejerKernel_le_order (N : ℕ) (z : UnitAddCircle) :
    ‖FejerLocalMass.fejerKernel N z‖ ≤ N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [FejerLocalMass.fejerKernel, FejerLocalMass.dirichletBlock]
  · have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    rw [norm_fejerKernel_eq]
    have hD := norm_dirichletBlock_le N z
    calc
      (N : ℝ)⁻¹ * ‖FejerLocalMass.dirichletBlock N z‖ ^ 2 ≤
          (N : ℝ)⁻¹ * (N : ℝ) ^ 2 := by gcongr
      _ = (N : ℝ) := by field_simp

/-- The basic chord times the Dirichlet block is uniformly bounded by two. -/
theorem chord_mul_norm_dirichletBlock_le_two
    (N : ℕ) (z : UnitAddCircle) :
    ‖fourier 1 z - 1‖ * ‖FejerLocalMass.dirichletBlock N z‖ ≤ 2 := by
  rw [mul_comm, ← norm_mul, dirichletBlock_mul_chord]
  calc
    ‖fourier (N : ℤ) z - 1‖ ≤
        ‖fourier (N : ℤ) z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [fourier_apply, Circle.norm_coe]; norm_num

/-- Pointwise Fejér tail in division-free form.  Since `dist z 0 = ‖z‖`,
this is exactly `F_N(z) ≤ (4 N dist(z,0)^2)⁻¹` away from the origin. -/
theorem fejerKernel_quadratic_tail_mul
    (N : ℕ) (z : UnitAddCircle) :
    4 * (N : ℝ) * dist z 0 ^ 2 *
        ‖FejerLocalMass.fejerKernel N z‖ ≤ 1 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [FejerLocalMass.fejerKernel, FejerLocalMass.dirichletBlock]
  · have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hchord := four_mul_norm_le_norm_fourier_one_sub z
    have hprod := chord_mul_norm_dirichletBlock_le_two N z
    have hbasic : 2 * ‖z‖ * ‖FejerLocalMass.dirichletBlock N z‖ ≤ 1 := by
      nlinarith [norm_nonneg (fourier 1 z - 1),
        norm_nonneg (FejerLocalMass.dirichletBlock N z), norm_nonneg z]
    have ha0 : 0 ≤
        2 * ‖z‖ * ‖FejerLocalMass.dirichletBlock N z‖ := by positivity
    have hsquare := pow_le_pow_left₀ ha0 hbasic 2
    have hsq :
        4 * ‖z‖ ^ 2 * ‖FejerLocalMass.dirichletBlock N z‖ ^ 2 ≤ 1 := by
      ring_nf at hsquare ⊢
      exact hsquare
    rw [norm_fejerKernel_eq]
    rw [dist_eq_norm, sub_zero]
    calc
      4 * (N : ℝ) * ‖z‖ ^ 2 *
          ((N : ℝ)⁻¹ * ‖FejerLocalMass.dirichletBlock N z‖ ^ 2) =
        4 * ‖z‖ ^ 2 * ‖FejerLocalMass.dirichletBlock N z‖ ^ 2 := by
          field_simp
      _ ≤ 1 := hsq

/-- Conventional inverse-form pointwise tail away from the kernel center. -/
theorem norm_fejerKernel_le_quadratic_tail
    {N : ℕ} (hN : 0 < N) {z : UnitAddCircle} (hz : z ≠ 0) :
    ‖FejerLocalMass.fejerKernel N z‖ ≤
      (4 * (N : ℝ) * dist z 0 ^ 2)⁻¹ := by
  have hden : 0 < 4 * (N : ℝ) * dist z 0 ^ 2 := by
    have hd : 0 < dist z 0 := dist_pos.mpr hz
    positivity
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hden).2
  calc
    ‖FejerLocalMass.fejerKernel N z‖ *
        (4 * (N : ℝ) * dist z 0 ^ 2) =
      4 * (N : ℝ) * dist z 0 ^ 2 *
        ‖FejerLocalMass.fejerKernel N z‖ := by ring
    _ ≤ 1 := fejerKernel_quadratic_tail_mul N z

/-- Grid indices wide enough to cover a full set of circle residues.  The
single extra endpoint on each side makes rounding tie-safe. -/
def fejerGridIndices (M : ℕ) : Finset ℤ :=
  Finset.Icc (-((M / 2 + 1 : ℕ) : ℤ)) ((M / 2 + 1 : ℕ) : ℤ)

/-- The literal grid center, translated by an arbitrary circle point. -/
def fejerGridCenter (M : ℕ) (x : UnitAddCircle) (j : ℤ) : UnitAddCircle :=
  x + (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle)

/-- Closed grid cells. Closed endpoints are deliberate: ties and the antipodal
point are covered rather than discarded. -/
def fejerGridBall (M : ℕ) (x : UnitAddCircle) (j : ℤ) : Set UnitAddCircle :=
  closedBall (fejerGridCenter M x j) ((2 * (M : ℝ))⁻¹)

/-- A real integer maps to zero in the unit additive circle. -/
theorem coe_intCast_unitAddCircle_eq_zero (j : ℤ) :
    (((j : ℝ) : ℝ) : UnitAddCircle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨j, by simp⟩

/-- The tie-safe grid of radius `1/(2M)` closed balls covers the whole circle,
uniformly after translation. This is the wraparound/endpoint covering lemma
needed by the annular argument. -/
theorem mem_fejerGridBall
    {M : ℕ} (hM : 0 < M) (x y : UnitAddCircle) :
    ∃ j ∈ fejerGridIndices M, y ∈ fejerGridBall M x j := by
  obtain ⟨a : ℝ, ha⟩ := QuotientAddGroup.mk_surjective (y - x)
  let t : ℝ := a - (round a : ℝ)
  let j : ℤ := round ((M : ℝ) * t)
  have ht : |t| ≤ (1 : ℝ) / 2 := by
    simpa only [t] using abs_sub_round a
  have hMt : |(M : ℝ) * t - (j : ℝ)| ≤ (1 : ℝ) / 2 := by
    simpa only [j] using abs_sub_round ((M : ℝ) * t)
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hterr : |t - (j : ℝ) / (M : ℝ)| ≤ (2 * (M : ℝ))⁻¹ := by
    rw [abs_sub_comm]
    have heq : (j : ℝ) / (M : ℝ) - t =
        ((j : ℝ) - (M : ℝ) * t) / (M : ℝ) := by field_simp
    rw [heq, abs_div, abs_of_pos hMreal]
    rw [abs_sub_comm]
    calc
      |(M : ℝ) * t - (j : ℝ)| / (M : ℝ) ≤
          ((1 : ℝ) / 2) / (M : ℝ) :=
        (div_le_div_iff_of_pos_right hMreal).2 hMt
      _ = (2 * (M : ℝ))⁻¹ := by field_simp
  have hhalf : |t - (j : ℝ) / (M : ℝ)| ≤ (1 : ℝ) / 2 := by
    exact hterr.trans (by
      rw [one_div]
      apply (inv_le_inv₀ (by positivity) (by positivity)).2
      have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
      nlinarith)
  have htcoe : (t : UnitAddCircle) = y - x := by
    calc
      (t : UnitAddCircle) =
          (a : UnitAddCircle) - (((round a : ℤ) : ℝ) : UnitAddCircle) := by
            rw [← AddCircle.coe_sub]
      _ = (a : UnitAddCircle) := by rw [coe_intCast_unitAddCircle_eq_zero, sub_zero]
      _ = y - x := ha
  have hmod : M % 2 < 2 := Nat.mod_lt M (by omega)
  have hdecomp : 2 * (M / 2) + M % 2 = M := Nat.div_add_mod M 2
  have hMupperNat : M ≤ 2 * (M / 2) + 1 := by omega
  have hMupperReal : (M : ℝ) / 2 ≤ (M / 2 : ℕ) + 1 / 2 := by
    have hc : (M : ℝ) ≤ 2 * (M / 2 : ℕ) + 1 := by
      exact_mod_cast hMupperNat
    linarith
  have hjupperReal : (j : ℝ) ≤ (M / 2 + 1 : ℕ) := by
    have hj := round_le_add_half ((M : ℝ) * t)
    have htupper : t ≤ 1 / 2 := (abs_le.mp ht).2
    have hprod : (M : ℝ) * t ≤ (M : ℝ) / 2 := by nlinarith
    push_cast at hj ⊢
    linarith
  have hjlowerReal : -((M / 2 + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
    have hj := sub_half_lt_round ((M : ℝ) * t)
    have htlower : -(1 / 2 : ℝ) ≤ t := (abs_le.mp ht).1
    have hprod : -(M : ℝ) / 2 ≤ (M : ℝ) * t := by nlinarith
    push_cast at hj ⊢
    linarith
  have hjmem : j ∈ fejerGridIndices M := by
    rw [fejerGridIndices, Finset.mem_Icc]
    constructor
    · have hr : ((↑(-((M / 2 + 1 : ℕ) : ℤ)) : ℝ) ≤ (j : ℝ)) := by
        rw [Int.cast_neg, Int.cast_natCast]
        exact hjlowerReal
      exact (Int.cast_le (R := ℝ)).mp hr
    · have hr : ((j : ℝ) ≤ (↑((M / 2 + 1 : ℕ) : ℤ) : ℝ)) := by
        rw [Int.cast_natCast]
        exact hjupperReal
      exact (Int.cast_le (R := ℝ)).mp hr
  refine ⟨j, hjmem, ?_⟩
  rw [fejerGridBall, mem_closedBall, dist_eq_norm]
  have hdiff :
      y - fejerGridCenter M x j =
        ((t - (j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) := by
    rw [fejerGridCenter, AddCircle.coe_sub]
    rw [htcoe]
    abel
  rw [hdiff]
  rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2]
  · exact hterr
  · simpa using hhalf

/-- Interior grid centers have their expected intrinsic distance from the
translated origin; the quotient does not wrap before half a period. -/
theorem dist_fejerGridCenter_eq
    {M : ℕ} (hM : 0 < M) (x : UnitAddCircle) {j : ℤ}
    (hj : j.natAbs ≤ M / 2) :
    dist (fejerGridCenter M x j) x = (j.natAbs : ℝ) / M := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  rw [dist_eq_norm]
  have hsub : fejerGridCenter M x j - x =
      (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) := by
    rw [fejerGridCenter]
    abel
  rw [hsub]
  rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2]
  · rw [abs_div, abs_of_pos hMreal]
    have habs : |(j : ℝ)| = (j.natAbs : ℝ) := by
      rw [← Int.cast_abs, Nat.cast_natAbs]
    rw [habs]
  · rw [abs_div, abs_of_pos hMreal]
    have habs : |(j : ℝ)| = (j.natAbs : ℝ) := by
      rw [← Int.cast_abs, Nat.cast_natAbs]
    rw [habs]
    have hjreal : ((j.natAbs : ℕ) : ℝ) ≤ (M / 2 : ℕ) := by exact_mod_cast hj
    have hhalf : ((M / 2 : ℕ) : ℝ) / (M : ℝ) ≤ (1 : ℝ) / 2 := by
      apply (div_le_iff₀ hMreal).2
      have hdivNat : 2 * (M / 2) ≤ M := by omega
      have hdivReal : (2 : ℝ) * (M / 2 : ℕ) ≤ M := by
        exact_mod_cast hdivNat
      linarith
    norm_num only [abs_one]
    exact (div_le_div_of_nonneg_right hjreal hMreal.le).trans hhalf

/-- On a noncentral interior grid cell, distance from the kernel center is
bounded below by half the grid-index distance. Closed boundary points are
included. -/
theorem fejerGridBall_distance_lower
    {M : ℕ} (hM : 0 < M) (x y : UnitAddCircle) {j : ℤ}
    (hj0 : 0 < j.natAbs) (hj : j.natAbs ≤ M / 2)
    (hy : y ∈ fejerGridBall M x j) :
    (j.natAbs : ℝ) / (2 * (M : ℝ)) ≤ dist (x - y) 0 := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hyball : dist y (fejerGridCenter M x j) ≤ (2 * (M : ℝ))⁻¹ := by
    simpa only [fejerGridBall, mem_closedBall] using hy
  have hcenter := dist_fejerGridCenter_eq hM x hj
  have htriangle :
      dist (fejerGridCenter M x j) x ≤
        dist (fejerGridCenter M x j) y + dist y x :=
    dist_triangle _ _ _
  have hraw : (j.natAbs : ℝ) / M - (2 * (M : ℝ))⁻¹ ≤ dist y x := by
    rw [hcenter] at htriangle
    rw [dist_comm (fejerGridCenter M x j) y] at htriangle
    linarith
  have hjone : (1 : ℝ) ≤ j.natAbs := by exact_mod_cast hj0
  have halgebra :
      (j.natAbs : ℝ) / (2 * (M : ℝ)) ≤
        (j.natAbs : ℝ) / M - (2 * (M : ℝ))⁻¹ := by
    rw [inv_eq_one_div]
    field_simp
    nlinarith
  have hdist : dist y x = dist (x - y) 0 := by
    simp only [dist_eq_norm, sub_zero]
    rw [norm_sub_rev]
  rw [← hdist]
  exact halgebra.trans hraw

/-- Quadratic kernel decay on every noncentral interior grid cell. -/
theorem norm_shiftedFejerSpatialKernel_le_on_gridBall
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (c : ℤ) (x y : UnitAddCircle) {j : ℤ}
    (hj0 : 0 < j.natAbs) (hj : j.natAbs ≤ M / 2)
    (hy : y ∈ fejerGridBall M x j) :
    ‖shiftedFejerSpatialKernel N c (x - y)‖ ≤
      (M : ℝ) ^ 2 / ((N : ℝ) * j.natAbs ^ 2) := by
  rw [norm_shiftedFejerSpatialKernel]
  have hz : -(x - y) ≠ 0 := by
    intro hz
    have hzero : dist (x - y) 0 = 0 := by simpa using congrArg (fun z ↦ dist (-z) 0) hz
    have hlower := fejerGridBall_distance_lower hM x y hj0 hj hy
    rw [hzero] at hlower
    have : (0 : ℝ) < (j.natAbs : ℝ) / (2 * M) := by positivity
    linarith
  have htail := norm_fejerKernel_le_quadratic_tail hN hz
  have hlower := fejerGridBall_distance_lower hM x y hj0 hj hy
  have hdistneg : dist (-(x - y)) 0 = dist (x - y) 0 := by
    simp only [dist_eq_norm, sub_zero, norm_neg]
  rw [hdistneg] at htail
  calc
    ‖FejerLocalMass.fejerKernel N (-(x - y))‖ ≤
        (4 * (N : ℝ) * dist (x - y) 0 ^ 2)⁻¹ := htail
    _ ≤ (M : ℝ) ^ 2 / ((N : ℝ) * j.natAbs ^ 2) := by
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hjr : (0 : ℝ) < j.natAbs := by exact_mod_cast hj0
      have hden : 0 < 4 * (N : ℝ) * dist (x - y) 0 ^ 2 := by
        have hd : 0 < dist (x - y) 0 := lt_of_lt_of_le (by positivity) hlower
        positivity
      have hsquare := pow_le_pow_left₀
        (by positivity : 0 ≤ (j.natAbs : ℝ) / (2 * (M : ℝ))) hlower 2
      have hdenlower :
          (N : ℝ) * (j.natAbs : ℝ) ^ 2 / (M : ℝ) ^ 2 ≤
            4 * (N : ℝ) * dist (x - y) 0 ^ 2 := by
        field_simp at hsquare ⊢
        nlinarith
      have hsmallpos : 0 <
          (N : ℝ) * (j.natAbs : ℝ) ^ 2 / (M : ℝ) ^ 2 := by positivity
      rw [inv_eq_one_div]
      calc
        1 / (4 * (N : ℝ) * dist (x - y) 0 ^ 2) ≤
            1 / ((N : ℝ) * (j.natAbs : ℝ) ^ 2 / (M : ℝ) ^ 2) :=
          one_div_le_one_div_of_le hsmallpos hdenlower
        _ = (M : ℝ) ^ 2 / ((N : ℝ) * (j.natAbs : ℝ) ^ 2) := by
          field_simp

/-- A `natAbs` fiber of any finite integer set contains at most the two
points `n` and `-n`. -/
theorem card_filter_natAbs_eq_le_two (s : Finset ℤ) (n : ℕ) :
    ((s.filter fun j ↦ j.natAbs = n).card : ℕ) ≤ 2 := by
  calc
    (s.filter fun j ↦ j.natAbs = n).card ≤
        ({(n : ℤ), -(n : ℤ)} : Finset ℤ).card := by
      apply Finset.card_le_card
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact Int.natAbs_eq_iff.mp hj.2
    _ ≤ 2 := Finset.card_le_two

/-- The reciprocal-square mass of all noncentral interior grid indices is
uniformly bounded. Both signs and all closed endpoints are counted. -/
theorem fejerGrid_interior_inv_sq_sum_le_four (M : ℕ) :
    (∑ j ∈ fejerGridIndices M,
      if 0 < j.natAbs ∧ j.natAbs ≤ M / 2 then
        (((j.natAbs : ℝ) ^ 2)⁻¹) else 0) ≤ 4 := by
  classical
  let s : Finset ℤ := (fejerGridIndices M).filter
    (fun j ↦ 0 < j.natAbs ∧ j.natAbs ≤ M / 2)
  let t : Finset ℕ := Finset.Icc 1 (M / 2)
  have hmap : ∀ j ∈ s, j.natAbs ∈ t := by
    intro j hj
    change j ∈ (fejerGridIndices M).filter
      (fun j ↦ 0 < j.natAbs ∧ j.natAbs ≤ M / 2) at hj
    change j.natAbs ∈ Finset.Icc 1 (M / 2)
    simp only [Finset.mem_filter] at hj
    rw [Finset.mem_Icc]
    omega
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (M := ℝ) hmap (fun j : ℤ ↦ (((j.natAbs : ℝ) ^ 2)⁻¹))
  have hrewrite :
      (∑ j ∈ fejerGridIndices M,
        if 0 < j.natAbs ∧ j.natAbs ≤ M / 2 then
          (((j.natAbs : ℝ) ^ 2)⁻¹) else 0) =
        ∑ j ∈ s, (((j.natAbs : ℝ) ^ 2)⁻¹) := by
    simp only [s, Finset.sum_filter]
  rw [hrewrite, ← hfiber]
  calc
    (∑ n ∈ t, ∑ j ∈ s with j.natAbs = n,
        (((j.natAbs : ℝ) ^ 2)⁻¹)) ≤
      ∑ n ∈ t, 2 * (((n : ℝ) ^ 2)⁻¹) := by
        apply Finset.sum_le_sum
        intro n hn
        have hcard := card_filter_natAbs_eq_le_two s n
        calc
          (∑ j ∈ s with j.natAbs = n,
              (((j.natAbs : ℝ) ^ 2)⁻¹)) =
            ∑ j ∈ s with j.natAbs = n, (((n : ℝ) ^ 2)⁻¹) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [(Finset.mem_filter.mp hj).2]
          _ = ((s.filter fun j ↦ j.natAbs = n).card : ℝ) *
              (((n : ℝ) ^ 2)⁻¹) := by
                rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 2 * (((n : ℝ) ^ 2)⁻¹) := by
            gcongr
            exact_mod_cast hcard
    _ = 2 * ∑ n ∈ t, (((n : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * 2 := by
      gcongr
      have hteq : t = Finset.Ioo 0 (M / 2 + 1) := by
        ext n
        change n ∈ Finset.Icc 1 (M / 2) ↔ n ∈ Finset.Ioo 0 (M / 2 + 1)
        simp only [Finset.mem_Icc, Finset.mem_Ioo]
        omega
      rw [hteq]
      simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (M / 2 + 1))
    _ = 4 := by norm_num

/-- A noncentral reciprocal-square majorant on interior cells, and the
global height bound on the central and two tie-safe endpoint cells. -/
def gridKernelMajorant (N M : ℕ) (j : ℤ) : ℝ :=
  if 0 < j.natAbs ∧ j.natAbs ≤ M / 2 then
    (M : ℝ) ^ 2 / ((N : ℝ) * (j.natAbs : ℝ) ^ 2)
  else (N : ℝ)

 theorem gridKernelMajorant_nonneg (N M : ℕ) (j : ℤ) :
    0 ≤ gridKernelMajorant N M j := by
  rw [gridKernelMajorant]
  split_ifs <;> positivity

/-- The spatial kernel is bounded by the grid majorant on each literal cell. -/
theorem norm_shiftedFejerSpatialKernel_le_gridKernelMajorant
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (c : ℤ) (x y : UnitAddCircle) {j : ℤ}
    (hy : y ∈ fejerGridBall M x j) :
    ‖shiftedFejerSpatialKernel N c (x - y)‖ ≤
      gridKernelMajorant N M j := by
  rw [gridKernelMajorant]
  by_cases hj : 0 < j.natAbs ∧ j.natAbs ≤ M / 2
  · rw [if_pos hj]
    exact norm_shiftedFejerSpatialKernel_le_on_gridBall
      hN hM c x y hj.1 hj.2 hy
  · rw [if_neg hj, norm_shiftedFejerSpatialKernel]
    exact norm_fejerKernel_le_order N (-(x - y))

/-- Only the central residue and the two tie-safe extreme residues can fail
the noncentral interior condition. -/
theorem card_fejerGrid_noninterior_le_three (M : ℕ) :
    ((fejerGridIndices M).filter
      (fun j ↦ ¬(0 < j.natAbs ∧ j.natAbs ≤ M / 2))).card ≤ 3 := by
  let R : ℕ := M / 2 + 1
  calc
    ((fejerGridIndices M).filter
        (fun j ↦ ¬(0 < j.natAbs ∧ j.natAbs ≤ M / 2))).card ≤
      ({(0 : ℤ), (R : ℤ), -(R : ℤ)} : Finset ℤ).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_filter] at hj
        have hrange := hj.1
        rw [fejerGridIndices, Finset.mem_Icc] at hrange
        have habsInt : |j| ≤ (R : ℤ) := by
          rw [abs_le]
          simpa only [R] using hrange
        have habsCast : (j.natAbs : ℤ) ≤ (R : ℤ) := by
          simpa only [Int.natCast_natAbs] using habsInt
        have habs : j.natAbs ≤ R := by exact_mod_cast habsCast
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
        by_cases hj0 : j.natAbs = 0
        · left
          exact Int.natAbs_eq_zero.mp hj0
        · right
          have hjpos : 0 < j.natAbs := Nat.pos_of_ne_zero hj0
          have hnon := hj.2
          have hjlarge : M / 2 < j.natAbs := by
            push Not at hnon
            exact hnon hjpos
          have heq : j.natAbs = R := by omega
          exact Int.natAbs_eq_iff.mp heq
    _ ≤ 3 := by
      calc
        ({(0 : ℤ), (R : ℤ), -(R : ℤ)} : Finset ℤ).card ≤
            ({(R : ℤ), -(R : ℤ)} : Finset ℤ).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ 2 + 1 := by gcongr; exact Finset.card_le_two
        _ = 3 := by norm_num

/-- The complete grid-majorant mass is `O(M)` at the paper-safe order
`N = 2M + 2`. -/
theorem sum_gridKernelMajorant_translatedOrder_le
    {M : ℕ} (hM : 0 < M) :
    (∑ j ∈ fejerGridIndices M, gridKernelMajorant (2 * M + 2) M j) ≤
      14 * (M : ℝ) := by
  classical
  let P : ℤ → Prop := fun j ↦ 0 < j.natAbs ∧ j.natAbs ≤ M / 2
  have hbad := card_fejerGrid_noninterior_le_three M
  have hinter := fejerGrid_interior_inv_sq_sum_le_four M
  have hcardeqNat :
      ((fejerGridIndices M).filter (fun j ↦ ¬ P j)).card =
        ∑ j ∈ fejerGridIndices M, if P j then 0 else 1 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hp : P j <;> simp [hp]
  have hcardeq :
      (((fejerGridIndices M).filter (fun j ↦ ¬ P j)).card : ℝ) =
        ∑ j ∈ fejerGridIndices M, if P j then 0 else 1 := by
    exact_mod_cast hcardeqNat
  have hsplit :
      (∑ j ∈ fejerGridIndices M,
        gridKernelMajorant (2 * M + 2) M j) =
      ((M : ℝ) ^ 2 / (2 * M + 2 : ℕ)) *
        (∑ j ∈ fejerGridIndices M,
          if P j then (((j.natAbs : ℝ) ^ 2)⁻¹) else 0) +
      (2 * M + 2 : ℕ) *
        (((fejerGridIndices M).filter (fun j ↦ ¬ P j)).card : ℝ) := by
    rw [hcardeq, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [gridKernelMajorant]
    by_cases hp : P j
    · have hp' : 0 < j.natAbs ∧ j.natAbs ≤ M / 2 := hp
      simp only [hp, if_true]
      simp [hp'.1, hp'.2]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · have hp' : ¬(0 < j.natAbs ∧ j.natAbs ≤ M / 2) := hp
      rw [if_neg hp']
      simp only [hp, if_false, mul_zero, mul_one, zero_add]
  rw [hsplit]
  have hNreal : (0 : ℝ) < (2 * M + 2 : ℕ) := by positivity
  have hcoef : (M : ℝ) ^ 2 / (2 * M + 2 : ℕ) ≤ (M : ℝ) / 2 := by
    push_cast
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * M + 2)).2
    nlinarith
  have hsum0 : 0 ≤
      (∑ j ∈ fejerGridIndices M,
        if P j then (((j.natAbs : ℝ) ^ 2)⁻¹) else 0) := by positivity
  have hcoef0 : 0 ≤ (M : ℝ) ^ 2 / (2 * M + 2 : ℕ) := by positivity
  have hterm1 :
      (M : ℝ) ^ 2 / (2 * M + 2 : ℕ) *
          (∑ j ∈ fejerGridIndices M,
            if P j then (((j.natAbs : ℝ) ^ 2)⁻¹) else 0) ≤
        ((M : ℝ) / 2) * 4 := by
    apply mul_le_mul hcoef
    · simpa only [P] using hinter
    · exact hsum0
    · positivity
  have hbadReal :
      (((fejerGridIndices M).filter (fun j ↦ ¬ P j)).card : ℝ) ≤ 3 := by
    exact_mod_cast (by simpa only [P] using hbad)
  have hterm2 :
      (2 * M + 2 : ℕ) *
          (((fejerGridIndices M).filter (fun j ↦ ¬ P j)).card : ℝ) ≤
        (2 * (M : ℝ) + 2) * 3 := by
    push_cast
    exact mul_le_mul_of_nonneg_left hbadReal (by positivity)
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  push_cast at hterm1 hterm2 ⊢
  nlinarith

/-- Every grid cell is contained in the requested radius-`1/(2H)` arc when
`H ≤ M`; therefore its closed endpoints and any wraparound mass are covered
by the literal local hypothesis. -/
theorem fejerGridBall_subset_centeredArc
    {H : ℝ} {M : ℕ} (hH : 0 < H) (hHM : H ≤ M)
    (x : UnitAddCircle) (j : ℤ) :
    fejerGridBall M x j ⊆
      PrimePairEndpoints.centeredArc H (fejerGridCenter M x j) := by
  intro y hy
  rw [fejerGridBall, mem_closedBall] at hy
  rw [PrimePairEndpoints.centeredArc, mem_closedBall]
  exact hy.trans (by
    have hM : (0 : ℝ) < M := lt_of_lt_of_le hH hHM
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < 2 * M)
      (by positivity : (0 : ℝ) < 2 * H)]
    nlinarith)

/-- Conjugating the paper-facing Fourier coefficient reverses the character
inside the normalized-Haar integral. -/
theorem conj_circleCoefficient_eq_integral
    {w : UnitAddCircle → ℝ}
    (_hw : Integrable w AddCircle.haarAddCircle) (h : ℤ) :
    conj (circleCoefficient w h) =
      ∫ y : UnitAddCircle, (w y : ℂ) * fourier h y
        ∂AddCircle.haarAddCircle := by
  rw [circleCoefficient, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  simp only [map_mul, Complex.conj_ofReal, ← fourier_neg]
  simp

/-- A Fourier character evaluated on a group difference. -/
theorem fourier_sub_argument (h : ℤ) (x y : UnitAddCircle) :
    fourier h (x - y) = fourier h x * fourier (-h) y := by
  rw [fourier_apply, zsmul_sub, sub_eq_add_neg, toCircle_add,
    toCircle_neg, Circle.coe_mul, Circle.coe_inv_eq_conj]
  rw [← fourier_apply, ← fourier_apply, ← fourier_neg]

/-- Each summand has the spatial form obtained by multiplying its character
at `x` by the conjugated coefficient. -/
theorem shiftedFejerConvolution_eq_integral_sum
    {w : UnitAddCircle → ℝ}
    (hw : Integrable w AddCircle.haarAddCircle)
    (N : ℕ) (c : ℤ) (x : UnitAddCircle) :
    shiftedFejerConvolution w N c x =
      ∫ y : UnitAddCircle,
        (w y : ℂ) * shiftedFejerSpatialKernel N c (x - y)
          ∂AddCircle.haarAddCircle := by
  classical
  simp only [shiftedFejerConvolution, shiftedFejerSpatialKernel]
  have hfun :
      (fun y : UnitAddCircle ↦
        (w y : ℂ) *
          ∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
            ((FejerLocalMass.pairMultiplicity N k : ℝ) / N : ℂ) *
              fourier (-(c + k)) (x - y)) =
      (fun y : UnitAddCircle ↦
        ∑ k ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1),
          ((FejerLocalMass.pairMultiplicity N k : ℝ) / N : ℂ) *
            fourier (-(c + k)) x *
              ((w y : ℂ) * fourier (c + k) y)) := by
    funext y
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [fourier_sub_argument]
    simp only [neg_neg]
    ring
  rw [hfun, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul, conj_circleCoefficient_eq_integral hw]
  · intro k hk
    exact (hw.ofReal.mul_bdd
      (map_continuous (fourier (c + k))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦ by
        rw [fourier_apply, Circle.norm_coe])).const_mul _

/-- The closed grid, pointwise kernel bounds, and nonnegative local mass
hypothesis combine into a literal convolution estimate. -/
theorem norm_shiftedFejerConvolution_le_grid_sum
    {w : UnitAddCircle → ℝ}
    (hw : Integrable w AddCircle.haarAddCircle)
    (hw0 : ∀ y, 0 ≤ w y)
    {H : ℝ} {M N : ℕ} (hH : 0 < H) (hHM : H ≤ M)
    (hM : 0 < M) (hN : 0 < N)
    (c : ℤ) {localBound : ℝ} (_hlocal0 : 0 ≤ localBound)
    (hlocal : ∀ center : UnitAddCircle,
      (∫ y in PrimePairEndpoints.centeredArc H center, w y
        ∂AddCircle.haarAddCircle) ≤ localBound)
    (x : UnitAddCircle) :
    ‖shiftedFejerConvolution w N c x‖ ≤
      localBound * ∑ j ∈ fejerGridIndices M, gridKernelMajorant N M j := by
  classical
  let G : UnitAddCircle → ℝ := fun y ↦
    ∑ j ∈ fejerGridIndices M,
      (fejerGridBall M x j).indicator
        (fun y ↦ w y * gridKernelMajorant N M j) y
  have htermInt : ∀ j ∈ fejerGridIndices M,
      Integrable
        ((fejerGridBall M x j).indicator
          (fun y ↦ w y * gridKernelMajorant N M j))
        AddCircle.haarAddCircle := by
    intro j hj
    exact (hw.mul_const (gridKernelMajorant N M j)).indicator
      measurableSet_closedBall
  have hGint : Integrable G AddCircle.haarAddCircle := by
    exact integrable_finsetSum _ htermInt
  have hpoint : ∀ y : UnitAddCircle,
      w y * ‖shiftedFejerSpatialKernel N c (x - y)‖ ≤ G y := by
    intro y
    obtain ⟨j, hj, hy⟩ := mem_fejerGridBall hM x y
    have hk := norm_shiftedFejerSpatialKernel_le_gridKernelMajorant
      hN hM c x y hy
    calc
      w y * ‖shiftedFejerSpatialKernel N c (x - y)‖ ≤
          w y * gridKernelMajorant N M j :=
        mul_le_mul_of_nonneg_left hk (hw0 y)
      _ = (fejerGridBall M x j).indicator
          (fun y ↦ w y * gridKernelMajorant N M j) y := by
        rw [Set.indicator_of_mem hy]
      _ ≤ G y := by
        change (fejerGridBall M x j).indicator
            (fun y ↦ w y * gridKernelMajorant N M j) y ≤
          ∑ k ∈ fejerGridIndices M,
            (fejerGridBall M x k).indicator
              (fun y ↦ w y * gridKernelMajorant N M k) y
        apply Finset.single_le_sum
          (s := fejerGridIndices M)
          (f := fun k ↦ (fejerGridBall M x k).indicator
            (fun y ↦ w y * gridKernelMajorant N M k) y)
        · intro k hk
          by_cases hyk : y ∈ fejerGridBall M x k
          · rw [Set.indicator_of_mem hyk]
            exact mul_nonneg (hw0 y) (gridKernelMajorant_nonneg N M k)
          · rw [Set.indicator_of_notMem hyk]
        · exact hj
  have hnorm :
      ‖shiftedFejerConvolution w N c x‖ ≤
        ∫ y : UnitAddCircle,
          w y * ‖shiftedFejerSpatialKernel N c (x - y)‖
            ∂AddCircle.haarAddCircle := by
    rw [shiftedFejerConvolution_eq_integral_sum hw]
    calc
      ‖∫ y : UnitAddCircle,
          (w y : ℂ) * shiftedFejerSpatialKernel N c (x - y)
            ∂AddCircle.haarAddCircle‖ ≤
        ∫ y : UnitAddCircle,
          ‖(w y : ℂ) * shiftedFejerSpatialKernel N c (x - y)‖
            ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
      _ = ∫ y : UnitAddCircle,
          w y * ‖shiftedFejerSpatialKernel N c (x - y)‖
            ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards with y
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw0 y)]
  have htoG :
      (∫ y : UnitAddCircle,
          w y * ‖shiftedFejerSpatialKernel N c (x - y)‖
            ∂AddCircle.haarAddCircle) ≤
        ∫ y : UnitAddCircle, G y ∂AddCircle.haarAddCircle := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun y ↦
        mul_nonneg (hw0 y) (norm_nonneg _)
    · exact hGint
    · exact Filter.Eventually.of_forall hpoint
  have hGIntegral :
      (∫ y : UnitAddCircle, G y ∂AddCircle.haarAddCircle) =
        ∑ j ∈ fejerGridIndices M,
          (∫ y in fejerGridBall M x j, w y
            ∂AddCircle.haarAddCircle) * gridKernelMajorant N M j := by
    rw [show G = fun y : UnitAddCircle ↦
        ∑ j ∈ fejerGridIndices M,
          (fejerGridBall M x j).indicator
            (fun y ↦ w y * gridKernelMajorant N M j) y by rfl]
    rw [integral_finsetSum _ htermInt]
    apply Finset.sum_congr rfl
    intro j hj
    have hmeas : MeasurableSet (fejerGridBall M x j) := by
      rw [fejerGridBall]
      exact measurableSet_closedBall
    rw [integral_indicator hmeas, integral_mul_const]
  have hcell : ∀ j ∈ fejerGridIndices M,
      (∫ y in fejerGridBall M x j, w y
        ∂AddCircle.haarAddCircle) ≤ localBound := by
    intro j hj
    have hsubset := fejerGridBall_subset_centeredArc hH hHM x j
    have hmono :
        (∫ y in fejerGridBall M x j, w y
          ∂AddCircle.haarAddCircle) ≤
        ∫ y in PrimePairEndpoints.centeredArc H (fejerGridCenter M x j), w y
          ∂AddCircle.haarAddCircle := by
      exact integral_mono_measure
        (Measure.restrict_mono hsubset le_rfl)
        (Filter.Eventually.of_forall hw0)
        hw.integrableOn
    exact hmono.trans (hlocal (fejerGridCenter M x j))
  calc
    ‖shiftedFejerConvolution w N c x‖ ≤
        ∫ y : UnitAddCircle,
          w y * ‖shiftedFejerSpatialKernel N c (x - y)‖
            ∂AddCircle.haarAddCircle := hnorm
    _ ≤ ∫ y : UnitAddCircle, G y
          ∂AddCircle.haarAddCircle := htoG
    _ = ∑ j ∈ fejerGridIndices M,
          (∫ y in fejerGridBall M x j, w y
            ∂AddCircle.haarAddCircle) * gridKernelMajorant N M j := hGIntegral
    _ ≤ ∑ j ∈ fejerGridIndices M,
          localBound * gridKernelMajorant N M j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hcell j hj)
        (gridKernelMajorant_nonneg N M j)
    _ = localBound * ∑ j ∈ fejerGridIndices M,
          gridKernelMajorant N M j := by rw [Finset.mul_sum]

/-- The exact open bridge is discharged with the explicit absolute constant
`28`. The real translated center is unchanged, normalized Haar is literal,
and all endpoint/wraparound mass is retained in closed grid cells. -/
theorem arcMassControlsShiftedFejerConvolution_proved :
    ArcMassControlsShiftedFejerConvolution := by
  refine ⟨28, by norm_num, ?_⟩
  intro w H h₀ localBound hw hw0 hH hlocal0 hlocal x
  let M : ℕ := ⌈H⌉₊
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hM : 0 < M := Nat.ceil_pos.mpr hHpos
  have hHM : H ≤ (M : ℝ) := Nat.le_ceil H
  have horder : translatedFejerOrder H = 2 * M + 2 := by
    rfl
  have hgrid := norm_shiftedFejerConvolution_le_grid_sum
    hw hw0 hHpos hHM hM (by omega : 0 < 2 * M + 2)
      (integerFrequencyCenter h₀) hlocal0 hlocal x
  rw [horder]
  calc
    ‖shiftedFejerConvolution w (2 * M + 2)
        (integerFrequencyCenter h₀) x‖ ≤
      localBound *
        ∑ j ∈ fejerGridIndices M,
          gridKernelMajorant (2 * M + 2) M j := hgrid
    _ ≤ localBound * (14 * (M : ℝ)) := by
      gcongr
      exact sum_gridKernelMajorant_translatedOrder_le hM
    _ ≤ 28 * H * localBound := by
      have hceil : (M : ℝ) < H + 1 := Nat.ceil_lt_add_one hHpos.le
      have hMle : (M : ℝ) ≤ 2 * H := by linarith
      nlinarith

/-- Consequently the report-level positive-measure large-sieve endpoint is
unconditional at the harmonic layer. -/
theorem exists_positiveMeasureFejerLocalFourierConstant :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (w : UnitAddCircle → ℝ)
        (H h₀ totalBound localBound : ℝ),
        Integrable w AddCircle.haarAddCircle →
        (∀ x, 0 ≤ w x) →
        1 ≤ H → 0 ≤ totalBound → 0 ≤ localBound →
        (∫ x : UnitAddCircle, w x ∂AddCircle.haarAddCircle) ≤ totalBound →
        (∀ center : UnitAddCircle,
          (∫ x in PrimePairEndpoints.centeredArc H center, w x
            ∂AddCircle.haarAddCircle) ≤ localBound) →
        (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
          ‖circleCoefficient w h‖ ^ 2) ≤
            C₀ * H * totalBound * localBound :=
  exists_positiveMeasureFejerLocalFourierConstant_of_arcMassControl
    arcMassControlsShiftedFejerConvolution_proved

end

end MAPHarmonicEndpoint
