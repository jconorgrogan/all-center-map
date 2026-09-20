import GuthMaynardJIterationPoisson

/-!
# Quantitative Poisson tails and Tonelli weld for Guth--Maynard Lemma 9.2

This module formalizes the quantitative passage in TeX 1609--1635.  It gives
an explicit shifted-lattice tail bound for a Fourier transform with a named
Schwartz decay seminorm, a uniform `T^-100` specialization with the exact
cutoff budget exposed, a Tonelli-safe summable majorant theorem, and a
countable termwise weld into the affine smoothing proved in
`GuthMaynardJIterationPoisson`.

The scale `A` is left explicit so the source specialization can use
`A = M₂/T`; the shift `y` is bounded uniformly by `Y`.  No change is made to
the corrected absolute Fourier dilation or to the forced `M₃` affine
frequency in the preceding module.
-/

open scoped BigOperators Real

noncomputable section
namespace GuthMaynardJIteration

def integerQuadraticEnvelope (j : ℤ) : ℝ :=
  if j = 0 then 1 else |(j : ℝ)| ^ (-2 : ℝ)

theorem summable_integerQuadraticEnvelope :
    Summable integerQuadraticEnvelope := by
  have hbase : Summable (fun j : ℤ => |(j : ℝ)| ^ (-2 : ℝ)) :=
    Real.summable_abs_int_rpow (by norm_num)
  have hsingle : Summable (fun j : ℤ => if j = 0 then (1 : ℝ) else 0) := by
    refine (hasSum_single (f := fun j : ℤ => if j = 0 then (1 : ℝ) else 0) 0 ?_).summable
    intro j hj
    simp [hj]
  apply (hbase.add hsingle).congr
  intro j
  by_cases hj : j = 0
  · subst j
    simp [integerQuadraticEnvelope, Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0)]
  · simp [integerQuadraticEnvelope, hj]

def scaledShiftedQuadraticWeight (A y : ℝ) (j : ℤ) : ℝ :=
  1 / (1 + |((j : ℝ) - y) / A|) ^ 2

theorem scaledShiftedQuadraticWeight_le_envelope
    {A : ℝ} (hA : 0 < A) (y : ℝ) (j : ℤ) :
    scaledShiftedQuadraticWeight A y j ≤
      (1 + |y| / A) ^ 2 * max 1 (A ^ 2) * integerQuadraticEnvelope j := by
  by_cases hj : j = 0
  · subst j
    simp only [scaledShiftedQuadraticWeight, Int.cast_zero, zero_sub,
      integerQuadraticEnvelope, if_pos]
    have hden : 1 ≤ (1 + |-y / A|) ^ 2 := by
      nlinarith [abs_nonneg (-y / A)]
    have hleft : 1 / (1 + |-y / A|) ^ 2 ≤ 1 := by
      exact (div_le_one (by positivity)).2 hden
    have hyfac : 1 ≤ (1 + |y| / A) ^ 2 := by
      have : 0 ≤ |y| / A := div_nonneg (abs_nonneg _) hA.le
      nlinarith
    have hmax : 1 ≤ max 1 (A ^ 2) := le_max_left _ _
    nlinarith [mul_nonneg (sq_nonneg (1 + |y| / A))
      (le_trans (sq_nonneg A) (le_max_right 1 (A ^ 2)))]
  · have hjabs : 0 < |(j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
    let d : ℝ := |((j : ℝ) - y) / A|
    let e : ℝ := |(j : ℝ)| / A
    let v : ℝ := |y| / A
    have hd : 0 ≤ d := abs_nonneg _
    have he : 0 ≤ e := div_nonneg (abs_nonneg _) hA.le
    have hv : 0 ≤ v := div_nonneg (abs_nonneg _) hA.le
    have htri : e ≤ d + v := by
      dsimp only [d, e, v]
      rw [abs_div, abs_of_pos hA]
      rw [← add_div]
      apply (div_le_div_iff_of_pos_right hA).2
      have h := abs_add_le ((j : ℝ) - y) y
      simpa only [sub_add_cancel] using h
    have hprod : 1 + e ≤ (1 + d) * (1 + v) := by nlinarith [mul_nonneg hd hv]
    have hfirst : 1 / (1 + d) ^ 2 ≤ (1 + v) ^ 2 / (1 + e) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity : 0 < (1 + d) ^ 2)
        (by positivity : 0 < (1 + e) ^ 2)]
      nlinarith [sq_nonneg ((1 + d) * (1 + v) - (1 + e))]
    have hsecond : 1 / (1 + e) ^ 2 ≤ A ^ 2 / |(j : ℝ)| ^ 2 := by
      dsimp only [e]
      rw [div_le_div_iff₀ (by positivity : 0 < (1 + |(j : ℝ)| / A) ^ 2)
        (sq_pos_of_pos hjabs)]
      have hAe : |(j : ℝ)| ≤ A * (1 + |(j : ℝ)| / A) := by
        field_simp [hA.ne']
        linarith
      nlinarith [sq_nonneg (A * (1 + |(j : ℝ)| / A) - |(j : ℝ)|)]
    have hcombine : 1 / (1 + d) ^ 2 ≤
        (1 + v) ^ 2 * (A ^ 2 / |(j : ℝ)| ^ 2) := by
      calc
        _ ≤ (1 + v) ^ 2 / (1 + e) ^ 2 := hfirst
        _ = (1 + v) ^ 2 * (1 / (1 + e) ^ 2) := by ring
        _ ≤ (1 + v) ^ 2 * (A ^ 2 / |(j : ℝ)| ^ 2) := by
          gcongr
    rw [scaledShiftedQuadraticWeight]
    change 1 / (1 + d) ^ 2 ≤ _
    rw [integerQuadraticEnvelope, if_neg hj, Real.rpow_neg (abs_nonneg _)]
    rw [Real.rpow_two, inv_eq_one_div]
    calc
      _ ≤ (1 + v) ^ 2 * (A ^ 2 / |(j : ℝ)| ^ 2) := hcombine
      _ ≤ (1 + v) ^ 2 * max 1 (A ^ 2) * (1 / |(j : ℝ)| ^ 2) := by
        have hfac : A ^ 2 ≤ max 1 (A ^ 2) := le_max_right _ _
        have hnonneg : 0 ≤ (1 + v) ^ 2 := sq_nonneg _
        have hinvnonneg : 0 ≤ (1 / |(j : ℝ)| ^ 2) := by positivity
        calc
          (1 + v) ^ 2 * (A ^ 2 / |(j : ℝ)| ^ 2) =
              (1 + v) ^ 2 * A ^ 2 * (1 / |(j : ℝ)| ^ 2) := by ring
          _ ≤ (1 + v) ^ 2 * max 1 (A ^ 2) * (1 / |(j : ℝ)| ^ 2) := by
            gcongr
      _ = _ := by rfl

def integerQuadraticMass : ℝ :=
  ∑' j : ℤ, integerQuadraticEnvelope j

theorem tsum_scaledShiftedQuadraticWeight_le
    {A : ℝ} (hA : 0 < A) (y : ℝ) :
    (∑' j : ℤ, scaledShiftedQuadraticWeight A y j) ≤
      (1 + |y| / A) ^ 2 * max 1 (A ^ 2) * integerQuadraticMass := by
  let coeff : ℝ := (1 + |y| / A) ^ 2 * max 1 (A ^ 2)
  have hcoeff : 0 ≤ coeff := mul_nonneg (sq_nonneg _) (le_trans (sq_nonneg _) (le_max_right _ _))
  have henv0 : ∀ j, 0 ≤ integerQuadraticEnvelope j := by
    intro j
    rw [integerQuadraticEnvelope]
    split_ifs
    · norm_num
    · positivity
  have hmajor : ∀ j, scaledShiftedQuadraticWeight A y j ≤
      coeff * integerQuadraticEnvelope j := by
    intro j
    exact scaledShiftedQuadraticWeight_le_envelope hA y j
  have hmajor_sum : Summable (fun j : ℤ => coeff * integerQuadraticEnvelope j) :=
    summable_integerQuadraticEnvelope.mul_left coeff
  have hweight0 : ∀ j, 0 ≤ scaledShiftedQuadraticWeight A y j := by
    intro j
    unfold scaledShiftedQuadraticWeight
    positivity
  have hweight : Summable (scaledShiftedQuadraticWeight A y) :=
    hmajor_sum.of_nonneg_of_le hweight0 hmajor
  calc
    (∑' j : ℤ, scaledShiftedQuadraticWeight A y j) ≤
        ∑' j : ℤ, coeff * integerQuadraticEnvelope j :=
      hweight.tsum_le_tsum hmajor hmajor_sum
    _ = coeff * integerQuadraticMass := by
      rw [integerQuadraticMass, summable_integerQuadraticEnvelope.tsum_mul_left]
    _ = _ := by rfl

def scaledShiftedDecayTail (q : ℕ) (A B y : ℝ) (j : ℤ) : ℝ :=
  if B ≤ |((j : ℝ) - y) / A| then
    1 / (1 + |((j : ℝ) - y) / A|) ^ (q + 2)
  else 0

theorem scaledShiftedDecayTail_le_quadratic
    (q : ℕ) {A B : ℝ} (hB : 0 < B) (y : ℝ) (j : ℤ) :
    scaledShiftedDecayTail q A B y j ≤
      (1 / B ^ q) * scaledShiftedQuadraticWeight A y j := by
  rw [scaledShiftedDecayTail]
  split_ifs with hj
  · let d : ℝ := |((j : ℝ) - y) / A|
    have hd : 0 ≤ d := abs_nonneg _
    have hBd : B ≤ 1 + d := by dsimp only [d]; linarith
    have hpow : B ^ q ≤ (1 + d) ^ q :=
      pow_le_pow_left₀ hB.le hBd q
    change 1 / (1 + d) ^ (q + 2) ≤
      (1 / B ^ q) * (1 / (1 + d) ^ 2)
    rw [pow_add]
    have hden : B ^ q * (1 + d) ^ 2 ≤
        (1 + d) ^ q * (1 + d) ^ 2 := by gcongr
    calc
      1 / ((1 + d) ^ q * (1 + d) ^ 2) ≤
          1 / (B ^ q * (1 + d) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) hden
      _ = (1 / B ^ q) * (1 / (1 + d) ^ 2) := by field_simp
  · have hquad : 0 ≤ scaledShiftedQuadraticWeight A y j := by
      unfold scaledShiftedQuadraticWeight
      positivity
    exact mul_nonneg (by positivity) hquad

theorem tsum_scaledShiftedDecayTail_le
    (q : ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (y : ℝ) :
    (∑' j : ℤ, scaledShiftedDecayTail q A B y j) ≤
      (1 / B ^ q) *
        ((1 + |y| / A) ^ 2 * max 1 (A ^ 2) * integerQuadraticMass) := by
  have hquad : Summable (scaledShiftedQuadraticWeight A y) := by
    let coeff : ℝ := (1 + |y| / A) ^ 2 * max 1 (A ^ 2)
    have hmajor_sum : Summable (fun j : ℤ => coeff * integerQuadraticEnvelope j) :=
      summable_integerQuadraticEnvelope.mul_left coeff
    apply hmajor_sum.of_nonneg_of_le
    · intro j
      unfold scaledShiftedQuadraticWeight
      positivity
    · intro j
      exact scaledShiftedQuadraticWeight_le_envelope hA y j
  have htail : Summable (scaledShiftedDecayTail q A B y) := by
    apply (hquad.mul_left (1 / B ^ q)).of_nonneg_of_le
    · intro j
      rw [scaledShiftedDecayTail]
      split_ifs
      · positivity
      · exact le_rfl
    · intro j
      exact scaledShiftedDecayTail_le_quadratic q hB y j
  calc
    (∑' j : ℤ, scaledShiftedDecayTail q A B y j) ≤
        ∑' j : ℤ, (1 / B ^ q) * scaledShiftedQuadraticWeight A y j :=
      htail.tsum_le_tsum
        (scaledShiftedDecayTail_le_quadratic q hB y) (hquad.mul_left _)
    _ = (1 / B ^ q) *
        (∑' j : ℤ, scaledShiftedQuadraticWeight A y j) := by
      rw [hquad.tsum_mul_left]
    _ ≤ (1 / B ^ q) *
        ((1 + |y| / A) ^ 2 * max 1 (A ^ 2) * integerQuadraticMass) := by
      gcongr
      exact tsum_scaledShiftedQuadraticWeight_le hA y

theorem summable_scaledShiftedDecayTail
    (q : ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (y : ℝ) :
    Summable (scaledShiftedDecayTail q A B y) := by
  have hquad : Summable (scaledShiftedQuadraticWeight A y) := by
    let coeff : ℝ := (1 + |y| / A) ^ 2 * max 1 (A ^ 2)
    have hmajor_sum : Summable (fun j : ℤ => coeff * integerQuadraticEnvelope j) :=
      summable_integerQuadraticEnvelope.mul_left coeff
    apply hmajor_sum.of_nonneg_of_le
    · intro j
      unfold scaledShiftedQuadraticWeight
      positivity
    · intro j
      exact scaledShiftedQuadraticWeight_le_envelope hA y j
  apply (hquad.mul_left (1 / B ^ q)).of_nonneg_of_le
  · intro j
    rw [scaledShiftedDecayTail]
    split_ifs
    · positivity
    · exact le_rfl
  · intro j
    exact scaledShiftedDecayTail_le_quadratic q hB y j

def schwartzIntegerTail (F : ℝ → ℂ) (A B y : ℝ) (j : ℤ) : ℂ :=
  if B ≤ |((j : ℝ) - y) / A| then F (((j : ℝ) - y) / A) else 0

theorem norm_tsum_schwartzIntegerTail_le
    (F : ℝ → ℂ) (q : ℕ) {K A B : ℝ}
    (hK : 0 ≤ K) (hA : 0 < A) (hB : 0 < B)
    (hdecay : ∀ xi, ‖F xi‖ ≤ K / (1 + |xi|) ^ (q + 2)) (y : ℝ) :
    ‖∑' j : ℤ, schwartzIntegerTail F A B y j‖ ≤
      K * ((1 / B ^ q) *
        ((1 + |y| / A) ^ 2 * max 1 (A ^ 2) * integerQuadraticMass)) := by
  have htail := summable_scaledShiftedDecayTail q hA hB y
  have hpoint : ∀ j, ‖schwartzIntegerTail F A B y j‖ ≤
      K * scaledShiftedDecayTail q A B y j := by
    intro j
    rw [schwartzIntegerTail, scaledShiftedDecayTail]
    split_ifs with hj
    · simpa only [div_eq_mul_inv, one_mul] using
        hdecay (((j : ℝ) - y) / A)
    · simp
  have hmajor : Summable (fun j : ℤ => K * scaledShiftedDecayTail q A B y j) :=
    htail.mul_left K
  have hnorms : Summable (fun j : ℤ => ‖schwartzIntegerTail F A B y j‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  calc
    ‖∑' j : ℤ, schwartzIntegerTail F A B y j‖ ≤
        ∑' j : ℤ, ‖schwartzIntegerTail F A B y j‖ :=
      norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' j : ℤ, K * scaledShiftedDecayTail q A B y j :=
      hnorms.tsum_le_tsum hpoint hmajor
    _ = K * (∑' j : ℤ, scaledShiftedDecayTail q A B y j) := by
      rw [htail.tsum_mul_left]
    _ ≤ K * ((1 / B ^ q) *
        ((1 + |y| / A) ^ 2 * max 1 (A ^ 2) * integerQuadraticMass)) := by
      gcongr
      exact tsum_scaledShiftedDecayTail_le q hA hB y

theorem norm_tsum_schwartzIntegerTail_le_uniform
    (F : ℝ → ℂ) (q : ℕ) {K A B Y : ℝ}
    (hK : 0 ≤ K) (hA : 0 < A) (hB : 0 < B) (hY : 0 ≤ Y)
    (hdecay : ∀ xi, ‖F xi‖ ≤ K / (1 + |xi|) ^ (q + 2))
    {y : ℝ} (hy : |y| ≤ Y) :
    ‖∑' j : ℤ, schwartzIntegerTail F A B y j‖ ≤
      K * ((1 / B ^ q) *
        ((1 + Y / A) ^ 2 * max 1 (A ^ 2) * integerQuadraticMass)) := by
  refine (norm_tsum_schwartzIntegerTail_le F q hK hA hB hdecay y).trans ?_
  have hdiv : |y| / A ≤ Y / A := (div_le_div_iff_of_pos_right hA).2 hy
  have hsq : (1 + |y| / A) ^ 2 ≤ (1 + Y / A) ^ 2 := by
    nlinarith [div_nonneg hY hA.le, div_nonneg (abs_nonneg y) hA.le]
  have hmass : 0 ≤ integerQuadraticMass := by
    unfold integerQuadraticMass
    exact tsum_nonneg fun j => by
      rw [integerQuadraticEnvelope]
      split_ifs <;> positivity
  gcongr

/-- Explicit `O(T^-100)` specialization.  The budget hypothesis states the
exact polynomial domination required of the chosen Schwartz seminorm and
cutoff; it is uniform for every `|y| ≤ Y`. -/
theorem norm_tsum_schwartzIntegerTail_le_time_neg100
    (F : ℝ → ℂ) (q : ℕ) {K A B Y C T : ℝ}
    (hK : 0 ≤ K) (hA : 0 < A) (hB : 0 < B) (hY : 0 ≤ Y)
    (hT : 0 < T)
    (hdecay : ∀ xi, ‖F xi‖ ≤ K / (1 + |xi|) ^ (q + 2))
    (hbudget : K *
      ((1 + Y / A) ^ 2 * max 1 (A ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        C * B ^ q)
    {y : ℝ} (hy : |y| ≤ Y) :
    ‖∑' j : ℤ, schwartzIntegerTail F A B y j‖ ≤ C / T ^ 100 := by
  refine (norm_tsum_schwartzIntegerTail_le_uniform
    F q hK hA hB hY hdecay hy).trans ?_
  have hBq : 0 < B ^ q := pow_pos hB _
  have hT100 : 0 < T ^ 100 := pow_pos hT _
  calc
    K * ((1 / B ^ q) *
        ((1 + Y / A) ^ 2 * max 1 (A ^ 2) * integerQuadraticMass)) =
        (K * ((1 + Y / A) ^ 2 * max 1 (A ^ 2) * integerQuadraticMass)) /
          B ^ q := by ring
    _ ≤ (C * B ^ q / T ^ 100) / B ^ q := by
      gcongr
      exact (le_div_iff₀ hT100).2 (by simpa [mul_assoc] using hbudget)
    _ = C / T ^ 100 := by field_simp [hBq.ne', hT100.ne']

/-- Exact conversion of the retained Poisson-window condition into the
affine `u'`-ball.  The radius keeps the source ratio `M₂/m₂'`; replacing it
by an unnamed constant is a later dyadic-range bound. -/
theorem poissonLocalization_iff_mem_affineBall
    {m2p M2 T : ℝ} (hm2p : 0 < m2p) (hT : 0 < T)
    (m2 j u u' B : ℝ) :
    |j - m2p * u' + m2 * u| ≤ (M2 / T) * B ↔
      u' ∈ Metric.closedBall ((m2 * u + j) / m2p)
        ((M2 / m2p) * B / T) := by
  rw [Metric.mem_closedBall, Real.dist_eq]
  have hid : u' - (m2 * u + j) / m2p =
      -(j - m2p * u' + m2 * u) / m2p := by
    field_simp [hm2p.ne']
    ring
  rw [hid, abs_div, abs_neg, abs_of_pos hm2p]
  rw [div_le_iff₀ hm2p]
  field_simp [hm2p.ne', hT.ne']

open MeasureTheory

/-- A Tonelli-safe real majorant: summable scalar weights times one
integrable nonnegative function justify the sum-integral exchange and bound
the exchanged expression. -/
theorem integral_tsum_of_summable_majorant
    {alpha iota : Type*} [MeasurableSpace alpha] [Countable iota]
    (mu : Measure alpha) (F : iota → alpha → ℝ) (c : iota → ℝ) (g : alpha → ℝ)
    (hc : Summable c)
    (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g mu)
    (hF0 : ∀ i x, 0 ≤ F i x)
    (hFmeas : ∀ i, AEStronglyMeasurable (F i) mu)
    (hmajor : ∀ i x, F i x ≤ c i * g x) :
    (∫ x, ∑' i, F i x ∂mu) = ∑' i, ∫ x, F i x ∂mu ∧
      (∑' i, ∫ x, F i x ∂mu) ≤ (∑' i, c i) * ∫ x, g x ∂mu := by
  have hFi : ∀ i, Integrable (F i) mu := by
    intro i
    apply (hg.const_mul (c i)).mono' (hFmeas i)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 i x)]
    exact hmajor i x
  have hibound : ∀ i, (∫ x, ‖F i x‖ ∂mu) ≤ c i * ∫ x, g x ∂mu := by
    intro i
    rw [← integral_const_mul]
    apply integral_mono (hFi i).norm (hg.const_mul (c i))
    intro x
    change ‖F i x‖ ≤ c i * g x
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 i x)]
    exact hmajor i x
  have hIg : 0 ≤ ∫ x, g x ∂mu := integral_nonneg hg0
  have hmajorSummable : Summable (fun i => c i * ∫ x, g x ∂mu) := hc.mul_right _
  have hnormSummable : Summable (fun i => ∫ x, ‖F i x‖ ∂mu) :=
    hmajorSummable.of_nonneg_of_le
      (fun i => integral_nonneg fun x => norm_nonneg (F i x)) hibound
  constructor
  · exact (integral_tsum_of_summable_integral_norm hFi hnormSummable).symm
  · calc
      (∑' i, ∫ x, F i x ∂mu) = ∑' i, ∫ x, ‖F i x‖ ∂mu := by
        apply tsum_congr
        intro i
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 i x)]
      _ ≤ ∑' i, c i * ∫ x, g x ∂mu :=
        hnormSummable.tsum_le_tsum hibound hmajorSummable
      _ = (∑' i, c i) * ∫ x, g x ∂mu := by
        rw [hc.tsum_mul_right]

/-- Countable termwise weld from the localized Poisson kernel to the affine
smoothing already promoted from TeX 1637--1645. -/
theorem tsum_source_localized_integral_le_affineSmoothing
    {iota : Type*} [Countable iota] {C T : ℝ} (hT : 0 < T)
    (center : iota → ℝ) (psi f : ℝ → ℝ)
    (hf0 : ∀ u, 0 ≤ f u) (hpsi0 : ∀ z, 0 ≤ psi z)
    (hpsi_major : ∀ z, |z| ≤ C → 1 ≤ psi z)
    (hlocal : ∀ i, IntegrableOn (fun u => T * f u)
      (Metric.closedBall (center i) (C / T)))
    (hsmooth : ∀ i, Integrable
      (fun u => T * psi (T * (center i - u)) * f u))
    (hsum : Summable (fun i => affineSmoothing T psi f (center i))) :
    (∑' i, ∫ u in Metric.closedBall (center i) (C / T), T * f u) ≤
      ∑' i, affineSmoothing T psi f (center i) := by
  have hterm : ∀ i, (∫ u in Metric.closedBall (center i) (C / T), T * f u) ≤
      affineSmoothing T psi f (center i) := by
    intro i
    exact source_localized_integral_le_affineSmoothing hT psi f hf0 hpsi0
      hpsi_major (hlocal i) (hsmooth i)
  have hleft0 : ∀ i, 0 ≤
      ∫ u in Metric.closedBall (center i) (C / T), T * f u := by
    intro i
    exact integral_nonneg fun u => mul_nonneg hT.le (hf0 u)
  have hleft : Summable
      (fun i => ∫ u in Metric.closedBall (center i) (C / T), T * f u) :=
    hsum.of_nonneg_of_le hleft0 hterm
  exact hleft.tsum_le_tsum hterm hsum

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.summable_integerQuadraticEnvelope
#print axioms GuthMaynardJIteration.scaledShiftedQuadraticWeight_le_envelope
#print axioms GuthMaynardJIteration.tsum_scaledShiftedQuadraticWeight_le
#print axioms GuthMaynardJIteration.scaledShiftedDecayTail_le_quadratic
#print axioms GuthMaynardJIteration.tsum_scaledShiftedDecayTail_le
#print axioms GuthMaynardJIteration.summable_scaledShiftedDecayTail
#print axioms GuthMaynardJIteration.norm_tsum_schwartzIntegerTail_le
#print axioms GuthMaynardJIteration.norm_tsum_schwartzIntegerTail_le_uniform
#print axioms GuthMaynardJIteration.norm_tsum_schwartzIntegerTail_le_time_neg100
#print axioms GuthMaynardJIteration.poissonLocalization_iff_mem_affineBall
#print axioms GuthMaynardJIteration.integral_tsum_of_summable_majorant
#print axioms GuthMaynardJIteration.tsum_source_localized_integral_le_affineSmoothing
