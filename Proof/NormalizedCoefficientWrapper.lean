import MixedMeanFrontend

/-!
# Square-root-normalized paper wrapper for the MAP mixed mean

`MixedMeanFrontend` deliberately accepts raw coefficient functions.  The
manuscript instead uses `a(n) n^{-1/2-it}`.  This module supplies that missing
paper-facing instantiation and proves, on the literal dyadic tuple box, the
coefficient majorant with an explicit `(M*N)⁻¹` factor.
-/

noncomputable section

namespace MAPNormalizedWrapper

open MeasureTheory DeterminantCountWeld MixedMeanFrontend MixedMellinCert

/-- Insert the manuscript's real square-root denominator into a complex
coefficient. -/
def sqrtNormalizedCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n / (Real.sqrt (n : ℝ) : ℂ)

/-- The manuscript's short polynomial `sum beta(m) m^{-1/2-it}`. -/
def paperShortFactor (M : ℕ) (β : ℕ → ℂ) (t : ℝ) : ℂ :=
  shortFactor M (sqrtNormalizedCoeff β) t

/-- The manuscript's long polynomial `sum g(n) n^{-1/2-it}`. -/
def paperLongFactor (N : ℕ) (g : ℕ → ℂ) (t : ℝ) : ℂ :=
  longFactor N (sqrtNormalizedCoeff g) t

/-- The literal mixed mean with both paper coefficients normalized. -/
def paperLiteralMixedMean (M N : ℕ) (β g : ℕ → ℂ)
    (t₀ T U : ℝ) : ℂ :=
  literalMixedMean M N (sqrtNormalizedCoeff β)
    (sqrtNormalizedCoeff g) t₀ T U

/-- The exact tuple coefficient produced by expanding the paper-facing mixed
mean. -/
def paperTupleCoefficient (β g : ℕ → ℂ) (q : LiteralTuple) : ℂ :=
  tupleCoefficient (sqrtNormalizedCoeff β) (sqrtNormalizedCoeff g) q

/-- The existing exact finite expansion, instantiated with the manuscript's
square-root-normalized coefficients. -/
theorem paperLiteralMixedMean_eq_integral_tupleSum
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ T U : ℝ) :
    paperLiteralMixedMean M N β g t₀ T U =
      ∫ t in (t₀ - T / 2)..(t₀ + T / 2),
        ∫ u in (-2 * U)..(2 * U),
          ∑ q ∈ dyadicTupleBox M N,
            tupleTerm (sqrtNormalizedCoeff β)
              (sqrtNormalizedCoeff g) q t u := by
  exact literalMixedMean_eq_integral_tupleSum
    M N (sqrtNormalizedCoeff β) (sqrtNormalizedCoeff g) t₀ T U

/-- The existing two-clock frequency identity, instantiated with the paper's
normalized coefficient. -/
theorem paperTupleTerm_frequency_form
    (β g : ℕ → ℂ) (q : LiteralTuple) (t u : ℝ) :
    tupleTerm (sqrtNormalizedCoeff β) (sqrtNormalizedCoeff g) q t u =
      paperTupleCoefficient β g q *
        Complex.exp
          (((t * jointFrequency q + u * shortFrequency q : ℝ) : ℂ) *
            Complex.I) := by
  simpa [paperTupleCoefficient] using
    tupleTerm_frequency_form (sqrtNormalizedCoeff β)
      (sqrtNormalizedCoeff g) q t u

theorem paperShortFactor_eq_sum (M : ℕ) (β : ℕ → ℂ) (t : ℝ) :
    paperShortFactor M β t =
      ∑ m ∈ dyadic M,
        (β m / (Real.sqrt (m : ℝ) : ℂ)) * mellinPhase m t := by
  rfl

theorem paperLongFactor_eq_sum (N : ℕ) (g : ℕ → ℂ) (t : ℝ) :
    paperLongFactor N g t =
      ∑ n ∈ dyadic N,
        (g n / (Real.sqrt (n : ℝ) : ℂ)) * mellinPhase n t := by
  rfl

theorem norm_sqrtNormalizedCoeff (a : ℕ → ℂ) (n : ℕ) :
    ‖sqrtNormalizedCoeff a n‖ = ‖a n‖ / Real.sqrt (n : ℝ) := by
  simp [sqrtNormalizedCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

theorem sqrt_base_le_sqrt_of_mem_dyadic
    {M n : ℕ} (hn : n ∈ dyadic M) :
    Real.sqrt (M : ℝ) ≤ Real.sqrt (n : ℝ) := by
  apply Real.sqrt_le_sqrt
  simp only [dyadic, Finset.mem_Ioc] at hn
  exact_mod_cast hn.1.le

/-- A pointwise raw coefficient envelope loses only `sqrt M` after the
paper normalization on `(M,2M]`. -/
theorem norm_sqrtNormalizedCoeff_le_base
    {M n : ℕ} {a : ℕ → ℂ} {A : ℝ}
    (hM : 0 < M) (hn : n ∈ dyadic M) (ha : ‖a n‖ ≤ A) :
    ‖sqrtNormalizedCoeff a n‖ ≤ A / Real.sqrt (M : ℝ) := by
  rw [norm_sqrtNormalizedCoeff]
  have hA : 0 ≤ A := (norm_nonneg (a n)).trans ha
  exact div_le_div₀ hA ha (Real.sqrt_pos.2 (by exact_mod_cast hM))
    (sqrt_base_le_sqrt_of_mem_dyadic hn)

/-- The genuine analytic input at the coefficient boundary.  This is exactly
the pointwise hypothesis in the manuscript's mixed-mean lemma. -/
def PaperCoefficientBounds
    (M N a k : ℕ) (β g : ℕ → ℂ) : Prop :=
  (∀ m ∈ dyadic M,
      ‖β m‖ ≤ Real.log (2 * (m : ℝ)) ^ a) ∧
  (∀ n ∈ dyadic N,
      ‖g n‖ ≤ (tauAF k n : ℝ) * Real.log (2 * (n : ℝ)) ^ a)

/-- The literal product of the four manuscript coefficient envelopes before
the harmless common-log majorization. -/
def pointwiseTupleEnvelope (a k : ℕ) (q : LiteralTuple) : ℝ :=
  ((tauAF k q.2.1 : ℝ) * Real.log (2 * (q.2.1 : ℝ)) ^ a) *
    ((tauAF k q.2.2 : ℝ) * Real.log (2 * (q.2.2 : ℝ)) ^ a) *
    (Real.log (2 * (q.1.1 : ℝ)) ^ a *
      Real.log (2 * (q.1.2 : ℝ)) ^ a)

/-- The common logarithmic envelope displayed after (2.2) in the manuscript,
kept in a four-factor form that exposes where each power comes from. -/
def commonLogTupleEnvelope
    (M N a k : ℕ) (q : LiteralTuple) : ℝ :=
  let L := Real.log (2 * (M : ℝ) * (N : ℝ))
  ((tauAF k q.2.1 : ℝ) * L ^ a) *
    ((tauAF k q.2.2 : ℝ) * L ^ a) * (L ^ a * L ^ a)

theorem commonLogTupleEnvelope_eq_logPow
    (M N a k : ℕ) (q : LiteralTuple) :
    commonLogTupleEnvelope M N a k q =
      ((tauAF k q.2.1 : ℝ) * (tauAF k q.2.2 : ℝ)) *
        Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) := by
  unfold commonLogTupleEnvelope
  rw [show 4 * a = a * 4 by omega, pow_mul]
  ring

theorem log_two_index_le_common_of_mem_short
    {M N m : ℕ} (hN : 2 ≤ N) (hm : m ∈ dyadic M) :
    Real.log (2 * (m : ℝ)) ≤
      Real.log (2 * (M : ℝ) * (N : ℝ)) := by
  have hmBox := hm
  simp only [dyadic, Finset.mem_Ioc] at hmBox
  have hnat : 2 * m ≤ 2 * M * N := by
    calc
      2 * m ≤ 2 * (2 * M) := Nat.mul_le_mul_left 2 hmBox.2
      _ = (2 * M) * 2 := by ring
      _ ≤ (2 * M) * N := Nat.mul_le_mul_left (2 * M) hN
      _ = 2 * M * N := by ring
  apply Real.strictMonoOn_log.monotoneOn
  · show 0 < 2 * (m : ℝ)
    have hmpos : 0 < m := by omega
    positivity
  · have hM : 0 < M := by omega
    show 0 < 2 * (M : ℝ) * (N : ℝ)
    positivity
  · exact_mod_cast hnat

theorem log_two_index_le_common_of_mem_long
    {M N n : ℕ} (hM : 2 ≤ M) (hn : n ∈ dyadic N) :
    Real.log (2 * (n : ℝ)) ≤
      Real.log (2 * (M : ℝ) * (N : ℝ)) := by
  have hnBox := hn
  simp only [dyadic, Finset.mem_Ioc] at hnBox
  have hnat : 2 * n ≤ 2 * M * N := by
    calc
      2 * n ≤ 2 * (2 * N) := Nat.mul_le_mul_left 2 hnBox.2
      _ = (2 * N) * 2 := by ring
      _ ≤ (2 * N) * M := Nat.mul_le_mul_left (2 * N) hM
      _ = 2 * M * N := by ring
  apply Real.strictMonoOn_log.monotoneOn
  · show 0 < 2 * (n : ℝ)
    have hnpos : 0 < n := by omega
    positivity
  · have hN : 0 < N := by omega
    show 0 < 2 * (M : ℝ) * (N : ℝ)
    positivity
  · exact_mod_cast hnat

theorem pointwiseTupleEnvelope_le_commonLog
    {M N a k : ℕ} {q : LiteralTuple}
    (hM : 2 ≤ M) (hN : 2 ≤ N) (hq : q ∈ dyadicTupleBox M N) :
    pointwiseTupleEnvelope a k q ≤ commonLogTupleEnvelope M N a k q := by
  rcases q with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  simp [dyadicTupleBox] at hq
  rcases hq with ⟨⟨hm₁, hm₂⟩, hn₁, hn₂⟩
  have hm₁log := log_two_index_le_common_of_mem_short hN hm₁
  have hm₂log := log_two_index_le_common_of_mem_short hN hm₂
  have hn₁log := log_two_index_le_common_of_mem_long hM hn₁
  have hn₂log := log_two_index_le_common_of_mem_long hM hn₂
  have hm₁pos : 0 < m₁ := by
    simp only [dyadic, Finset.mem_Ioc] at hm₁
    omega
  have hm₂pos : 0 < m₂ := by
    simp only [dyadic, Finset.mem_Ioc] at hm₂
    omega
  have hn₁pos : 0 < n₁ := by
    simp only [dyadic, Finset.mem_Ioc] at hn₁
    omega
  have hn₂pos : 0 < n₂ := by
    simp only [dyadic, Finset.mem_Ioc] at hn₂
    omega
  have hm₁log0 : 0 ≤ Real.log (2 * (m₁ : ℝ)) := by
    apply Real.log_nonneg
    have h : 1 ≤ 2 * m₁ := by omega
    exact_mod_cast h
  have hm₂log0 : 0 ≤ Real.log (2 * (m₂ : ℝ)) := by
    apply Real.log_nonneg
    have h : 1 ≤ 2 * m₂ := by omega
    exact_mod_cast h
  have hn₁log0 : 0 ≤ Real.log (2 * (n₁ : ℝ)) := by
    apply Real.log_nonneg
    have h : 1 ≤ 2 * n₁ := by omega
    exact_mod_cast h
  have hn₂log0 : 0 ≤ Real.log (2 * (n₂ : ℝ)) := by
    apply Real.log_nonneg
    have h : 1 ≤ 2 * n₂ := by omega
    exact_mod_cast h
  have hcommonLog0 : 0 ≤ Real.log (2 * (M : ℝ) * (N : ℝ)) := by
    apply Real.log_nonneg
    have hpos : 0 < 2 * M * N := by positivity
    have h : 1 ≤ 2 * M * N := by omega
    exact_mod_cast h
  have hm₁pow : Real.log (2 * (m₁ : ℝ)) ^ a ≤
      Real.log (2 * (M : ℝ) * (N : ℝ)) ^ a :=
    pow_le_pow_left₀ hm₁log0 hm₁log a
  have hm₂pow : Real.log (2 * (m₂ : ℝ)) ^ a ≤
      Real.log (2 * (M : ℝ) * (N : ℝ)) ^ a :=
    pow_le_pow_left₀ hm₂log0 hm₂log a
  have hn₁pow : Real.log (2 * (n₁ : ℝ)) ^ a ≤
      Real.log (2 * (M : ℝ) * (N : ℝ)) ^ a :=
    pow_le_pow_left₀ hn₁log0 hn₁log a
  have hn₂pow : Real.log (2 * (n₂ : ℝ)) ^ a ≤
      Real.log (2 * (M : ℝ) * (N : ℝ)) ^ a :=
    pow_le_pow_left₀ hn₂log0 hn₂log a
  have hn₁weighted :
      (tauAF k n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) ^ a ≤
        (tauAF k n₁ : ℝ) * Real.log (2 * (M : ℝ) * (N : ℝ)) ^ a :=
    mul_le_mul_of_nonneg_left hn₁pow (by positivity)
  have hn₂weighted :
      (tauAF k n₂ : ℝ) * Real.log (2 * (n₂ : ℝ)) ^ a ≤
        (tauAF k n₂ : ℝ) * Real.log (2 * (M : ℝ) * (N : ℝ)) ^ a :=
    mul_le_mul_of_nonneg_left hn₂pow (by positivity)
  have hlong :
      ((tauAF k n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) ^ a) *
          ((tauAF k n₂ : ℝ) * Real.log (2 * (n₂ : ℝ)) ^ a) ≤
        ((tauAF k n₁ : ℝ) * Real.log (2 * (M : ℝ) * (N : ℝ)) ^ a) *
          ((tauAF k n₂ : ℝ) * Real.log (2 * (M : ℝ) * (N : ℝ)) ^ a) := by
    exact mul_le_mul hn₁weighted hn₂weighted (by positivity) (by positivity)
  have hshort :
      Real.log (2 * (m₁ : ℝ)) ^ a * Real.log (2 * (m₂ : ℝ)) ^ a ≤
        Real.log (2 * (M : ℝ) * (N : ℝ)) ^ a *
          Real.log (2 * (M : ℝ) * (N : ℝ)) ^ a := by
    exact mul_le_mul hm₁pow hm₂pow (by positivity) (by positivity)
  unfold pointwiseTupleEnvelope commonLogTupleEnvelope
  exact mul_le_mul hlong hshort (by positivity) (by positivity)

/-- Four square-root denominators extract the manuscript's `(M*N)⁻¹` before
any analytic coefficient estimate is used.  The comparison constant is one. -/
theorem norm_paperTupleCoefficient_le_raw
    {M N : ℕ} {β g : ℕ → ℂ} {q : LiteralTuple}
    (hM : 0 < M) (hN : 0 < N)
    (hq : q ∈ dyadicTupleBox M N) :
    ‖paperTupleCoefficient β g q‖ ≤
      ((M : ℝ) * (N : ℝ))⁻¹ *
        ((‖g q.2.1‖ * ‖g q.2.2‖) *
          (‖β q.1.1‖ * ‖β q.1.2‖)) := by
  rcases q with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  simp [dyadicTupleBox] at hq
  rcases hq with ⟨⟨hm₁, hm₂⟩, hn₁, hn₂⟩
  have hb₁ := norm_sqrtNormalizedCoeff_le_base hM hm₁ (le_refl ‖β m₁‖)
  have hb₂ := norm_sqrtNormalizedCoeff_le_base hM hm₂ (le_refl ‖β m₂‖)
  have hg₁ := norm_sqrtNormalizedCoeff_le_base hN hn₁ (le_refl ‖g n₁‖)
  have hg₂ := norm_sqrtNormalizedCoeff_le_base hN hn₂ (le_refl ‖g n₂‖)
  rw [paperTupleCoefficient, tupleCoefficient, norm_mul, norm_mul,
    norm_star, norm_mul, norm_star]
  calc
    ‖sqrtNormalizedCoeff g n₁‖ * ‖sqrtNormalizedCoeff g n₂‖ *
        (‖sqrtNormalizedCoeff β m₁‖ * ‖sqrtNormalizedCoeff β m₂‖) ≤
      (‖g n₁‖ / Real.sqrt (N : ℝ)) *
        (‖g n₂‖ / Real.sqrt (N : ℝ)) *
        ((‖β m₁‖ / Real.sqrt (M : ℝ)) *
          (‖β m₂‖ / Real.sqrt (M : ℝ))) := by
      gcongr
    _ = ((M : ℝ) * (N : ℝ))⁻¹ *
        ((‖g n₁‖ * ‖g n₂‖) * (‖β m₁‖ * ‖β m₂‖)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      have hsM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hsN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hMne : (M : ℝ) ≠ 0 := by positivity
      have hNne : (N : ℝ) ≠ 0 := by positivity
      have hsMne : Real.sqrt (M : ℝ) ≠ 0 :=
        Real.sqrt_ne_zero'.2 (by positivity)
      have hsNne : Real.sqrt (N : ℝ) ≠ 0 :=
        Real.sqrt_ne_zero'.2 (by positivity)
      field_simp
      simp only [pow_two, hsM, hsN]
      ring

/-- Apply exactly the manuscript's pointwise coefficient hypotheses to the
algebraic `(M*N)⁻¹` extraction.  This is the first genuinely analytic input. -/
theorem norm_paperTupleCoefficient_le_pointwise_div
    {M N a k : ℕ} {β g : ℕ → ℂ} {q : LiteralTuple}
    (hM : 0 < M) (hN : 0 < N)
    (hq : q ∈ dyadicTupleBox M N)
    (hcoeff : PaperCoefficientBounds M N a k β g) :
    ‖paperTupleCoefficient β g q‖ ≤
      pointwiseTupleEnvelope a k q / ((M : ℝ) * (N : ℝ)) := by
  rcases q with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  have hqParts := hq
  simp [dyadicTupleBox] at hqParts
  rcases hqParts with ⟨⟨hm₁, hm₂⟩, hn₁, hn₂⟩
  rcases hcoeff with ⟨hβ, hg⟩
  have hβ₁ := hβ m₁ hm₁
  have hβ₂ := hβ m₂ hm₂
  have hg₁ := hg n₁ hn₁
  have hg₂ := hg n₂ hn₂
  have hB₁ : 0 ≤ Real.log (2 * (m₁ : ℝ)) ^ a :=
    (norm_nonneg (β m₁)).trans hβ₁
  have hB₂ : 0 ≤ Real.log (2 * (m₂ : ℝ)) ^ a :=
    (norm_nonneg (β m₂)).trans hβ₂
  have hG₁ : 0 ≤ (tauAF k n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) ^ a :=
    (norm_nonneg (g n₁)).trans hg₁
  have hG₂ : 0 ≤ (tauAF k n₂ : ℝ) * Real.log (2 * (n₂ : ℝ)) ^ a :=
    (norm_nonneg (g n₂)).trans hg₂
  calc
    ‖paperTupleCoefficient β g ((m₁, m₂), (n₁, n₂))‖ ≤
        ((M : ℝ) * (N : ℝ))⁻¹ *
          ((‖g n₁‖ * ‖g n₂‖) * (‖β m₁‖ * ‖β m₂‖)) :=
      norm_paperTupleCoefficient_le_raw hM hN hq
    _ ≤ ((M : ℝ) * (N : ℝ))⁻¹ *
        pointwiseTupleEnvelope a k ((m₁, m₂), (n₁, n₂)) := by
      unfold pointwiseTupleEnvelope
      gcongr
    _ = pointwiseTupleEnvelope a k ((m₁, m₂), (n₁, n₂)) /
        ((M : ℝ) * (N : ℝ)) := by
      rw [div_eq_mul_inv]
      ring

/-- Manuscript-facing corollary: the four logarithmic coefficient factors
become `log(2MN)^(4a)`, while the divisor envelope remains
`tau_k(n₁) tau_k(n₂)`, all multiplied by the explicit `(M*N)⁻¹`. -/
theorem norm_paperTupleCoefficient_le_commonLog_div
    {M N a k : ℕ} {β g : ℕ → ℂ} {q : LiteralTuple}
    (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hq : q ∈ dyadicTupleBox M N)
    (hcoeff : PaperCoefficientBounds M N a k β g) :
    ‖paperTupleCoefficient β g q‖ ≤
      (((tauAF k q.2.1 : ℝ) * (tauAF k q.2.2 : ℝ)) *
          Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a)) /
        ((M : ℝ) * (N : ℝ)) := by
  calc
    ‖paperTupleCoefficient β g q‖ ≤
        pointwiseTupleEnvelope a k q / ((M : ℝ) * (N : ℝ)) :=
      norm_paperTupleCoefficient_le_pointwise_div
        (by omega) (by omega) hq hcoeff
    _ ≤ commonLogTupleEnvelope M N a k q /
        ((M : ℝ) * (N : ℝ)) := by
      exact div_le_div_of_nonneg_right
        (pointwiseTupleEnvelope_le_commonLog hM hN hq) (by positivity)
    _ = (((tauAF k q.2.1 : ℝ) * (tauAF k q.2.2 : ℝ)) *
          Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a)) /
        ((M : ℝ) * (N : ℝ)) := by
      rw [commonLogTupleEnvelope_eq_logPow]

end MAPNormalizedWrapper
