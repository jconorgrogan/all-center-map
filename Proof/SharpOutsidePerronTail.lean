import UniformPsiDeterministicBridge
import PsiEndpointImprimitiveAdapters

/-!
# Sharp outside Perron tail at a half-integer endpoint

The existing coefficient-tail bound takes absolute values before exploiting
oscillation and therefore grows with the height.  Here the already proved
`y < 1` kernel estimate is applied termwise after the exact kernel-tsum
identity.  We fix the harmless legal right edge `c = 3`; the half-integer
distance then leaves the absolutely summable von Mangoldt series at exponent
two.
-/

namespace SharpOutsidePerronTail

open scoped BigOperators ArithmeticFunction
open PrimitiveExplicitFormulaSpine PrimitiveTruncatedExplicitFormulaBridge
open TruncatedTwistedPerron

noncomputable section

/-- Termwise sharp outside-kernel estimate. -/
theorem norm_tail_kernel_term_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N n : ℕ) {T : ℝ}
    (hT : 0 < T) (hn : n ∉ Finset.Icc 1 N) :
    ‖twistedMangoldtCoeff χ n *
        PerronKernel.kernel (halfIntegerPoint N / n) 3 T‖ ≤
      (2 * halfIntegerPoint N ^ (3 : ℕ) / (Real.pi * T)) *
        ‖LSeries.term (fun k : ℕ =>
          (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖ := by
  by_cases hn0 : n = 0
  · subst n
    simp [twistedMangoldtCoeff]
  have hnOne : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hNn : N < n := by
    by_contra hnot
    exact hn (Finset.mem_Icc.mpr ⟨hnOne, Nat.le_of_not_gt hnot⟩)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hxpos : 0 < halfIntegerPoint N := halfIntegerPoint_pos N
  have hxlt : halfIntegerPoint N < (n : ℝ) := by
    have hcast : ((N + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr hNn)
    unfold halfIntegerPoint
    norm_num at hcast ⊢
    linarith
  have hyratio : 0 < halfIntegerPoint N / (n : ℝ) := div_pos hxpos hnpos
  have hyratioOne : halfIntegerPoint N / (n : ℝ) < 1 :=
    (div_lt_one hnpos).2 hxlt
  have hkernel := SharpFinitePerronStep.norm_kernel_le_of_lt_one
    hyratio hyratioOne (by norm_num : (0 : ℝ) < 3) hT
  have hlogLower :
      1 / (2 * (n : ℝ)) ≤
        |Real.log (halfIntegerPoint N / (n : ℝ))| := by
    have hdist := PerronKernel.halfInteger_nat_distance N n
    have hlog := PerronKernel.abs_log_div_ge_abs_sub_div_max hxpos hnpos
    rw [max_eq_right hxlt.le] at hlog
    calc
      1 / (2 * (n : ℝ)) = (1 / 2 : ℝ) / (n : ℝ) := by ring
      _ ≤ |halfIntegerPoint N - (n : ℝ)| / (n : ℝ) := by
        gcongr
        simpa only [halfIntegerPoint] using hdist
      _ ≤ |Real.log (halfIntegerPoint N / (n : ℝ))| := hlog
  have hlogpos : 0 < |Real.log (halfIntegerPoint N / (n : ℝ))| :=
    (show 0 < 1 / (2 * (n : ℝ)) by positivity).trans_le hlogLower
  have hdenpos : 0 < Real.pi * T * (1 / (2 * (n : ℝ))) := by positivity
  have hden :
      Real.pi * T * (1 / (2 * (n : ℝ))) ≤
        Real.pi * T * |Real.log (halfIntegerPoint N / (n : ℝ))| := by
    gcongr
  have hkernel' :
      ‖PerronKernel.kernel (halfIntegerPoint N / n) 3 T‖ ≤
        2 * halfIntegerPoint N ^ (3 : ℕ) /
          (Real.pi * T * (n : ℝ) ^ 2) := by
    calc
      ‖PerronKernel.kernel (halfIntegerPoint N / n) 3 T‖ ≤
          (halfIntegerPoint N / (n : ℝ)) ^ (3 : ℝ) /
            (Real.pi * T *
              |Real.log (halfIntegerPoint N / (n : ℝ))|) := hkernel
      _ ≤ (halfIntegerPoint N / (n : ℝ)) ^ (3 : ℝ) /
            (Real.pi * T * (1 / (2 * (n : ℝ)))) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hyratio.le 3) hdenpos hden
      _ = 2 * halfIntegerPoint N ^ (3 : ℕ) /
            (Real.pi * T * (n : ℝ) ^ 2) := by
        norm_num [Real.rpow_natCast]
        rw [div_pow]
        field_simp [hnpos.ne', hT.ne', Real.pi_ne_zero]
  have hcoeff : ‖twistedMangoldtCoeff χ n‖ ≤
      ArithmeticFunction.vonMangoldt n := norm_twistedMangoldtCoeff_le χ n
  have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  rw [norm_mul]
  calc
    ‖twistedMangoldtCoeff χ n‖ *
        ‖PerronKernel.kernel (halfIntegerPoint N / n) 3 T‖ ≤
      ArithmeticFunction.vonMangoldt n *
        (2 * halfIntegerPoint N ^ (3 : ℕ) /
          (Real.pi * T * (n : ℝ) ^ 2)) :=
      mul_le_mul hcoeff hkernel' (norm_nonneg _) hvm0
    _ = (2 * halfIntegerPoint N ^ (3 : ℕ) / (Real.pi * T)) *
        ‖LSeries.term (fun k : ℕ =>
          (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖ := by
      rw [LSeries.norm_term_eq, if_neg hn0]
      norm_num [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hvm0, Real.rpow_natCast]
      field_simp [hnpos.ne', hT.ne', Real.pi_ne_zero]

/-- Summed sharp coefficient-tail estimate at the legal fixed right edge
`c = 3`.  Unlike the older absolute-integral estimate, this decays as `1/T`.
The remaining scalar series is the convergent ordinary von Mangoldt
Dirichlet series at exponent two. -/
theorem norm_coefficientTail_le_sharp_outside
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) {T : ℝ}
    (hT : 0 < T) :
    ‖coefficientTail χ (halfIntegerPoint N) 3 T (Finset.Icc 1 N)‖ ≤
      (2 * halfIntegerPoint N ^ (3 : ℕ) / (Real.pi * T)) *
        ∑' n : {n // n ∉ Finset.Icc 1 N},
          ‖LSeries.term (fun k : ℕ =>
            (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖ := by
  let f : {n // n ∉ Finset.Icc 1 N} → ℂ := fun n =>
    twistedMangoldtCoeff χ n *
      PerronKernel.kernel (halfIntegerPoint N / n) 3 T
  let g : {n // n ∉ Finset.Icc 1 N} → ℝ := fun n =>
    ‖LSeries.term (fun k : ℕ =>
      (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖
  let K : ℝ := 2 * halfIntegerPoint N ^ (3 : ℕ) / (Real.pi * T)
  have hgBase : Summable fun n : ℕ =>
      ‖LSeries.term (fun k : ℕ =>
        (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖ := by
    apply summable_norm_iff.mpr
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hg : Summable g := by
    simpa only [g, Function.comp_apply] using
      hgBase.subtype {n : ℕ | n ∉ Finset.Icc 1 N}
  have hmajor : Summable fun n => K * g n := hg.mul_left K
  have hbound : ∀ n, ‖f n‖ ≤ K * g n := by
    intro n
    exact norm_tail_kernel_term_le χ N n hT n.property
  have hf : Summable f := Summable.of_norm_bounded hmajor hbound
  rw [UniformPsiDeterministicBridge.coefficientTail_eq_tsum_kernels
    χ (halfIntegerPoint_pos N) (Finset.Icc 1 N)]
  change ‖∑' n, f n‖ ≤ K * ∑' n, g n
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, K * g n := hf.norm.tsum_le_tsum hbound hmajor
    _ = K * ∑' n, g n := by rw [tsum_mul_left]

/-- Character- and endpoint-uniform version with one fixed convergent scalar
constant.  This is the form usable in a quantitative explicit formula. -/
theorem norm_coefficientTail_le_sharp_outside_global
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) {T : ℝ}
    (hT : 0 < T) :
    ‖coefficientTail χ (halfIntegerPoint N) 3 T (Finset.Icc 1 N)‖ ≤
      (2 * halfIntegerPoint N ^ (3 : ℕ) / (Real.pi * T)) *
        ∑' n : ℕ,
          ‖LSeries.term (fun k : ℕ =>
            (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖ := by
  have hbase := norm_coefficientTail_le_sharp_outside χ N hT
  have hsum : Summable fun n : ℕ =>
      ‖LSeries.term (fun k : ℕ =>
        (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖ := by
    apply summable_norm_iff.mpr
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hsub : Summable fun n : {n // n ∉ Finset.Icc 1 N} =>
      ‖LSeries.term (fun k : ℕ =>
        (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖ := by
    simpa only [Function.comp_apply] using
      hsum.subtype {n : ℕ | n ∉ Finset.Icc 1 N}
  have hsuble :
      (∑' n : {n // n ∉ Finset.Icc 1 N},
          ‖LSeries.term (fun k : ℕ =>
            (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖) ≤
        ∑' n : ℕ,
          ‖LSeries.term (fun k : ℕ =>
            (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖ := by
    apply Summable.tsum_le_tsum_of_inj (fun n : {n // n ∉ Finset.Icc 1 N} => (n : ℕ))
      Subtype.coe_injective
    · intro n hn
      exact norm_nonneg _
    · intro n
      exact le_rfl
    · exact hsub
    · exact hsum
  have hfactor0 :
      0 ≤ 2 * halfIntegerPoint N ^ (3 : ℕ) / (Real.pi * T) := by
    apply div_nonneg
    · exact mul_nonneg (by norm_num)
        (pow_nonneg (halfIntegerPoint_pos N).le 3)
    · exact (mul_pos Real.pi_pos hT).le
  exact hbase.trans (mul_le_mul_of_nonneg_left hsuble hfactor0)

/-- Ambient twisted-prefix majorant with both the inside and outside sharp
Perron estimates.  The only unevaluated analytic norms are now the zero sum
and the two shifted contour segments. -/
theorem norm_twistedMangoldtPrefix_sub_characterMain_le_sharp_majorant
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {t σ T : ℝ}
    (ht : 0 ≤ t) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hT : 0 < T)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      DirichletZeros.regularizedLFunction χ.primitiveCharacter
        ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ 3,
      DirichletZeros.regularizedLFunction χ.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ 3,
      DirichletZeros.regularizedLFunction χ.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ‖APFoundation.twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤
      1 / 2 +
      ‖multiplicityWeightedPerronZeroSum χ.primitiveCharacter σ T
        (halfIntegerPoint ⌊t⌋₊)‖ +
      ‖leftLineIntegral χ.primitiveCharacter
        (halfIntegerPoint ⌊t⌋₊) σ T‖ +
      ‖horizontalBoundaryIntegral χ.primitiveCharacter
        (halfIntegerPoint ⌊t⌋₊) σ 3 T‖ +
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
        ArithmeticFunction.vonMangoldt n *
          ((halfIntegerPoint ⌊t⌋₊ / n) ^ (3 : ℝ) /
            (Real.pi * T *
              |Real.log (halfIntegerPoint ⌊t⌋₊ / n)|))) +
      ((2 * halfIntegerPoint ⌊t⌋₊ ^ (3 : ℕ) / (Real.pi * T)) *
        ∑' n : ℕ,
          ‖LSeries.term (fun k : ℕ =>
            (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖) +
      (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
  have hbase :=
    UniformPsiDeterministicBridge.norm_twistedMangoldtPrefix_sub_characterMain_le_explicit_terms
      χ ht hσ0 hσ1 (by norm_num : (1 : ℝ) < 3) hT
        hleftNonzero hbottomNonzero htopNonzero
  have hinside := SharpPerronRemainderBridge.norm_insideKernelError_le_sharp
    χ.primitiveCharacter ⌊t⌋₊ (by norm_num : (0 : ℝ) < 3) hT
  have htail := norm_coefficientTail_le_sharp_outside_global
    χ.primitiveCharacter ⌊t⌋₊ hT
  have hbad := norm_imprimitiveMangoldtCorrection_prefix_le χ ⌊t⌋₊
  exact hbase.trans (by gcongr)

/-- Primitive-character version, with no imprimitive term.  This is the exact
analytic majorant that feeds the endpoint/conductor adapter. -/
theorem norm_primitivePrefix_sub_characterMain_le_sharp_majorant
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t σ T : ℝ}
    (ht : 0 ≤ t) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hT : 0 < T)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      DirichletZeros.regularizedLFunction χ
        ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ 3,
      DirichletZeros.regularizedLFunction χ
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ 3,
      DirichletZeros.regularizedLFunction χ
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ‖APFoundation.twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤
      1 / 2 +
      ‖multiplicityWeightedPerronZeroSum χ σ T
        (halfIntegerPoint ⌊t⌋₊)‖ +
      ‖leftLineIntegral χ (halfIntegerPoint ⌊t⌋₊) σ T‖ +
      ‖horizontalBoundaryIntegral χ (halfIntegerPoint ⌊t⌋₊) σ 3 T‖ +
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
        ArithmeticFunction.vonMangoldt n *
          ((halfIntegerPoint ⌊t⌋₊ / n) ^ (3 : ℝ) /
            (Real.pi * T *
              |Real.log (halfIntegerPoint ⌊t⌋₊ / n)|))) +
      ((2 * halfIntegerPoint ⌊t⌋₊ ^ (3 : ℕ) / (Real.pi * T)) *
        ∑' n : ℕ,
          ‖LSeries.term (fun k : ℕ =>
            (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖) := by
  have hbase :=
    MAPPsiEndpointImprimitiveAdapters.norm_twistedMangoldtPrefix_sub_characterMain_le_explicitTerms
      χ ht hσ0 hσ1 (by norm_num : (1 : ℝ) < 3) hT
        hleftNonzero hbottomNonzero htopNonzero
  have hinside := SharpPerronRemainderBridge.norm_insideKernelError_le_sharp
    χ ⌊t⌋₊ (by norm_num : (0 : ℝ) < 3) hT
  have htail := norm_coefficientTail_le_sharp_outside_global χ ⌊t⌋₊ hT
  exact hbase.trans (by gcongr)

/-- Direct constructor for the existing `UniformTwistedMangoldtPsi` from the
literal analytic quantities still missing after the sharp finite Perron
work.  The premise is inline rather than packaged as a new proposition. -/
theorem uniformTwistedMangoldtPsi_of_primitive_sharp_majorant
    (hanalytic :
      ∀ A B : ℕ, ∃ C X0 : ℝ,
        0 < C ∧ 2 ≤ X0 ∧
          ∀ X : ℝ, X0 ≤ X →
          ∀ q : ℕ, ∀ _hq0 : NeZero q,
            1 ≤ q →
            (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
          ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
            ∃ σ T : ℝ,
              0 < σ ∧ σ < 1 ∧ 0 < T ∧
              (∀ u ∈ Set.Icc (-T) T,
                DirichletZeros.regularizedLFunction χ
                  ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0) ∧
              (∀ r ∈ Set.Icc σ 3,
                DirichletZeros.regularizedLFunction χ
                  ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
              (∀ r ∈ Set.Icc σ 3,
                DirichletZeros.regularizedLFunction χ
                  ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) ∧
              (1 / 2 +
                ‖multiplicityWeightedPerronZeroSum χ σ T
                  (halfIntegerPoint ⌊t⌋₊)‖ +
                ‖leftLineIntegral χ (halfIntegerPoint ⌊t⌋₊) σ T‖ +
                ‖horizontalBoundaryIntegral χ
                  (halfIntegerPoint ⌊t⌋₊) σ 3 T‖ +
                (∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
                  ArithmeticFunction.vonMangoldt n *
                    ((halfIntegerPoint ⌊t⌋₊ / n) ^ (3 : ℝ) /
                      (Real.pi * T *
                        |Real.log (halfIntegerPoint ⌊t⌋₊ / n)|))) +
                ((2 * halfIntegerPoint ⌊t⌋₊ ^ (3 : ℕ) /
                    (Real.pi * T)) *
                  ∑' n : ℕ,
                    ‖LSeries.term (fun k : ℕ =>
                      (ArithmeticFunction.vonMangoldt k : ℂ))
                        (2 : ℂ) n‖) ≤
                C * X / (Real.log X) ^ A)) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi := by
  apply MAPPsiEndpointImprimitiveAdapters.uniformTwistedMangoldtPsi_of_primitive
  intro A B
  obtain ⟨C, X0, hC, hX0, hsource⟩ := hanalytic A B
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X hX q hq hqcap χ hχ t ht
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  obtain ⟨σ, T, hσ0, hσ1, hT, hleft, hbottom, htop, hbound⟩ :=
    hsource X hX q (inferInstance : NeZero q) hq hqcap χ hχ t ht
  exact (norm_primitivePrefix_sub_characterMain_le_sharp_majorant
    χ (by linarith [hX0, hX, ht.1]) hσ0 hσ1 hT
      hleft hbottom htop).trans hbound

end

end SharpOutsidePerronTail

#print axioms SharpOutsidePerronTail.norm_tail_kernel_term_le
#print axioms SharpOutsidePerronTail.norm_coefficientTail_le_sharp_outside
#print axioms SharpOutsidePerronTail.norm_coefficientTail_le_sharp_outside_global
#print axioms SharpOutsidePerronTail.norm_twistedMangoldtPrefix_sub_characterMain_le_sharp_majorant
#print axioms SharpOutsidePerronTail.norm_primitivePrefix_sub_characterMain_le_sharp_majorant
#print axioms SharpOutsidePerronTail.uniformTwistedMangoldtPsi_of_primitive_sharp_majorant
