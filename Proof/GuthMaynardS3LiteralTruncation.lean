import GuthMaynardS2ReflectionBridge

/-!
# Quantitative truncation of the literal S3 Fourier cube

The two-sided nonzero prefix and both infinite tails are those already
certified for Section 6. The cubic telescoping estimate is used only to
bound the truncation error, not as a substitute for the affine S3 estimate.
-/

namespace GuthMaynardS3LiteralTruncation

open scoped BigOperators
open GuthMaynardS2ReflectionBridge GuthMaynardSectorFactorization
open GuthMaynardLemma62InfiniteTail GuthMaynardLemma62FarTail
open GuthMaynardS1Source GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardEquation55Infinite

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def nonzeroFourierPrefix (N M : ℕ) (t : ℝ) : ℂ :=
  (∑ m ∈ Finset.Icc 1 M,sectionThreeFourierCoefficient t ((m : ℝ)*N)) +
  (∑ m ∈ Finset.Icc 1 M,sectionThreeFourierCoefficient t (-((m : ℝ)*N)))

def prefixError (T : ℝ) (N M j : ℕ) : ℝ :=
  2*(lemma43DerivativeConstant j*(1+T)^j*Real.rpow (N : ℝ) (-(j : ℝ))) *
    (Real.rpow (M : ℝ) (1-(j : ℝ))/((j : ℝ)-1))

def prefixEnvelope (T : ℝ) (N M j : ℕ) : ℝ :=
  2*(M : ℝ)*lemma43DerivativeConstant 0+prefixError T N M j

def sourceS3Prefix (N M : ℕ) (W : Finset ℝ) : ℂ :=
  (N : ℂ)^3 * ∑ a∈W,∑ b∈W,∑ c∈W,
    nonzeroFourierPrefix N M (a-b)*nonzeroFourierPrefix N M (b-c)*nonzeroFourierPrefix N M (c-a)

def nonzeroPrefix (M : ℕ) : Finset ℤ :=
  (Finset.Icc 1 M).image (fun m : ℕ => (m : ℤ)) ∪
    (Finset.Icc 1 M).image (fun m : ℕ => -(m : ℤ))

def prefixFrequencyCube (M : ℕ) : Finset Frequency :=
  ((nonzeroPrefix M).product (nonzeroPrefix M)).product (nonzeroPrefix M)

theorem nonzeroPrefix_ne_zero {M : ℕ} {m : ℤ} (hm : m∈nonzeroPrefix M) : m≠0 := by
  rcases Finset.mem_union.mp hm with h|h
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp h
    have := (Finset.mem_Icc.mp hn).1
    omega
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp h
    have := (Finset.mem_Icc.mp hn).1
    omega

theorem nonzeroFourierPrefix_eq_sum (N M : ℕ) (t : ℝ) :
    nonzeroFourierPrefix N M t =
      ∑ m∈nonzeroPrefix M,sourceHhat t ((m : ℝ)*N) := by
  have hd : Disjoint ((Finset.Icc 1 M).image (fun m : ℕ => (m : ℤ)))
      ((Finset.Icc 1 M).image (fun m : ℕ => -(m : ℤ))) := by
    apply Finset.disjoint_left.mpr
    intro m hp hn
    obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hp
    obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hn
    have := (Finset.mem_Icc.mp ha).1
    have := (Finset.mem_Icc.mp hb).1
    omega
  symm
  unfold nonzeroPrefix
  rw [Finset.sum_union hd,Finset.sum_image (by intro a ha b hb h; dsimp only at h; exact_mod_cast h),
    Finset.sum_image (by intro a ha b hb h; dsimp only at h; exact_mod_cast neg_injective h)]
  simp only [Int.cast_natCast,Int.cast_neg,neg_mul]
  rfl

private theorem sum_cube_product (P : Finset ℝ) (f g h : ℝ → ℂ) :
    (∑ a∈P,f a)*(∑ b∈P,g b)*(∑ c∈P,h c) =
      ∑ a∈P,∑ b∈P,∑ c∈P,f a*g b*h c := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul,Finset.mul_sum]

private theorem sum_int_cube_product (P : Finset ℤ) (f g h : ℤ → ℂ) :
    (∑ a∈P,f a)*(∑ b∈P,g b)*(∑ c∈P,h c) =
      ∑ p∈(P.product P).product P,f p.1.1*g p.1.2*h p.2 := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul,Finset.mul_sum,Finset.product_eq_sprod,Finset.sum_product]

/-- The retained cube is exactly a finite block of the original nonzero
frequency terms, including its two signs and exclusion of all planes. -/
theorem sourceS3Prefix_eq_finite_frequency_block (N M : ℕ) (W : Finset ℝ) :
    sourceS3Prefix N M W = ∑ p∈prefixFrequencyCube M,
      if GuthMaynardEquation55Split.exactlyThreeNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0 := by
  let V := (W.product W).product W
  have hmask (p : Frequency) (hp : p∈prefixFrequencyCube M) :
      GuthMaynardEquation55Split.exactlyThreeNonzero p.1.1 p.1.2 p.2 := by
    obtain ⟨h12,h3⟩ := Finset.mem_product.mp hp
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp h12
    exact ⟨nonzeroPrefix_ne_zero h1,nonzeroPrefix_ne_zero h2,nonzeroPrefix_ne_zero h3⟩
  symm
  calc
    _ = ∑ p∈prefixFrequencyCube M,frequencyTerm N W p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [if_pos (hmask p hp)]
    _ = (N : ℂ)^3 * ∑ p∈prefixFrequencyCube M,∑ w∈V,
        sourceHhat (w.1.1-w.1.2) ((p.1.1 : ℝ)*N)*
          sourceHhat (w.1.2-w.2) ((p.1.2 : ℝ)*N)*sourceHhat (w.2-w.1.1) ((p.2 : ℝ)*N) := by
      simp only [frequencyTerm,GuthMaynardEquation55Split.sourceIm,V,Finset.product_eq_sprod,Finset.sum_product,Finset.mul_sum]
    _ = (N : ℂ)^3 * ∑ w∈V,∑ p∈prefixFrequencyCube M,
        sourceHhat (w.1.1-w.1.2) ((p.1.1 : ℝ)*N)*
          sourceHhat (w.1.2-w.2) ((p.1.2 : ℝ)*N)*sourceHhat (w.2-w.1.1) ((p.2 : ℝ)*N) := by
      rw [Finset.sum_comm]
    _ = (N : ℂ)^3 * ∑ w∈V,
        nonzeroFourierPrefix N M (w.1.1-w.1.2)*nonzeroFourierPrefix N M (w.1.2-w.2)*
          nonzeroFourierPrefix N M (w.2-w.1.1) := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      simp_rw [nonzeroFourierPrefix_eq_sum]
      simpa only [prefixFrequencyCube] using (sum_int_cube_product (nonzeroPrefix M)
        (fun m => sourceHhat (w.1.1-w.1.2) ((m : ℝ)*N))
        (fun m => sourceHhat (w.1.2-w.2) ((m : ℝ)*N))
        (fun m => sourceHhat (w.2-w.1.1) ((m : ℝ)*N))).symm
    _ = _ := by simp only [sourceS3Prefix,V,Finset.product_eq_sprod,Finset.sum_product]

theorem prefixError_nonneg {T : ℝ} (hT : 0 ≤ T) (N M j : ℕ) (hj : 2 ≤ j) :
    0 ≤ prefixError T N M j := by
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  unfold prefixError
  exact mul_nonneg
    (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (lemma43DerivativeConstant_nonneg j) (by positivity))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by linarith))

/-- The existing two literal tails, with one uniform ordinate envelope. -/
theorem norm_nonzeroFourier_sub_prefix_le {N M j : ℕ} (hN : 0<N) (hM : 1 ≤ M) (hj : 2 ≤ j)
    {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖sourceNonzeroFourier N t-nonzeroFourierPrefix N M t‖ ≤ prefixError T N M j := by
  have hp := norm_tsum_positiveFourierTail_le t (Nat.cast_pos.mpr hN) hM hj
  have hn := norm_tsum_negativeFourierTail_le t (Nat.cast_pos.mpr hN) hM hj
  have heq : sourceNonzeroFourier N t-nonzeroFourierPrefix N M t =
      (∑' i,positiveFourierTail t N M i)+(∑' i,negativeFourierTail t N M i) := by
    rw [sourceNonzeroFourier_eq_prefix_and_tails hN t M]
    unfold nonzeroFourierPrefix
    ring
  rw [heq]
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|t|) (by linarith : 1+|t| ≤ 1+T) j
  have hconst : 0 ≤ lemma43DerivativeConstant j*Real.rpow (N : ℝ) (-(j : ℝ))*
      (Real.rpow (M : ℝ) (1-(j : ℝ))/((j : ℝ)-1)) :=
    mul_nonneg (mul_nonneg (lemma43DerivativeConstant_nonneg j) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by linarith))
  have hm := mul_le_mul_of_nonneg_left hpow hconst
  have htri := norm_add_le (∑' i,positiveFourierTail t N M i) (∑' i,negativeFourierTail t N M i)
  unfold prefixError
  change ‖∑' i,positiveFourierTail t N M i‖ ≤
    (lemma43DerivativeConstant j*(1+|t|)^j*Real.rpow (N : ℝ) (-(j : ℝ)))*
      (Real.rpow (M : ℝ) (1-(j : ℝ))/((j : ℝ)-1)) at hp
  change ‖∑' i,negativeFourierTail t N M i‖ ≤
    (lemma43DerivativeConstant j*(1+|t|)^j*Real.rpow (N : ℝ) (-(j : ℝ)))*
      (Real.rpow (M : ℝ) (1-(j : ℝ))/((j : ℝ)-1)) at hn
  nlinarith only [hp,hn,htri,hm]

theorem norm_nonzeroFourierPrefix_le (N M : ℕ) (t : ℝ) :
    ‖nonzeroFourierPrefix N M t‖ ≤ 2*(M : ℝ)*lemma43DerivativeConstant 0 := by
  have hpos : ‖∑ m ∈ Finset.Icc 1 M,sectionThreeFourierCoefficient t ((m : ℝ)*N)‖ ≤
      (M : ℝ)*lemma43DerivativeConstant 0 := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _m ∈ Finset.Icc 1 M,lemma43DerivativeConstant 0 := by
        apply Finset.sum_le_sum
        intro m hm
        exact norm_sourceHhat_le_fixed _ _
      _ = _ := by simp
  have hneg : ‖∑ m ∈ Finset.Icc 1 M,sectionThreeFourierCoefficient t (-((m : ℝ)*N))‖ ≤
      (M : ℝ)*lemma43DerivativeConstant 0 := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _m ∈ Finset.Icc 1 M,lemma43DerivativeConstant 0 := by
        apply Finset.sum_le_sum
        intro m hm
        exact norm_sourceHhat_le_fixed _ _
      _ = _ := by simp
  exact (norm_add_le _ _).trans (by nlinarith only [hpos,hneg])

theorem norm_cube_difference_le {x1 x2 x3 y1 y2 y3 : ℂ} {A E : ℝ}
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hx2 : ‖x2‖ ≤ A) (hx3 : ‖x3‖ ≤ A) (hy1 : ‖y1‖ ≤ A) (hy2 : ‖y2‖ ≤ A)
    (hd1 : ‖x1-y1‖ ≤ E) (hd2 : ‖x2-y2‖ ≤ E) (hd3 : ‖x3-y3‖ ≤ E) :
    ‖x1*x2*x3-y1*y2*y3‖ ≤ 3*E*A^2 := by
  have heq : x1*x2*x3-y1*y2*y3=(x1-y1)*x2*x3+y1*(x2-y2)*x3+y1*y2*(x3-y3) := by ring
  rw [heq]
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
  simp only [norm_mul]
  have h1 := mul_le_mul (mul_le_mul hd1 hx2 (norm_nonneg _) hE) hx3 (norm_nonneg _) (mul_nonneg hE hA)
  have h2 := mul_le_mul (mul_le_mul hy1 hd2 (norm_nonneg _) hA) hx3 (norm_nonneg _) (mul_nonneg hA hE)
  have h3 := mul_le_mul (mul_le_mul hy1 hy2 (norm_nonneg _) hA) hd3 (norm_nonneg _) (mul_nonneg hA hA)
  nlinarith only [h1,h2,h3]

/-- Quantitative truncation of the actual complex S3, before any triangle
inequality is applied to its retained frequency block. -/
theorem norm_sourceS3_sub_prefix_le {N M j : ℕ} (hN : 0<N) (hM : 1 ≤ M) (hj : 2 ≤ j)
    {T : ℝ} (hT : 0 ≤ T) (W : Finset ℝ)
    (hdiam : ∀ a∈W,∀ b∈W,|a-b| ≤ T) :
    ‖sourceS3 N W-sourceS3Prefix N M W‖ ≤
      3*(N : ℝ)^3*(W.card : ℝ)^3*prefixError T N M j*(prefixEnvelope T N M j)^2 := by
  let E := prefixError T N M j
  let A := prefixEnvelope T N M j
  have hE : 0 ≤ E := prefixError_nonneg hT N M j hj
  have hA : 0 ≤ A := by dsimp [A,prefixEnvelope]; have := lemma43DerivativeConstant_nonneg 0; positivity
  have hp (a b : ℝ) : ‖nonzeroFourierPrefix N M (a-b)‖ ≤ A :=
    (norm_nonzeroFourierPrefix_le N M _).trans (by dsimp [A,prefixEnvelope]; linarith)
  have hd (a : ℝ) (ha : a∈W) (b : ℝ) (hb : b∈W) :
      ‖sourceNonzeroFourier N (a-b)-nonzeroFourierPrefix N M (a-b)‖ ≤ E :=
    norm_nonzeroFourier_sub_prefix_le hN hM hj hT (hdiam a ha b hb)
  have hz (a : ℝ) (ha : a∈W) (b : ℝ) (hb : b∈W) : ‖sourceNonzeroFourier N (a-b)‖ ≤ A := by
    have heq : sourceNonzeroFourier N (a-b) =
        (sourceNonzeroFourier N (a-b)-nonzeroFourierPrefix N M (a-b))+nonzeroFourierPrefix N M (a-b) := by ring
    rw [heq]
    have hh := (norm_add_le _ _).trans (add_le_add (hd a ha b hb) (norm_nonzeroFourierPrefix_le N M (a-b)))
    exact hh.trans_eq (by dsimp [A,E,prefixEnvelope]; ring)
  rw [sourceS3_eq_nonzeroFourier_cube hN,sourceS3Prefix,← mul_sub]
  have heq :
      (∑ a∈W,∑ b∈W,∑ c∈W,sourceNonzeroFourier N (a-b)*sourceNonzeroFourier N (b-c)*sourceNonzeroFourier N (c-a))-
      (∑ a∈W,∑ b∈W,∑ c∈W,nonzeroFourierPrefix N M (a-b)*nonzeroFourierPrefix N M (b-c)*nonzeroFourierPrefix N M (c-a)) =
      ∑ a∈W,∑ b∈W,∑ c∈W,(sourceNonzeroFourier N (a-b)*sourceNonzeroFourier N (b-c)*sourceNonzeroFourier N (c-a)-
        nonzeroFourierPrefix N M (a-b)*nonzeroFourierPrefix N M (b-c)*nonzeroFourierPrefix N M (c-a)) := by
    simp only [Finset.sum_sub_distrib]
  rw [heq,norm_mul,norm_pow,Complex.norm_natCast]
  have hsum : ‖∑ a∈W,∑ b∈W,∑ c∈W,(sourceNonzeroFourier N (a-b)*sourceNonzeroFourier N (b-c)*sourceNonzeroFourier N (c-a)-
      nonzeroFourierPrefix N M (a-b)*nonzeroFourierPrefix N M (b-c)*nonzeroFourierPrefix N M (c-a))‖ ≤
        (W.card : ℝ)^3*(3*E*A^2) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ a∈W,∑ b∈W,∑ c∈W,3*E*A^2 := by
        apply Finset.sum_le_sum
        intro a ha
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro b hb
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro c hc
        exact norm_cube_difference_le hA hE (hz b hb c hc) (hz c hc a ha)
          (hp a b) (hp b c) (hd a ha b hb) (hd b hb c hc) (hd c hc a ha)
      _ = _ := by simp; ring
  have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (N : ℝ)^3 by positivity)
  dsimp [E,A] at hm
  nlinarith only [hm]


/-- The literal infinite S3 sum is reduced to its actual finite nonzero
frequency cube, with the explicit source Fourier-tail error. -/
theorem norm_sourceS3_le_finite_block_add_error {N M j : ℕ} (hN : 0<N)
    (hM : 1 ≤ M) (hj : 2 ≤ j) {T : ℝ} (hT : 0 ≤ T) (W : Finset ℝ)
    (hdiam : ∀ a∈W,∀ b∈W,|a-b| ≤ T) :
    ‖sourceS3 N W‖ ≤
      ‖∑ p∈prefixFrequencyCube M,
        if GuthMaynardEquation55Split.exactlyThreeNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0‖ +
      3*(N : ℝ)^3*(W.card : ℝ)^3*prefixError T N M j*(prefixEnvelope T N M j)^2 := by
  have he := norm_sourceS3_sub_prefix_le hN hM hj hT W hdiam
  have ht := norm_add_le (sourceS3 N W-sourceS3Prefix N M W) (sourceS3Prefix N M W)
  rw [sub_add_cancel] at ht
  rw [← sourceS3Prefix_eq_finite_frequency_block]
  linarith only [he,ht]

end
end GuthMaynardS3LiteralTruncation

#print axioms GuthMaynardS3LiteralTruncation.norm_sourceS3_sub_prefix_le

#print axioms GuthMaynardS3LiteralTruncation.sourceS3Prefix_eq_finite_frequency_block

#print axioms GuthMaynardS3LiteralTruncation.norm_sourceS3_le_finite_block_add_error
