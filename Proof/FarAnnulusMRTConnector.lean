import CertifiedShiuLemma21

/-!
# Exact Type-d cell normalization in the MAP far annulus

This file formalizes the algebra between the certified manuscript Lemma 2.1
and equations (3.6)--(3.7).  It deliberately does **not** assume the completed
far-annulus estimate.  The remaining analytic input is the preceding
MRT/Heath--Brown/Perron/Cauchy--Fubini reduction identifying each actual
Type-`d_j` cell with `characterPairMixedMass` below.
-/

namespace MAPFarAnnulusMRT

open scoped BigOperators
open MixedMeanMajorantWeld MAPNormalizedWrapper ShiuFinalCertification

noncomputable section

/-! ## The factor-length geometry for `3 ≤ j ≤ 7` -/

/-- If `M` is the shortest beta length and two other beta factors are no
shorter, their product already supplies the square-complement condition in
Lemma 2.1.  The alpha factor and all remaining beta factors are absorbed in
`extra`, which is at least one. -/
theorem two_noShorter_beta_force_square_complement
    {M M₂ M₃ alpha extra : ℕ}
    (hM₂ : M ≤ M₂) (hM₃ : M ≤ M₃)
    (halpha : 1 ≤ alpha) (hextra : 1 ≤ extra) :
    M ^ 2 ≤ alpha * M₂ * M₃ * extra := by
  have hsq : M * M ≤ M₂ * M₃ := Nat.mul_le_mul hM₂ hM₃
  have hone : 1 ≤ alpha * extra :=
    Nat.mul_pos (Nat.zero_lt_of_lt halpha) (Nat.zero_lt_of_lt hextra)
  calc
    M ^ 2 = M * M := by ring
    _ ≤ M₂ * M₃ := hsq
    _ = 1 * (M₂ * M₃) := by simp
    _ ≤ (alpha * extra) * (M₂ * M₃) := Nat.mul_le_mul_right _ hone
    _ = alpha * M₂ * M₃ * extra := by ring

/-- The decomposition lower bound on every displayed beta factor passes to
the selected shortest beta factor. -/
theorem selected_beta_retains_H0
    {H₀ M : ℕ} (hM : H₀ ≤ M) : H₀ ≤ M := hM

/-! ## Literal character-pair sum of manuscript mixed means -/

/-- After expanding the square of the character sum in MRT Corollary 5.3,
there are at most `q^2` mixed means.  The leading `U` is the overlap length
produced when the outer `t` integral is performed after Cauchy and Fubini.
-/
def characterPairMixedMass
    (q M N : ℕ)
    (beta long : Fin q → Fin q → ℕ → ℂ)
    (t₀ T U : ℝ) : ℝ :=
  U * ∑ chi : Fin q, ∑ chi' : Fin q,
    (MixedMeanMajorantWeld.paperLiteralMixedMean
      M N (beta chi chi') (long chi chi') t₀ T U).re

/-- The exact `q^2 U` consequence of the now premise-free manuscript
Lemma 2.1.  This is the load-bearing replacement for treating (3.6) as an
opaque analytic premise. -/
theorem exists_characterPairMixedMass_bound
    {c : ℝ} {a k q M N : ℕ}
    (hc : 0 < c) (hk : 1 ≤ k)
    (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hMN : c * (M : ℝ) ^ 2 ≤ (N : ℝ))
    {t₀ T U : ℝ} (hT : 1 ≤ T) (hU : 1 ≤ U)
    (beta long : Fin q → Fin q → ℕ → ℂ)
    (hcoeff : ∀ chi chi',
      PaperCoefficientBounds M N a k (beta chi chi') (long chi chi')) :
    ∃ C : ℝ, 0 < C ∧
      characterPairMixedMass q M N beta long t₀ T U ≤
        U * (q : ℝ) ^ 2 * C *
          Real.log (2 * (M : ℝ) * (N : ℝ)) ^
            (4 * a + 2 * max 2 (k * k) + 2) *
          (U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T) := by
  have hlemma : PaperMixedMeanLemma21 c a k :=
    certifiedPaperMixedMeanLemma21 c a k
  obtain ⟨C, hC, hbound⟩ := hlemma hc hk
  refine ⟨C, hC, ?_⟩
  let E : ℝ := C *
    Real.log (2 * (M : ℝ) * (N : ℝ)) ^
      (4 * a + 2 * max 2 (k * k) + 2) *
    (U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T)
  have hpair : ∀ chi chi',
      (MixedMeanMajorantWeld.paperLiteralMixedMean
        M N (beta chi chi') (long chi chi') t₀ T U).re ≤ E := by
    intro chi chi'
    exact hbound M N (beta chi chi') (long chi chi') t₀ T U
      hM hN hMN hT hU (hcoeff chi chi')
  have hsum :
      (∑ chi : Fin q, ∑ chi' : Fin q,
        (MixedMeanMajorantWeld.paperLiteralMixedMean M N (beta chi chi')
          (long chi chi') t₀ T U).re) ≤ (q : ℝ) ^ 2 * E := by
    calc
      (∑ chi : Fin q, ∑ chi' : Fin q,
        (MixedMeanMajorantWeld.paperLiteralMixedMean M N (beta chi chi')
          (long chi chi') t₀ T U).re)
          ≤ ∑ _chi : Fin q, ∑ _chi' : Fin q, E := by
              exact Finset.sum_le_sum fun chi _ ↦
                Finset.sum_le_sum fun chi' _ ↦ hpair chi chi'
      _ = (q : ℝ) ^ 2 * E := by simp [pow_two]; ring
  unfold characterPairMixedMass
  have hUnonneg : 0 ≤ U := le_trans (by norm_num) hU
  have := mul_le_mul_of_nonneg_left hsum hUnonneg
  dsimp [E] at this ⊢
  convert this using 1 <;> ring

/-! ## MRT stationary-phase normalization -/

/-- The four dimensionless terms left after dividing a Type-d cell by the
literal MRT denominator `q U^2 X`. -/
def paperCellTerms (q M N T U X : ℝ) : ℝ :=
  q * T / X + q * N / X + q * M * N / (U * X) + q * T / (U * X)

/-- Pure normalization identity behind (3.6).  `raw` is the cell contribution
after character expansion.  Its assumed upper bound is exactly what the
certified mixed-mean theorem supplies once the source-level Cauchy--Fubini
reduction has identified the actual cell with `characterPairMixedMass`.

The divisor factor is retained rather than hidden in `L^{O(1)}`. -/
theorem stationary_normalization_to_paperCellTerms
    {divisorLoss q M N T U X E raw : ℝ}
    (hdiv : 0 ≤ divisorLoss) (hq : 0 < q) (hU : 0 < U) (hX : 0 < X)
    (hraw : raw ≤ U * q ^ 2 * E * (U * T + U * N + M * N + T)) :
    divisorLoss / (q * U ^ 2 * X) * raw ≤
      divisorLoss * E * paperCellTerms q M N T U X := by
  have hpref : 0 ≤ divisorLoss / (q * U ^ 2 * X) := by positivity
  calc
    divisorLoss / (q * U ^ 2 * X) * raw
        ≤ divisorLoss / (q * U ^ 2 * X) *
            (U * q ^ 2 * E * (U * T + U * N + M * N + T)) :=
      mul_le_mul_of_nonneg_left hraw hpref
    _ = divisorLoss * E * paperCellTerms q M N T U X := by
      simp only [paperCellTerms]
      field_simp [ne_of_gt hq, ne_of_gt hU, ne_of_gt hX]
      <;> ring

/-! ## Exact passage from (3.6) to (3.7) -/

/-- The first term uses Dirichlet approximation:
`q * |lambda| ≤ 1/Q`. -/
theorem first_cell_term_le
    {q Q lambda T X : ℝ}
    (hq : 0 ≤ q) (hQ : 0 < Q) (hlambda : 0 ≤ lambda) (hX : 0 < X)
    (hT : T ≤ Real.sqrt Q * lambda * X)
    (hDirichlet : q * lambda ≤ 1 / Q) :
    q * T / X ≤ 1 / Real.sqrt Q := by
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hqT : q * T ≤ q * (Real.sqrt Q * lambda * X) :=
    mul_le_mul_of_nonneg_left hT hq
  rw [div_le_iff₀ hX]
  calc
    q * T ≤ q * (Real.sqrt Q * lambda * X) := hqT
    _ = Real.sqrt Q * (q * lambda) * X := by ring
    _ ≤ Real.sqrt Q * (1 / Q) * X := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDirichlet (Real.sqrt_nonneg Q)) hX.le
    _ = (1 / Real.sqrt Q) * X := by
      have hsq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ.le
      field_simp [ne_of_gt hsqrt, ne_of_gt hQ]
      nlinarith

/-- The long complementary length is `O(X/M)`, and the selected beta length
retains the decomposition lower bound `H0`. -/
theorem second_cell_term_le
    {q Q M N H₀ X K₀ : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) (hM : 0 < M) (hH₀ : 0 < H₀)
    (hH₀M : H₀ ≤ M) (hN : 0 ≤ N) (hX : 0 < X) (hK₀ : 0 ≤ K₀)
    (hprod : M * N ≤ K₀ * X) :
    q * N / X ≤ K₀ * Q / H₀ := by
  have hqN : q * N ≤ Q * N := mul_le_mul_of_nonneg_right hqQ hN
  have hMN : H₀ * N ≤ M * N := mul_le_mul_of_nonneg_right hH₀M hN
  rw [div_le_div_iff₀ hX hH₀]
  calc
    q * N * H₀ = H₀ * (q * N) := by ring
    _ ≤ H₀ * (Q * N) := mul_le_mul_of_nonneg_left hqN hH₀.le
    _ = Q * (H₀ * N) := by ring
    _ ≤ Q * (M * N) := by
      exact mul_le_mul_of_nonneg_left hMN (hq.trans hqQ)
    _ ≤ Q * (K₀ * X) := by
      exact mul_le_mul_of_nonneg_left hprod (hq.trans hqQ)
    _ = K₀ * Q * X := by ring

/-- The product term becomes `q/U`; the far threshold then gives `Q/R`. -/
theorem third_cell_term_le
    {q Q M N U R X K₀ : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hU : 0 < U) (hR : 0 < R)
    (hRU : R ≤ U) (hX : 0 < X) (hK₀ : 0 ≤ K₀)
    (hprod : M * N ≤ K₀ * X) :
    q * M * N / (U * X) ≤ K₀ * Q / R := by
  have hQ : 0 ≤ Q := hq.trans hqQ
  rw [div_le_div_iff₀ (mul_pos hU hX) hR]
  calc
    q * M * N * R ≤ q * M * N * U := by
      have hqMN : 0 ≤ q * M * N := by positivity
      exact mul_le_mul_of_nonneg_left hRU hqMN
    _ = q * (M * N) * U := by ring
    _ ≤ q * (K₀ * X) * U := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod hq) hU.le
    _ ≤ Q * (K₀ * X) * U := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hqQ (mul_nonneg hK₀ hX.le)) hU.le
    _ = K₀ * Q * (U * X) := by ring

/-- The final `T` term uses `U = |lambda| H` and `q ≤ Q`. -/
theorem fourth_cell_term_le
    {q Q lambda T U H X : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) (hQ : 0 ≤ Q)
    (hlambda : 0 < lambda) (hH : 0 < H) (hX : 0 < X)
    (hU : U = lambda * H)
    (hT : T ≤ Real.sqrt Q * lambda * X) :
    q * T / (U * X) ≤ (Q * Real.sqrt Q) / H := by
  have hsqrt : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg Q
  have hUpos : 0 < U := by rw [hU]; positivity
  rw [div_le_div_iff₀ (mul_pos hUpos hX) hH]
  have hqT : q * T ≤ q * (Real.sqrt Q * lambda * X) :=
    mul_le_mul_of_nonneg_left hT hq
  calc
    q * T * H ≤ q * (Real.sqrt Q * lambda * X) * H :=
      mul_le_mul_of_nonneg_right hqT hH.le
    _ = (q * Real.sqrt Q) * (lambda * H * X) := by ring
    _ ≤ (Q * Real.sqrt Q) * (lambda * H * X) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hqQ hsqrt) (by positivity)
    _ = (Q * Real.sqrt Q) * (U * X) := by rw [hU]

/-- The exact four-term envelope in (3.7), with the fixed support-comparison
constant `K0` left visible instead of absorbed into Vinogradov notation. -/
def paperFarEnvelope (Q R H H₀ K₀ : ℝ) : ℝ :=
  1 / Real.sqrt Q + K₀ * Q / H₀ + K₀ * Q / R +
    (Q * Real.sqrt Q) / H

/-- Equations (3.6) to (3.7), with every scale hypothesis exposed. -/
theorem paperCellTerms_le_paperFarEnvelope
    {q Q lambda M N T U R H H₀ X K₀ : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) (hQ : 0 < Q)
    (hlambda : 0 < lambda) (hM : 0 < M) (hN : 0 ≤ N)
    (hU : U = lambda * H) (hH : 0 < H)
    (hR : 0 < R) (hRU : R ≤ U)
    (hH₀ : 0 < H₀) (hH₀M : H₀ ≤ M)
    (hX : 0 < X) (hK₀ : 0 ≤ K₀)
    (hT : T ≤ Real.sqrt Q * lambda * X)
    (hDirichlet : q * lambda ≤ 1 / Q)
    (hprod : M * N ≤ K₀ * X) :
    paperCellTerms q M N T U X ≤ paperFarEnvelope Q R H H₀ K₀ := by
  have h1 : q * T / X ≤ 1 / Real.sqrt Q :=
    first_cell_term_le hq hQ hlambda.le hX hT hDirichlet
  have h2 : q * N / X ≤ K₀ * Q / H₀ :=
    second_cell_term_le hq hqQ hM hH₀ hH₀M hN hX hK₀ hprod
  have h3 : q * M * N / (U * X) ≤ K₀ * Q / R :=
    third_cell_term_le hq hqQ hM.le hN (by rw [hU]; positivity)
      hR hRU hX hK₀ hprod
  have h4 : q * T / (U * X) ≤ (Q * Real.sqrt Q) / H :=
    fourth_cell_term_le hq hqQ hQ.le hlambda hH hX hU hT
  unfold paperCellTerms paperFarEnvelope
  linarith

/-- Full Type-d cell weld from the raw Cauchy--Fubini majorant to (3.7).
The only non-algebraic premise left here is `hraw`, whose intended source is
the literal MRT/HB/Perron reduction followed by
`exists_characterPairMixedMass_bound`. -/
theorem stationary_normalization_to_paperFarEnvelope
    {divisorLoss E raw q Q lambda M N T U R H H₀ X K₀ : ℝ}
    (hdiv : 0 ≤ divisorLoss) (hE : 0 ≤ E)
    (hqpos : 0 < q) (hqQ : q ≤ Q) (hQ : 0 < Q)
    (hlambda : 0 < lambda) (hM : 0 < M) (hN : 0 ≤ N)
    (hU : U = lambda * H) (hH : 0 < H)
    (hR : 0 < R) (hRU : R ≤ U)
    (hH₀ : 0 < H₀) (hH₀M : H₀ ≤ M)
    (hX : 0 < X) (hK₀ : 0 ≤ K₀)
    (hT : T ≤ Real.sqrt Q * lambda * X)
    (hDirichlet : q * lambda ≤ 1 / Q)
    (hprod : M * N ≤ K₀ * X)
    (hraw : raw ≤ U * q ^ 2 * E * (U * T + U * N + M * N + T)) :
    divisorLoss / (q * U ^ 2 * X) * raw ≤
      divisorLoss * E * paperFarEnvelope Q R H H₀ K₀ := by
  have hUpos : 0 < U := by rw [hU]; positivity
  have hnorm := stationary_normalization_to_paperCellTerms
    hdiv hqpos hUpos hX hraw
  have hscale := paperCellTerms_le_paperFarEnvelope
    hqpos.le hqQ hQ hlambda hM hN hU hH hR hRU hH₀ hH₀M
    hX hK₀ hT hDirichlet hprod
  exact hnorm.trans (mul_le_mul_of_nonneg_left hscale (mul_nonneg hdiv hE))

/-- Premise-free Lemma 2.1 specialized all the way through the MRT
stationary denominator and the paper's far-annulus scale conversion.  This
closes the high Type-`d_j` **model cell** once the source-level reduction has
produced the coefficient arrays and support comparisons appearing here. -/
theorem exists_characterPairMixedMass_stationary_bound
    {c divisorLoss : ℝ} {a k q M N : ℕ}
    (hc : 0 < c) (hk : 1 ≤ k) (hqNat : 1 ≤ q)
    (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hMN : c * (M : ℝ) ^ 2 ≤ (N : ℝ))
    {Q lambda t₀ T U R H H₀ X K₀ : ℝ}
    (hdiv : 0 ≤ divisorLoss) (hqQ : (q : ℝ) ≤ Q) (hQ : 0 < Q)
    (hlambda : 0 < lambda) (hU : U = lambda * H) (hH : 0 < H)
    (hR : 0 < R) (hRU : R ≤ U)
    (hH₀ : 0 < H₀) (hH₀M : H₀ ≤ (M : ℝ))
    (hX : 0 < X) (hK₀ : 0 ≤ K₀)
    (hTone : 1 ≤ T) (hUone : 1 ≤ U)
    (hT : T ≤ Real.sqrt Q * lambda * X)
    (hDirichlet : (q : ℝ) * lambda ≤ 1 / Q)
    (hprod : (M : ℝ) * (N : ℝ) ≤ K₀ * X)
    (beta long : Fin q → Fin q → ℕ → ℂ)
    (hcoeff : ∀ chi chi',
      PaperCoefficientBounds M N a k (beta chi chi') (long chi chi')) :
    ∃ C : ℝ, 0 < C ∧
      divisorLoss / ((q : ℝ) * U ^ 2 * X) *
          characterPairMixedMass q M N beta long t₀ T U ≤
        divisorLoss *
          (C * Real.log (2 * (M : ℝ) * (N : ℝ)) ^
            (4 * a + 2 * max 2 (k * k) + 2)) *
          paperFarEnvelope Q R H H₀ K₀ := by
  obtain ⟨C, hC, hmass⟩ := exists_characterPairMixedMass_bound
    hc hk hM hN hMN hTone hUone beta long hcoeff
  refine ⟨C, hC, ?_⟩
  let E : ℝ := C * Real.log (2 * (M : ℝ) * (N : ℝ)) ^
    (4 * a + 2 * max 2 (k * k) + 2)
  have hlog : 0 ≤ Real.log (2 * (M : ℝ) * (N : ℝ)) := by
    apply Real.log_nonneg
    have hnat : 1 ≤ 2 * M * N :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    exact_mod_cast hnat
  have hE : 0 ≤ E := by
    exact mul_nonneg hC.le (pow_nonneg hlog _)
  have hraw : characterPairMixedMass q M N beta long t₀ T U ≤
      U * (q : ℝ) ^ 2 * E *
        (U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T) := by
    dsimp [E]
    convert hmass using 1 <;> ring
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hqNat)
  exact stationary_normalization_to_paperFarEnvelope
    hdiv hE hqpos hqQ hQ hlambda (by positivity) (by positivity)
    hU hH hR hRU hH₀ hH₀M hX hK₀ hT hDirichlet hprod hraw

end
end MAPFarAnnulusMRT

#print axioms MAPFarAnnulusMRT.two_noShorter_beta_force_square_complement
#print axioms MAPFarAnnulusMRT.exists_characterPairMixedMass_bound
#print axioms MAPFarAnnulusMRT.stationary_normalization_to_paperCellTerms
#print axioms MAPFarAnnulusMRT.first_cell_term_le
#print axioms MAPFarAnnulusMRT.second_cell_term_le
#print axioms MAPFarAnnulusMRT.third_cell_term_le
#print axioms MAPFarAnnulusMRT.fourth_cell_term_le
#print axioms MAPFarAnnulusMRT.paperCellTerms_le_paperFarEnvelope
#print axioms MAPFarAnnulusMRT.stationary_normalization_to_paperFarEnvelope
#print axioms MAPFarAnnulusMRT.exists_characterPairMixedMass_stationary_bound
