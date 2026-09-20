import MRTLemma210DyadicMeanSquare
import RecenteredSampling

/-!
# Fixed-modulus hybrid character sampling

This file upgrades the premise-free continuous all-character mean square on
one dyadic block to variable one-separated ordinate sets, one set for every
character.  It is the sharp mean-square precursor used inside the hybrid
character large-value input in Montgomery's proof of Theorem 12.1; it does
not by itself claim the Halasz/powering refinement of source Theorem 8.3.

The proof keeps the sharp `q*T + N` scale.  Summing a separate
single-character mean square would lose a factor `q` on the `N` term; instead
we pack the unit intervals separately for each character and only then use
character orthogonality on the two resulting continuous integrals.
-/

namespace MAPMontgomeryHybridCharacterSampling

open scoped BigOperators
open CGLProofDAG
open MontgomeryVaughanFiniteReduction
open MAPMRTLemma210DyadicMeanSquare
open RecenteredSampling

noncomputable section

/-- The recentered character polynomial has the same norm as the original
character polynomial. -/
theorem norm_recentered_characterPolynomial
    {q N : ℕ} (a : ℕ → ℂ) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖recenteredPolynomial (fun n => a n * chi n) N t‖ =
      ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ := by
  rw [norm_recenteredPolynomial]
  rw [dirichletPolynomial_eq]
  rfl

/-- Differentiating after recentering retains one common coefficient sequence
and the same character twist. -/
theorem recenteredDerivative_character_eq
    {q N : ℕ} (a : ℕ → ℂ) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    recenteredDerivative (fun n => a n * chi n) N t =
      recenteredPolynomial
        (fun n => derivativeCoefficient a N n * chi n) N t := by
  rw [recenteredDerivative_eq_recenteredPolynomial]
  unfold recenteredPolynomial derivativeCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Consequently the recentered derivative is measured by the same
all-character mean-square theorem, with the common differentiated
coefficient sequence. -/
theorem norm_recenteredDerivative_character
    {q N : ℕ} (a : ℕ → ℂ) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖recenteredDerivative (fun n => a n * chi n) N t‖ =
      ‖characterPacketPolynomial q (dyadicSupport N)
        (derivativeCoefficient a N) chi t‖ := by
  rw [recenteredDerivative_character_eq, norm_recenteredPolynomial]
  rw [dirichletPolynomial_eq]
  rfl

/-- Variable-set sampling at one fixed modulus.  Every character may carry a
different one-separated ordinate set.  The conclusion retains the sharp
`q*T + N` scale needed in the zero detector. -/
theorem sum_character_sample_norm_sq_le
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (a : ℕ → ℂ)
    {T : ℝ} (hT : 0 ≤ T)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, 0 ≤ t ∧ t ≤ T) :
    (∑ chi : DirichletCharacter ℂ q,
        ∑ t ∈ W chi,
          ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2) ≤
      3 * ((q : ℝ) * (T + 1) + 8 * Real.pi * (N : ℝ)) *
        coefficientEnergy a N := by
  have hsample (chi : DirichletCharacter ℂ q) :
      (∑ t ∈ W chi,
          ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2) ≤
        2 * (∫ x in (0 : ℝ)..T + 1,
          ‖characterPacketPolynomial q (dyadicSupport N) a chi x‖ ^ 2) +
        ∫ x in (0 : ℝ)..T + 1,
          ‖characterPacketPolynomial q (dyadicSupport N)
            (derivativeCoefficient a N) chi x‖ ^ 2 := by
    have hderivCont :
        Continuous (recenteredDerivative (fun n => a n * chi n) N) := by
      unfold recenteredDerivative shiftedPhase shiftedLogFrequency
      fun_prop
    have h := sum_norm_sq_le_collar_energy
      (T := T) (W := W chi)
      (f := recenteredPolynomial (fun n => a n * chi n) N)
      (f' := recenteredDerivative (fun n => a n * chi n) N)
      hT (hasDerivAt_recenteredPolynomial (fun n => a n * chi n) N)
      hderivCont (hsep chi) (hheight chi)
    simpa only [norm_recentered_characterPolynomial,
      norm_recenteredDerivative_character] using h
  have hsum :
      (∑ chi : DirichletCharacter ℂ q,
          ∑ t ∈ W chi,
            ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2) ≤
        ∑ chi : DirichletCharacter ℂ q,
          (2 * (∫ x in (0 : ℝ)..T + 1,
              ‖characterPacketPolynomial q (dyadicSupport N) a chi x‖ ^ 2) +
            ∫ x in (0 : ℝ)..T + 1,
              ‖characterPacketPolynomial q (dyadicSupport N)
                (derivativeCoefficient a N) chi x‖ ^ 2) := by
    exact Finset.sum_le_sum fun chi hchi => hsample chi
  have hbaseSwap :
      (∑ chi : DirichletCharacter ℂ q,
          ∫ x in (0 : ℝ)..T + 1,
            ‖characterPacketPolynomial q (dyadicSupport N) a chi x‖ ^ 2) =
        ∫ x in (0 : ℝ)..T + 1,
          ∑ chi : DirichletCharacter ℂ q,
            ‖characterPacketPolynomial q (dyadicSupport N) a chi x‖ ^ 2 := by
    rw [intervalIntegral.integral_finsetSum]
    intro chi hchi
    apply Continuous.intervalIntegrable
    unfold characterPacketPolynomial phase
    fun_prop
  have hderivSwap :
      (∑ chi : DirichletCharacter ℂ q,
          ∫ x in (0 : ℝ)..T + 1,
            ‖characterPacketPolynomial q (dyadicSupport N)
              (derivativeCoefficient a N) chi x‖ ^ 2) =
        ∫ x in (0 : ℝ)..T + 1,
          ∑ chi : DirichletCharacter ℂ q,
            ‖characterPacketPolynomial q (dyadicSupport N)
              (derivativeCoefficient a N) chi x‖ ^ 2 := by
    rw [intervalIntegral.integral_finsetSum]
    intro chi hchi
    apply Continuous.intervalIntegrable
    unfold characterPacketPolynomial phase derivativeCoefficient
    fun_prop
  have hsumRewrite :
      (∑ chi : DirichletCharacter ℂ q,
          (2 * (∫ x in (0 : ℝ)..T + 1,
              ‖characterPacketPolynomial q (dyadicSupport N) a chi x‖ ^ 2) +
            ∫ x in (0 : ℝ)..T + 1,
              ‖characterPacketPolynomial q (dyadicSupport N)
                (derivativeCoefficient a N) chi x‖ ^ 2)) =
        2 * (∫ x in (0 : ℝ)..T + 1,
          ∑ chi : DirichletCharacter ℂ q,
            ‖characterPacketPolynomial q (dyadicSupport N) a chi x‖ ^ 2) +
        ∫ x in (0 : ℝ)..T + 1,
          ∑ chi : DirichletCharacter ℂ q,
            ‖characterPacketPolynomial q (dyadicSupport N)
              (derivativeCoefficient a N) chi x‖ ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hbaseSwap, hderivSwap]
  have hS : 0 ≤ T + 1 := by linarith
  have hbase := dyadic_character_mean_square_le
    (q := q) hN a hS
  have hderiv := dyadic_character_mean_square_le
    (q := q) hN (derivativeCoefficient a N) hS
  have henergy := coefficientEnergy_derivativeCoefficient_le a N hN
  have hfactor0 :
      0 ≤ (q : ℝ) * (T + 1) + 8 * Real.pi * (N : ℝ) := by positivity
  have hderiv' :
      (∫ x in (0 : ℝ)..T + 1,
        ∑ chi : DirichletCharacter ℂ q,
          ‖characterPacketPolynomial q (dyadicSupport N)
            (derivativeCoefficient a N) chi x‖ ^ 2) ≤
        ((q : ℝ) * (T + 1) + 8 * Real.pi * (N : ℝ)) *
          coefficientEnergy a N := by
    exact hderiv.trans (mul_le_mul_of_nonneg_left henergy hfactor0)
  calc
    (∑ chi : DirichletCharacter ℂ q,
        ∑ t ∈ W chi,
          ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2) ≤
      ∑ chi : DirichletCharacter ℂ q,
        (2 * (∫ x in (0 : ℝ)..T + 1,
            ‖characterPacketPolynomial q (dyadicSupport N) a chi x‖ ^ 2) +
          ∫ x in (0 : ℝ)..T + 1,
            ‖characterPacketPolynomial q (dyadicSupport N)
              (derivativeCoefficient a N) chi x‖ ^ 2) := hsum
    _ = 2 * (∫ x in (0 : ℝ)..T + 1,
          ∑ chi : DirichletCharacter ℂ q,
            ‖characterPacketPolynomial q (dyadicSupport N) a chi x‖ ^ 2) +
        ∫ x in (0 : ℝ)..T + 1,
          ∑ chi : DirichletCharacter ℂ q,
            ‖characterPacketPolynomial q (dyadicSupport N)
              (derivativeCoefficient a N) chi x‖ ^ 2 := hsumRewrite
    _ ≤ 2 *
          (((q : ℝ) * (T + 1) + 8 * Real.pi * (N : ℝ)) *
            coefficientEnergy a N) +
        (((q : ℝ) * (T + 1) + 8 * Real.pi * (N : ℝ)) *
          coefficientEnergy a N) := by gcongr
    _ = 3 * ((q : ℝ) * (T + 1) + 8 * Real.pi * (N : ℝ)) *
          coefficientEnergy a N := by ring

/-- Large-value cardinality consequence in the exact variable-character
sampling geometry. -/
theorem sum_character_card_le_of_large_values
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (a : ℕ → ℂ)
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, 0 ≤ t ∧ t ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      3 * ((q : ℝ) * (T + 1) + 8 * Real.pi * (N : ℝ)) *
        coefficientEnergy a N := by
  have hleft :
      (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
        ∑ chi : DirichletCharacter ℂ q,
          ∑ t ∈ W chi,
            ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro chi hchi
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro t ht
    have hv := hlarge chi t ht
    have hnorm : 0 ≤
        ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ :=
      norm_nonneg _
    norm_num
    nlinarith
  exact hleft.trans
    (sum_character_sample_norm_sq_le hN a hT W hsep hheight)

/-! ## Symmetric-height form -/

/-- Translate all character ordinate sets by the same height. -/
def shiftedCharacterSamples
    {q : ℕ} (W : DirichletCharacter ℂ q → Finset ℝ) (T : ℝ)
    (chi : DirichletCharacter ℂ q) : Finset ℝ :=
  (W chi).image fun t => t + T

/-- One common coefficient modulation implements the same translation for
every character. -/
def shiftedPacketCoefficient (a : ℕ → ℂ) (T : ℝ) (n : ℕ) : ℂ :=
  a n * phase n (-T)

theorem characterPacketPolynomial_shifted
    {q : ℕ} (S : Finset ℕ) (a : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (T t : ℝ) :
    characterPacketPolynomial q S (shiftedPacketCoefficient a T) chi (t + T) =
      characterPacketPolynomial q S a chi t := by
  unfold characterPacketPolynomial shiftedPacketCoefficient phase
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (a n * Complex.exp ((((-T) * Real.log n : ℝ) : ℂ) * Complex.I) *
        chi n) *
        Complex.exp ((((t + T) * Real.log n : ℝ) : ℂ) * Complex.I) =
      (a n * chi n) *
        (Complex.exp ((((-T) * Real.log n : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((((t + T) * Real.log n : ℝ) : ℂ) * Complex.I)) := by
        ring
    _ = (a n * chi n) *
        Complex.exp
          ((((-T) * Real.log n : ℝ) : ℂ) * Complex.I +
            ((((t + T) * Real.log n : ℝ) : ℂ) * Complex.I)) := by
      rw [Complex.exp_add]
    _ = a n * chi n *
        Complex.exp ((((t * Real.log n : ℝ) : ℂ) * Complex.I)) := by
      congr 2
      push_cast
      ring

theorem coefficientEnergy_shiftedPacketCoefficient
    (a : ℕ → ℂ) (T : ℝ) (N : ℕ) :
    coefficientEnergy (shiftedPacketCoefficient a T) N =
      coefficientEnergy a N := by
  unfold coefficientEnergy shiftedPacketCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  rw [norm_mul, show ‖phase n (-T)‖ = 1 by
    unfold phase
    exact Complex.norm_exp_ofReal_mul_I _]
  ring

theorem shiftedCharacterSamples_oneSeparated
    {q : ℕ} (W : DirichletCharacter ℂ q → Finset ℝ) (T : ℝ)
    (hsep : ∀ chi, OneSeparated (W chi)) :
    ∀ chi, OneSeparated (shiftedCharacterSamples W T chi) := by
  intro chi u hu v hv huv
  rw [shiftedCharacterSamples, Finset.mem_image] at hu hv
  obtain ⟨t, ht, rfl⟩ := hu
  obtain ⟨s, hs, rfl⟩ := hv
  have hts : t ≠ s := by
    intro h
    apply huv
    rw [h]
  simpa only [add_sub_add_right_eq_sub] using hsep chi t ht s hs hts

theorem shiftedCharacterSamples_height
    {q : ℕ} (W : DirichletCharacter ℂ q → Finset ℝ) {T : ℝ}
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T) :
    ∀ chi, ∀ u ∈ shiftedCharacterSamples W T chi,
      0 ≤ u ∧ u ≤ 2 * T := by
  intro chi u hu
  rw [shiftedCharacterSamples, Finset.mem_image] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  have habs := abs_le.mp (hheight chi t ht)
  constructor <;> linarith

theorem sum_shiftedCharacterSamples
    {q : ℕ} (W : DirichletCharacter ℂ q → Finset ℝ) (T : ℝ)
    (F : DirichletCharacter ℂ q → ℝ → ℝ) :
    (∑ chi : DirichletCharacter ℂ q,
        ∑ u ∈ shiftedCharacterSamples W T chi, F chi u) =
      ∑ chi : DirichletCharacter ℂ q,
        ∑ t ∈ W chi, F chi (t + T) := by
  apply Finset.sum_congr rfl
  intro chi hchi
  unfold shiftedCharacterSamples
  rw [Finset.sum_image]
  intro x hx y hy hxy
  linarith

/-- Symmetric-height version of the sharp hybrid character sampler. -/
theorem sum_character_sample_norm_sq_le_symmetric
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (a : ℕ → ℂ)
    {T : ℝ} (hT : 0 ≤ T)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T) :
    (∑ chi : DirichletCharacter ℂ q,
        ∑ t ∈ W chi,
          ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2) ≤
      3 * ((q : ℝ) * (2 * T + 1) + 8 * Real.pi * (N : ℝ)) *
        coefficientEnergy a N := by
  have hs := sum_character_sample_norm_sq_le hN
    (shiftedPacketCoefficient a T) (by linarith : 0 ≤ 2 * T)
    (shiftedCharacterSamples W T)
    (shiftedCharacterSamples_oneSeparated W T hsep)
    (shiftedCharacterSamples_height W hheight)
  rw [sum_shiftedCharacterSamples W T
    (fun chi u =>
      ‖characterPacketPolynomial q (dyadicSupport N)
        (shiftedPacketCoefficient a T) chi u‖ ^ 2)] at hs
  simpa only [characterPacketPolynomial_shifted,
    coefficientEnergy_shiftedPacketCoefficient] using hs

/-- Symmetric-height large-value cardinality consequence. -/
theorem sum_character_card_le_of_large_values_symmetric
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (a : ℕ → ℂ)
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      3 * ((q : ℝ) * (2 * T + 1) + 8 * Real.pi * (N : ℝ)) *
        coefficientEnergy a N := by
  have hleft :
      (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
        ∑ chi : DirichletCharacter ℂ q,
          ∑ t ∈ W chi,
            ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro chi hchi
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro t ht
    have hv := hlarge chi t ht
    have hn := norm_nonneg
      (characterPacketPolynomial q (dyadicSupport N) a chi t)
    norm_num
    nlinarith
  exact hleft.trans
    (sum_character_sample_norm_sq_le_symmetric hN a hT W hsep hheight)

end
end MAPMontgomeryHybridCharacterSampling

#print axioms MAPMontgomeryHybridCharacterSampling.norm_recentered_characterPolynomial
#print axioms MAPMontgomeryHybridCharacterSampling.recenteredDerivative_character_eq
#print axioms MAPMontgomeryHybridCharacterSampling.sum_character_sample_norm_sq_le
#print axioms MAPMontgomeryHybridCharacterSampling.sum_character_card_le_of_large_values
#print axioms MAPMontgomeryHybridCharacterSampling.characterPacketPolynomial_shifted
#print axioms MAPMontgomeryHybridCharacterSampling.sum_character_sample_norm_sq_le_symmetric
#print axioms MAPMontgomeryHybridCharacterSampling.sum_character_card_le_of_large_values_symmetric
