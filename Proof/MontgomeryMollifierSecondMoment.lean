import MontgomeryMixedMomentIntegral
import MRTLemma210DyadicMeanSquare
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Full Möbius mollifier second moment

The same-residue Hilbert argument extends from dyadic supports to every
positive integer at most the cutoff: negative normalized logarithms only
improve the exponential weight bound. Character orthogonality therefore
retains the hybrid `q*T + U` scale without a dyadic decomposition loss.

The exact L-series mollifier is identified with its full finite polynomial,
including the unit term. Its coefficient energy costs one harmonic logarithm.
The final interval and Perron-weighted estimates include the principal
character and arbitrary translations, with no analytic source premise.
-/

namespace MAPMontgomeryMollifierSecondMoment
open scoped BigOperators ComplexConjugate Interval Real
open MeasureTheory intervalIntegral Complex
open MontgomeryVaughanFiniteReduction
open MAPMRTLemma210SameResidueHilbert MAPMRTLemma210DyadicMeanSquare
open MAPMRTLemma210OrthogonalityReduction
noncomputable section

theorem normalizedLogWeight_norm_le_two_of_mem_prefix
    {N n : ℕ} (hN : 1 ≤ N) (hn : n ∈ Finset.Icc 1 (2*N))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ‖normalizedLogWeight N n u‖ ≤ 2 := by
  have hn' := Finset.mem_Icc.mp hn
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnu : (n : ℝ) ≤ 2*N := by exact_mod_cast hn'.2
  have hl : Real.log n - Real.log N ≤ Real.log 2 := by
    have h := Real.log_le_log hnp hnu
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hNp.ne'] at h
    linarith
  have hex : u*(Real.log n - Real.log N) ≤ Real.log 2 := by
    by_cases hh : 0 ≤ Real.log n - Real.log N
    · exact (mul_le_mul_of_nonneg_right hu.2 hh).trans (by simpa using hl)
    · exact (mul_nonpos_of_nonneg_of_nonpos hu.1 (le_of_not_ge hh)).trans
        (Real.log_nonneg (by norm_num))
  unfold normalizedLogWeight
  rw [Complex.norm_exp, Complex.ofReal_re]
  rw [← Real.exp_log (by norm_num : (0:ℝ)<2)]
  exact Real.exp_le_exp.mpr hex

theorem normalizedWeightedEnergyOn_le_prefix
    (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) (hN : 1 ≤ N)
    (hsub : ∀ n ∈ S, n ∈ Finset.Icc 1 (2*N))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∑ n ∈ S, ‖normalizedLogWeight N n u * a n‖ ^ 2) ≤
      4 * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  calc
    (∑ n ∈ S, ‖normalizedLogWeight N n u * a n‖ ^ 2) ≤
        ∑ n ∈ S, 4 * ‖a n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hw := normalizedLogWeight_norm_le_two_of_mem_prefix
        hN (hsub n hn) hu
      rw [norm_mul]
      nlinarith [norm_nonneg (normalizedLogWeight N n u), norm_nonneg (a n),
        sq_nonneg (2 * ‖a n‖ - ‖normalizedLogWeight N n u‖ * ‖a n‖)]
    _ = 4 * ∑ n ∈ S, ‖a n‖ ^ 2 := by rw [Finset.mul_sum]

/-- The same-residue logarithmic Hilbert estimate with the source-critical
`N/q` saving.  This closes the first formal leaf identified after character
orthogonality in MRT Lemma 2.10. -/
theorem norm_sameResidueLogHilbertForm_le_prefix
    {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (S : Finset ℕ) (hsub : ∀ n ∈ S, n ∈ Finset.Icc 1 (2*N))
    (hres : ∀ n ∈ S, n % q = r) (a : ℕ → ℂ) :
    ‖sameResidueLogHilbertForm S a‖ ≤
      4 * Real.pi * ((N : ℝ) / (q : ℝ)) *
        ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    have hnIoc := Finset.mem_Icc.mp (hsub n hn)
    omega
  rw [sameResidueLogHilbertForm_eq_normalizedIntegral hN hq S hpos hres a]
  let E : ℝ := ∑ n ∈ S, ‖a n‖ ^ 2
  have hE : 0 ≤ E := by
    unfold E
    positivity
  have hint :
      ‖∫ t in (0 : ℝ)..1,
        residueQuotientHilbertForm q S
          (fun n ↦ normalizedLogWeight N n t * a n)
          (fun m ↦ normalizedLogWeight N m (1 - t) * a m)‖ ≤
        4 * Real.pi * E := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..1, 4 * Real.pi * E := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · filter_upwards with t ht
          have hut : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
          have hu1t : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
            constructor <;> linarith [ht.1, ht.2]
          have hleft := normalizedWeightedEnergyOn_le_prefix N S a hN hsub hut
          have hright := normalizedWeightedEnergyOn_le_prefix N S a hN hsub hu1t
          have hbase := norm_residueQuotientHilbertForm_le hq S hres
            (fun n ↦ normalizedLogWeight N n t * a n)
            (fun m ↦ normalizedLogWeight N m (1 - t) * a m)
          have hsqrt : Real.sqrt (4 * E) = 2 * Real.sqrt E := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
            norm_num
          calc
            _ ≤ Real.pi *
                Real.sqrt (∑ n ∈ S,
                  ‖normalizedLogWeight N n t * a n‖ ^ 2) *
                Real.sqrt (∑ n ∈ S,
                  ‖normalizedLogWeight N n (1 - t) * a n‖ ^ 2) := hbase
            _ ≤ Real.pi * Real.sqrt (4 * E) * Real.sqrt (4 * E) := by
              gcongr
            _ = 4 * Real.pi * E := by
              rw [hsqrt]
              calc
                Real.pi * (2 * Real.sqrt E) * (2 * Real.sqrt E) =
                    4 * Real.pi * Real.sqrt E ^ 2 := by ring
                _ = 4 * Real.pi * E := by rw [Real.sq_sqrt hE]
        · exact intervalIntegrable_const
      _ = 4 * Real.pi * E := by simp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hscale : ‖(N : ℂ) / (q : ℂ)‖ = (N : ℝ) / (q : ℝ) := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  calc
    ‖((N : ℂ) / (q : ℂ)) * ∫ t in (0 : ℝ)..1,
        residueQuotientHilbertForm q S
          (fun n ↦ normalizedLogWeight N n t * a n)
          (fun m ↦ normalizedLogWeight N m (1 - t) * a m)‖ =
        ((N : ℝ) / (q : ℝ)) *
          ‖∫ t in (0 : ℝ)..1,
            residueQuotientHilbertForm q S
              (fun n ↦ normalizedLogWeight N n t * a n)
              (fun m ↦ normalizedLogWeight N m (1 - t) * a m)‖ := by
      rw [norm_mul, hscale]
    _ ≤ ((N : ℝ) / (q : ℝ)) * (4 * Real.pi * E) := by
      exact mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 4 * Real.pi * ((N : ℝ) / (q : ℝ)) *
        ∑ n ∈ S, ‖a n‖ ^ 2 := by
      unfold E
      ring

theorem norm_integratedResiduePacketOffDiagonal_le_prefix
    {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (S : Finset ℕ) (hsub : ∀ n ∈ S, n ∈ Finset.Icc 1 (2*N))
    (hres : ∀ n ∈ S, n % q = r) (a : ℕ → ℂ) (T : ℝ) :
    ‖integratedResiduePacketOffDiagonal S a T‖ ≤
      8 * Real.pi * ((N : ℝ) / (q : ℝ)) * residuePacketEnergy S a := by
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    have hnIoc := Finset.mem_Icc.mp (hsub n hn)
    omega
  rw [integratedResiduePacketOffDiagonal_eq_hilbertDifference S a hpos T,
    norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hmod := norm_sameResidueLogHilbertForm_le_prefix hN hq S hsub hres
    (modulatedCoefficient a T)
  have hbase := norm_sameResidueLogHilbertForm_le_prefix hN hq S hsub hres a
  calc
    ‖sameResidueLogHilbertForm S (modulatedCoefficient a T) -
        sameResidueLogHilbertForm S a‖ ≤
      ‖sameResidueLogHilbertForm S (modulatedCoefficient a T)‖ +
        ‖sameResidueLogHilbertForm S a‖ := norm_sub_le _ _
    _ ≤ 4 * Real.pi * ((N : ℝ) / (q : ℝ)) *
          ∑ n ∈ S, ‖modulatedCoefficient a T n‖ ^ 2 +
        4 * Real.pi * ((N : ℝ) / (q : ℝ)) *
          ∑ n ∈ S, ‖a n‖ ^ 2 := add_le_add hmod hbase
    _ = 8 * Real.pi * ((N : ℝ) / (q : ℝ)) * residuePacketEnergy S a := by
      have henergy := residuePacketEnergy_modulated S a T
      unfold residuePacketEnergy at henergy ⊢
      rw [henergy]
      ring

/-- Continuous mean square for one arithmetic-progression packet. -/
theorem integral_norm_sq_residuePacketPolynomial_le_prefix
    {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (S : Finset ℕ) (hsub : ∀ n ∈ S, n ∈ Finset.Icc 1 (2*N))
    (hres : ∀ n ∈ S, n % q = r) (a : ℕ → ℂ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖residuePacketPolynomial S a t‖ ^ 2) ≤
      (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
        residuePacketEnergy S a := by
  have heqC := integral_residuePacket_square_eq S a T
  have hleft :
      (∫ t in (0 : ℝ)..T,
        residuePacketPolynomial S a t * star (residuePacketPolynomial S a t)) =
      ((∫ t in (0 : ℝ)..T, ‖residuePacketPolynomial S a t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t ht
    change residuePacketPolynomial S a t * conj (residuePacketPolynomial S a t) = _
    rw [Complex.mul_conj, ← Complex.sq_norm]
  rw [hleft] at heqC
  have heqR := congrArg Complex.re heqC
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_im, mul_zero, sub_zero] at heqR
  have hoff := norm_integratedResiduePacketOffDiagonal_le_prefix
    hN hq S hsub hres a T
  have hre := Complex.re_le_norm (integratedResiduePacketOffDiagonal S a T)
  rw [heqR]
  calc
    T * residuePacketEnergy S a +
        (integratedResiduePacketOffDiagonal S a T).re ≤
      T * residuePacketEnergy S a +
        ‖integratedResiduePacketOffDiagonal S a T‖ :=
      add_le_add (le_refl _) hre
    _ ≤ T * residuePacketEnergy S a +
        8 * Real.pi * ((N : ℝ) / (q : ℝ)) * residuePacketEnergy S a :=
      add_le_add (le_refl _) hoff
    _ = (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
        residuePacketEnergy S a := by ring

theorem prefix_character_mean_square_le
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (a : ℕ → ℂ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      ∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q (Finset.Icc 1 N) a chi t‖ ^ 2) ≤
      ((q : ℝ) * T + 8 * Real.pi * (N : ℝ)) * residuePacketEnergy (Finset.Icc 1 N) a := by
  have hq : 0 < q := NeZero.pos q
  rw [integral_character_norm_sq_eq_packet_integrals]
  have hpacket (r : ℕ) (hr : r ∈ Finset.range q) :
      (∫ t in (0 : ℝ)..T,
        ‖residuePacketPolynomial
          (unitResiduePacket q (Finset.Icc 1 N) r) a t‖ ^ 2) ≤
        (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
          residuePacketEnergy (unitResiduePacket q (Finset.Icc 1 N) r) a := by
    apply integral_norm_sq_residuePacketPolynomial_le_prefix hN hq
    · intro n hn
      have hh := Finset.mem_Icc.mp (unitResiduePacket_subset hn)
      exact Finset.mem_Icc.mpr ⟨hh.1, by omega⟩
    · intro n hn
      exact unitResiduePacket_residue hn
    · exact hT
  have hsum :
      (∑ r ∈ Finset.range q,
        ∫ t in (0 : ℝ)..T,
          ‖residuePacketPolynomial
            (unitResiduePacket q (Finset.Icc 1 N) r) a t‖ ^ 2) ≤
      (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
        ∑ r ∈ Finset.range q,
          residuePacketEnergy (unitResiduePacket q (Finset.Icc 1 N) r) a := by
    calc
      _ ≤ ∑ r ∈ Finset.range q,
          (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
            residuePacketEnergy (unitResiduePacket q (Finset.Icc 1 N) r) a := by
        exact Finset.sum_le_sum fun r hr ↦ hpacket r hr
      _ = _ := by rw [Finset.mul_sum]
  have henergy := sum_unitResiduePacket_energy_le hq (Finset.Icc 1 N) a
  have hfactor0 : 0 ≤ T + 8 * Real.pi * ((N : ℝ) / (q : ℝ)) := by positivity
  have hphi0 : (0 : ℝ) ≤ q.totient := by positivity
  have hfirst :
      (q.totient : ℝ) *
          (∑ r ∈ Finset.range q,
            ∫ t in (0 : ℝ)..T,
              ‖residuePacketPolynomial
                (unitResiduePacket q (Finset.Icc 1 N) r) a t‖ ^ 2) ≤
        (q.totient : ℝ) *
          (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
            residuePacketEnergy (Finset.Icc 1 N) a := by
    calc
      _ ≤ (q.totient : ℝ) *
          ((T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
            ∑ r ∈ Finset.range q,
              residuePacketEnergy (unitResiduePacket q (Finset.Icc 1 N) r) a) :=
        mul_le_mul_of_nonneg_left hsum hphi0
      _ ≤ (q.totient : ℝ) *
          ((T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
            residuePacketEnergy (Finset.Icc 1 N) a) := by
        gcongr
        simpa [residuePacketEnergy] using henergy
      _ = _ := by ring
  have hphi : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcoef :
      (q.totient : ℝ) *
          (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) ≤
        (q : ℝ) * T + 8 * Real.pi * (N : ℝ) := by
    have hdiag : (q.totient : ℝ) * T ≤ (q : ℝ) * T := by gcongr
    have hoff : (q.totient : ℝ) *
        (8 * Real.pi * ((N : ℝ) / (q : ℝ))) ≤
        8 * Real.pi * (N : ℝ) := by
      calc
        (q.totient : ℝ) * (8 * Real.pi * ((N : ℝ) / (q : ℝ))) =
            ((q.totient : ℝ) / (q : ℝ)) * (8 * Real.pi * (N : ℝ)) := by
          field_simp
        _ ≤ 1 * (8 * Real.pi * (N : ℝ)) := by
          gcongr
          exact (div_le_one hqR).2 hphi
        _ = _ := one_mul _
    nlinarith
  calc
    _ ≤ (q.totient : ℝ) *
        (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
          residuePacketEnergy (Finset.Icc 1 N) a := hfirst
    _ ≤ ((q : ℝ) * T + 8 * Real.pi * (N : ℝ)) *
        residuePacketEnergy (Finset.Icc 1 N) a := by
      exact mul_le_mul_of_nonneg_right hcoef (by
        unfold residuePacketEnergy
        positivity)

theorem prefix_character_mean_square_interval_le
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (a : ℕ → ℂ)
    (T0 : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in T0..(T0 + T),
      ∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q (Finset.Icc 1 N) a chi t‖ ^ 2) ≤
      ((q : ℝ) * T + 8 * Real.pi * (N : ℝ)) * residuePacketEnergy (Finset.Icc 1 N) a := by
  let F : ℝ → ℝ := fun t ↦
    ∑ chi : DirichletCharacter ℂ q,
      ‖characterPacketPolynomial q (Finset.Icc 1 N) a chi t‖ ^ 2
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := (0 : ℝ)) (b := T) F (-T0)
  have hinterval :
      (∫ t in T0..(T0 + T), F t) =
        ∫ u in (0 : ℝ)..T, F (u + T0) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hshift.symm
  rw [show (∫ t in T0..(T0 + T),
      ∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q (Finset.Icc 1 N) a chi t‖ ^ 2) =
      ∫ t in T0..(T0 + T), F t by rfl]
  rw [hinterval]
  have hpoint (u : ℝ) : F (u + T0) =
      ∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q (Finset.Icc 1 N)
          (modulatedCoefficient a T0) chi u‖ ^ 2 := by
    unfold F
    apply Finset.sum_congr rfl
    intro chi hchi
    rw [add_comm, characterPacketPolynomial_add_eq_modulated]
  rw [intervalIntegral.integral_congr (fun u hu ↦ hpoint u)]
  have hbound := prefix_character_mean_square_le (q := q) hN
    (modulatedCoefficient a T0) hT
  rw [residuePacketEnergy_modulated] at hbound
  exact hbound
theorem prefix_twisted_character_mean_square_interval_le
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (a : ℕ → ℂ)
    (T0 : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in T0..(T0 + T),
      ∑ chi : DirichletCharacter ℂ q,
        ‖twistedFinitePolynomial q (Finset.Icc 1 N) a chi t‖ ^ 2) ≤
      ((q : ℝ) * T + 8 * Real.pi * (N : ℝ)) * residuePacketEnergy (Finset.Icc 1 N) a := by
  let F : ℝ → ℝ := fun t ↦
    ∑ chi : DirichletCharacter ℂ q,
      ‖characterPacketPolynomial q (Finset.Icc 1 N) a chi t‖ ^ 2
  have hreflect := intervalIntegral.integral_comp_sub_left
    (a := T0) (b := T0 + T) F 0
  have hinterval :
      (∫ t in T0..(T0 + T), F (-t)) =
        ∫ u in (-(T0 + T))..(-T0), F u := by
    simpa using hreflect
  calc
    (∫ t in T0..(T0 + T),
      ∑ chi : DirichletCharacter ℂ q,
        ‖twistedFinitePolynomial q (Finset.Icc 1 N) a chi t‖ ^ 2) =
        ∫ t in T0..(T0 + T), F (-t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      unfold F
      apply Finset.sum_congr rfl
      intro chi hchi
      rw [twistedFinitePolynomial_eq_characterPacket_neg]
    _ = ∫ u in (-(T0 + T))..(-T0), F u := hinterval
    _ ≤ ((q : ℝ) * T + 8 * Real.pi * (N : ℝ)) * residuePacketEnergy (Finset.Icc 1 N) a := by
      have h := prefix_character_mean_square_interval_le (q := q)
        hN a (-(T0 + T)) hT
      simpa [F] using h

open MAPMollifierCoefficientIdentity MAPMRTLemma210OrthogonalityReduction
open MAPMontgomeryMixedMomentIntegral

def mollifierSecondCoefficient (U n : ℕ) : ℂ :=
  truncatedMoebius U n * ((Real.sqrt (n : ℝ) : ℂ)⁻¹)

theorem mollifier_eq_twisted_prefix {q : ℕ}
    (chi : DirichletCharacter ℂ q) (U : ℕ) (t : ℝ) :
    mollifier chi U (((1/2 : ℝ):ℂ) + t*I) =
      twistedFinitePolynomial q (Finset.Icc 1 U) (mollifierSecondCoefficient U) chi t := by
  rw [MAPAppendixA4Detector.mollifier_eq_sum_range]
  have hsum : (∑ n ∈ Finset.range (U+1),
      LSeries.term (((chi ·) : ℕ → ℂ) * truncatedMoebius U)
        (((1/2 : ℝ):ℂ) + t*I) n) =
      ∑ n ∈ Finset.Icc 1 U,
      LSeries.term (((chi ·) : ℕ → ℂ) * truncatedMoebius U)
        (((1/2 : ℝ):ℂ) + t*I) n := by
    symm
    apply Finset.sum_subset
    · intro n hn; have := Finset.mem_Icc.mp hn; simp; omega
    · intro n hn hn'; have hn0 : n = 0 := by
        have := Finset.mem_range.mp hn
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn'
        omega
      subst n; simp
  rw [hsum]
  unfold twistedFinitePolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := Finset.mem_Icc.mp hn; omega
  have hnp : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  unfold mollifierSecondCoefficient twistedPhase
  rw [LSeries.term_of_ne_zero hn0]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn0)]
  have hsqrt : ((Real.sqrt (n : ℝ) : ℂ)⁻¹) =
      Complex.exp (-(((1/2 : ℝ):ℂ) * Real.log (n : ℝ))) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnp, Complex.ofReal_exp,
      ← Complex.exp_neg]
    congr 1; push_cast; ring
  rw [hsqrt, div_eq_mul_inv, ← Complex.exp_neg]
  have hex : -(Complex.log (n : ℂ) * ((((1/2 : ℝ):ℂ) + t*I))) =
      -(((1/2 : ℝ):ℂ) * Real.log (n : ℝ)) +
        ((-(t * Real.log (n : ℝ)) : ℝ):ℂ)*I := by
    rw [← Complex.natCast_log]; push_cast; ring
  rw [hex, Complex.exp_add]
  simp only [Pi.mul_apply]
  ring

theorem mollifierSecondCoefficient_energy_le_log (U : ℕ) :
    residuePacketEnergy (Finset.Icc 1 U) (mollifierSecondCoefficient U) ≤
      1 + Real.log U := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 U, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnR : (0:ℝ)<n := by exact_mod_cast (by have := Finset.mem_Icc.mp hn; omega : 0<n)
      have hmu := norm_truncatedMoebius_le_one U n
      unfold mollifierSecondCoefficient
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hnR.le]
      have hs : ‖truncatedMoebius U n‖^2 ≤ 1 := by
        nlinarith [norm_nonneg (truncatedMoebius U n)]
      simpa using mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hnR.le)
    _ = (harmonic U : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log U := harmonic_le_one_add_log U

theorem mollifier_second_moment_interval_le
    {q U : ℕ} [NeZero q] (hU : 1 ≤ U) (T0 : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in T0..(T0+T), ∑ chi : DirichletCharacter ℂ q,
      criticalLineMollifierNorm chi U t ^ 2) ≤
      ((q : ℝ)*T + 8*Real.pi*(U : ℝ)) * (1 + Real.log U) := by
  have h := prefix_twisted_character_mean_square_interval_le (q := q)
    hU (mollifierSecondCoefficient U) T0 hT
  simp only [criticalLineMollifierNorm, mollifier_eq_twisted_prefix]
  exact h.trans (mul_le_mul_of_nonneg_left
    (mollifierSecondCoefficient_energy_le_log U) (by positivity))

/-- Arbitrary compact continuous weights, with their exact uniform bound. -/
theorem mollifier_second_moment_weighted_interval_le
    {q U : ℕ} [NeZero q] (hU : 1 ≤ U) (T0 : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {w : ℝ → ℝ} (hw : Continuous w) {W : ℝ} (hW : 0 ≤ W)
    (hwW : ∀ t ∈ Set.Icc T0 (T0+T), w t ≤ W) :
    (∫ t in T0..(T0+T), w t * ∑ chi : DirichletCharacter ℂ q,
      criticalLineMollifierNorm chi U t ^ 2) ≤
      W * (((q : ℝ)*T + 8*Real.pi*(U : ℝ)) * (1 + Real.log U)) := by
  have hc : Continuous (fun t => ∑ chi : DirichletCharacter ℂ q,
      criticalLineMollifierNorm chi U t ^ 2) := by
    apply continuous_finsetSum
    intro chi hchi
    exact (continuous_criticalLineMollifierNorm chi U).pow 2
  calc
    _ ≤ ∫ t in T0..(T0+T), W * ∑ chi : DirichletCharacter ℂ q,
        criticalLineMollifierNorm chi U t ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((hw.mul hc).intervalIntegrable _ _) ((continuous_const.mul hc).intervalIntegrable _ _)
      intro t ht
      exact mul_le_mul_of_nonneg_right (hwW t ht) (by positivity)
    _ = W * (∫ t in T0..(T0+T), ∑ chi : DirichletCharacter ℂ q,
        criticalLineMollifierNorm chi U t ^ 2) := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (mollifier_second_moment_interval_le hU T0 hT) hW

open MAPMRTCorollary25Minkowski MAPMRTLemma211AllCharacterSource

/-- The exact shifted Perron weight used by the retained central Gamma integral. -/
theorem sum_mollifier_perronConvolution_le
    {q U : ℕ} [NeZero q] (hU : 1 ≤ U) (t : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    (∑ chi : DirichletCharacter ℂ q,
      perronConvolution (fun s => criticalLineMollifierNorm chi U s ^ 2) B t) ≤
      ((q : ℝ)*(2*B) + 8*Real.pi*(U : ℝ)) * (1 + Real.log U) := by
  simp_rw [perronConvolution_eq_translatedIntegral]
  rw [← intervalIntegral.integral_finsetSum]
  · simp_rw [← Finset.mul_sum]
    have h := mollifier_second_moment_weighted_interval_le (q := q) hU (-B+t)
      (show 0 ≤ 2*B by linarith)
      (w := fun s => perronWeight (s-t))
      (continuous_perronWeight.comp (continuous_id.sub continuous_const))
      (W := 1) (by norm_num) (by
        intro s hs
        unfold perronWeight
        exact (div_le_one (by positivity)).mpr (by linarith [abs_nonneg (s-t)]))
    have he : -B+t+2*B = B+t := by ring
    simpa only [he, one_mul] using h
  · intro chi hchi
    exact ((continuous_perronWeight.comp (continuous_id.sub continuous_const)).mul
      ((continuous_criticalLineMollifierNorm chi U).pow 2)).intervalIntegrable _ _

end
end MAPMontgomeryMollifierSecondMoment

#print axioms MAPMontgomeryMollifierSecondMoment.mollifier_second_moment_interval_le
#print axioms MAPMontgomeryMollifierSecondMoment.sum_mollifier_perronConvolution_le
