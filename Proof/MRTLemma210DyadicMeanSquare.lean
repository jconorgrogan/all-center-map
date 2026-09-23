import MRTLemma210OrthogonalityReduction
import MRTLemma210SameResidueHilbert

/-!
# MRT Lemma 2.10 on one dyadic block

This file welds the exact character-orthogonality identity to the
same-residue logarithmic Hilbert theorem.  The result is the source-critical
`q*T + N` mean-square scale on `(N,2N]`, with no analytic premise.
-/

namespace MAPMRTLemma210DyadicMeanSquare

open scoped BigOperators ComplexConjugate Interval Real
open MeasureTheory intervalIntegral Complex
open MontgomeryVaughanFiniteReduction
open MAPMRTLemma210OrthogonalityReduction
open MAPMRTLemma210SameResidueHilbert

noncomputable section

local instance classicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def unitResiduePacket (q : ℕ) (S : Finset ℕ) (r : ℕ) : Finset ℕ := by
  classical
  exact S.filter fun n ↦ IsUnit (n : ZMod q) ∧ n % q = r

theorem unitResiduePacket_subset
    {q : ℕ} {S : Finset ℕ} {r n : ℕ}
    (hn : n ∈ unitResiduePacket q S r) : n ∈ S := by
  exact (Finset.mem_filter.mp hn).1

theorem unitResiduePacket_residue
    {q : ℕ} {S : Finset ℕ} {r n : ℕ}
    (hn : n ∈ unitResiduePacket q S r) : n % q = r := by
  exact (Finset.mem_filter.mp hn).2.2

theorem characterPairMask_iff_nat
    {q n m : ℕ} :
    characterPairMask q n m ↔
      IsUnit (m : ZMod q) ∧ m % q = n % q := by
  unfold characterPairMask
  rw [ZMod.natCast_eq_natCast_iff']

theorem unit_of_same_residue
    {q n m : ℕ} (hm : IsUnit (m : ZMod q)) (hmod : m % q = n % q) :
    IsUnit (n : ZMod q) := by
  have heq : (m : ZMod q) = (n : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff' m n q).2 hmod
  exact heq ▸ hm

private theorem sum_residue_pair_indicator
    {q n m : ℕ} (hq : 0 < q) (z : ℂ) :
    (∑ r ∈ Finset.range q,
        if IsUnit (n : ZMod q) ∧ n % q = r then
          if IsUnit (m : ZMod q) ∧ m % q = r then z else 0
        else 0) =
      if IsUnit (n : ZMod q) ∧ IsUnit (m : ZMod q) ∧ n % q = m % q
      then z else 0 := by
  classical
  by_cases hnunit : IsUnit (n : ZMod q)
  · by_cases hmunit : IsUnit (m : ZMod q)
    · by_cases hmod : n % q = m % q
      · have hnrange : n % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt n hq)
        have hmrange : m % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt m hq)
        simp [hnunit, hmunit, hmod, hnrange, hmrange]
      · have hnrange : n % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt n hq)
        have hmrange : m % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt m hq)
        have hmod' : m % q ≠ n % q := Ne.symm hmod
        simp [hnunit, hmunit, hmod, hmod', hnrange, hmrange]
    · simp [hmunit]
  · simp [hnunit]

/-- The orthogonality mask is exactly the disjoint sum over unit residue
packets. -/
private theorem unitResiduePacket_pair_sum_eq
    {q : ℕ} (S : Finset ℕ) (r : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ unitResiduePacket q S r,
        ∑ m ∈ unitResiduePacket q S r, F n m) =
      ∑ n ∈ S, ∑ m ∈ S,
        if IsUnit (n : ZMod q) ∧ n % q = r then
          if IsUnit (m : ZMod q) ∧ m % q = r then F n m else 0
        else 0 := by
  classical
  unfold unitResiduePacket
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnr : IsUnit (n : ZMod q) ∧ n % q = r
  · rw [if_pos hnr, Finset.sum_filter]
    simp [hnr]
  · rw [if_neg hnr]
    simp [hnr]

theorem masked_pair_sum_eq_sum_unitResiduePackets
    {q : ℕ} (hq : 0 < q) (S : Finset ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ S, ∑ m ∈ S,
        if characterPairMask q n m then F n m else 0) =
      ∑ r ∈ Finset.range q,
        ∑ n ∈ unitResiduePacket q S r,
          ∑ m ∈ unitResiduePacket q S r, F n m := by
  classical
  simp_rw [unitResiduePacket_pair_sum_eq]
  have hreorder :
      (∑ r ∈ Finset.range q,
          ∑ n ∈ S, ∑ m ∈ S,
            if IsUnit (n : ZMod q) ∧ n % q = r then
              if IsUnit (m : ZMod q) ∧ m % q = r then F n m else 0
            else 0) =
        ∑ n ∈ S, ∑ m ∈ S,
          ∑ r ∈ Finset.range q,
            if IsUnit (n : ZMod q) ∧ n % q = r then
              if IsUnit (m : ZMod q) ∧ m % q = r then F n m else 0
            else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.sum_comm]
  calc
    (∑ n ∈ S, ∑ m ∈ S,
        if characterPairMask q n m then F n m else 0) =
      ∑ n ∈ S, ∑ m ∈ S,
        if IsUnit (n : ZMod q) ∧ IsUnit (m : ZMod q) ∧ n % q = m % q
        then F n m else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmask : characterPairMask q n m
      · have hsource := characterPairMask_iff_nat.mp hmask
        have hnunit := unit_of_same_residue hsource.1 hsource.2
        have htarget : IsUnit (n : ZMod q) ∧ IsUnit (m : ZMod q) ∧
            n % q = m % q := ⟨hnunit, hsource.1, hsource.2.symm⟩
        simp [hmask, htarget]
      · have htarget : ¬(IsUnit (n : ZMod q) ∧ IsUnit (m : ZMod q) ∧
            n % q = m % q) := by
          intro h
          apply hmask
          exact characterPairMask_iff_nat.mpr ⟨h.2.1, h.2.2.symm⟩
        simp [hmask, htarget]
    _ = ∑ n ∈ S, ∑ m ∈ S,
        ∑ r ∈ Finset.range q,
          if IsUnit (n : ZMod q) ∧ n % q = r then
            if IsUnit (m : ZMod q) ∧ m % q = r then F n m else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      rw [sum_residue_pair_indicator hq]
    _ = _ := hreorder.symm

def characterPacketPolynomial
    (q : ℕ) (S : Finset ℕ) (a : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ S, (a n * chi n) * phase n t

theorem phase_eq_twistedPhase_neg (n : ℕ) (t : ℝ) :
    phase n t = twistedPhase n (-t) := by
  unfold phase twistedPhase
  congr 1
  push_cast
  ring

theorem characterPacketPolynomial_eq_twisted
    {q : ℕ} (S : Finset ℕ) (a : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    characterPacketPolynomial q S a chi t =
      twistedFinitePolynomial q S a chi (-t) := by
  unfold characterPacketPolynomial twistedFinitePolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [← phase_eq_twistedPhase_neg]

theorem sum_characterPacketPolynomial_norm_sq
    {q : ℕ} [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ((∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q S a chi t‖ ^ 2 : ℝ) : ℂ) =
      (q.totient : ℂ) *
        ∑ n ∈ S, ∑ m ∈ S,
          if characterPairMask q n m then
            (a n * phase n t) * star (a m * phase m t)
          else 0 := by
  have h := sum_twistedFinitePolynomial_norm_sq (q := q) S a (-t)
  simpa only [← characterPacketPolynomial_eq_twisted,
    ← phase_eq_twistedPhase_neg] using h

theorem residuePacketPolynomial_mul_star
    (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    residuePacketPolynomial S a t * star (residuePacketPolynomial S a t) =
      ∑ n ∈ S, ∑ m ∈ S,
        (a n * phase n t) * star (a m * phase m t) := by
  unfold residuePacketPolynomial
  rw [MontgomeryVaughanFiniteReduction.finite_square_expansion]

/-- Pointwise character orthogonality, now expressed as a sum of squared
packet polynomials over the residue classes. -/
theorem sum_character_norm_sq_eq_totient_mul_packet_sum
    {q : ℕ} [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q S a chi t‖ ^ 2 : ℝ) =
      (q.totient : ℝ) *
        ∑ r ∈ Finset.range q,
          ‖residuePacketPolynomial (unitResiduePacket q S r) a t‖ ^ 2 := by
  have hq : 0 < q := NeZero.pos q
  have horth := sum_characterPacketPolynomial_norm_sq (q := q) S a t
  rw [masked_pair_sum_eq_sum_unitResiduePackets hq] at horth
  simp_rw [← residuePacketPolynomial_mul_star] at horth
  have hpacket (r : ℕ) :
      residuePacketPolynomial (unitResiduePacket q S r) a t *
          star (residuePacketPolynomial (unitResiduePacket q S r) a t) =
        ((‖residuePacketPolynomial (unitResiduePacket q S r) a t‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow,
      RCLike.star_def] using!
      (RCLike.mul_conj
        (residuePacketPolynomial (unitResiduePacket q S r) a t))
  simp_rw [hpacket] at horth
  exact_mod_cast horth

theorem sum_unitResiduePacket_energy_eq
    {q : ℕ} (hq : 0 < q) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ r ∈ Finset.range q,
        residuePacketEnergy (unitResiduePacket q S r) a) =
      ∑ n ∈ S, if IsUnit (n : ZMod q) then ‖a n‖ ^ 2 else 0 := by
  classical
  have hreorder :
      (∑ r ∈ Finset.range q, ∑ n ∈ S,
          if IsUnit (n : ZMod q) ∧ n % q = r then ‖a n‖ ^ 2 else 0) =
        ∑ n ∈ S, ∑ r ∈ Finset.range q,
          if IsUnit (n : ZMod q) ∧ n % q = r then ‖a n‖ ^ 2 else 0 := by
    rw [Finset.sum_comm]
  unfold residuePacketEnergy unitResiduePacket
  simp_rw [Finset.sum_filter]
  rw [hreorder]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hunit : IsUnit (n : ZMod q)
  · have hrange : n % q ∈ Finset.range q :=
      Finset.mem_range.mpr (Nat.mod_lt n hq)
    simp [hunit, hrange]
  · simp [hunit]

theorem sum_unitResiduePacket_energy_le
    {q : ℕ} (hq : 0 < q) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ r ∈ Finset.range q,
        residuePacketEnergy (unitResiduePacket q S r) a) ≤
      ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rw [sum_unitResiduePacket_energy_eq hq]
  apply Finset.sum_le_sum
  intro n hn
  split_ifs
  · exact le_rfl
  · positivity

theorem integral_character_norm_sq_eq_packet_integrals
    {q : ℕ} [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
      ∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q S a chi t‖ ^ 2) =
      (q.totient : ℝ) *
        ∑ r ∈ Finset.range q,
          ∫ t in (0 : ℝ)..T,
            ‖residuePacketPolynomial (unitResiduePacket q S r) a t‖ ^ 2 := by
  calc
    _ = ∫ t in (0 : ℝ)..T,
        (q.totient : ℝ) *
          ∑ r ∈ Finset.range q,
            ‖residuePacketPolynomial (unitResiduePacket q S r) a t‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact sum_character_norm_sq_eq_totient_mul_packet_sum S a t
    _ = (q.totient : ℝ) * ∫ t in (0 : ℝ)..T,
        ∑ r ∈ Finset.range q,
          ‖residuePacketPolynomial (unitResiduePacket q S r) a t‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum]
      intro r hr
      apply Continuous.intervalIntegrable
      unfold residuePacketPolynomial phase
      fun_prop

/-- Premise-free one-block form of MRT Lemma 2.10.  The logarithmic loss in
the published statement is not needed for this finite Hilbert proof. -/
theorem dyadic_character_mean_square_le
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (a : ℕ → ℂ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      ∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2) ≤
      ((q : ℝ) * T + 8 * Real.pi * (N : ℝ)) * coefficientEnergy a N := by
  have hq : 0 < q := NeZero.pos q
  rw [integral_character_norm_sq_eq_packet_integrals]
  have hpacket (r : ℕ) (hr : r ∈ Finset.range q) :
      (∫ t in (0 : ℝ)..T,
        ‖residuePacketPolynomial
          (unitResiduePacket q (dyadicSupport N) r) a t‖ ^ 2) ≤
        (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
          residuePacketEnergy (unitResiduePacket q (dyadicSupport N) r) a := by
    apply integral_norm_sq_residuePacketPolynomial_le hN hq
    · intro n hn
      exact unitResiduePacket_subset hn
    · intro n hn
      exact unitResiduePacket_residue hn
    · exact hT
  have hsum :
      (∑ r ∈ Finset.range q,
        ∫ t in (0 : ℝ)..T,
          ‖residuePacketPolynomial
            (unitResiduePacket q (dyadicSupport N) r) a t‖ ^ 2) ≤
      (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
        ∑ r ∈ Finset.range q,
          residuePacketEnergy (unitResiduePacket q (dyadicSupport N) r) a := by
    calc
      _ ≤ ∑ r ∈ Finset.range q,
          (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
            residuePacketEnergy (unitResiduePacket q (dyadicSupport N) r) a := by
        exact Finset.sum_le_sum fun r hr ↦ hpacket r hr
      _ = _ := by rw [Finset.mul_sum]
  have henergy := sum_unitResiduePacket_energy_le hq (dyadicSupport N) a
  have hfactor0 : 0 ≤ T + 8 * Real.pi * ((N : ℝ) / (q : ℝ)) := by positivity
  have hphi0 : (0 : ℝ) ≤ q.totient := by positivity
  have hfirst :
      (q.totient : ℝ) *
          (∑ r ∈ Finset.range q,
            ∫ t in (0 : ℝ)..T,
              ‖residuePacketPolynomial
                (unitResiduePacket q (dyadicSupport N) r) a t‖ ^ 2) ≤
        (q.totient : ℝ) *
          (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
            coefficientEnergy a N := by
    calc
      _ ≤ (q.totient : ℝ) *
          ((T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
            ∑ r ∈ Finset.range q,
              residuePacketEnergy (unitResiduePacket q (dyadicSupport N) r) a) :=
        mul_le_mul_of_nonneg_left hsum hphi0
      _ ≤ (q.totient : ℝ) *
          ((T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
            coefficientEnergy a N) := by
        gcongr
        simpa [coefficientEnergy] using henergy
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
          coefficientEnergy a N := hfirst
    _ ≤ ((q : ℝ) * T + 8 * Real.pi * (N : ℝ)) *
        coefficientEnergy a N := by
      exact mul_le_mul_of_nonneg_right hcoef (by
        unfold coefficientEnergy
        positivity)

theorem phase_add (n : ℕ) (s t : ℝ) :
    phase n (s + t) = phase n s * phase n t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem characterPacketPolynomial_add_eq_modulated
    {q : ℕ} (S : Finset ℕ) (a : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (s t : ℝ) :
    characterPacketPolynomial q S a chi (s + t) =
      characterPacketPolynomial q S (modulatedCoefficient a s) chi t := by
  unfold characterPacketPolynomial modulatedCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  rw [phase_add]
  ring

/-- Translation of the one-block estimate to the arbitrary interval used in
the published Lemma 2.10. -/
theorem dyadic_character_mean_square_interval_le
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (a : ℕ → ℂ)
    (T0 : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in T0..(T0 + T),
      ∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2) ≤
      ((q : ℝ) * T + 8 * Real.pi * (N : ℝ)) * coefficientEnergy a N := by
  let F : ℝ → ℝ := fun t ↦
    ∑ chi : DirichletCharacter ℂ q,
      ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := (0 : ℝ)) (b := T) F (-T0)
  have hinterval :
      (∫ t in T0..(T0 + T), F t) =
        ∫ u in (0 : ℝ)..T, F (u + T0) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hshift.symm
  rw [show (∫ t in T0..(T0 + T),
      ∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2) =
      ∫ t in T0..(T0 + T), F t by rfl]
  rw [hinterval]
  have hpoint (u : ℝ) : F (u + T0) =
      ∑ chi : DirichletCharacter ℂ q,
        ‖characterPacketPolynomial q (dyadicSupport N)
          (modulatedCoefficient a T0) chi u‖ ^ 2 := by
    unfold F
    apply Finset.sum_congr rfl
    intro chi hchi
    rw [add_comm, characterPacketPolynomial_add_eq_modulated]
  rw [intervalIntegral.integral_congr (fun u hu ↦ hpoint u)]
  have hbound := dyadic_character_mean_square_le (q := q) hN
    (modulatedCoefficient a T0) hT
  rw [coefficientEnergy_modulated] at hbound
  exact hbound

theorem twistedFinitePolynomial_eq_characterPacket_neg
    {q : ℕ} (S : Finset ℕ) (a : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    twistedFinitePolynomial q S a chi t =
      characterPacketPolynomial q S a chi (-t) := by
  simpa using (characterPacketPolynomial_eq_twisted S a chi (-t)).symm

/-- Literal dyadic specialization of MRT Lemma 2.10, including its
`n^(-it)` phase and arbitrary starting ordinate `T0`. -/
theorem dyadic_twisted_character_mean_square_interval_le
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N) (a : ℕ → ℂ)
    (T0 : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in T0..(T0 + T),
      ∑ chi : DirichletCharacter ℂ q,
        ‖twistedFinitePolynomial q (dyadicSupport N) a chi t‖ ^ 2) ≤
      ((q : ℝ) * T + 8 * Real.pi * (N : ℝ)) * coefficientEnergy a N := by
  let F : ℝ → ℝ := fun t ↦
    ∑ chi : DirichletCharacter ℂ q,
      ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2
  have hreflect := intervalIntegral.integral_comp_sub_left
    (a := T0) (b := T0 + T) F 0
  have hinterval :
      (∫ t in T0..(T0 + T), F (-t)) =
        ∫ u in (-(T0 + T))..(-T0), F u := by
    simpa using hreflect
  calc
    (∫ t in T0..(T0 + T),
      ∑ chi : DirichletCharacter ℂ q,
        ‖twistedFinitePolynomial q (dyadicSupport N) a chi t‖ ^ 2) =
        ∫ t in T0..(T0 + T), F (-t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      unfold F
      apply Finset.sum_congr rfl
      intro chi hchi
      rw [twistedFinitePolynomial_eq_characterPacket_neg]
    _ = ∫ u in (-(T0 + T))..(-T0), F u := hinterval
    _ ≤ ((q : ℝ) * T + 8 * Real.pi * (N : ℝ)) * coefficientEnergy a N := by
      have h := dyadic_character_mean_square_interval_le (q := q)
        hN a (-(T0 + T)) hT
      simpa [F] using h

end
end MAPMRTLemma210DyadicMeanSquare

#print axioms MAPMRTLemma210DyadicMeanSquare.sum_character_norm_sq_eq_totient_mul_packet_sum
#print axioms MAPMRTLemma210DyadicMeanSquare.dyadic_character_mean_square_le
#print axioms MAPMRTLemma210DyadicMeanSquare.dyadic_twisted_character_mean_square_interval_le
