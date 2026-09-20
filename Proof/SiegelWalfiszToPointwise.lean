import SiegelWalfiszContract
import PointwiseAbelWeld
import RamanujanTailWeighted
import Mathlib.NumberTheory.Chebyshev

/-!
# Deterministic Siegel--Walfisz to rational-prefix connector

`UniformSiegelWalfiszPsi` is the sole external analytic input in this file.
Everything after it is finite residue algebra, the elementary prime-power
correction, and Abel summation.
-/

namespace MAPSiegelWalfiszToPointwise

open AddCircle Finset Set
open scoped ArithmeticFunction BigOperators
open MAPMajorArcWeld MAPPointwiseMajorArc MAPRamanujanTailWeighted

noncomputable section

theorem rational_phase_comm
    {q : ℕ} [NeZero q] (a r : ℕ) :
    fourier (r : ℤ) (rationalCenter q a) =
      fourier (a : ℤ) (rationalCenter q r) := by
  rw [fourier_rationalCenter_eq_stdAddChar,
    fourier_rationalCenter_eq_stdAddChar]
  rw [mul_comm]

/-- A reduced additive character has Ramanujan sum `mu(q)`. -/
theorem ramanujanCoefficient_neg_of_coprime
    {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    ramanujanCoefficient q (-(a : ℤ)) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  rw [ramanujanCoefficient_eq_moebius_divisorFormula hq0]
  have hmain : (q, 1) ∈ q.divisorsAntidiagonal := by
    simp [Nat.mem_divisorsAntidiagonal, hq0]
  rw [Finset.sum_eq_single (q, 1)]
  · simp
  · intro de hde hneq
    have hprod : de.1 * de.2 = q :=
      (Nat.mem_divisorsAntidiagonal.mp hde).1
    have hde2q : de.2 ∣ q :=
      ⟨de.1, by simpa [mul_comm] using hprod.symm⟩
    have hnotdvd : ¬ (de.2 : ℤ) ∣ -(a : ℤ) := by
      intro hd
      have hde2a : de.2 ∣ a := by
        exact Int.natCast_dvd_natCast.mp (dvd_neg.mp hd)
      have hone : de.2 = 1 := Nat.eq_one_of_dvd_coprimes ha hde2a hde2q
      apply hneq
      apply Prod.ext
      · simpa [hone] using hprod
      · exact hone
    simp [hnotdvd]
  · intro hnot
    exact (hnot hmain).elim

/-- Main-term phase identity in exactly the residue convention of
`sum_rationalRawCoefficient_eq_sum_progressionPsi`. -/
theorem sum_coprime_rational_phase_eq_moebius
    {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    (∑ r ∈ Finset.range q with r.Coprime q,
      fourier (r : ℤ) (rationalCenter q a)) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  rw [← ramanujanCoefficient_neg_of_coprime hq ha]
  unfold ramanujanCoefficient reducedResidues
  apply Finset.sum_congr rfl
  intro r hr
  simpa using (rational_phase_comm (q := q) a r)

/-! ## The non-coprime prime-power correction -/

/-- Mangoldt mass on integers whose residue is not coprime to `q`. -/
def badMangoldtMass (t : ℝ) (q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊t⌋₊).filter (fun n ↦ ¬ n.Coprime q),
    ArithmeticFunction.vonMangoldt n

theorem badMangoldtMass_nonneg (t : ℝ) (q : ℕ) :
    0 ≤ badMangoldtMass t q := by
  unfold badMangoldtMass
  exact Finset.sum_nonneg fun n hn ↦ ArithmeticFunction.vonMangoldt_nonneg

/-- The complete non-prime Mangoldt mass is exactly `psi - theta`. -/
theorem sum_not_prime_vonMangoldt_eq_psi_sub_theta (t : ℝ) :
    (∑ n ∈ (Finset.Ioc 0 ⌊t⌋₊).filter (fun n ↦ ¬ n.Prime),
      ArithmeticFunction.vonMangoldt n) =
      Chebyshev.psi t - Chebyshev.theta t := by
  have hsplit :
      (∑ n ∈ (Finset.Ioc 0 ⌊t⌋₊).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt n) +
        ∑ n ∈ (Finset.Ioc 0 ⌊t⌋₊).filter (fun n ↦ ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n = Chebyshev.psi t := by
    simpa only [Chebyshev.psi] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.Ioc 0 ⌊t⌋₊) Nat.Prime ArithmeticFunction.vonMangoldt)
  have hprime :
      (∑ n ∈ (Finset.Ioc 0 ⌊t⌋₊).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt n) = Chebyshev.theta t := by
    unfold Chebyshev.theta
    apply Finset.sum_congr rfl
    intro p hp
    exact ArithmeticFunction.vonMangoldt_apply_prime
      (Finset.mem_filter.mp hp).2
  linarith

theorem bad_prime_mangoldt_le_log
    {t : ℝ} {q : ℕ} (hq : 1 ≤ q) :
    (∑ n ∈ ((Finset.Ioc 0 ⌊t⌋₊).filter
        (fun n ↦ ¬ n.Coprime q)).filter Nat.Prime,
      ArithmeticFunction.vonMangoldt n) ≤ Real.log q := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hsubset :
      ((Finset.Ioc 0 ⌊t⌋₊).filter
        (fun n ↦ ¬ n.Coprime q)).filter Nat.Prime ⊆ q.divisors := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpbad := (Finset.mem_filter.mp hp'.1).2
    have hpdvd : p ∣ q := by
      exact Classical.byContradiction fun hnot ↦
        hpbad ((hp'.2.coprime_iff_not_dvd).mpr hnot)
    exact Nat.mem_divisors.mpr ⟨hpdvd, hq0⟩
  calc
    (∑ n ∈ ((Finset.Ioc 0 ⌊t⌋₊).filter
        (fun n ↦ ¬ n.Coprime q)).filter Nat.Prime,
      ArithmeticFunction.vonMangoldt n) ≤
        ∑ n ∈ q.divisors, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n hn hnot ↦ ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log q := ArithmeticFunction.vonMangoldt_sum

/-- Every non-coprime contribution is either a prime divisor of `q`, or a
higher prime power.  Mathlib's explicit Chebyshev bound controls the latter. -/
theorem badMangoldtMass_le
    {t : ℝ} {q : ℕ} (ht : 1 ≤ t) (hq : 1 ≤ q) :
    badMangoldtMass t q ≤
      Real.log q + 2 * Real.sqrt t * Real.log t := by
  let S := (Finset.Ioc 0 ⌊t⌋₊).filter (fun n ↦ ¬ n.Coprime q)
  have hsplit : badMangoldtMass t q =
      (∑ n ∈ S.filter Nat.Prime, ArithmeticFunction.vonMangoldt n) +
      ∑ n ∈ S.filter (fun n ↦ ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n := by
    unfold badMangoldtMass S
    exact (Finset.sum_filter_add_sum_filter_not
      ((Finset.Ioc 0 ⌊t⌋₊).filter (fun n ↦ ¬ n.Coprime q))
      Nat.Prime ArithmeticFunction.vonMangoldt).symm
  have hprime :
      (∑ n ∈ S.filter Nat.Prime, ArithmeticFunction.vonMangoldt n) ≤
        Real.log q := by
    simpa only [S] using bad_prime_mangoldt_le_log (t := t) hq
  have hnonprimeSubset :
      S.filter (fun n ↦ ¬ n.Prime) ⊆
        (Finset.Ioc 0 ⌊t⌋₊).filter (fun n ↦ ¬ n.Prime) := by
    intro n hn
    simp only [S, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1.1, hn.2⟩
  have hnonprime :
      (∑ n ∈ S.filter (fun n ↦ ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n) ≤
        Chebyshev.psi t - Chebyshev.theta t := by
    rw [← sum_not_prime_vonMangoldt_eq_psi_sub_theta t]
    exact Finset.sum_le_sum_of_subset_of_nonneg hnonprimeSubset
      (fun n hn hnot ↦ ArithmeticFunction.vonMangoldt_nonneg)
  have hcheb := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log ht
  have hdiff : Chebyshev.psi t - Chebyshev.theta t ≤
      2 * Real.sqrt t * Real.log t :=
    (le_abs_self _).trans hcheb
  rw [hsplit]
  linarith

theorem coprime_mod_left_iff (n q : ℕ) :
    (n % q).Coprime q ↔ n.Coprime q := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one]
  have hgcd : n.gcd q = (n % q).gcd q := by
    calc
      n.gcd q = q.gcd n := Nat.gcd_comm _ _
      _ = (n % q).gcd q := Nat.gcd_rec q n
  rw [hgcd]

/-- Summing the progression functions over non-coprime residue classes gives
exactly the bad Mangoldt mass. -/
theorem sum_bad_progressionPsi_eq_badMangoldtMass
    {q : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    (∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ r.Coprime q),
      APFoundation.progressionPsi t q r) = badMangoldtMass t q := by
  classical
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hsupport : Finset.Icc 1 ⌊t⌋₊ = Finset.Ioc 0 ⌊t⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  unfold APFoundation.progressionPsi badMangoldtMass
  rw [hsupport]
  simp_rw [Finset.sum_filter]
  have hdistribute (r : ℕ) :
      (if ¬ r.Coprime q then
          ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊,
            if n % q = r % q then ArithmeticFunction.vonMangoldt n else 0
        else 0) =
      ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊,
        if ¬ r.Coprime q ∧ n % q = r % q then
          ArithmeticFunction.vonMangoldt n else 0 := by
    by_cases hr : r.Coprime q
    · simp [hr]
    · simp [hr]
  simp_rw [hdistribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hrange : n % q ∈ Finset.range q :=
    Finset.mem_range.mpr (Nat.mod_lt n hqpos)
  rw [Finset.sum_eq_single (n % q)]
  · rw [Nat.mod_eq_of_lt (Nat.mod_lt n hqpos)]
    by_cases hbad : ¬ n.Coprime q
    · have hbadmod : ¬ (n % q).Coprime q := by
        simpa [coprime_mod_left_iff] using hbad
      simp [hbad, hbadmod]
    · simp [hbad]
  · intro r hr hne
    have hrlt := Finset.mem_range.mp hr
    have hrmod : r % q = r := Nat.mod_eq_of_lt hrlt
    have hneq : n % q ≠ r % q := by simpa [hrmod] using hne.symm
    simp [hneq]
  · intro hnot
    exact (hnot hrange).elim

/-- The complex non-coprime residue contribution is bounded by the preceding
positive mass, since every additive-character phase has norm one. -/
theorem norm_sum_bad_residue_contribution_le
    {q a : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    ‖∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ r.Coprime q),
        fourier (r : ℤ) (rationalCenter q a) *
          (APFoundation.progressionPsi t q r : ℂ)‖ ≤
      badMangoldtMass t q := by
  calc
    ‖∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ r.Coprime q),
        fourier (r : ℤ) (rationalCenter q a) *
          (APFoundation.progressionPsi t q r : ℂ)‖ ≤
      ∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ r.Coprime q),
        ‖fourier (r : ℤ) (rationalCenter q a) *
          (APFoundation.progressionPsi t q r : ℂ)‖ := norm_sum_le _ _
    _ = ∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ r.Coprime q),
        APFoundation.progressionPsi t q r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [norm_mul, fourier_apply, Circle.norm_coe, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg]
      unfold APFoundation.progressionPsi
      exact Finset.sum_nonneg fun n hn ↦ by
        split_ifs
        · exact ArithmeticFunction.vonMangoldt_nonneg
        · exact le_rfl
    _ = badMangoldtMass t q := sum_bad_progressionPsi_eq_badMangoldtMass hq t

/-! ## Exact rational-prefix estimate -/

/-- Fixed-parameter deterministic conversion from progression errors to the
rational additive-character prefix error. -/
theorem norm_rationalContinuousPrefixError_le_of_progression
    {q a : ℕ} {t W : ℝ}
    (hq : 1 ≤ q) (ha : a.Coprime q) (hW : 0 ≤ W)
    (hprogression : ∀ r : ℕ, r < q → r.Coprime q →
      |APFoundation.progressionPsi t q r - t / (q.totient : ℝ)| ≤ W) :
    ‖rationalContinuousPrefixError q a t‖ ≤
      (q : ℝ) * W + badMangoldtMass t q := by
  classical
  let good := (Finset.range q).filter (fun r ↦ r.Coprime q)
  let bad := (Finset.range q).filter (fun r ↦ ¬ r.Coprime q)
  let phase : ℕ → ℂ := fun r ↦ fourier (r : ℤ) (rationalCenter q a)
  let psiC : ℕ → ℂ := fun r ↦ (APFoundation.progressionPsi t q r : ℂ)
  let mainC : ℂ := ((t / (q.totient : ℝ) : ℝ) : ℂ)
  have hsplit :
      (∑ r ∈ Finset.range q, phase r * psiC r) =
        (∑ r ∈ good, phase r * psiC r) +
        ∑ r ∈ bad, phase r * psiC r := by
    dsimp [good, bad]
    exact (Finset.sum_filter_add_sum_filter_not
      (Finset.range q) (fun r ↦ r.Coprime q)
      (fun r ↦ phase r * psiC r)).symm
  have hphase : (∑ r ∈ good, phase r) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
    simpa only [good, phase] using sum_coprime_rational_phase_eq_moebius hq ha
  have hmain :
      (∑ r ∈ good, phase r * mainC) =
        primeMajorCoefficient q * (t : ℂ) := by
    calc
      (∑ r ∈ good, phase r * mainC) =
          (∑ r ∈ good, phase r) * mainC := by
        rw [Finset.sum_mul]
      _ = ((ArithmeticFunction.moebius q : ℤ) : ℂ) * mainC := by rw [hphase]
      _ = primeMajorCoefficient q * (t : ℂ) := by
        unfold primeMajorCoefficient mainC
        push_cast
        ring
  have hgoodExact :
      (∑ r ∈ good, phase r * psiC r) -
          primeMajorCoefficient q * (t : ℂ) =
        ∑ r ∈ good, phase r * (psiC r - mainC) := by
    rw [← hmain, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have hgoodNorm :
      ‖(∑ r ∈ good, phase r * psiC r) -
          primeMajorCoefficient q * (t : ℂ)‖ ≤ (q : ℝ) * W := by
    rw [hgoodExact]
    calc
      ‖∑ r ∈ good, phase r * (psiC r - mainC)‖ ≤
          ∑ r ∈ good, ‖phase r * (psiC r - mainC)‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ good, W := by
        apply Finset.sum_le_sum
        intro r hr
        have hr' := Finset.mem_filter.mp hr
        rw [norm_mul]
        have hphaseNorm : ‖phase r‖ = 1 := by
          simp only [phase, fourier_apply, Circle.norm_coe]
        rw [hphaseNorm, one_mul]
        have hcast : psiC r - mainC =
            ((APFoundation.progressionPsi t q r -
              t / (q.totient : ℝ) : ℝ) : ℂ) := by
          simp only [psiC, mainC, Complex.ofReal_sub]
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
        exact hprogression r (Finset.mem_range.mp hr'.1) hr'.2
      _ = (good.card : ℝ) * W := by simp
      _ ≤ (q : ℝ) * W := by
        apply mul_le_mul_of_nonneg_right _ hW
        have hcard : good.card ≤ q := by
          calc
            good.card ≤ (Finset.range q).card := by
              exact Finset.card_filter_le _ _
            _ = q := Finset.card_range q
        exact_mod_cast hcard
  have hbadNorm : ‖∑ r ∈ bad, phase r * psiC r‖ ≤
      badMangoldtMass t q := by
    simpa only [bad, phase, psiC] using
      norm_sum_bad_residue_contribution_le (q := q) (a := a) hq t
  unfold rationalContinuousPrefixError
  rw [sum_rationalRawCoefficient_eq_sum_progressionPsi hq a t]
  change ‖(∑ r ∈ Finset.range q, phase r * psiC r) -
    primeMajorCoefficient q * (t : ℂ)‖ ≤ _
  rw [hsplit]
  have hreassoc :
      (∑ r ∈ good, phase r * psiC r) +
          (∑ r ∈ bad, phase r * psiC r) -
            primeMajorCoefficient q * (t : ℂ) =
        ((∑ r ∈ good, phase r * psiC r) -
            primeMajorCoefficient q * (t : ℂ)) +
          ∑ r ∈ bad, phase r * psiC r := by ring
  rw [hreassoc]
  exact (norm_add_le _ _).trans (add_le_add hgoodNorm hbadNorm)

/-- Exact common prefix envelope after summing the Siegel--Walfisz errors
over reduced residues and retaining the prime-power correction. -/
def rationalPrefixEnvelope (X C : ℝ) (A B : ℕ) : ℝ :=
  (Real.log X) ^ B * (C * X / (Real.log X) ^ A + 1) +
    2 * Real.sqrt (2 * X) * Real.log (2 * X)

theorem rationalPrefixEnvelope_nonneg
    {X C : ℝ} {A B : ℕ} (hX : 2 ≤ X) (hC : 0 ≤ C) :
    0 ≤ rationalPrefixEnvelope X C A B := by
  unfold rationalPrefixEnvelope
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have h2X : 1 ≤ 2 * X := by linarith
  exact add_nonneg
    (mul_nonneg (pow_nonneg hlog0 _)
      (add_nonneg (div_nonneg (mul_nonneg hC (by linarith))
        (pow_nonneg hlog0 _)) zero_le_one))
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.log_nonneg h2X))

/-- The missing connector: uniform Siegel--Walfisz implies a uniform bound
for the exact additive-character prefix used by the Abel theorem. -/
theorem UniformSiegelWalfiszPsi.exists_uniform_rationalPrefix
    (hSW : UniformSiegelWalfiszPsi) (A B : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
      ∀ q a : ℕ,
        1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
        a < q → a.Coprime q →
      ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        ‖rationalContinuousPrefixError q a t‖ ≤
          rationalPrefixEnvelope X C A B := by
  obtain ⟨C, X₀, hC, hX₀, hsw⟩ := hSW.specialize A B
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X hXX₀ q a hq hqL haq hcop t ht
  have hX2 : 2 ≤ X := hX₀.trans hXX₀
  have hXpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  let W : ℝ := C * X / (Real.log X) ^ A
  have hW : 0 ≤ W := by
    dsimp [W]
    exact div_nonneg (mul_nonneg hC.le hXpos.le) (pow_nonneg hlogpos.le _)
  have hprog : ∀ r : ℕ, r < q → r.Coprime q →
      |APFoundation.progressionPsi t q r - t / (q.totient : ℝ)| ≤ W := by
    intro r hr hrcop
    exact hsw X hXX₀ q r hq hqL hr hrcop t ht
  have hfixed := norm_rationalContinuousPrefixError_le_of_progression
    hq hcop hW hprog
  have ht1 : 1 ≤ t := le_trans (by linarith : 1 ≤ X) ht.1
  have hbad := badMangoldtMass_le ht1 hq
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hlogq : Real.log q ≤ (q : ℝ) := Real.log_le_self hqnonneg
  have hcommon : 0 ≤ W + 1 := by linarith
  have hqpart : (q : ℝ) * W + Real.log q ≤
      (Real.log X) ^ B * (W + 1) := by
    calc
      (q : ℝ) * W + Real.log q ≤ (q : ℝ) * W + (q : ℝ) :=
        by linarith
      _ = (q : ℝ) * (W + 1) := by ring
      _ ≤ (Real.log X) ^ B * (W + 1) :=
        mul_le_mul_of_nonneg_right hqL hcommon
  have hsqrt : Real.sqrt t ≤ Real.sqrt (2 * X) :=
    Real.sqrt_le_sqrt ht.2
  have hlogt : Real.log t ≤ Real.log (2 * X) :=
    Real.log_le_log (by linarith) ht.2
  have hsqrt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hsqrt2X0 : 0 ≤ Real.sqrt (2 * X) := Real.sqrt_nonneg _
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlog2X0 : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hprimePower : 2 * Real.sqrt t * Real.log t ≤
      2 * Real.sqrt (2 * X) * Real.log (2 * X) := by
    gcongr
  calc
    ‖rationalContinuousPrefixError q a t‖ ≤
        (q : ℝ) * W + badMangoldtMass t q := hfixed
    _ ≤ (q : ℝ) * W +
        (Real.log q + 2 * Real.sqrt t * Real.log t) :=
      by linarith
    _ = ((q : ℝ) * W + Real.log q) +
        2 * Real.sqrt t * Real.log t := by ring
    _ ≤ (Real.log X) ^ B * (W + 1) +
        2 * Real.sqrt (2 * X) * Real.log (2 * X) :=
      add_le_add hqpart hprimePower
    _ = rationalPrefixEnvelope X C A B := by
      simp only [rationalPrefixEnvelope, W]

/-- Exact common pointwise error inserted into the final major-arc weld. -/
def primePolynomialEnvelope (X C : ℝ) (A B D : ℕ) : ℝ :=
  (2 + X * (2 * Real.pi * paperArcRadius X D)) *
    rationalPrefixEnvelope X C A B

theorem UniformSiegelWalfiszPsi.exists_uniform_primePolynomial
    (hSW : UniformSiegelWalfiszPsi) (A B D : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
      ∀ q a : ℕ, ∀ β : ℝ,
        1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
        a < q → a.Coprime q →
        |β| ≤ paperArcRadius X D →
        ‖PrimePairEndpoints.primeExponentialSum X
            (rationalCenter q a + (β : UnitAddCircle)) -
          primeMajorCoefficient q * MAPMajorArcWeld.dyadicContinuousAmplitude X β‖ ≤
            primePolynomialEnvelope X C A B D := by
  obtain ⟨C, X₀, hC, hX₀, hprefix⟩ :=
    UniformSiegelWalfiszPsi.exists_uniform_rationalPrefix hSW A B
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X hXX₀ q a β hq hqL haq hcop hβ
  have hX2 : 2 ≤ X := hX₀.trans hXX₀
  have hX0 : 0 ≤ X := by linarith
  let E := rationalPrefixEnvelope X C A B
  have hE : 0 ≤ E := rationalPrefixEnvelope_nonneg hX2 hC.le
  have hpref : ∀ t ∈ Set.Icc X (2 * X),
      ‖rationalContinuousPrefixError q a t‖ ≤ E := by
    intro t ht
    exact hprefix X hXX₀ q a hq hqL haq hcop t ht
  have habel := norm_primeExponentialSum_sub_continuous_model_le_of_prefix
    (β := β) hX0 hE q a hpref
  have hR0 : 0 ≤ paperArcRadius X D := by
    unfold paperArcRadius
    exact div_nonneg (pow_nonneg (Real.log_nonneg (by linarith)) _) hX0
  have hbetaPart : X * (2 * Real.pi * |β|) * E ≤
      X * (2 * Real.pi * paperArcRadius X D) * E := by
    gcongr
  unfold primePolynomialEnvelope
  change _ ≤ (2 + X * (2 * Real.pi * paperArcRadius X D)) * E
  calc
    ‖PrimePairEndpoints.primeExponentialSum X
          (rationalCenter q a + (β : UnitAddCircle)) -
        primeMajorCoefficient q * MAPMajorArcWeld.dyadicContinuousAmplitude X β‖ ≤
      2 * E + X * (2 * Real.pi * |β|) * E := habel
    _ ≤ 2 * E + X * (2 * Real.pi * paperArcRadius X D) * E :=
      by linarith
    _ = (2 + X * (2 * Real.pi * paperArcRadius X D)) * E := by ring

end

end MAPSiegelWalfiszToPointwise
