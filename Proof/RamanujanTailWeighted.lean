import MajorArcPrimePairWeld
import SingularSeriesFiniteFactors

/-!
# Weighted truncation interface for the Ramanujan coefficient

This file does not assume the desired major-arc estimate.  It proves the
functional-analytic tail step that explains the manuscript's `Q^{-1/2}` loss:
a finite coefficient series whose square-root weighted absolute mass is finite
has a `Q^{-1/2}` truncation tail.  The remaining arithmetic work is thereby
reduced to (i) the exact Ramanujan-sum evaluation and Euler-product identity and
(ii) a bound for that weighted mass.

The zero shift is kept separate: `singularSeriesTotal 0 = 0`, whereas the
Ramanujan coefficient at zero is the positive reduced-residue count.  Thus no
uniform theorem including `h=0` can be true without deleting that coordinate,
as the public endpoint already does.
-/

namespace MAPRamanujanTailWeighted

open scoped BigOperators ArithmeticFunction
open MAPMajorArcWeld PrimePairEndpoints ArithmeticFunction

noncomputable section

/-- The literal coefficient at denominator `q`. -/
def literalRamanujanTerm (h : ℤ) (q : ℕ) : ℂ :=
  primeMajorSquareCoefficient q * ramanujanCoefficient q h

/-- Square-root weighted absolute mass of the literal coefficient series. -/
def sqrtWeightedRamanujanMass (h : ℤ) : ℝ :=
  ∑' q : ℕ, Real.sqrt q * ‖literalRamanujanTerm h q‖

@[simp] theorem literalRamanujanTerm_zero_denominator (h : ℤ) :
    literalRamanujanTerm h 0 = 0 := by
  simp [literalRamanujanTerm, primeMajorSquareCoefficient,
    primeMajorCoefficient]

@[simp] theorem ramanujanCoefficient_zero_shift (q : ℕ) :
    ramanujanCoefficient q 0 = q.totient := by
  unfold ramanujanCoefficient
  simp only [neg_zero, fourier_zero, Finset.sum_const, Finset.card_filter,
    nsmul_eq_mul, mul_one]
  norm_cast
  rw [Nat.totient_eq_card_coprime]
  apply congrArg Finset.card
  ext a
  simp [reducedResidues, Nat.coprime_comm]

/-- The public totalization deliberately deletes the forbidden zero shift. -/
@[simp] theorem singularSeriesTotal_zero : singularSeriesTotal 0 = 0 := by
  simp [singularSeriesTotal]

/-- A generic exact square-root weighted tail estimate over naturals.  It is
stated with the finite range `0,...,Q`; the literal `q=0` coefficient vanishes,
so this is exactly the manuscript's range `1 ≤ q ≤ Q` after specialization. -/
theorem norm_tsum_sub_sum_range_le_sqrtWeighted
    (f : ℕ → ℂ)
    (hsqrt : Summable (fun q : ℕ => Real.sqrt q * ‖f q‖))
    (Q : ℕ) :
    ‖(∑' q : ℕ, f q) - ∑ q ∈ Finset.range (Q + 1), f q‖ ≤
      (∑' q : ℕ, Real.sqrt q * ‖f q‖) / Real.sqrt (Q + 1) := by
  have hnorm : Summable (fun q : ℕ => ‖f q‖) := by
    have hdelta : Summable (fun q : ℕ =>
        if q = 0 then ‖f 0‖ else 0) :=
      (hasSum_ite_eq 0 ‖f 0‖).summable
    apply Summable.of_nonneg_of_le (fun q => norm_nonneg (f q))
      (fun q => ?_) (hdelta.add hsqrt)
    by_cases hq : q = 0
    · subst q
      simp
    · simp only [hq, ↓reduceIte, zero_add]
      have hq1 : (1 : ℝ) ≤ Real.sqrt (q : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
      nlinarith [norm_nonneg (f q)]
  have hf : Summable f := hnorm.of_norm
  have hsplit := hf.sum_add_tsum_compl (s := Finset.range (Q + 1))
  have hdiff :
      (∑' q : ℕ, f q) - ∑ q ∈ Finset.range (Q + 1), f q =
        ∑' q : {q : ℕ // q ∉ Finset.range (Q + 1)}, f q := by
    rw [← hsplit]
    abel
  rw [hdiff]
  have hsubsqrt : Summable (fun q : {q : ℕ // q ∉ Finset.range (Q + 1)} =>
      Real.sqrt (q : ℝ) * ‖f q‖) :=
    hsqrt.subtype {q : ℕ | q ∉ Finset.range (Q + 1)}
  have hsubnorm : Summable (fun q : {q : ℕ // q ∉ Finset.range (Q + 1)} =>
      ‖f q‖) := hnorm.subtype _
  calc
    ‖∑' q : {q : ℕ // q ∉ Finset.range (Q + 1)}, f q‖ ≤
        ∑' q : {q : ℕ // q ∉ Finset.range (Q + 1)}, ‖f q‖ :=
      norm_tsum_le_tsum_norm hsubnorm
    _ ≤ ∑' q : {q : ℕ // q ∉ Finset.range (Q + 1)},
        (Real.sqrt (q : ℝ) * ‖f q‖) / Real.sqrt (Q + 1) := by
      apply Summable.tsum_le_tsum
      · intro q
        have hq : Q + 1 ≤ q := by
          simpa [Finset.mem_range, Nat.not_lt] using q.2
        have hsqrtpos : 0 < Real.sqrt ((Q : ℝ) + 1) :=
          Real.sqrt_pos.2 (by positivity)
        have hsqrtle : Real.sqrt ((Q : ℝ) + 1) ≤
            Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hq)
        apply (le_div_iff₀ hsqrtpos).2
        nlinarith [norm_nonneg (f q)]
      · exact hsubnorm
      · exact hsubsqrt.div_const _
    _ ≤ (∑' q : ℕ, Real.sqrt q * ‖f q‖) / Real.sqrt (Q + 1) := by
      rw [tsum_div_const]
      exact div_le_div_of_nonneg_right
        (Summable.tsum_subtype_le
          (fun q : ℕ => Real.sqrt q * ‖f q‖)
          {q : ℕ | q ∉ Finset.range (Q + 1)}
          (fun _ => by positivity) hsqrt)
        (Real.sqrt_nonneg _)

/-- The finite range in `truncatedSingularCoefficient` is the range through
`Q`, since the zero-denominator term is exactly zero. -/
theorem truncatedSingularCoefficient_eq_sum_range (Q : ℕ) (h : ℤ) :
    truncatedSingularCoefficient Q h =
      ∑ q ∈ Finset.range (Q + 1), literalRamanujanTerm h q := by
  unfold truncatedSingularCoefficient literalRamanujanTerm
  have hfin : (Finset.range (Q + 1)).erase 0 = Finset.Icc 1 Q := by
    ext q
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [← hfin]
  have hs := Finset.sum_erase_add
    (s := Finset.range (Q + 1)) (f := fun q =>
      primeMajorSquareCoefficient q * ramanujanCoefficient q h)
    (by simp : 0 ∈ Finset.range (Q + 1))
  have hzero :
      primeMajorSquareCoefficient 0 * ramanujanCoefficient 0 h = 0 := by
    simp [primeMajorSquareCoefficient, primeMajorCoefficient]
  calc
    (∑ q ∈ (Finset.range (Q + 1)).erase 0,
        primeMajorSquareCoefficient q * ramanujanCoefficient q h) =
      (∑ q ∈ (Finset.range (Q + 1)).erase 0,
        primeMajorSquareCoefficient q * ramanujanCoefficient q h) +
          primeMajorSquareCoefficient 0 * ramanujanCoefficient 0 h := by
            rw [hzero, add_zero]
    _ = _ := hs

/-- Literal `Q^{-1/2}` truncation theorem, conditional only on absolute
square-root weighted summability and the exact full-series identity.  Neither
hypothesis is the desired tail estimate: both are strictly local arithmetic
facts about the denominator coefficients. -/
theorem norm_truncatedSingularCoefficient_sub_singular_le
    {h : ℤ} (hh : h ≠ 0)
    (hsqrt : Summable (fun q : ℕ =>
      Real.sqrt q * ‖literalRamanujanTerm h q‖))
    (hfull : (∑' q : ℕ, literalRamanujanTerm h q) =
      ((singularSeries ⟨h, hh⟩ : ℝ) : ℂ))
    (Q : ℕ) :
    ‖truncatedSingularCoefficient Q h -
        ((singularSeriesTotal h : ℝ) : ℂ)‖ ≤
      sqrtWeightedRamanujanMass h / Real.sqrt (Q + 1) := by
  have htail := norm_tsum_sub_sum_range_le_sqrtWeighted
    (literalRamanujanTerm h) hsqrt Q
  rw [hfull] at htail
  rw [singularSeriesTotal, dif_pos hh]
  rw [truncatedSingularCoefficient_eq_sum_range]
  simpa [sqrtWeightedRamanujanMass, norm_sub_rev] using htail




/-- Exact denominator-two coefficient.  This is the parity-sensitive Euler
factor which forces the odd-shift singular series to vanish. -/
theorem ramanujanCoefficient_two (h : ℤ) :
    ramanujanCoefficient 2 h =
      Complex.exp (-(Real.pi * Complex.I * h)) := by
  rw [show ramanujanCoefficient 2 h =
      fourier (-h) (rationalCenter 2 1) by
    have hs : (Finset.range 2).filter (fun a => a.Coprime 2) = {1} := by decide
    rw [ramanujanCoefficient, reducedResidues, hs]
    simp]
  unfold rationalCenter
  rw [fourier_coe_apply]
  push_cast
  norm_num
  congr 1
  ring

/-- Odd shifts have the exact local coefficient `c₂(h)=-1`. -/
theorem ramanujanCoefficient_two_of_odd
    {h : ℤ} (hh : ¬ (2 : ℤ) ∣ h) :
    ramanujanCoefficient 2 h = -1 := by
  rw [ramanujanCoefficient_two]
  have hodd : Odd h := Int.not_even_iff_odd.mp (by
    simpa only [even_iff_two_dvd] using hh)
  rcases hodd with ⟨k, hk⟩
  rw [hk]
  push_cast
  have heq : -(Real.pi * Complex.I * ((2 : ℂ) * k + 1)) =
      ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
        -(Real.pi * Complex.I) := by
    rw [Int.cast_neg]
    ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  rw [show Complex.exp (-(Real.pi * Complex.I)) = -1 by
    rw [Complex.exp_neg]
    simp]
  norm_num

/-- At zero shift the very first truncated coefficient is already `1`, while
the public totalized singular series is `0`.  This gives a kernel-checked death
test for any purported Ramanujan-tail theorem quantified over `h = 0`. -/
theorem truncatedSingularCoefficient_one_zero :
    truncatedSingularCoefficient 1 0 = 1 := by
  simp [truncatedSingularCoefficient, primeMajorSquareCoefficient,
    primeMajorCoefficient, ramanujanCoefficient_zero_shift,
    ArithmeticFunction.moebius_apply_one]

theorem zero_shift_truncation_error_at_one :
    ‖truncatedSingularCoefficient 1 0 -
        ((singularSeriesTotal 0 : ℝ) : ℂ)‖ = 1 := by
  rw [truncatedSingularCoefficient_one_zero, singularSeriesTotal_zero]
  norm_num

/-- If the denominator divides the shift, every reduced-residue phase is one.
This is the positive local branch of the classical Ramanujan-sum formula. -/
theorem ramanujanCoefficient_eq_totient_of_dvd
    {q : ℕ} (hq : q ≠ 0) {h : ℤ} (hdiv : (q : ℤ) ∣ h) :
    ramanujanCoefficient q h = q.totient := by
  rcases hdiv with ⟨k, rfl⟩
  unfold ramanujanCoefficient
  have hphase : ∀ a : ℕ,
      fourier (-((q : ℤ) * k)) (rationalCenter q a) = 1 := by
    intro a
    unfold rationalCenter
    rw [fourier_coe_apply]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    norm_num
    push_cast
    have hexp :
        -(2 * (Real.pi : ℂ) * Complex.I *
              ((q : ℂ) * (k : ℂ)) * ((a : ℂ) / (q : ℂ))) =
          ((-(k * (a : ℤ)) : ℤ) : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      field_simp [hqR, hqC]
    rw [hexp, Complex.exp_int_mul_two_pi_mul_I]
  simp_rw [hphase]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  norm_cast
  rw [Nat.totient_eq_card_coprime]
  apply congrArg Finset.card
  ext a
  simp [reducedResidues, Nat.coprime_comm]


/-! ## Exact finite Ramanujan-sum evaluation -/

def ramanujanRoot (q : ℕ) (h : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(h : ℂ)) / (q : ℂ))

theorem phase_eq_pow {q : ℕ} (hq : q ≠ 0) (h : ℤ) (a : ℕ) :
    fourier (-h) (rationalCenter q a) = ramanujanRoot q h ^ a := by
  unfold rationalCenter ramanujanRoot
  rw [fourier_coe_apply, ← Complex.exp_nat_mul]
  push_cast
  norm_num
  congr 1
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  field_simp [hqC]

theorem ramanujanRoot_pow_q {q : ℕ} (hq : q ≠ 0) (h : ℤ) : ramanujanRoot q h ^ q = 1 := by
  unfold ramanujanRoot
  rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_int_mul_two_pi_mul_I (-h)]
  congr 1
  push_cast
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  field_simp [hqC]

theorem ramanujanRoot_ne_one {q : ℕ} (hq : q ≠ 0) {h : ℤ} (hnd : ¬(q : ℤ) ∣ h) : ramanujanRoot q h ≠ 1 := by
  intro heq
  rw [ramanujanRoot, Complex.exp_eq_one_iff] at heq
  rcases heq with ⟨n, hn⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) this) Complex.I_ne_zero
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hratio : -(h : ℂ) / (q : ℂ) = (n : ℂ) := by
    apply (mul_left_cancel₀ hpi)
    calc
      (2 * (Real.pi : ℂ) * Complex.I) * (-(h : ℂ) / (q : ℂ)) =
          2 * (Real.pi : ℂ) * Complex.I * (-(h : ℂ)) / (q : ℂ) := by ring
      _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
      _ = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by ring
  have hc : -(h : ℂ) = (n : ℂ) * (q : ℂ) :=
    (div_eq_iff hqC).mp hratio
  have hcast : -(h : ℤ) = (q : ℤ) * n := by
    exact_mod_cast (show -(h : ℂ) = (q : ℂ) * (n : ℂ) by
      rw [hc]
      ring)
  apply hnd
  refine ⟨-n, ?_⟩
  calc
    h = -(-h) := by ring
    _ = -((q : ℤ) * n) := by rw [hcast]
    _ = (q : ℤ) * (-n) := by ring

def completeResidueSum (q : ℕ) (h : ℤ) : ℂ := ∑ a ∈ Finset.range q, fourier (-h) (rationalCenter q a)

theorem completeResidueSum_eq {q : ℕ} (hq : q ≠ 0) (h : ℤ) :
    completeResidueSum q h = if (q : ℤ) ∣ h then q else 0 := by
  unfold completeResidueSum
  simp_rw [phase_eq_pow hq]
  by_cases hd : (q : ℤ) ∣ h
  · rw [if_pos hd]
    have hr : ramanujanRoot q h = 1 := by
      rcases hd with ⟨k, rfl⟩
      unfold ramanujanRoot
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (-((q : ℤ) * k : ℤ) : ℂ) / (q : ℂ) =
          ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        push_cast
        have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
        field_simp [hqC]]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp [hr]
  · rw [if_neg hd]
    have hgeom := geom_sum_mul (ramanujanRoot q h) q
    have hrne := ramanujanRoot_ne_one hq hd
    rw [ramanujanRoot_pow_q hq h, sub_self] at hgeom
    simpa using (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hrne)

theorem sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ)) =
      if n = 1 then 1 else 0 := by
  calc
    _ = ((zeta : ArithmeticFunction ℤ) * ArithmeticFunction.moebius) n :=
      coe_zeta_mul_apply.symm
    _ = (1 : ArithmeticFunction ℤ) n := by rw [coe_zeta_mul_moebius]
    _ = _ := one_apply

theorem coprimeIndicator_moebius {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    (if a.Coprime q then (1 : ℂ) else 0) =
      ∑ d ∈ (Nat.gcd q a).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
  by_cases hc : a.Coprime q
  · rw [if_pos hc]
    have hg : Nat.gcd q a = 1 := by
      rw [Nat.coprime_comm] at hc
      exact Nat.coprime_iff_gcd_eq_one.mp hc
    simp [hg]
  · rw [if_neg hc]
    have hg : Nat.gcd q a ≠ 1 := by
      intro heq
      apply hc
      rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
      exact heq
    have hm := sum_moebius_divisors (Nat.gcd q a)
    rw [if_neg hg] at hm
    exact_mod_cast hm.symm

theorem sum_multiples_phase {q d : ℕ} (hq : q ≠ 0) (hd : d ∣ q) (hd0 : d ≠ 0) (h : ℤ) :
    (∑ a ∈ (Finset.range q).filter (fun a => d ∣ a),
      fourier (-h) (rationalCenter q a)) = completeResidueSum (q / d) h := by
  unfold completeResidueSum
  apply Finset.sum_bij (fun a _ => a / d)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact (Nat.div_lt_div_right hd0 ha.2 hd).2 ha.1
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    calc
      a = d * (a / d) := (Nat.mul_div_cancel' ha.2).symm
      _ = d * (b / d) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hb.2
  · intro b hb
    simp only [Finset.mem_range] at hb
    let a := d * b
    have hqdpos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hd)
      (Nat.pos_of_ne_zero hd0)
    have hqeq : d * (q / d) = q := Nat.mul_div_cancel' hd
    have ha_lt : a < q := by
      dsimp [a]
      rw [← hqeq]
      exact (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hd0)).2 hb
    refine ⟨a, ?_, ?_⟩
    · simp [a, ha_lt]
    · exact Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero hd0)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    have hqd0 : q / d ≠ 0 := by
      exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hd)
        (Nat.pos_of_ne_zero hd0))
    have haeq : d * (a / d) = a := Nat.mul_div_cancel' ha.2
    have hqeq : d * (q / d) = q := Nat.mul_div_cancel' hd
    congr 1
    unfold rationalCenter
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    have hqdR : ((q / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hqd0
    apply congrArg (fun x : ℝ => (x : UnitAddCircle))
    calc
      (a : ℝ) / (q : ℝ) =
          ((d : ℝ) * (a / d : ℕ)) / ((d : ℝ) * (q / d : ℕ)) := by
            rw [← Nat.cast_mul, haeq, ← Nat.cast_mul, hqeq]
      _ = ((a / d : ℕ) : ℝ) / ((q / d : ℕ) : ℝ) := by
            field_simp [hdR, hqdR]

theorem ramanujanCoefficient_eq_moebius_fullSum {q : ℕ} (hq : q ≠ 0) (h : ℤ) :
    ramanujanCoefficient q h =
      ∑ de ∈ q.divisorsAntidiagonal,
        ((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) * completeResidueSum de.2 h := by
  have hgcd (a : ℕ) :
      (Nat.gcd q a).divisors = q.divisors.filter (fun d => d ∣ a) := by
    ext d
    have hg0 : Nat.gcd q a ≠ 0 := by
      exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_left a (Nat.pos_of_ne_zero hq))
    simp only [Nat.mem_divisors, hg0, hq, and_true, Finset.mem_filter,
      Nat.dvd_gcd_iff]
    tauto
  unfold ramanujanCoefficient reducedResidues
  rw [Finset.sum_filter]
  simp_rw [show ∀ a : ℕ,
      (if a.Coprime q then fourier (-h) (rationalCenter q a) else 0) =
        (if a.Coprime q then (1 : ℂ) else 0) *
          fourier (-h) (rationalCenter q a) by
    intro a
    split_ifs <;> simp]
  simp_rw [coprimeIndicator_moebius hq, hgcd, Finset.sum_mul]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [← mul_ite_zero]
  simp_rw [← Finset.mul_sum]
  have hinner (d : ℕ) (hd : d ∈ q.divisors) :
      (∑ a ∈ Finset.range q,
          if d ∣ a then fourier (-h) (rationalCenter q a) else 0) =
        completeResidueSum (q / d) h := by
    rw [← Finset.sum_filter]
    exact sum_multiples_phase hq (Nat.dvd_of_mem_divisors hd)
      (Nat.ne_of_gt (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd)
        (Nat.pos_of_ne_zero hq))) h
  calc
    _ = ∑ d ∈ q.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          completeResidueSum (q / d) h := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hinner d hd]
    _ = _ := (Nat.sum_divisorsAntidiagonal
      (fun d e => ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        completeResidueSum e h)).symm


theorem ramanujanCoefficient_eq_moebius_divisorFormula {q : ℕ} (hq : q ≠ 0) (h : ℤ) :
    ramanujanCoefficient q h =
      ∑ de ∈ q.divisorsAntidiagonal,
        ((moebius de.1 : ℤ) : ℂ) *
          (if (de.2 : ℤ) ∣ h then (de.2 : ℂ) else 0) := by
  rw [ramanujanCoefficient_eq_moebius_fullSum hq h]
  apply Finset.sum_congr rfl
  intro de hde
  have hde2 : de.2 ≠ 0 := by
    intro hz
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hde).1
    rw [hz, mul_zero] at hprod
    exact hq hprod.symm
  rw [completeResidueSum_eq hde2]
  push_cast
  split_ifs <;> norm_num

theorem ramanujanCoefficient_prime {p : ℕ} (hp : p.Prime) (h : ℤ) :
    ramanujanCoefficient p h =
      if (p : ℤ) ∣ h then ((p - 1 : ℕ) : ℂ) else (-1 : ℂ) := by
  rw [ramanujanCoefficient_eq_moebius_divisorFormula hp.ne_zero h]
  rw [Nat.sum_divisorsAntidiagonal
    (fun d e => ((moebius d : ℤ) : ℂ) *
      if (e : ℤ) ∣ h then (e : ℂ) else 0)]
  rw [show p = p ^ 1 by simp, Nat.divisors_prime_pow hp]
  split_ifs with hd
  · norm_num [Finset.sum_range_succ, ArithmeticFunction.moebius_apply_prime hp,
      hp.ne_zero, hd]
    simp only [pow_one] at hd
    rw [if_pos hd, Nat.cast_sub hp.one_lt.le]
    push_cast
    ring
  · norm_num [Finset.sum_range_succ, ArithmeticFunction.moebius_apply_prime hp,
      hp.ne_zero, hd]
    simpa only [pow_one] using hd

theorem literalRamanujanTerm_prime {p : ℕ} (hp : p.Prime) (h : ℤ) :
    literalRamanujanTerm h p =
      if (p : ℤ) ∣ h then (((p - 1 : ℕ) : ℂ)⁻¹)
      else -((((p - 1 : ℕ) : ℂ) ^ 2)⁻¹) := by
  rw [literalRamanujanTerm, primeMajorSquareCoefficient_eq_arithmetic,
    ramanujanCoefficient_prime hp h, ArithmeticFunction.moebius_apply_prime hp,
    Nat.totient_prime hp]
  have hp1 : ((p - 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hp.one_lt))
  split_ifs <;> field_simp [hp1] <;> ring

def divisorMultipleArithmetic (h : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun n => if (n : ℤ) ∣ h then (n : ℂ) else 0, by simp⟩

@[simp] theorem divisorMultipleArithmetic_apply (h : ℤ) (n : ℕ) :
    divisorMultipleArithmetic h n = if (n : ℤ) ∣ h then (n : ℂ) else 0 := rfl

theorem divisorMultipleArithmetic_isMultiplicative (h : ℤ) :
    (divisorMultipleArithmetic h).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp
  · intro m n hm0 hn0 hcop
    simp only [divisorMultipleArithmetic_apply, Nat.cast_mul]
    have hdvd_iff : (m : ℤ) * (n : ℤ) ∣ h ↔
        (m : ℤ) ∣ h ∧ (n : ℤ) ∣ h := by
      rw [← Nat.cast_mul]
      simp only [Int.natCast_dvd]
      constructor
      · intro hmn
        exact ⟨dvd_trans (dvd_mul_right m n) hmn,
          dvd_trans (dvd_mul_left n m) hmn⟩
      · rintro ⟨hm, hn⟩
        exact hcop.mul_dvd_of_dvd_of_dvd hm hn
    by_cases hm : (m : ℤ) ∣ h <;> by_cases hn : (n : ℤ) ∣ h <;>
      simp [hm, hn, hdvd_iff]

def ramanujanArithmetic (h : ℤ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
    divisorMultipleArithmetic h

@[simp] theorem ramanujanArithmetic_apply (h : ℤ) (q : ℕ) :
    ramanujanArithmetic h q = ramanujanCoefficient q h := by
  by_cases hq : q = 0
  · subst q
    simp [ramanujanArithmetic, ramanujanCoefficient, reducedResidues]
  · rw [ramanujanArithmetic, ArithmeticFunction.mul_apply,
      ramanujanCoefficient_eq_moebius_divisorFormula hq h]
    rfl

theorem ramanujanArithmetic_isMultiplicative (h : ℤ) :
    (ramanujanArithmetic h).IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_moebius.intCast).mul
    (divisorMultipleArithmetic_isMultiplicative h)

def primeSquareArithmetic : ArithmeticFunction ℂ :=
  ⟨fun q => if q = 0 then 0 else
      (((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2) /
        ((q.totient : ℂ) ^ 2), by simp⟩

@[simp] theorem primeSquareArithmetic_apply_of_ne_zero
    {q : ℕ} (hq : q ≠ 0) :
    primeSquareArithmetic q = primeMajorSquareCoefficient q := by
  rw [primeSquareArithmetic, ArithmeticFunction.coe_mk, if_neg hq,
    primeMajorSquareCoefficient_eq_arithmetic]

theorem primeSquareArithmetic_isMultiplicative :
    primeSquareArithmetic.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [primeSquareArithmetic]
  · intro m n hm hn hcop
    rw [primeSquareArithmetic_apply_of_ne_zero (mul_ne_zero hm hn),
      primeSquareArithmetic_apply_of_ne_zero hm,
      primeSquareArithmetic_apply_of_ne_zero hn]
    simp only [primeMajorSquareCoefficient_eq_arithmetic]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      Nat.totient_mul hcop]
    push_cast
    have hmphi : (m.totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)))
    have hnphi : (n.totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)))
    field_simp [hmphi, hnphi]

def literalRamanujanArithmetic (h : ℤ) : ArithmeticFunction ℂ :=
  primeSquareArithmetic.pmul (ramanujanArithmetic h)

@[simp] theorem literalRamanujanArithmetic_apply (h : ℤ) (q : ℕ) :
    literalRamanujanArithmetic h q = literalRamanujanTerm h q := by
  by_cases hq : q = 0
  · subst q
    simp [literalRamanujanArithmetic]
  · simp [literalRamanujanArithmetic, ArithmeticFunction.pmul_apply,
      primeSquareArithmetic_apply_of_ne_zero hq, ramanujanArithmetic_apply,
      literalRamanujanTerm]

theorem literalRamanujanArithmetic_isMultiplicative (h : ℤ) :
    (literalRamanujanArithmetic h).IsMultiplicative :=
  primeSquareArithmetic_isMultiplicative.pmul
    (ramanujanArithmetic_isMultiplicative h)

theorem literalRamanujanTerm_prime_pow_eq_zero
    {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (h : ℤ) :
    literalRamanujanTerm h (p ^ e) = 0 := by
  rw [literalRamanujanTerm, primeMajorSquareCoefficient_eq_arithmetic]
  rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
  simp [show e ≠ 1 by omega]

@[simp] theorem literalRamanujanTerm_one (h : ℤ) :
    literalRamanujanTerm h 1 = 1 := by
  rw [literalRamanujanTerm, ramanujanCoefficient_eq_totient_of_dvd
    (q := 1) (by norm_num) (one_dvd h)]
  norm_num [primeMajorSquareCoefficient, primeMajorCoefficient]

theorem tsum_literalRamanujan_prime_powers
    {p : ℕ} (hp : p.Prime) (h : ℤ) :
    (∑' e : ℕ, literalRamanujanTerm h (p ^ e)) =
      1 + literalRamanujanTerm h p := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, literalRamanujanTerm_one]
  · intro e he
    simp only [Finset.mem_range, Nat.not_lt] at he
    exact literalRamanujanTerm_prime_pow_eq_zero hp he h

/-- The exact Euler-product expansion of the literal denominator series.  This
statement isolates convergence honestly: the only hypothesis is absolute
summability of the literal arithmetic function, and every local factor is
evaluated by the finite Ramanujan formula above. -/
theorem tsum_literalRamanujan_eq_tprod_local
    (h : ℤ)
    (hsum : Summable (fun q : ℕ => ‖literalRamanujanTerm h q‖)) :
    (∑' q : ℕ, literalRamanujanTerm h q) =
      ∏' p : Nat.Primes, (1 + literalRamanujanTerm h p) := by
  have heuler :=
    (literalRamanujanArithmetic_isMultiplicative h).eulerProduct_tprod
      (by simpa only [literalRamanujanArithmetic_apply] using hsum)
  calc
    (∑' q : ℕ, literalRamanujanTerm h q) =
        ∑' q : ℕ, literalRamanujanArithmetic h q := by
          apply tsum_congr
          intro q
          exact (literalRamanujanArithmetic_apply h q).symm
    _ = ∏' p : Nat.Primes,
        ∑' e : ℕ, literalRamanujanArithmetic h (p ^ e) := heuler.symm
    _ = ∏' p : Nat.Primes, (1 + literalRamanujanTerm h p) := by
      apply tprod_congr
      intro p
      simpa only [literalRamanujanArithmetic_apply] using
        tsum_literalRamanujan_prime_powers p.property h

theorem one_add_literalRamanujanTerm_prime
    (h : ℤ) (hh : h ≠ 0) (p : Nat.Primes) :
    1 + literalRamanujanTerm h p =
      if (p : ℕ) = 2 then
        if (2 : ℤ) ∣ h then 2 else 0
      else
        ((twinPrimeFactor p * singularLocalFactor ⟨h, hh⟩ p : ℝ) : ℂ) := by
  rw [literalRamanujanTerm_prime p.property h]
  have hpminus1C : ((((p : ℕ) - 1 : ℕ) : ℂ)) = (p : ℂ) - 1 := by
    rw [Nat.cast_sub p.property.one_le]
    norm_num
  rw [hpminus1C]
  by_cases hp2 : (p : ℕ) = 2
  · rw [if_pos hp2]
    by_cases hd : (2 : ℤ) ∣ h <;> norm_num [hp2, hd]
  · rw [if_neg hp2]
    have hpgt : 2 < (p : ℕ) := by
      have := p.property.two_le
      omega
    by_cases hd : ((p : ℕ) : ℤ) ∣ h
    · rw [if_pos hd]
      have hp1R : ((p : ℝ) - 1) ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt (lt_trans (by omega) hpgt)))
      have hp2R : ((p : ℝ) - 2) ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hpgt))
      have hreal :
          (1 : ℝ) + (((p : ℝ) - 1)⁻¹) =
            twinPrimeFactor p * singularLocalFactor ⟨h, hh⟩ p := by
        rw [twinPrimeFactor, if_pos ⟨p.property, hpgt⟩,
          singularLocalFactor, if_pos ⟨p.property, hpgt, hd⟩]
        field_simp [hp1R, hp2R]
        ring
      calc
        (1 : ℂ) + ((p : ℂ) - 1)⁻¹ =
            (((1 : ℝ) + ((p : ℝ) - 1)⁻¹ : ℝ) : ℂ) := by
              push_cast
              rfl
        _ = _ := congrArg Complex.ofReal hreal
    · rw [if_neg hd]
      have hp1R : ((p : ℝ) - 1) ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt (lt_trans (by omega) hpgt)))
      have hreal :
          (1 : ℝ) - (((p : ℝ) - 1) ^ 2)⁻¹ =
            twinPrimeFactor p * singularLocalFactor ⟨h, hh⟩ p := by
        rw [twinPrimeFactor, if_pos ⟨p.property, hpgt⟩,
          singularLocalFactor, if_neg (by simp [hd])]
        field_simp [hp1R]
        ring
      calc
        (1 : ℂ) + -(((p : ℂ) - 1) ^ 2)⁻¹ =
            (((1 : ℝ) - (((p : ℝ) - 1) ^ 2)⁻¹ : ℝ) : ℂ) := by
              push_cast
              ring
        _ = _ := congrArg Complex.ofReal hreal

/-- Restrict the already certified twin-prime Euler product to prime indices
and transport it from `ℝ` to `ℂ`. -/
theorem twinPrimeFactor_hasProd_primes_complex :
    HasProd (fun p : Nat.Primes => (twinPrimeFactor p : ℂ))
      (twinPrimeConstant : ℂ) := by
  have hsupp : Function.mulSupport twinPrimeFactor ⊆
      {p : ℕ | p.Prime} := by
    intro p hp
    simp only [Function.mem_mulSupport, Set.mem_setOf_eq] at hp ⊢
    by_contra hn
    apply hp
    simp [twinPrimeFactor, hn]
  have hr : HasProd (fun p : Nat.Primes => twinPrimeFactor p)
      twinPrimeConstant :=
    (hasProd_subtype_iff_of_mulSupport_subset hsupp).2
      twinPrimeEulerProduct_hasProd
  simpa only [Function.comp_apply] using
    hr.map Complex.ofRealHom Complex.continuous_ofReal

/-- The correction factors for primes dividing a fixed nonzero shift form a
finite product, again transported to the complex coefficient field. -/
theorem singularLocalFactor_hasProd_primes_complex
    (h : {z : ℤ // z ≠ 0}) :
    HasProd (fun p : Nat.Primes => (singularLocalFactor h p : ℂ))
      ((∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p : ℝ) : ℂ) := by
  have hsupp : Function.mulSupport (singularLocalFactor h) ⊆
      {p : ℕ | p.Prime} := by
    intro p hp
    simp only [Function.mem_mulSupport, Set.mem_setOf_eq] at hp ⊢
    by_contra hn
    apply hp
    simp [singularLocalFactor, hn]
  have hrAll : HasProd (singularLocalFactor h)
      (∏' p : ℕ, singularLocalFactor h p) :=
    (singularLocalFactor_multipliable h).hasProd
  have hr : HasProd (fun p : Nat.Primes => singularLocalFactor h p)
      (∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p) := by
    rw [singularLocalFactor_tprod_eq_divisors_prod h] at hrAll
    exact (hasProd_subtype_iff_of_mulSupport_subset hsupp).2 hrAll
  simpa only [Function.comp_apply] using
    hr.map Complex.ofRealHom Complex.continuous_ofReal

def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- Exact full Euler product: the literal local Ramanujan factors reproduce
the Hardy--Littlewood singular series, including the vanishing odd-shift
factor at `p=2`. -/
theorem tprod_literalRamanujan_local_eq_singularSeries
    (h : ℤ) (hh : h ≠ 0) :
    (∏' p : Nat.Primes, (1 + literalRamanujanTerm h p)) =
      ((singularSeries ⟨h, hh⟩ : ℝ) : ℂ) := by
  by_cases heven : (2 : ℤ) ∣ h
  · have hbase := twinPrimeFactor_hasProd_primes_complex.mul
        (singularLocalFactor_hasProd_primes_complex ⟨h, hh⟩)
    have htwo : HasProd
        (fun p : Nat.Primes => if p = primeTwo then (2 : ℂ) else 1) 2 :=
      hasProd_ite_eq primeTwo 2
    have hall := htwo.mul hbase
    calc
      (∏' p : Nat.Primes, (1 + literalRamanujanTerm h p)) =
          ∏' p : Nat.Primes,
            (if p = primeTwo then (2 : ℂ) else 1) *
              ((twinPrimeFactor p : ℂ) *
                (singularLocalFactor ⟨h, hh⟩ p : ℂ)) := by
        apply tprod_congr
        intro p
        rw [one_add_literalRamanujanTerm_prime h hh p]
        by_cases hp2 : (p : ℕ) = 2
        · have hpEq : p = primeTwo := Subtype.ext hp2
          simp [hpEq, heven, primeTwo, twinPrimeFactor,
            singularLocalFactor]
        · have hpNe : p ≠ primeTwo := by
            intro hpEq
            apply hp2
            exact congrArg Subtype.val hpEq
          simp [hp2, hpNe]
      _ = (2 : ℂ) *
          ((twinPrimeConstant : ℂ) *
            ((∏ p ∈ Int.natAbs h |>.divisors,
              singularLocalFactor ⟨h, hh⟩ p : ℝ) : ℂ)) := hall.tprod_eq
      _ = ((singularSeries ⟨h, hh⟩ : ℝ) : ℂ) := by
        rw [singularSeries_eq_finite_divisor_product, if_pos heven]
        push_cast
        ring
  · have hzero :
        1 + literalRamanujanTerm h primeTwo = 0 := by
      rw [one_add_literalRamanujanTerm_prime h hh primeTwo]
      simp [primeTwo, heven]
    calc
      (∏' p : Nat.Primes, (1 + literalRamanujanTerm h p)) = 0 :=
        tprod_of_exists_eq_zero ⟨primeTwo, hzero⟩
      _ = ((singularSeries ⟨h, hh⟩ : ℝ) : ℂ) := by
        rw [singularSeries_eq_finite_divisor_product, if_neg heven]
        norm_num

theorem sqrt_div_sub_one_sq_le_rpow (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt n / ((n : ℝ) - 1) ^ 2 ≤
      4 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
  have hhalfpos : 0 < (n : ℝ) / 2 := div_pos hnpos (by norm_num)
  have hsubnonneg : 0 ≤ (n : ℝ) - 1 := by linarith
  have hsq : ((n : ℝ) / 2) ^ 2 ≤ ((n : ℝ) - 1) ^ 2 :=
    (sq_le_sq₀ hhalfpos.le hsubnonneg).2 hhalf
  calc
    Real.sqrt n / ((n : ℝ) - 1) ^ 2 ≤
        Real.sqrt n / ((n : ℝ) / 2) ^ 2 :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (sq_pos_of_pos hhalfpos) hsq
    _ = 4 * (Real.sqrt n / (n : ℝ) ^ 2) := by
      field_simp [ne_of_gt hnpos]
      ring
    _ = 4 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (n : ℝ) 2,
        ← Real.rpow_sub hnpos]
      congr 1
      norm_num

def basePrimeWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then Real.sqrt n / ((n : ℝ) - 1) ^ 2 else 0

theorem summable_basePrimeWeight : Summable basePrimeWeight := by
  have hg : Summable (fun n : ℕ =>
      4 * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    apply Summable.mul_left
    rw [Real.summable_nat_rpow]
    norm_num
  apply Summable.of_nonneg_of_le
  · intro n
    simp only [basePrimeWeight]
    split_ifs
    · positivity
    · rfl
  · intro n
    simp only [basePrimeWeight]
    split_ifs with hn
    · exact sqrt_div_sub_one_sq_le_rpow n hn
    · positivity
  · exact hg

def weightedRamanujanPrime (h : ℤ) (p : Nat.Primes) : ℝ :=
  Real.sqrt p * ‖literalRamanujanTerm h p‖

theorem weightedRamanujanPrime_nonneg (h : ℤ) (p : Nat.Primes) :
    0 ≤ weightedRamanujanPrime h p := by
  rw [weightedRamanujanPrime]
  positivity

theorem weightedRamanujanPrime_eq_base_of_not_dvd
    (h : ℤ) (p : Nat.Primes) (hd : ¬ ((p : ℕ) : ℤ) ∣ h) :
    weightedRamanujanPrime h p = basePrimeWeight p := by
  rw [weightedRamanujanPrime, literalRamanujanTerm_prime p.property h,
    if_neg hd]
  rw [basePrimeWeight, if_pos p.property.two_le]
  have hpminus1C : ((((p : ℕ) - 1 : ℕ) : ℂ)) = (p : ℂ) - 1 := by
    rw [Nat.cast_sub p.property.one_le]
    norm_num
  rw [hpminus1C, norm_neg, norm_inv, norm_pow]
  have hdiff : (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
  have hp1nonneg : 0 ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_le
    linarith
  rw [abs_of_nonneg hp1nonneg]
  rw [div_eq_mul_inv]

theorem summable_weightedRamanujanPrime (h : ℤ) (hh : h ≠ 0) :
    Summable (weightedRamanujanPrime h) := by
  have hbase : Summable (fun p : Nat.Primes => basePrimeWeight p) := by
    simpa only [Function.comp_apply] using
      summable_basePrimeWeight.subtype {p : ℕ | p.Prime}
  have hfinite : Set.Finite {p : Nat.Primes | ((p : ℕ) : ℤ) ∣ h} := by
    have hpre : Set.Finite
        ((fun p : Nat.Primes => (p : ℕ)) ⁻¹'
          (h.natAbs.primeFactors : Set ℕ)) :=
      h.natAbs.primeFactors.finite_toSet.preimage
        Subtype.val_injective.injOn
    apply hpre.subset
    intro p hp
    have hpd : (p : ℕ) ∣ h.natAbs := Int.natCast_dvd.mp hp
    exact Nat.mem_primeFactors.mpr ⟨p.property, hpd,
      Int.natAbs_ne_zero.mpr hh⟩
  have hcorr : Summable (fun p : Nat.Primes =>
      if ((p : ℕ) : ℤ) ∣ h then weightedRamanujanPrime h p else 0) :=
    summable_of_finite_support (hfinite.subset (by
      intro p hp
      change ((p : ℕ) : ℤ) ∣ h
      by_contra hnd
      apply hp
      simp [hnd]))
  apply Summable.of_nonneg_of_le
    (f := fun p : Nat.Primes => basePrimeWeight p +
      if ((p : ℕ) : ℤ) ∣ h then weightedRamanujanPrime h p else 0)
  · exact weightedRamanujanPrime_nonneg h
  · intro p
    by_cases hd : ((p : ℕ) : ℤ) ∣ h
    · simp only [hd, if_true]
      exact le_add_of_nonneg_left (by
        rw [basePrimeWeight, if_pos p.property.two_le]
        positivity)
    · simp only [hd, if_false, add_zero]
      exact le_of_eq (weightedRamanujanPrime_eq_base_of_not_dvd h p hd)
  · exact hbase.add hcorr

def weightedRamanujanArithmetic (h : ℤ) : ArithmeticFunction ℝ :=
  ⟨fun q => Real.sqrt q * ‖literalRamanujanTerm h q‖, by simp⟩

@[simp] theorem weightedRamanujanArithmetic_apply (h : ℤ) (q : ℕ) :
    weightedRamanujanArithmetic h q =
      Real.sqrt q * ‖literalRamanujanTerm h q‖ := rfl

theorem weightedRamanujanArithmetic_isMultiplicative (h : ℤ) :
    (weightedRamanujanArithmetic h).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [weightedRamanujanArithmetic]
  · intro m n hm hn hcop
    have hterm : literalRamanujanTerm h (m * n) =
        literalRamanujanTerm h m * literalRamanujanTerm h n := by
      calc
        literalRamanujanTerm h (m * n) =
            literalRamanujanArithmetic h (m * n) :=
          (literalRamanujanArithmetic_apply h (m * n)).symm
        _ = literalRamanujanArithmetic h m *
            literalRamanujanArithmetic h n :=
          (literalRamanujanArithmetic_isMultiplicative h).map_mul_of_coprime hcop
        _ = _ := by simp only [literalRamanujanArithmetic_apply]
    simp only [weightedRamanujanArithmetic_apply, Nat.cast_mul]
    rw [Real.sqrt_mul (by positivity), hterm, norm_mul]
    ring

theorem literalRamanujanTerm_eq_zero_of_not_squarefree
    (h : ℤ) {q : ℕ} (hq : ¬ Squarefree q) :
    literalRamanujanTerm h q = 0 := by
  rw [literalRamanujanTerm, primeMajorSquareCoefficient_eq_arithmetic,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]
  norm_num

theorem weightedRamanujanArithmetic_eq_zero_of_not_squarefree
    (h : ℤ) {q : ℕ} (hq : ¬ Squarefree q) :
    weightedRamanujanArithmetic h q = 0 := by
  rw [weightedRamanujanArithmetic_apply,
    literalRamanujanTerm_eq_zero_of_not_squarefree h hq, norm_zero, mul_zero]

theorem weightedRamanujanArithmetic_eq_prod_primeFactors
    (h : ℤ) {q : ℕ} (hq : Squarefree q) :
    weightedRamanujanArithmetic h q =
      ∏ p ∈ q.primeFactors, weightedRamanujanArithmetic h p := by
  have hm := ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors
    (weightedRamanujanArithmetic_isMultiplicative h)
    q q.primeFactors Finset.Subset.rfl
  simpa only [Nat.prod_primeFactors_of_squarefree hq] using hm

def weightedPrimeOnNat (h : ℤ) (p : ℕ) : ℝ :=
  if hp : p.Prime then weightedRamanujanPrime h ⟨p, hp⟩ else 0

theorem weightedPrimeOnNat_nonneg (h : ℤ) (p : ℕ) :
    0 ≤ weightedPrimeOnNat h p := by
  rw [weightedPrimeOnNat]
  split_ifs
  · exact weightedRamanujanPrime_nonneg h _
  · rfl

theorem summable_weightedPrimeOnNat (h : ℤ) (hh : h ≠ 0) :
    Summable (weightedPrimeOnNat h) := by
  have hsub : Summable (fun p : Nat.Primes =>
      weightedPrimeOnNat h p) := by
    apply (summable_weightedRamanujanPrime h hh).congr
    intro p
    rw [weightedPrimeOnNat, dif_pos p.property]
    congr 1
  apply (Subtype.val_injective.summable_iff (f := weightedPrimeOnNat h) ?_).mp hsub
  intro p hp
  rw [weightedPrimeOnNat]
  split_ifs with hprime
  · exact (hp ⟨⟨p, hprime⟩, rfl⟩).elim
  · rfl

def primeFinsets : Set (Finset ℕ) :=
  {s | ∀ p ∈ s, p.Prime}

def squarefreeNats : Set ℕ := {n | Squarefree n}

def primeFinsetProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

theorem primeFinsetProduct_mapsTo_squarefree :
    Set.MapsTo primeFinsetProduct primeFinsets squarefreeNats := by
  intro s hs
  rw [primeFinsets] at hs
  rw [squarefreeNats]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    apply (hs p hp).coprime_iff_not_dvd.mpr
    intro hdiv
    apply hpq
    exact (Nat.prime_dvd_prime_iff_eq (hs p hp) (hs q hq)).mp hdiv
  · intro p hp
    exact (hs p hp).squarefree

theorem primeFactors_mapsTo_primeFinsets :
    Set.MapsTo (fun n : ℕ => n.primeFactors) squarefreeNats primeFinsets := by
  intro n hn p hp
  exact Nat.prime_of_mem_primeFactors hp

noncomputable def primeFinsetSquarefreeEquiv :
    primeFinsets ≃ squarefreeNats :=
  Set.BijOn.equiv primeFinsetProduct
    (Nat.prod_primeFactors_invOn_squarefree.bijOn
      primeFinsetProduct_mapsTo_squarefree
      primeFactors_mapsTo_primeFinsets)

theorem weightedRamanujanArithmetic_prime
    (h : ℤ) (p : Nat.Primes) :
    weightedRamanujanArithmetic h p = weightedRamanujanPrime h p := rfl

theorem weightedPrimeOnNat_eq_weightedArithmetic_of_prime
    (h : ℤ) {p : ℕ} (hp : p.Prime) :
    weightedPrimeOnNat h p = weightedRamanujanArithmetic h p := by
  rw [weightedPrimeOnNat, dif_pos hp]
  rfl

theorem summable_sqrtWeightedRamanujan (h : ℤ) (hh : h ≠ 0) :
    Summable (fun q : ℕ => Real.sqrt q * ‖literalRamanujanTerm h q‖) := by
  have hlocal := summable_weightedPrimeOnNat h hh
  have hfinset : Summable (fun s : Finset ℕ =>
      ∏ p ∈ s, weightedPrimeOnNat h p) :=
    summable_finsetProd_of_summable_nonneg
      (weightedPrimeOnNat_nonneg h) hlocal
  have hsource : Summable (fun s : primeFinsets =>
      ∏ p ∈ (s : Finset ℕ), weightedPrimeOnNat h p) := by
    simpa only [Function.comp_apply] using hfinset.subtype primeFinsets
  have hsourceEq : (fun s : primeFinsets =>
      weightedRamanujanArithmetic h (primeFinsetSquarefreeEquiv s)) =
      (fun s : primeFinsets =>
        ∏ p ∈ (s : Finset ℕ), weightedPrimeOnNat h p) := by
    funext s
    have hsquare : Squarefree (primeFinsetProduct s) :=
      primeFinsetProduct_mapsTo_squarefree s.property
    rw [show (primeFinsetSquarefreeEquiv s : ℕ) =
        primeFinsetProduct s by rfl]
    rw [weightedRamanujanArithmetic_eq_prod_primeFactors h hsquare]
    have hpf : (primeFinsetProduct s).primeFactors = (s : Finset ℕ) := by
      exact Nat.primeFactors_prod s.property
    rw [hpf]
    apply Finset.prod_congr rfl
    intro p hp
    exact (weightedPrimeOnNat_eq_weightedArithmetic_of_prime h
      (s.property p hp)).symm
  have hsquareSub : Summable (fun q : squarefreeNats =>
      weightedRamanujanArithmetic h q) := by
    apply (primeFinsetSquarefreeEquiv.summable_iff).mp
    change Summable (fun s : primeFinsets =>
      weightedRamanujanArithmetic h (primeFinsetSquarefreeEquiv s))
    rw [hsourceEq]
    exact hsource
  have hall : Summable (fun q : ℕ => weightedRamanujanArithmetic h q) := by
    apply (Subtype.val_injective.summable_iff
      (f := fun q : ℕ => weightedRamanujanArithmetic h q) ?_).mp hsquareSub
    intro q hq
    apply weightedRamanujanArithmetic_eq_zero_of_not_squarefree h
    intro hsquare
    exact hq ⟨⟨q, hsquare⟩, rfl⟩
  simpa only [weightedRamanujanArithmetic_apply] using hall

theorem summable_norm_literalRamanujanTerm (h : ℤ) (hh : h ≠ 0) :
    Summable (fun q : ℕ => ‖literalRamanujanTerm h q‖) := by
  have hsqrt := summable_sqrtWeightedRamanujan h hh
  apply Summable.of_nonneg_of_le
    (f := fun q : ℕ => Real.sqrt q * ‖literalRamanujanTerm h q‖)
  · intro q
    positivity
  · intro q
    by_cases hq : q = 0
    · subst q
      simp
    · have hq1 : (1 : ℝ) ≤ Real.sqrt q := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
      nlinarith [norm_nonneg (literalRamanujanTerm h q)]
  · exact hsqrt

/-- The absolutely convergent literal Ramanujan series is exactly the
Hardy--Littlewood singular series. -/
theorem tsum_literalRamanujan_eq_singularSeries (h : ℤ) (hh : h ≠ 0) :
    (∑' q : ℕ, literalRamanujanTerm h q) =
      ((singularSeries ⟨h, hh⟩ : ℝ) : ℂ) := by
  rw [tsum_literalRamanujan_eq_tprod_local h
    (summable_norm_literalRamanujanTerm h hh)]
  exact tprod_literalRamanujan_local_eq_singularSeries h hh

/-- Unconditional `Q^{-1/2}` tail for every legal nonzero shift.  The exact
arithmetic mass is kept visible for the subsequent translated-average divisor
bound rather than hidden behind a fictitious `Q^{-C}` constant. -/
theorem norm_truncatedSingularCoefficient_sub_singular_unconditional
    {h : ℤ} (hh : h ≠ 0) (Q : ℕ) :
    ‖truncatedSingularCoefficient Q h -
        ((singularSeriesTotal h : ℝ) : ℂ)‖ ≤
      sqrtWeightedRamanujanMass h / Real.sqrt (Q + 1) := by
  exact norm_truncatedSingularCoefficient_sub_singular_le hh
    (summable_sqrtWeightedRamanujan h hh)
    (tsum_literalRamanujan_eq_singularSeries h hh) Q

theorem weightedRamanujanPrime_eq_div_of_dvd
    (h : ℤ) (p : Nat.Primes) (hd : ((p : ℕ) : ℤ) ∣ h) :
    weightedRamanujanPrime h p =
      Real.sqrt p / ((p : ℝ) - 1) := by
  rw [weightedRamanujanPrime, literalRamanujanTerm_prime p.property h,
    if_pos hd]
  have hpminus1C : ((((p : ℕ) - 1 : ℕ) : ℂ)) = (p : ℂ) - 1 := by
    rw [Nat.cast_sub p.property.one_le]
    norm_num
  rw [hpminus1C, norm_inv]
  have hdiff : (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
  have hp1nonneg : 0 ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_le
    linarith
  rw [abs_of_nonneg hp1nonneg, div_eq_mul_inv]

theorem weightedRamanujanPrime_le_two_of_dvd
    (h : ℤ) (p : Nat.Primes) (hd : ((p : ℕ) : ℤ) ∣ h) :
    weightedRamanujanPrime h p ≤ 2 := by
  rw [weightedRamanujanPrime_eq_div_of_dvd h p hd]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hpden : 0 < (p : ℝ) - 1 := by linarith
  rw [div_le_iff₀ hpden, Real.sqrt_le_iff]
  constructor
  · linarith
  · nlinarith

theorem weightedRamanujanArithmetic_prime_pow_eq_zero
    {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (h : ℤ) :
    weightedRamanujanArithmetic h (p ^ e) = 0 := by
  rw [weightedRamanujanArithmetic_apply,
    literalRamanujanTerm_prime_pow_eq_zero hp he h, norm_zero, mul_zero]

@[simp] theorem weightedRamanujanArithmetic_one (h : ℤ) :
    weightedRamanujanArithmetic h 1 = 1 := by
  simp [weightedRamanujanArithmetic_apply]

theorem tsum_weightedRamanujan_prime_powers
    {p : ℕ} (hp : p.Prime) (h : ℤ) :
    (∑' e : ℕ, weightedRamanujanArithmetic h (p ^ e)) =
      1 + weightedRamanujanPrime h ⟨p, hp⟩ := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, weightedRamanujanArithmetic_one]
    rw [weightedRamanujanArithmetic_prime h ⟨p, hp⟩]
  · intro e he
    simp only [Finset.mem_range, Nat.not_lt] at he
    exact weightedRamanujanArithmetic_prime_pow_eq_zero hp he h

theorem sqrtWeightedRamanujanMass_eq_tprod
    (h : ℤ) (hh : h ≠ 0) :
    sqrtWeightedRamanujanMass h =
      ∏' p : Nat.Primes, (1 + weightedRamanujanPrime h p) := by
  have hs := summable_sqrtWeightedRamanujan h hh
  have hnorm : Summable (fun q : ℕ =>
      ‖weightedRamanujanArithmetic h q‖) := by
    apply hs.congr
    intro q
    rw [weightedRamanujanArithmetic_apply, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have heuler := ArithmeticFunction.IsMultiplicative.eulerProduct_tprod
    (weightedRamanujanArithmetic_isMultiplicative h) hnorm
  rw [sqrtWeightedRamanujanMass]
  calc
    (∑' q : ℕ, Real.sqrt q * ‖literalRamanujanTerm h q‖) =
        ∑' q : ℕ, weightedRamanujanArithmetic h q := by rfl
    _ = ∏' p : Nat.Primes,
        ∑' e : ℕ, weightedRamanujanArithmetic h (p ^ e) := heuler.symm
    _ = _ := by
      apply tprod_congr
      intro p
      exact tsum_weightedRamanujan_prime_powers p.property h

def shiftPrimeCorrection (h : ℤ) (p : Nat.Primes) : ℝ :=
  if ((p : ℕ) : ℤ) ∣ h then 4 else 1

def basePrimeMassConstant : ℝ :=
  ∏' p : Nat.Primes, (1 + basePrimeWeight p)

def shiftPrimeCorrectionMass (h : ℤ) : ℝ :=
  ∏' p : Nat.Primes, shiftPrimeCorrection h p

theorem finite_prime_divisors (h : ℤ) (hh : h ≠ 0) :
    Set.Finite {p : Nat.Primes | ((p : ℕ) : ℤ) ∣ h} := by
  have hpre : Set.Finite
      ((fun p : Nat.Primes => (p : ℕ)) ⁻¹'
        (h.natAbs.primeFactors : Set ℕ)) :=
    h.natAbs.primeFactors.finite_toSet.preimage
      Subtype.val_injective.injOn
  apply hpre.subset
  intro p hp
  have hpd : (p : ℕ) ∣ h.natAbs := Int.natCast_dvd.mp hp
  exact Nat.mem_primeFactors.mpr ⟨p.property, hpd,
    Int.natAbs_ne_zero.mpr hh⟩

theorem shiftPrimeCorrection_multipliable
    (h : ℤ) (hh : h ≠ 0) :
    Multipliable (shiftPrimeCorrection h) := by
  apply multipliable_of_ne_finset_one
    (s := (finite_prime_divisors h hh).toFinset)
  intro p hp
  rw [shiftPrimeCorrection, if_neg]
  intro hd
  apply hp
  simpa only [Set.Finite.mem_toFinset] using hd

theorem basePrimeMass_multipliable :
    Multipliable (fun p : Nat.Primes => 1 + basePrimeWeight p) := by
  have hbase : Summable (fun p : Nat.Primes => basePrimeWeight p) := by
    simpa only [Function.comp_apply] using
      summable_basePrimeWeight.subtype {p : ℕ | p.Prime}
  have hbaseNorm : Summable (fun p : Nat.Primes => ‖basePrimeWeight p‖) := by
    apply hbase.congr
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg]
    rw [basePrimeWeight, if_pos p.property.two_le]
    positivity
  exact multipliable_one_add_of_summable hbaseNorm

theorem one_add_weightedPrime_le_correction_mul_base
    (h : ℤ) (p : Nat.Primes) :
    1 + weightedRamanujanPrime h p ≤
      shiftPrimeCorrection h p * (1 + basePrimeWeight p) := by
  by_cases hd : ((p : ℕ) : ℤ) ∣ h
  · rw [shiftPrimeCorrection, if_pos hd]
    have hw := weightedRamanujanPrime_le_two_of_dvd h p hd
    have hb : 0 ≤ basePrimeWeight p := by
      rw [basePrimeWeight, if_pos p.property.two_le]
      positivity
    nlinarith
  · rw [shiftPrimeCorrection, if_neg hd, one_mul,
      weightedRamanujanPrime_eq_base_of_not_dvd h p hd]

/-- Quantitative structure of the weighted mass.  The only shift dependence
is a finite factor `4` for each prime divisor of `h`; the other product is a
universal convergent constant. -/
theorem sqrtWeightedRamanujanMass_le_divisorCorrection
    (h : ℤ) (hh : h ≠ 0) :
    sqrtWeightedRamanujanMass h ≤
      shiftPrimeCorrectionMass h * basePrimeMassConstant := by
  rw [sqrtWeightedRamanujanMass_eq_tprod h hh]
  have hactual : Multipliable (fun p : Nat.Primes =>
      1 + weightedRamanujanPrime h p) := by
    have hnorm : Summable (fun p : Nat.Primes =>
        ‖weightedRamanujanPrime h p‖) := by
      apply (summable_weightedRamanujanPrime h hh).congr
      intro p
      rw [Real.norm_eq_abs, abs_of_nonneg
        (weightedRamanujanPrime_nonneg h p)]
    exact multipliable_one_add_of_summable hnorm
  have hcorr := shiftPrimeCorrection_multipliable h hh
  have hbase := basePrimeMass_multipliable
  calc
    (∏' p : Nat.Primes, (1 + weightedRamanujanPrime h p)) ≤
        ∏' p : Nat.Primes,
          shiftPrimeCorrection h p * (1 + basePrimeWeight p) :=
      le_of_tendsto_of_tendsto' hactual.hasProd (hcorr.mul hbase).hasProd
        (fun s => Finset.prod_le_prod
          (fun p _ => by
            have hw := weightedRamanujanPrime_nonneg h p
            linarith)
          (fun p _ => one_add_weightedPrime_le_correction_mul_base h p))
    _ = shiftPrimeCorrectionMass h * basePrimeMassConstant := by
      exact hcorr.tprod_mul hbase

theorem finite_prime_divisors_card_eq_primeFactors_card
    (h : ℤ) (hh : h ≠ 0) :
    (finite_prime_divisors h hh).toFinset.card =
      h.natAbs.primeFactors.card := by
  apply Finset.card_bij
    (s := (finite_prime_divisors h hh).toFinset)
    (t := h.natAbs.primeFactors)
    (fun (p : Nat.Primes) _ => (p : ℕ))
  · intro p hp
    have hd : ((p : ℕ) : ℤ) ∣ h :=
      (by simpa only [Set.Finite.mem_toFinset] using hp)
    exact Nat.mem_primeFactors.mpr ⟨p.property, Int.natCast_dvd.mp hd,
      Int.natAbs_ne_zero.mpr hh⟩
  · intro p hp q hq hpq
    exact Subtype.ext hpq
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdNat : p ∣ h.natAbs := Nat.dvd_of_mem_primeFactors hp
    let pp : Nat.Primes := ⟨p, hprime⟩
    refine ⟨pp, ?_, rfl⟩
    simpa only [Set.Finite.mem_toFinset] using (Int.natCast_dvd.mpr hdNat)

theorem shiftPrimeCorrectionMass_eq_four_pow
    (h : ℤ) (hh : h ≠ 0) :
    shiftPrimeCorrectionMass h =
      (4 : ℝ) ^ h.natAbs.primeFactors.card := by
  let s := (finite_prime_divisors h hh).toFinset
  have hout : ∀ p ∉ s, shiftPrimeCorrection h p = 1 := by
    intro p hp
    change p ∉ (finite_prime_divisors h hh).toFinset at hp
    rw [shiftPrimeCorrection, if_neg]
    intro hd
    apply hp
    simpa only [Set.Finite.mem_toFinset] using hd
  rw [shiftPrimeCorrectionMass, tprod_eq_prod (s := s) hout]
  calc
    (∏ p ∈ s, shiftPrimeCorrection h p) = ∏ _p ∈ s, (4 : ℝ) := by
      apply Finset.prod_congr rfl
      intro p hp
      change p ∈ (finite_prime_divisors h hh).toFinset at hp
      rw [shiftPrimeCorrection, if_pos]
      simpa only [Set.Finite.mem_toFinset] using hp
    _ = (4 : ℝ) ^ s.card := Finset.prod_const 4
    _ = (4 : ℝ) ^ h.natAbs.primeFactors.card := by
      rw [finite_prime_divisors_card_eq_primeFactors_card h hh]

theorem two_pow_primeFactors_card_le_card_divisors
    (n : ℕ) (hn : n ≠ 0) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn]
  calc
    2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by
      rw [Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
      apply Finset.prod_le_prod
      · intro p hp
        omega
      · intro p hp
        have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
        have hpos := hpprime.factorization_pos_of_dvd hn hpdvd
        omega

theorem four_pow_primeFactors_card_le_card_divisors_sq
    (n : ℕ) (hn : n ≠ 0) :
    4 ^ n.primeFactors.card ≤ n.divisors.card ^ 2 := by
  have htwo := two_pow_primeFactors_card_le_card_divisors n hn
  calc
    4 ^ n.primeFactors.card = (2 ^ n.primeFactors.card) ^ 2 := by
      rw [show 4 = 2 * 2 by norm_num, mul_pow, pow_two]
    _ ≤ n.divisors.card ^ 2 := Nat.pow_le_pow_left htwo 2

theorem basePrimeMassConstant_nonneg : 0 ≤ basePrimeMassConstant := by
  rw [basePrimeMassConstant]
  apply ge_of_tendsto basePrimeMass_multipliable.hasProd
  exact Filter.Eventually.of_forall (fun s =>
    Finset.prod_nonneg (fun p _ => by
      have hb : 0 ≤ basePrimeWeight p := by
        rw [basePrimeWeight, if_pos p.property.two_le]
        positivity
      linarith))

/-- Pointwise divisor bound suitable for translated averaging.  This is the
literal `τ(|h|)^2 / √Q` shape (up to the universal convergent constant) used
by the manuscript; `h=0` remains explicitly excluded. -/
theorem sqrtWeightedRamanujanMass_le_card_divisors_sq
    (h : ℤ) (hh : h ≠ 0) :
    sqrtWeightedRamanujanMass h ≤
      basePrimeMassConstant * (h.natAbs.divisors.card : ℝ) ^ 2 := by
  have hstruct := sqrtWeightedRamanujanMass_le_divisorCorrection h hh
  rw [shiftPrimeCorrectionMass_eq_four_pow h hh] at hstruct
  have hpowNat := four_pow_primeFactors_card_le_card_divisors_sq
    h.natAbs (Int.natAbs_ne_zero.mpr hh)
  have hpowReal :
      ((4 ^ h.natAbs.primeFactors.card : ℕ) : ℝ) ≤
        (h.natAbs.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast hpowNat
  have hfour : (4 : ℝ) ^ h.natAbs.primeFactors.card =
      ((4 ^ h.natAbs.primeFactors.card : ℕ) : ℝ) := by norm_num
  rw [hfour] at hstruct
  calc
    sqrtWeightedRamanujanMass h ≤
        ((4 ^ h.natAbs.primeFactors.card : ℕ) : ℝ) *
          basePrimeMassConstant := hstruct
    _ ≤ (h.natAbs.divisors.card : ℝ) ^ 2 *
          basePrimeMassConstant :=
      mul_le_mul_of_nonneg_right hpowReal basePrimeMassConstant_nonneg
    _ = basePrimeMassConstant *
          (h.natAbs.divisors.card : ℝ) ^ 2 := by ring

theorem norm_truncatedSingularCoefficient_sub_singular_le_divisors
    {h : ℤ} (hh : h ≠ 0) (Q : ℕ) :
    ‖truncatedSingularCoefficient Q h -
        ((singularSeriesTotal h : ℝ) : ℂ)‖ ≤
      (basePrimeMassConstant * (h.natAbs.divisors.card : ℝ) ^ 2) /
        Real.sqrt (Q + 1) := by
  exact (norm_truncatedSingularCoefficient_sub_singular_unconditional hh Q).trans
    (div_le_div_of_nonneg_right
      (sqrtWeightedRamanujanMass_le_card_divisors_sq h hh)
      (Real.sqrt_nonneg _))

end

end MAPRamanujanTailWeighted
