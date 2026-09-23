import RamachandraTheorem6ShiftedStripSource
import PrimitiveEulerZeroTransport
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The source proof chain below Ramachandra Theorem 6

Printed p. 88 proves Theorem 6 by combining two ingredients:

1. a shifted-strip fourth moment over primitive characters at every
   conductor `d | q`, with logarithmic exponent `50 k^2`;
2. primitive induction and the finite missing-Euler-factor product.

For `k=2`, the primitive logarithmic exponent is `200`; the published
all-character conclusion uses exponent `400` and the factor
`exp(sqrt(log q))`.

The paper does not prove the shifted primitive estimate on p. 88.  It says
that it can be proved "in much the same way as Theorem 3".  The definitions
below isolate that exact analytic leaf separately from the deterministic
conductor partition, Euler transfer, and divisor/log absorption.  The final
theorem proves that these strictly lower obligations imply the literal
all-character Theorem 6 boundary; it never assumes Theorem 6 itself.
-/

namespace RamachandraTheorem6SourceProofChain

open scoped BigOperators
open Complex MeasureTheory
open RamachandraTheorem6ShiftedStripSource

noncomputable section

/-- The shifted fourth moment at one primitive conductor.  The `if` realizes
the star on the character sum printed in the intermediate estimate on p. 88. -/
def primitiveFamilyShiftedFourthIntegral
    (d : ℕ) [NeZero d] (T sigma : ℝ) : ℝ := by
  classical
  exact ∑ psi : DirichletCharacter ℂ d,
    if psi.IsPrimitive then
      ∫ t in (-T)..T, shiftedStripLFourth psi sigma t
    else 0

/-- Totalized version used to write an ordinary divisor sum.  The zero branch
is never reached for a divisor of a nonzero ambient modulus. -/
def primitiveFamilyShiftedFourthIntegralAt
    (d : ℕ) (T sigma : ℝ) : ℝ := by
  classical
  by_cases hd : d = 0
  · exact 0
  · letI : NeZero d := ⟨hd⟩
    exact primitiveFamilyShiftedFourthIntegral d T sigma

/-- The precise analytic leaf asserted, but not proved in detail, in the proof
of Theorem 6.  Its strip is the ambient `(q,T)` strip from Theorem 6, while the
moment is over primitive characters modulo each divisor `d | q`.

At `k=2`, `50 k^2 = 200` and `(dT)^(k/2) = dT`.  One absolute constant is
outside all arithmetic and height parameters. -/
def RamachandraPrimitiveShiftedFourthK2 : Prop :=
  ∃ Cprim : ℝ, 0 < Cprim ∧
    ∀ (q d : ℕ) [NeZero q] [NeZero d] (T sigma : ℝ),
      d ∣ q → 3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      primitiveFamilyShiftedFourthIntegral d T sigma ≤
        Cprim * ((d : ℝ) * T) *
          Real.log ((d : ℝ) * T) ^ 200

/-- One shifted fourth power after replacing an ambient character by its
unique primitive inducer. -/
def primitiveInducerShiftedFourth
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma t : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact ‖DirichletCharacter.LFunction chi.primitiveCharacter
    ((sigma : ℂ) + t * Complex.I)‖ ^ 4

/-- The moment after replacing each ambient character by its unique primitive
inducer.  This quantity contains no missing Euler factors. -/
def ambientPrimitiveInducerFourthIntegral
    (q : ℕ) [NeZero q] (T sigma : ℝ) : ℝ :=
  ∑ chi : DirichletCharacter ℂ q,
    ∫ t in (-T)..T, primitiveInducerShiftedFourth chi sigma t

/-- The divisor-indexed primitive-family mass in the conductor partition. -/
def primitiveDivisorFamilySum
    (q : ℕ) [NeZero q] (T sigma : ℝ) : ℝ :=
  ∑ d ∈ q.divisors, primitiveFamilyShiftedFourthIntegralAt d T sigma

/-- Exact finite conductor partition.  This is the type-correct form of
partitioning ambient characters by their conductor and replacing each by its
unique primitive inducer.  It is deterministic, but Mathlib currently has no
packaged dependent equivalence for this family reindex, so it remains a
separate first-order obligation rather than being hidden in the analytic
source statement. -/
def RamachandraConductorPartitionIdentity : Prop :=
  ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
    ambientPrimitiveInducerFourthIntegral q T sigma =
      primitiveDivisorFamilySum q T sigma

/-! ## Exact dependent conductor reindex -/

theorem cast_dirichletCharacter_eq_of_changeLevel_eq
    {c d q : ℕ} [NeZero q]
    (h : c = d) (hcq : c ∣ q) (hdq : d ∣ q)
    (chi : DirichletCharacter ℂ c) (psi : DirichletCharacter ℂ d)
    (heq : DirichletCharacter.changeLevel hcq chi =
      DirichletCharacter.changeLevel hdq psi) :
    cast (congrArg (fun n => DirichletCharacter ℂ n) h) chi = psi := by
  subst d
  have hp : hcq = hdq := Subsingleton.elim _ _
  subst hp
  exact DirichletCharacter.changeLevel_injective hcq heq

/-- Computation of the dependent cast used by the conductor equivalence. -/
theorem rec_primitiveSubtype_val
    {q c d : ℕ} (hc : c = d)
    (pc : c ∈ q.divisors) (pd : d ∈ q.divisors)
    (x : {psi : DirichletCharacter ℂ c // psi.IsPrimitive}) :
    let A := {n : ℕ // n ∈ q.divisors}
    let F : A → Type := fun z =>
      {psi : DirichletCharacter ℂ z.1 // psi.IsPrimitive}
    let ac : A := ⟨c, pc⟩
    let ad : A := ⟨d, pd⟩
    let hsub : ac = ad := Subtype.ext hc
    ((Eq.recOn hsub x : F ad) : DirichletCharacter ℂ d) =
      cast (congrArg (fun n => DirichletCharacter ℂ n) hc)
        (x : DirichletCharacter ℂ c) := by
  subst d
  rfl

/-- Inducing a primitive character from a divisor `d` to level `q` preserves
its conductor exactly. -/
theorem conductor_changeLevel_of_primitive
    {d q : ℕ} [NeZero d] [NeZero q]
    (hd : d ∣ q) (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive) :
    (DirichletCharacter.changeLevel hd psi).conductor = d := by
  let chi : DirichletCharacter ℂ q :=
    DirichletCharacter.changeLevel hd psi
  have hfacd : chi.FactorsThrough d :=
    DirichletCharacter.changeLevel_factorsThrough psi hd
  have hcdvd : chi.conductor ∣ d :=
    DirichletCharacter.conductor_dvd_of_mem_conductorSet chi hfacd
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have heq :
      DirichletCharacter.changeLevel hcdvd chi.primitiveCharacter = psi := by
    apply DirichletCharacter.changeLevel_injective hd
    rw [← DirichletCharacter.changeLevel_trans]
    rw [chi.changeLevel_primitiveCharacter]
  have hfacC : psi.FactorsThrough chi.conductor :=
    ⟨hcdvd, chi.primitiveCharacter, heq.symm⟩
  have hdvdC : d ∣ chi.conductor := by
    rw [← hprim]
    exact DirichletCharacter.conductor_dvd_of_mem_conductorSet psi hfacC
  exact Nat.dvd_antisymm hcdvd hdvdC

/-- The finite dependent family of primitive characters over all `d | q`. -/
noncomputable def PrimitiveCharacterOverDivisors (q : ℕ) :=
  Σ d : {d : ℕ // d ∈ q.divisors},
    {psi : DirichletCharacter ℂ d.1 // psi.IsPrimitive}

noncomputable instance primitiveCharacterOverDivisorsFintype (q : ℕ) :
    Fintype (PrimitiveCharacterOverDivisors q) := by
  classical
  unfold PrimitiveCharacterOverDivisors
  letI (d : {d : ℕ // d ∈ q.divisors}) : Fintype
      {psi : DirichletCharacter ℂ d.1 // psi.IsPrimitive} :=
    Fintype.ofFinite _
  infer_instance

noncomputable def toPrimitiveOverDivisors (q : ℕ) [NeZero q]
    (chi : DirichletCharacter ℂ q) : PrimitiveCharacterOverDivisors q :=
  ⟨⟨chi.conductor, Nat.mem_divisors.mpr
      ⟨chi.conductor_dvd_level, NeZero.ne q⟩⟩,
    ⟨chi.primitiveCharacter, chi.primitiveCharacter_isPrimitive⟩⟩

noncomputable def fromPrimitiveOverDivisors (q : ℕ) [NeZero q]
    (z : PrimitiveCharacterOverDivisors q) :
    DirichletCharacter ℂ q := by
  rcases z with ⟨⟨d, hd⟩, ⟨psi, hpsi⟩⟩
  exact DirichletCharacter.changeLevel
    (Nat.dvd_of_mem_divisors hd) psi

/-- Characters modulo `q` are exactly primitive characters at the unique
conductors dividing `q`. -/
noncomputable def characterPrimitiveDivisorEquiv (q : ℕ) [NeZero q] :
    DirichletCharacter ℂ q ≃ PrimitiveCharacterOverDivisors q where
  toFun := toPrimitiveOverDivisors q
  invFun := fromPrimitiveOverDivisors q
  left_inv := by
    intro chi
    exact chi.changeLevel_primitiveCharacter
  right_inv := by
    intro z
    rcases z with ⟨⟨d, hdmem⟩, ⟨psi, hprim⟩⟩
    letI : NeZero d :=
      ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors hdmem)⟩
    let hd : d ∣ q := Nat.dvd_of_mem_divisors hdmem
    have hc : (DirichletCharacter.changeLevel hd psi).conductor = d :=
      conductor_changeLevel_of_primitive hd psi hprim
    have hcast : cast
        (congrArg (fun n => DirichletCharacter ℂ n) hc)
          (DirichletCharacter.changeLevel hd psi).primitiveCharacter = psi :=
      cast_dirichletCharacter_eq_of_changeLevel_eq hc
        (DirichletCharacter.changeLevel hd psi).conductor_dvd_level hd _ _
        (by rw [(DirichletCharacter.changeLevel hd psi).changeLevel_primitiveCharacter])
    refine Sigma.eq (Subtype.ext hc) ?_
    apply Subtype.ext
    dsimp [toPrimitiveOverDivisors, fromPrimitiveOverDivisors]
    rw [rec_primitiveSubtype_val hc]
    exact hcast

noncomputable def primitiveSigmaMoment
    (q : ℕ) [NeZero q] (T sigma : ℝ)
    (z : PrimitiveCharacterOverDivisors q) : ℝ := by
  rcases z with ⟨⟨d, hdmem⟩, ⟨psi, hprim⟩⟩
  letI : NeZero d :=
    ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors hdmem)⟩
  exact ∫ t in (-T)..T, shiftedStripLFourth psi sigma t

set_option backward.isDefEq.respectTransparency.types false in
/-- The dependent conductor partition is fully deterministic and requires no
analytic input. -/
theorem ramachandraConductorPartitionIdentity :
    RamachandraConductorPartitionIdentity := by
  classical
  intro q _inst T sigma
  letI (d : {d : ℕ // d ∈ q.divisors}) : Fintype
      {psi : DirichletCharacter ℂ d.1 // psi.IsPrimitive} :=
    Fintype.ofFinite _
  letI : Fintype (PrimitiveCharacterOverDivisors q) := by
    unfold PrimitiveCharacterOverDivisors
    infer_instance
  unfold ambientPrimitiveInducerFourthIntegral primitiveDivisorFamilySum
  calc
    (∑ chi : DirichletCharacter ℂ q,
        ∫ t in (-T)..T, primitiveInducerShiftedFourth chi sigma t) =
      ∑ chi : DirichletCharacter ℂ q,
        primitiveSigmaMoment q T sigma
          (characterPrimitiveDivisorEquiv q chi) := by
      apply Finset.sum_congr rfl
      intro chi hchi
      rfl
    _ = ∑ z : PrimitiveCharacterOverDivisors q,
        primitiveSigmaMoment q T sigma z :=
      characterPrimitiveDivisorEquiv q |>.sum_comp
        (primitiveSigmaMoment q T sigma)
    _ = ∑ d ∈ q.divisors,
        primitiveFamilyShiftedFourthIntegralAt d T sigma := by
      change (∑ z : (Σ d : {d : ℕ // d ∈ q.divisors},
        {psi : DirichletCharacter ℂ d.1 // psi.IsPrimitive}),
          primitiveSigmaMoment q T sigma z) = _
      rw [Fintype.sum_sigma]
      calc
        (∑ d : {d : ℕ // d ∈ q.divisors},
            ∑ psi : {psi : DirichletCharacter ℂ d.1 // psi.IsPrimitive},
              primitiveSigmaMoment q T sigma ⟨d, psi⟩) =
          ∑ d : {d : ℕ // d ∈ q.divisors},
            primitiveFamilyShiftedFourthIntegralAt d.1 T sigma := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdne : d.1 ≠ 0 :=
            Nat.ne_of_gt (Nat.pos_of_mem_divisors d.2)
          letI : NeZero d.1 := ⟨hdne⟩
          unfold primitiveFamilyShiftedFourthIntegralAt
          simp only [hdne, ↓reduceDIte]
          unfold primitiveFamilyShiftedFourthIntegral
          rw [← Finset.sum_filter]
          rw [Finset.sum_subtype
            (p := fun psi : DirichletCharacter ℂ d.1 => psi.IsPrimitive)
            (Finset.univ.filter
              (fun psi : DirichletCharacter ℂ d.1 => psi.IsPrimitive))
            (by simp)]
          apply Finset.sum_congr rfl
          intro psi hpsi
          rfl
        _ = ∑ d ∈ q.divisors,
            primitiveFamilyShiftedFourthIntegralAt d T sigma := by
          rw [Finset.sum_subtype
            (p := fun x : ℕ => x ∈ q.divisors)
            q.divisors (fun x => by simp)]

/-- Exact aggregate consequence of the change-of-level Euler product used on
p. 88.  It contains only the finite imprimitive correction: the target on the
right is still the uncontrolled primitive-inducer moment.

The absolute constant absorbs the finitely many small moduli in the source's
`O`-estimate for the missing Euler product. -/
def RamachandraImprimitiveEulerTransferK2 : Prop :=
  ∃ Ceuler : ℝ, 0 < Ceuler ∧
    ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
      3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      allCharacterShiftedStripFourthIntegral q T sigma ≤
        Ceuler * Real.exp (Real.sqrt (Real.log (q : ℝ))) *
          ambientPrimitiveInducerFourthIntegral q T sigma

/-- The genuinely local number-theoretic input behind the aggregate Euler
transfer: the fourth power of the finite missing-Euler-factor product has the
source's `exp(sqrt(log q))` envelope throughout the shifted strip. -/
def RamachandraEulerProductEnvelopeK2 : Prop :=
  ∃ Ceuler : ℝ, 0 < Ceuler ∧
    ∀ (q : ℕ) [NeZero q] (T sigma : ℝ), 3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      ∀ (chi : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ T →
      ‖PrimitiveEulerZeroTransport.eulerCorrection chi
          ((sigma : ℂ) + t * Complex.I)‖ ^ 4 ≤
        Ceuler * Real.exp (Real.sqrt (Real.log (q : ℝ)))

/-- The elementary divisor-sum/logarithm absorption left after applying the
primitive moment at every `d | q`.  It is deliberately separated from both
analytic inputs.  The gap from exponent `200` to exponent `400` has ample room
for the divisor sum, exactly as in the printed theorem. -/
def RamachandraDivisorLogAbsorptionK2 : Prop :=
  ∃ Cdiv : ℝ, 0 < Cdiv ∧
    ∀ (q : ℕ) [NeZero q] (T : ℝ), 3 ≤ T →
      (∑ d ∈ q.divisors,
          (d : ℝ) * T * Real.log ((d : ℝ) * T) ^ 200) ≤
        Cdiv * ((q : ℝ) * T) *
          Real.log ((q : ℝ) * T) ^ 400

/-! ## From the local Euler product to the aggregate transfer -/

/-- The source strip lies strictly to the left of the possible principal pole
at `1`; this is the only geometric fact needed for continuity and the exact
change-of-level identity. -/
theorem sigma_lt_one_of_ramachandraStrip
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) : sigma < 1 := by
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hTpos : 0 < T := by linarith
  have hprodpos : 0 < (q : ℝ) * T := mul_pos hqpos hTpos
  have hthree : (3 : ℝ) ≤ (q : ℝ) * T := by
    nlinarith [mul_le_mul hqone hT
      (by norm_num : (0 : ℝ) ≤ 3) hqpos.le]
  have hlogthree : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hlogone : 1 < Real.log ((q : ℝ) * T) := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3) hprodpos hthree
    exact hlogthree.trans_le hmono
  have hden : (100 : ℝ) <
      100 * Real.log ((q : ℝ) * T) := by nlinarith
  have hinv : (100 * Real.log ((q : ℝ) * T))⁻¹ <
      (100 : ℝ)⁻¹ := by
    exact (inv_lt_inv₀
      (by positivity : (0 : ℝ) < 100 * Real.log ((q : ℝ) * T))
      (by norm_num : (0 : ℝ) < 100)).2 hden
  have hupper : sigma - (1 / 2 : ℝ) ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹ :=
    (le_abs_self _).trans hstrip
  have hoff : sigma - (1 / 2 : ℝ) < (1 / 2 : ℝ) :=
    hupper.trans_lt (hinv.trans (by norm_num))
  linarith

theorem continuous_shiftedStripLFourth
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hsigma : sigma < 1) :
    Continuous (fun t : ℝ => shiftedStripLFourth chi sigma t) := by
  unfold shiftedStripLFourth
  apply Continuous.pow
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  have harg : ((sigma : ℂ) + t * Complex.I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have houter := (DirichletCharacter.differentiableAt_LFunction chi _
    (.inl harg)).continuousAt
  have hinner : ContinuousAt
      (fun u : ℝ => (sigma : ℂ) + u * Complex.I) t := by fun_prop
  exact ContinuousAt.comp_of_eq houter hinner rfl

theorem continuous_primitiveInducerShiftedFourth
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hsigma : sigma < 1) :
    Continuous (fun t : ℝ =>
      primitiveInducerShiftedFourth chi sigma t) := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  unfold primitiveInducerShiftedFourth
  exact continuous_shiftedStripLFourth chi.primitiveCharacter hsigma

/-- The local Euler-product envelope implies the exact aggregate transfer.
All remaining work here is continuity, interval integration, and summation. -/
theorem ramachandraImprimitiveEulerTransferK2_of_productEnvelope
    (henvelope : RamachandraEulerProductEnvelopeK2) :
    RamachandraImprimitiveEulerTransferK2 := by
  classical
  obtain ⟨Ceuler, hCeuler, henvelope⟩ := henvelope
  refine ⟨Ceuler, hCeuler, ?_⟩
  intro q _inst T sigma hT hstrip
  have hsigma : sigma < 1 :=
    sigma_lt_one_of_ramachandraStrip hT hstrip
  unfold allCharacterShiftedStripFourthIntegral
    ambientPrimitiveInducerFourthIntegral
  calc
    (∑ chi : DirichletCharacter ℂ q,
        ∫ t in (-T)..T, shiftedStripLFourth chi sigma t) ≤
      ∑ chi : DirichletCharacter ℂ q,
        (Ceuler * Real.exp (Real.sqrt (Real.log (q : ℝ)))) *
          ∫ t in (-T)..T,
            primitiveInducerShiftedFourth chi sigma t := by
      apply Finset.sum_le_sum
      intro chi hchi
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      have hambCont := continuous_shiftedStripLFourth chi hsigma
      have hprimCont :=
        continuous_primitiveInducerShiftedFourth chi hsigma
      have hpoint : ∀ t ∈ Set.Icc (-T) T,
          shiftedStripLFourth chi sigma t ≤
            (Ceuler * Real.exp (Real.sqrt (Real.log (q : ℝ)))) *
              primitiveInducerShiftedFourth chi sigma t := by
        intro t ht
        have htbound : |t| ≤ T := by
          rw [abs_le]
          exact ⟨by linarith [ht.1], ht.2⟩
        have harg : ((sigma : ℂ) + t * Complex.I) ≠ 1 := by
          intro h
          have hre := congrArg Complex.re h
          norm_num at hre
          linarith
        have hL :=
          PrimitiveEulerZeroTransport.LFunction_eq_primitive_mul_eulerCorrection
            chi (s := ((sigma : ℂ) + t * Complex.I)) (Or.inr harg)
        unfold shiftedStripLFourth primitiveInducerShiftedFourth
        rw [hL, norm_mul, mul_pow]
        have hcorr := mul_le_mul_of_nonneg_left
          (henvelope q T sigma hT hstrip chi t htbound)
          (pow_nonneg (norm_nonneg
            (DirichletCharacter.LFunction chi.primitiveCharacter
              ((sigma : ℂ) + t * Complex.I))) 4)
        simpa [mul_comm] using hcorr
      calc
        (∫ t in (-T)..T, shiftedStripLFourth chi sigma t) ≤
            ∫ t in (-T)..T,
              (Ceuler * Real.exp (Real.sqrt (Real.log (q : ℝ)))) *
                primitiveInducerShiftedFourth chi sigma t := by
          apply intervalIntegral.integral_mono_on (by linarith)
          · exact hambCont.intervalIntegrable _ _
          · exact (continuous_const.mul hprimCont).intervalIntegrable _ _
          · exact hpoint
        _ = (Ceuler * Real.exp (Real.sqrt (Real.log (q : ℝ)))) *
            ∫ t in (-T)..T,
              primitiveInducerShiftedFourth chi sigma t := by
          rw [intervalIntegral.integral_const_mul]
    _ = (Ceuler * Real.exp (Real.sqrt (Real.log (q : ℝ)))) *
        ∑ chi : DirichletCharacter ℂ q,
          ∫ t in (-T)..T,
            primitiveInducerShiftedFourth chi sigma t := by
      rw [Finset.mul_sum]

/-! ## Closing the elementary divisor/log leaf -/

/-- The sum of the positive divisors is at most
`q * (1 + log q)`.  The proof reindexes divisors by `d ↦ q/d` and embeds the
resulting reciprocal sum into the harmonic sum. -/
theorem sum_divisors_cast_le_mul_one_add_log (q : ℕ) [NeZero q] :
    (∑ d ∈ q.divisors, (d : ℝ)) ≤
      (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  classical
  have hqpos : 0 < q := NeZero.pos q
  have hsumNat : (∑ d ∈ q.divisors, q / d) =
      ∑ d ∈ q.divisors, d := by
    simpa using Nat.sum_div_divisors q (fun d => d)
  have hrewrite :
      (∑ d ∈ q.divisors, (d : ℝ)) =
        (q : ℝ) * ∑ d ∈ q.divisors, ((d : ℝ)⁻¹) := by
    calc
      (∑ d ∈ q.divisors, (d : ℝ)) =
          ((∑ d ∈ q.divisors, d : ℕ) : ℝ) := by push_cast; rfl
      _ = ((∑ d ∈ q.divisors, q / d : ℕ) : ℝ) := by rw [hsumNat]
      _ = ∑ d ∈ q.divisors, ((q / d : ℕ) : ℝ) := by norm_cast
      _ = ∑ d ∈ q.divisors, (q : ℝ) * (d : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdvd : d ∣ q := Nat.dvd_of_mem_divisors hd
        have hdne : (d : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))
        rw [Nat.cast_div hdvd hdne, div_eq_mul_inv]
      _ = (q : ℝ) * ∑ d ∈ q.divisors, ((d : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
  have hsubset : q.divisors ⊆ Finset.Icc 1 q := by
    intro d hd
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  have hrecip :
      (∑ d ∈ q.divisors, ((d : ℝ)⁻¹)) ≤ (harmonic q : ℝ) := by
    calc
      (∑ d ∈ q.divisors, ((d : ℝ)⁻¹)) ≤
          ∑ d ∈ Finset.Icc 1 q, ((d : ℝ)⁻¹) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro d hd hnot
        positivity
      _ = (harmonic q : ℝ) := by
        rw [harmonic_eq_sum_Icc, Rat.cast_sum]
        simp
  rw [hrewrite]
  calc
    (q : ℝ) * ∑ d ∈ q.divisors, ((d : ℝ)⁻¹) ≤
        (q : ℝ) * (harmonic q : ℝ) := by
      exact mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ ≤ (q : ℝ) * (1 + Real.log (q : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (harmonic_le_one_add_log q) (by positivity)

/-- The divisor/log absorption on p. 88 is unconditional.  In fact an
absolute constant `2` suffices: the divisor sum costs one harmonic logarithm,
and `T >= 3` gives `1 <= log(qT)`, so exponent `201` is absorbed by `400`. -/
theorem ramachandraDivisorLogAbsorptionK2 :
    RamachandraDivisorLogAbsorptionK2 := by
  refine ⟨2, by norm_num, ?_⟩
  intro q _inst T hT
  let L : ℝ := Real.log ((q : ℝ) * T)
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hprodpos : 0 < (q : ℝ) * T := mul_pos hqpos hTpos
  have hthree : (3 : ℝ) ≤ (q : ℝ) * T := by
    nlinarith [mul_le_mul hqone hT
      (by norm_num : (0 : ℝ) ≤ 3) hqpos.le]
  have hlogthree : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hLone : 1 ≤ L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3) hprodpos hthree
    exact (hlogthree.trans_le hmono).le
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hlogq : Real.log (q : ℝ) ≤ L := by
    have hqle : (q : ℝ) ≤ (q : ℝ) * T := by nlinarith
    exact Real.strictMonoOn_log.monotoneOn hqpos hprodpos hqle
  have hsumPoint :
      (∑ d ∈ q.divisors,
          (d : ℝ) * T * Real.log ((d : ℝ) * T) ^ 200) ≤
        ∑ d ∈ q.divisors, (d : ℝ) * T * L ^ 200 := by
    apply Finset.sum_le_sum
    intro d hd
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_mem_divisors hd
    have hdle : (d : ℝ) ≤ q := by
      exact_mod_cast Nat.divisor_le hd
    have hdTpos : 0 < (d : ℝ) * T := mul_pos hdpos hTpos
    have hdTle : (d : ℝ) * T ≤ (q : ℝ) * T :=
      mul_le_mul_of_nonneg_right hdle hTpos.le
    have hlogle : Real.log ((d : ℝ) * T) ≤ L :=
      Real.strictMonoOn_log.monotoneOn hdTpos hprodpos hdTle
    have hlogd0 : 0 ≤ Real.log ((d : ℝ) * T) := by
      apply Real.log_nonneg
      nlinarith [mul_le_mul
        (show (1 : ℝ) ≤ d by
          exact_mod_cast Nat.pos_of_mem_divisors hd)
        hTone (by positivity : (0 : ℝ) ≤ 1) hdpos.le]
    have hp := pow_le_pow_left₀ hlogd0 hlogle 200
    exact mul_le_mul_of_nonneg_left hp
      (mul_nonneg hdpos.le hTpos.le)
  have hsumd := sum_divisors_cast_le_mul_one_add_log q
  have hfac0 : 0 ≤ T * L ^ 200 :=
    mul_nonneg hTpos.le (pow_nonneg hL0 _)
  have hsumRewrite :
      (∑ d ∈ q.divisors, (d : ℝ) * T * L ^ 200) =
        (T * L ^ 200) * ∑ d ∈ q.divisors, (d : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hlogsum : 1 + Real.log (q : ℝ) ≤ 2 * L := by linarith
  have hpows : L ^ 201 ≤ L ^ 400 :=
    pow_le_pow_right₀ hLone (by norm_num)
  calc
    (∑ d ∈ q.divisors,
        (d : ℝ) * T * Real.log ((d : ℝ) * T) ^ 200) ≤
      ∑ d ∈ q.divisors, (d : ℝ) * T * L ^ 200 := hsumPoint
    _ = (T * L ^ 200) * ∑ d ∈ q.divisors, (d : ℝ) := hsumRewrite
    _ ≤ (T * L ^ 200) *
        ((q : ℝ) * (1 + Real.log (q : ℝ))) :=
      mul_le_mul_of_nonneg_left hsumd hfac0
    _ ≤ (T * L ^ 200) * ((q : ℝ) * (2 * L)) := by gcongr
    _ = 2 * ((q : ℝ) * T) * L ^ 201 := by ring
    _ ≤ 2 * ((q : ℝ) * T) * L ^ 400 := by
      exact mul_le_mul_of_nonneg_left hpows (by positivity)
    _ = 2 * ((q : ℝ) * T) *
        Real.log ((q : ℝ) * T) ^ 400 := by rfl

/-- The primitive analytic input and the exact conductor partition bound the
full primitive-inducer family by the divisor budget. -/
theorem ambientPrimitiveInducerFourthIntegral_le_divisorBudget
    (hprim : RamachandraPrimitiveShiftedFourthK2)
    (hpartition : RamachandraConductorPartitionIdentity)
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    ∃ Cprim : ℝ, 0 < Cprim ∧
      ambientPrimitiveInducerFourthIntegral q T sigma ≤
        Cprim * (∑ d ∈ q.divisors,
          (d : ℝ) * T * Real.log ((d : ℝ) * T) ^ 200) := by
  classical
  obtain ⟨Cprim, hCprim, hsource⟩ := hprim
  refine ⟨Cprim, hCprim, ?_⟩
  unfold RamachandraConductorPartitionIdentity at hpartition
  rw [hpartition q T sigma]
  unfold primitiveDivisorFamilySum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
  letI : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
  simpa [primitiveFamilyShiftedFourthIntegralAt, hdne, mul_assoc] using hsource q d T sigma
    (Nat.dvd_of_mem_divisors hd) hT hstrip

/-- Complete formal implication from the four source-level obligations to the
literal `k=2` statement of Ramachandra Theorem 6.  No premise is the desired
all-character theorem itself. -/
theorem ramachandraTheorem6K2Source_of_proofChain
    (hprim : RamachandraPrimitiveShiftedFourthK2)
    (hpartition : RamachandraConductorPartitionIdentity)
    (heuler : RamachandraImprimitiveEulerTransferK2)
    (hdivisor : RamachandraDivisorLogAbsorptionK2) :
    RamachandraTheorem6K2Source := by
  classical
  obtain ⟨Cprim, hCprim, hprimSource⟩ := hprim
  obtain ⟨Ceuler, hCeuler, heulerSource⟩ := heuler
  obtain ⟨Cdiv, hCdiv, hdivisorSource⟩ := hdivisor
  refine ⟨Ceuler * Cprim * Cdiv, by positivity, ?_⟩
  intro q _inst T sigma hT hstrip
  unfold RamachandraConductorPartitionIdentity at hpartition
  have hprimitive :
      ambientPrimitiveInducerFourthIntegral q T sigma ≤
        Cprim * (∑ d ∈ q.divisors,
          (d : ℝ) * T * Real.log ((d : ℝ) * T) ^ 200) := by
    rw [hpartition q T sigma]
    unfold primitiveDivisorFamilySum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
    letI : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
    simpa [primitiveFamilyShiftedFourthIntegralAt, hdne, mul_assoc] using hprimSource q d T sigma
      (Nat.dvd_of_mem_divisors hd) hT hstrip
  have hdiv := hdivisorSource q T hT
  have hprimitiveFinal :
      ambientPrimitiveInducerFourthIntegral q T sigma ≤
        (Cprim * Cdiv) * ((q : ℝ) * T) *
          Real.log ((q : ℝ) * T) ^ 400 := by
    calc
      ambientPrimitiveInducerFourthIntegral q T sigma ≤
          Cprim * (∑ d ∈ q.divisors,
            (d : ℝ) * T * Real.log ((d : ℝ) * T) ^ 200) := hprimitive
      _ ≤ Cprim *
          (Cdiv * ((q : ℝ) * T) *
            Real.log ((q : ℝ) * T) ^ 400) :=
        mul_le_mul_of_nonneg_left hdiv hCprim.le
      _ = (Cprim * Cdiv) * ((q : ℝ) * T) *
          Real.log ((q : ℝ) * T) ^ 400 := by ring
  have hexp0 : 0 ≤ Real.exp (Real.sqrt (Real.log (q : ℝ))) :=
    (Real.exp_pos _).le
  have hfactor0 : 0 ≤ Ceuler *
      Real.exp (Real.sqrt (Real.log (q : ℝ))) :=
    mul_nonneg hCeuler.le hexp0
  calc
    allCharacterShiftedStripFourthIntegral q T sigma ≤
        Ceuler * Real.exp (Real.sqrt (Real.log (q : ℝ))) *
          ambientPrimitiveInducerFourthIntegral q T sigma :=
      heulerSource q T sigma hT hstrip
    _ ≤ Ceuler * Real.exp (Real.sqrt (Real.log (q : ℝ))) *
        ((Cprim * Cdiv) * ((q : ℝ) * T) *
          Real.log ((q : ℝ) * T) ^ 400) :=
      mul_le_mul_of_nonneg_left hprimitiveFinal hfactor0
    _ = (Ceuler * Cprim * Cdiv) *
        ramachandraTheorem6K2Scale q T := by
      unfold ramachandraTheorem6K2Scale
      ring

/-- Reduced constructor after discharging the aggregate Euler transfer and
the divisor/log absorption.  The only remaining inputs are the paper's
shifted primitive estimate, the exact conductor reindex, and the local finite
Euler-product envelope. -/
theorem ramachandraTheorem6K2Source_of_primitive_partition_eulerEnvelope
    (hprim : RamachandraPrimitiveShiftedFourthK2)
    (hpartition : RamachandraConductorPartitionIdentity)
    (henvelope : RamachandraEulerProductEnvelopeK2) :
    RamachandraTheorem6K2Source :=
  ramachandraTheorem6K2Source_of_proofChain hprim hpartition
    (ramachandraImprimitiveEulerTransferK2_of_productEnvelope henvelope)
    ramachandraDivisorLogAbsorptionK2

end
end RamachandraTheorem6SourceProofChain

#print axioms RamachandraTheorem6SourceProofChain.ambientPrimitiveInducerFourthIntegral_le_divisorBudget
#print axioms RamachandraTheorem6SourceProofChain.sum_divisors_cast_le_mul_one_add_log
#print axioms RamachandraTheorem6SourceProofChain.ramachandraDivisorLogAbsorptionK2
#print axioms RamachandraTheorem6SourceProofChain.ramachandraImprimitiveEulerTransferK2_of_productEnvelope
#print axioms RamachandraTheorem6SourceProofChain.ramachandraTheorem6K2Source_of_proofChain
#print axioms RamachandraTheorem6SourceProofChain.ramachandraTheorem6K2Source_of_primitive_partition_eulerEnvelope
