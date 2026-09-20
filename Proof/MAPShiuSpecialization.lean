import ShiuFoundation
import Mathlib.Data.ZMod.Units

/-!
# Literal Shiu specialization used by the MAP mixed mean

No Shiu estimate is asserted here.  The analytic statements are definitions
of propositions.  The theorems prove the exact quotient-window and primitive
residue reductions needed to instantiate such a theorem.
-/

namespace MAPShiuSpecialization

open ArithmeticFunction MixedMellinCert DeterminantCountWeld ShiuFoundation
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-- Exact upper endpoint after dividing `(N,2N]` by `content`. -/
def quotientUpper (N content : ℕ) : ℕ := (2 * N) / content

/-- Exact length of the quotient interval.  This deliberately retains both
floors. -/
def quotientLength (N content : ℕ) : ℕ :=
  quotientUpper N content - N / content

theorem quotientLength_le_upper (N content : ℕ) :
    quotientLength N content ≤ quotientUpper N content := by
  exact Nat.sub_le _ _

/-- The floor-sensitive quotient window still has length at least `N/content`.
This is the elementary lower bound used when checking Shiu's range. -/
theorem quotientLower_le_length (N content : ℕ) :
    N / content ≤ quotientLength N content := by
  have hdouble : 2 * (N / content) ≤ (2 * N) / content :=
    Nat.mul_div_le_mul_div_assoc 2 N content
  unfold quotientLength quotientUpper
  omega

/-- The divisor-square sum in one primitive residue class on the exact
quotient of `(N,2N]`. -/
def quotientProgressionSum (k N content modulus residue : ℕ) : ℕ :=
  progressionSum ((tauAF k).pmul (tauAF k))
    (quotientUpper N content) (quotientLength N content) modulus residue

def quotientProgressionSet (N content modulus residue : ℕ) : Finset ℕ :=
  (quotientDyadic N content).filter fun n => n ≡ residue [MOD modulus]

theorem quotientWindow_eq_Ioc (N content : ℕ) :
    Finset.Ioc (quotientUpper N content - quotientLength N content)
        (quotientUpper N content) =
      quotientDyadic N content := by
  symm
  exact quotientDyadic_eq_shiuWindow N content

theorem quotientProgressionSum_eq (k N content modulus residue : ℕ) :
    quotientProgressionSum k N content modulus residue =
      ∑ n ∈ quotientDyadic N content,
        if n ≡ residue [MOD modulus] then tauAF k n ^ 2 else 0 := by
  classical
  unfold quotientProgressionSum progressionSum
  rw [quotientWindow_eq_Ioc]
  apply Finset.sum_congr rfl
  intro n _
  simp [ArithmeticFunction.pmul_apply, pow_two]

theorem quotientProgressionSum_eq_sum_set (k N content modulus residue : ℕ) :
    quotientProgressionSum k N content modulus residue =
      ∑ n ∈ quotientProgressionSet N content modulus residue, tauAF k n ^ 2 := by
  classical
  rw [quotientProgressionSum_eq]
  exact (Finset.sum_filter (fun n => n ≡ residue [MOD modulus])
    (fun n => tauAF k n ^ 2)).symm

/-- The exact direct-residue theorem required after determinant contents are
removed.  It is a proposition, not an axiom. -/
def DyadicQuotientTauSquareShiuTarget : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C x₀ : ℕ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ N content modulus residue : ℕ,
        x₀ ≤ quotientUpper N content →
        0 < modulus → residue < modulus → residue.Coprime modulus →
        quotientLength N content ≤ quotientUpper N content →
        quotientUpper N content < quotientLength N content ^ 3 →
        modulus ^ 3 < quotientLength N content ^ 2 →
        modulus * quotientProgressionSum k N content modulus residue ≤
          C * quotientLength N content *
            (Nat.log 2 (quotientUpper N content + 2) + 1) ^ (k * k)

/-- Shiu's general dyadic target specializes to the literal floor-sensitive
quotient window without any analytic work. -/
theorem dyadicTarget_implies_quotientTarget
    (hShiu : DyadicTauSquareShiuTarget) :
    DyadicQuotientTauSquareShiuTarget := by
  intro k hk
  obtain ⟨C, x₀, hC, hx₀, hbound⟩ := hShiu k hk
  refine ⟨C, x₀, hC, hx₀, ?_⟩
  intro N content modulus residue hx hmod hres hcop hyx hxy hmy
  exact hbound (quotientUpper N content) (quotientLength N content)
    modulus residue hx hmod hres hcop hyx hxy hmy

/-! ## Removing the multiplier from a primitive congruence -/

/-- Multiplication by a unit modulo `modulus` carries a primitive right-hand
side to one unique primitive residue class. -/
theorem exists_primitive_residue_for_twist
    {multiplier rhs modulus : ℕ}
    (hmod : 0 < modulus)
    (hmul : multiplier.Coprime modulus)
    (hrhs : rhs.Coprime modulus) :
    ∃ residue : ℕ, residue < modulus ∧ residue.Coprime modulus ∧
      ∀ n : ℕ,
        (multiplier * n ≡ rhs [MOD modulus] ↔
          n ≡ residue [MOD modulus]) := by
  letI : NeZero modulus := ⟨Nat.ne_of_gt hmod⟩
  have hmulUnit : IsUnit (multiplier : ZMod modulus) :=
    (ZMod.isUnit_iff_coprime multiplier modulus).2 hmul
  have hrhsUnit : IsUnit (rhs : ZMod modulus) :=
    (ZMod.isUnit_iff_coprime rhs modulus).2 hrhs
  let u : (ZMod modulus)ˣ := hmulUnit.unit⁻¹ * hrhsUnit.unit
  let residue : ℕ := (u : ZMod modulus).val
  have hreslt : residue < modulus := ZMod.val_lt (u : ZMod modulus)
  have hrescast : (residue : ZMod modulus) = (u : ZMod modulus) := by
    exact ZMod.natCast_zmod_val (u : ZMod modulus)
  have hresunit : IsUnit (residue : ZMod modulus) := by
    rw [hrescast]
    exact Units.isUnit u
  have hrescop : residue.Coprime modulus :=
    (ZMod.isUnit_iff_coprime residue modulus).1 hresunit
  refine ⟨residue, hreslt, hrescop, ?_⟩
  intro n
  rw [← ZMod.natCast_eq_natCast_iff n residue modulus,
    ← ZMod.natCast_eq_natCast_iff (multiplier * n) rhs modulus,
    Nat.cast_mul, hrescast]
  change (multiplier : ZMod modulus) * (n : ZMod modulus) = (rhs : ZMod modulus) ↔
    (n : ZMod modulus) = (u : ZMod modulus)
  have hmulcoe : (↑hmulUnit.unit : ZMod modulus) = (multiplier : ZMod modulus) :=
    hmulUnit.unit_spec
  have hrhscoe : (↑hrhsUnit.unit : ZMod modulus) = (rhs : ZMod modulus) :=
    hrhsUnit.unit_spec
  constructor
  · intro h
    calc
      (n : ZMod modulus) =
          (↑hmulUnit.unit⁻¹ : ZMod modulus) *
            ((↑hmulUnit.unit : ZMod modulus) * (n : ZMod modulus)) := by
              rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = (↑hmulUnit.unit⁻¹ : ZMod modulus) *
            ((multiplier : ZMod modulus) * (n : ZMod modulus)) := by rw [hmulcoe]
      _ = (↑hmulUnit.unit⁻¹ : ZMod modulus) * (rhs : ZMod modulus) := by rw [h]
      _ = (↑hmulUnit.unit⁻¹ : ZMod modulus) *
            (↑hrhsUnit.unit : ZMod modulus) := by rw [hrhscoe]
      _ = (u : ZMod modulus) := rfl
  · intro h
    calc
      (multiplier : ZMod modulus) * (n : ZMod modulus) =
          (↑hmulUnit.unit : ZMod modulus) * (u : ZMod modulus) := by
            rw [hmulcoe, h]
      _ = (↑hrhsUnit.unit : ZMod modulus) := by
        change (↑hmulUnit.unit : ZMod modulus) *
          (↑(hmulUnit.unit⁻¹ * hrhsUnit.unit) : ZMod modulus) = _
        rw [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
      _ = (rhs : ZMod modulus) := hrhscoe

/-- The affine form occurring in the second coordinate also reduces to a
unique primitive residue class. -/
theorem exists_primitive_residue_for_affine_zero
    {multiplier offset modulus : ℕ}
    (hmod : 0 < modulus)
    (hmul : multiplier.Coprime modulus)
    (hoffset : offset.Coprime modulus) :
    ∃ residue : ℕ, residue < modulus ∧ residue.Coprime modulus ∧
      ∀ n : ℕ,
        (multiplier * n + offset ≡ 0 [MOD modulus] ↔
          n ≡ residue [MOD modulus]) := by
  letI : NeZero modulus := ⟨Nat.ne_of_gt hmod⟩
  have hmulUnit : IsUnit (multiplier : ZMod modulus) :=
    (ZMod.isUnit_iff_coprime multiplier modulus).2 hmul
  have hoffsetUnit : IsUnit (offset : ZMod modulus) :=
    (ZMod.isUnit_iff_coprime offset modulus).2 hoffset
  let z : ZMod modulus :=
    -((↑hmulUnit.unit⁻¹ : ZMod modulus) * (offset : ZMod modulus))
  let residue : ℕ := z.val
  have hreslt : residue < modulus := ZMod.val_lt z
  have hrescast : (residue : ZMod modulus) = z := ZMod.natCast_zmod_val z
  have hzunit : IsUnit z := by
    dsimp [z]
    exact ((Units.isUnit hmulUnit.unit⁻¹).mul hoffsetUnit).neg
  have hresunit : IsUnit (residue : ZMod modulus) := by simpa [hrescast]
  have hrescop : residue.Coprime modulus :=
    (ZMod.isUnit_iff_coprime residue modulus).1 hresunit
  refine ⟨residue, hreslt, hrescop, ?_⟩
  intro n
  rw [← ZMod.natCast_eq_natCast_iff n residue modulus,
    ← ZMod.natCast_eq_natCast_iff (multiplier * n + offset) 0 modulus,
    Nat.cast_add, Nat.cast_mul, Nat.cast_zero, hrescast]
  change (multiplier : ZMod modulus) * (n : ZMod modulus) +
      (offset : ZMod modulus) = 0 ↔ (n : ZMod modulus) = z
  have hmulcoe : (↑hmulUnit.unit : ZMod modulus) = (multiplier : ZMod modulus) :=
    hmulUnit.unit_spec
  constructor
  · intro h
    have hprod : (multiplier : ZMod modulus) * (n : ZMod modulus) =
        -(offset : ZMod modulus) := eq_neg_of_add_eq_zero_left h
    calc
      (n : ZMod modulus) =
          (↑hmulUnit.unit⁻¹ : ZMod modulus) *
            ((↑hmulUnit.unit : ZMod modulus) * (n : ZMod modulus)) := by
              rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = (↑hmulUnit.unit⁻¹ : ZMod modulus) *
            ((multiplier : ZMod modulus) * (n : ZMod modulus)) := by rw [hmulcoe]
      _ = (↑hmulUnit.unit⁻¹ : ZMod modulus) * (-(offset : ZMod modulus)) := by
        rw [hprod]
      _ = z := by simp [z]
  · intro h
    rw [h]
    dsimp [z]
    have hreplace :
        (multiplier : ZMod modulus) *
            (-((↑hmulUnit.unit⁻¹ : ZMod modulus) * (offset : ZMod modulus))) =
          (↑hmulUnit.unit : ZMod modulus) *
            (-((↑hmulUnit.unit⁻¹ : ZMod modulus) * (offset : ZMod modulus))) :=
      congrArg
        (fun t : ZMod modulus =>
          t * (-((↑hmulUnit.unit⁻¹ : ZMod modulus) * (offset : ZMod modulus))))
        hmulcoe.symm
    rw [hreplace, mul_neg, ← mul_assoc, Units.mul_inv, one_mul, neg_add_cancel]

/-- The multiplier form of the exact Shiu input needed in the determinant
fibers.  The right-hand side and multiplier are primitive modulo `modulus`.
This is again only a proposition. -/
def TwistedDyadicTauSquareShiuTarget : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C x₀ : ℕ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x y modulus multiplier rhs : ℕ,
        x₀ ≤ x → 0 < modulus →
        multiplier.Coprime modulus → rhs.Coprime modulus →
        y ≤ x → x < y ^ 3 → modulus ^ 3 < y ^ 2 →
        modulus *
            (∑ n ∈ Finset.Ioc (x - y) x,
              if multiplier * n ≡ rhs [MOD modulus]
              then tauAF k n ^ 2 else 0) ≤
          C * y * (Nat.log 2 (x + 2) + 1) ^ (k * k)

/-- The ordinary primitive-residue Shiu target implies the multiplier form
by an exact change of residue. -/
theorem dyadicTarget_implies_twistedTarget
    (hShiu : DyadicTauSquareShiuTarget) :
    TwistedDyadicTauSquareShiuTarget := by
  intro k hk
  obtain ⟨C, x₀, hC, hx₀, hbound⟩ := hShiu k hk
  refine ⟨C, x₀, hC, hx₀, ?_⟩
  intro x y modulus multiplier rhs hx hmod hmul hrhs hyx hxy hmy
  obtain ⟨residue, hreslt, hrescop, hiff⟩ :=
    exists_primitive_residue_for_twist hmod hmul hrhs
  simpa only [progressionSum, ArithmeticFunction.pmul_apply, pow_two, hiff] using
    hbound x y modulus residue hx hmod hreslt hrescop hyx hxy hmy

/-- Affine-zero version needed by the symmetric coordinate. -/
def AffineZeroDyadicTauSquareShiuTarget : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C x₀ : ℕ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x y modulus multiplier offset : ℕ,
        x₀ ≤ x → 0 < modulus →
        multiplier.Coprime modulus → offset.Coprime modulus →
        y ≤ x → x < y ^ 3 → modulus ^ 3 < y ^ 2 →
        modulus *
            (∑ n ∈ Finset.Ioc (x - y) x,
              if multiplier * n + offset ≡ 0 [MOD modulus]
              then tauAF k n ^ 2 else 0) ≤
          C * y * (Nat.log 2 (x + 2) + 1) ^ (k * k)

theorem dyadicTarget_implies_affineZeroTarget
    (hShiu : DyadicTauSquareShiuTarget) :
    AffineZeroDyadicTauSquareShiuTarget := by
  intro k hk
  obtain ⟨C, x₀, hC, hx₀, hbound⟩ := hShiu k hk
  refine ⟨C, x₀, hC, hx₀, ?_⟩
  intro x y modulus multiplier offset hx hmod hmul hoffset hyx hxy hmy
  obtain ⟨residue, hreslt, hrescop, hiff⟩ :=
    exists_primitive_residue_for_affine_zero hmod hmul hoffset
  simpa only [progressionSum, ArithmeticFunction.pmul_apply, pow_two, hiff] using
    hbound x y modulus residue hx hmod hreslt hrescop hyx hxy hmy

/-! ## Literal determinant-fiber congruences -/

/-- The first quotient coordinate in a positive determinant fiber satisfies
the exact primitive multiplier congruence used by Shiu. -/
theorem positiveFiber_left_twisted_congruence
    {N a b ell : ℕ} {n : ℕ × ℕ}
    (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hn : n ∈ positiveEquationFiber N a b ell) :
    let content := ell.gcd b
    let modulus := b / content
    let rhs := ell / content
    n.1 / content ∈ quotientDyadic N content ∧
      a.Coprime modulus ∧ rhs.Coprime modulus ∧
      a * (n.1 / content) ≡ rhs [MOD modulus] := by
  dsimp
  obtain ⟨_, _, hwindow, _, _, _, heq, _⟩ :=
    positiveFiber_reduced_equations hab ha hb hn
  have hcontent : 0 < ell.gcd b := Nat.gcd_pos_of_pos_right ell hb
  have hamod : a.Coprime (b / ell.gcd b) :=
    hab.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right ell b))
  have hrhs : (ell / ell.gcd b).Coprime (b / ell.gcd b) :=
    Nat.coprime_div_gcd_div_gcd hcontent
  refine ⟨hwindow, hamod, hrhs, ?_⟩
  rw [heq]
  simp

/-- The second quotient coordinate satisfies the symmetric affine primitive
congruence `b*n₂' + rhs = 0 (mod modulus)`. -/
theorem positiveFiber_right_affine_congruence
    {N a b ell : ℕ} {n : ℕ × ℕ}
    (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hn : n ∈ positiveEquationFiber N a b ell) :
    let content := ell.gcd a
    let modulus := a / content
    let rhs := ell / content
    n.2 / content ∈ quotientDyadic N content ∧
      b.Coprime modulus ∧ rhs.Coprime modulus ∧
      b * (n.2 / content) + rhs ≡ 0 [MOD modulus] := by
  dsimp
  obtain ⟨_, _, _, hwindow, _, _, _, heq⟩ :=
    positiveFiber_reduced_equations hab ha hb hn
  have hcontent : 0 < ell.gcd a := Nat.gcd_pos_of_pos_right ell ha
  have hbmod : b.Coprime (a / ell.gcd a) :=
    hab.symm.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right ell a))
  have hrhs : (ell / ell.gcd a).Coprime (a / ell.gcd a) :=
    Nat.coprime_div_gcd_div_gcd hcontent
  refine ⟨hwindow, hbmod, hrhs, ?_⟩
  rw [Nat.ModEq, heq]
  simp

/-! ## The finite weighted-fiber reduction -/

def positiveLeftSquareMass (k N a b ell : ℕ) : ℕ :=
  ∑ n ∈ positiveEquationFiber N a b ell, tauAF k n.1 ^ 2

/-- Before invoking Shiu, the complete first-coordinate fiber mass is bounded
by one literal primitive quotient progression, with the exact content factor
coming from divisor-function submultiplicativity. -/
theorem positiveLeftSquareMass_le_primitive_progression
    (k N a b ell : ℕ) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    let content := ell.gcd b
    let modulus := b / content
    ∃ residue : ℕ, residue < modulus ∧ residue.Coprime modulus ∧
      positiveLeftSquareMass k N a b ell ≤
        tauAF k content ^ 2 *
          quotientProgressionSum k N content modulus residue := by
  classical
  dsimp
  let content := ell.gcd b
  let modulus := b / content
  let rhs := ell / content
  have hcontent : 0 < content := Nat.gcd_pos_of_pos_right ell hb
  have hcontent_b : content ∣ b := Nat.gcd_dvd_right ell b
  have hmod : 0 < modulus :=
    Nat.div_pos (Nat.le_of_dvd hb hcontent_b) hcontent
  have hamod : a.Coprime modulus := hab.coprime_dvd_right (Nat.div_dvd_of_dvd hcontent_b)
  have hrhs : rhs.Coprime modulus := by
    exact Nat.coprime_div_gcd_div_gcd hcontent
  obtain ⟨residue, hreslt, hrescop, htwist⟩ :=
    exists_primitive_residue_for_twist hmod hamod hrhs
  refine ⟨residue, hreslt, hrescop, ?_⟩
  let s := positiveEquationFiber N a b ell
  let project : ℕ × ℕ → ℕ := fun n => n.1 / content
  have hproject_inj : Set.InjOn project (s : Set (ℕ × ℕ)) := by
    intro n hn m hm hproj
    have hnmem : n ∈ positiveEquationFiber N a b ell := hn
    have hmmem : m ∈ positiveEquationFiber N a b ell := hm
    obtain ⟨hndiv, _, _, _, _, _, hneq, _⟩ :=
      positiveFiber_reduced_equations hab ha hb hnmem
    obtain ⟨hmdiv, _, _, _, _, _, hmeq, _⟩ :=
      positiveFiber_reduced_equations hab ha hb hmmem
    have hn₁ : n.1 = m.1 := by
      dsimp [project] at hproj
      calc
        n.1 = content * (n.1 / content) := (Nat.mul_div_cancel' hndiv).symm
        _ = content * (m.1 / content) := by rw [hproj]
        _ = m.1 := Nat.mul_div_cancel' hmdiv
    have hn₂ : n.2 = m.2 := by
      change a * project n = rhs + modulus * n.2 at hneq
      change a * project m = rhs + modulus * m.2 at hmeq
      have heqsum : rhs + modulus * n.2 = rhs + modulus * m.2 := by
        calc
          rhs + modulus * n.2 = a * project n := hneq.symm
          _ = a * project m := by rw [hproj]
          _ = rhs + modulus * m.2 := hmeq
      have heqmul : modulus * n.2 = modulus * m.2 := Nat.add_left_cancel heqsum
      apply Nat.eq_of_mul_eq_mul_left hmod
      exact heqmul
    exact Prod.ext hn₁ hn₂
  have hproject_mem :
      ∀ n ∈ s, project n ∈ quotientProgressionSet N content modulus residue := by
    intro n hn
    have hnmem : n ∈ positiveEquationFiber N a b ell := hn
    obtain ⟨hwindow, _, _, hcong⟩ :=
      positiveFiber_left_twisted_congruence hab ha hb hnmem
    exact Finset.mem_filter.mpr ⟨hwindow, (htwist (project n)).mp hcong⟩
  have hpoint : ∀ n ∈ s,
      tauAF k n.1 ^ 2 ≤ tauAF k content ^ 2 * tauAF k (project n) ^ 2 := by
    intro n hn
    have hnmem : n ∈ positiveEquationFiber N a b ell := hn
    obtain ⟨hndiv, _, _, _, _, _, _, _⟩ :=
      positiveFiber_reduced_equations hab ha hb hnmem
    have htau : tauAF k n.1 ≤ tauAF k content * tauAF k (project n) := by
      rw [show n.1 = content * project n from (Nat.mul_div_cancel' hndiv).symm]
      exact tauAF_submultiplicative k content (project n)
    calc
      tauAF k n.1 ^ 2 ≤ (tauAF k content * tauAF k (project n)) ^ 2 :=
        Nat.pow_le_pow_left htau 2
      _ = tauAF k content ^ 2 * tauAF k (project n) ^ 2 := by ring
  calc
    positiveLeftSquareMass k N a b ell ≤
        ∑ n ∈ s, tauAF k content ^ 2 * tauAF k (project n) ^ 2 := by
      unfold positiveLeftSquareMass
      exact Finset.sum_le_sum hpoint
    _ = tauAF k content ^ 2 * ∑ n ∈ s, tauAF k (project n) ^ 2 := by
      rw [Finset.mul_sum]
    _ = tauAF k content ^ 2 *
          ∑ v ∈ s.image project, tauAF k v ^ 2 := by
      congr 1
      exact (Finset.sum_image
        (f := fun v => tauAF k v ^ 2) hproject_inj).symm
    _ ≤ tauAF k content ^ 2 *
          ∑ v ∈ quotientProgressionSet N content modulus residue, tauAF k v ^ 2 := by
      apply Nat.mul_le_mul_left
      exact Finset.sum_le_sum_of_subset (fun v hv => by
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
        exact hproject_mem n hn)
    _ = tauAF k content ^ 2 *
          quotientProgressionSum k N content modulus residue := by
      rw [quotientProgressionSum_eq_sum_set]

/-- Complete first-coordinate specialization: assuming the genuine Shiu
theorem, the literal positive determinant fiber satisfies the exact weighted
bound required after Cauchy.  Shiu remains an ordinary theorem argument. -/
theorem dyadicTarget_implies_positiveLeftFiberBound
    (hShiu : DyadicTauSquareShiuTarget) :
    ∀ k : ℕ, 1 ≤ k →
      ∃ C x₀ : ℕ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ N a b ell : ℕ, a.Coprime b → 0 < a → 0 < b →
          let content := ell.gcd b
          let modulus := b / content
          x₀ ≤ quotientUpper N content →
          quotientLength N content ≤ quotientUpper N content →
          quotientUpper N content < quotientLength N content ^ 3 →
          modulus ^ 3 < quotientLength N content ^ 2 →
          modulus * positiveLeftSquareMass k N a b ell ≤
            tauAF k content ^ 2 *
              (C * quotientLength N content *
                (Nat.log 2 (quotientUpper N content + 2) + 1) ^ (k * k)) := by
  intro k hk
  obtain ⟨C, x₀, hC, hx₀, hbound⟩ := hShiu k hk
  refine ⟨C, x₀, hC, hx₀, ?_⟩
  intro N a b ell hab ha hb
  dsimp
  let content := ell.gcd b
  let modulus := b / content
  intro hx hyx hxy hmy
  have hcontent : 0 < content := Nat.gcd_pos_of_pos_right ell hb
  have hcontent_b : content ∣ b := Nat.gcd_dvd_right ell b
  have hmod : 0 < modulus :=
    Nat.div_pos (Nat.le_of_dvd hb hcontent_b) hcontent
  obtain ⟨residue, hreslt, hrescop, hmass⟩ :=
    positiveLeftSquareMass_le_primitive_progression k N a b ell hab ha hb
  have hprogression := hbound (quotientUpper N content)
    (quotientLength N content) modulus residue hx hmod hreslt hrescop hyx hxy hmy
  calc
    modulus * positiveLeftSquareMass k N a b ell ≤
        modulus * (tauAF k content ^ 2 *
          quotientProgressionSum k N content modulus residue) :=
      Nat.mul_le_mul_left modulus hmass
    _ = tauAF k content ^ 2 *
        (modulus * quotientProgressionSum k N content modulus residue) := by ring
    _ ≤ tauAF k content ^ 2 *
        (C * quotientLength N content *
          (Nat.log 2 (quotientUpper N content + 2) + 1) ^ (k * k)) :=
      Nat.mul_le_mul_left _ hprogression

end
end MAPShiuSpecialization
