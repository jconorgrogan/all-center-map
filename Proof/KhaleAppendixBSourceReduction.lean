import KhaleWeakVKAbsoluteBridge
import APPrimitiveRegularLowGap
import McCurleyHighImaginaryBridge
import FordHurwitzFirstLeaf

/-!
# Exact source boundary for Khale Appendix B

This module corrects the scope of the MAP consumer.  Khale's Appendix-B
Corollary is printed for levels `q ≥ 3`; it is not an all-positive-level
statement.  We retain that scope literally and prove the only character-
theoretic reduction needed by the regular AP branch: a primitive
nonprincipal character necessarily has level at least three.

The proposition below is a source statement, not a new axiom.  Every theorem
in this file takes it as a local hypothesis.  The proof in the primary source
uses Appendix-B Theorem B.1 above `exp 11450` and McCurley's Theorem 1.1 below
that height.  Thus an eventual premise-free proof must formalize those two
published analytic inputs; this module does not hide them in an all-`q` MAP
interface.
-/

namespace MAPKhaleAppendixBSource

open Filter Set
open MAPKhaleWeakVKApplication

noncomputable section


/-- Ford/Khale equation (1.2), expressed using Mathlib's periodic Hurwitz
zeta and the exact removed initial term. -/
abbrev FordHurwitzEquation12 (A B : ℝ) : Prop :=
  ∀ (u t sigma : ℝ), 0 < u → u ≤ 1 → 3 ≤ t →
    1 / 2 ≤ sigma → sigma ≤ 1 →
    ‖HurwitzZeta.hurwitzZeta (u : UnitAddCircle)
        ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      1 / (u : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      A * Real.rpow t
        (B * Real.rpow (1 - sigma) (3 / 2 : ℝ)) *
        Real.rpow (Real.log t) (2 / 3 : ℝ)

/-- The height-dependent correction inside Khale Appendix-B Theorem B.1. -/
def appendixBCorrection (A t : ℝ) : ℝ :=
  (-2.89 * Real.log (Real.log (Real.log t)) +
      14.44 * Real.log (A + 1) + 3.59) /
    Real.log (Real.log t)

/-- Literal `max_{t ≥ T₀}` coefficient in Appendix-B Theorem B.1. -/
def appendixBHeightCoefficient (A T₀ : ℝ) : ℝ :=
  31.76 + max (sSup (appendixBCorrection A '' Set.Ici T₀)) 0

/-- Khale Appendix-B Theorem B.1 with every startup condition visible.
This is the lowest exact primary Khale theorem whose proof remains to be
formalized.  It assumes Ford equation (1.2); the published proof also invokes
McCurley Theorem 1.1 to obtain `t ≥ q^(1/100000)` before applying its local
zero-count lemmas. -/
abbrev AppendixBTheoremB1 : Prop :=
  ∀ (A B T₀ : ℝ),
    0 < A → 0 < B → B ≤ 4.45 →
    FordHurwitzEquation12 A B →
    Real.exp 10650 ≤ T₀ →
    5110.6 / B ≤ Real.log T₀ / Real.log (Real.log T₀) →
    183 / B ^ 2 ≤ Real.log (Real.log T₀) →
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (t sigma : ℝ),
      3 ≤ q → T₀ ≤ t →
      1 - 1 /
        (18 * Real.log q +
          appendixBHeightCoefficient A T₀ * Real.rpow B (2 / 3 : ℝ) *
            Real.rpow (Real.log t) (2 / 3 : ℝ) *
            Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ)) < sigma →
        DirichletCharacter.LFunction chi
          ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- Exact part of McCurley Theorem 1.1 used in Khale's proof: every zero in
the published open region is real.  McCurley's theorem is stronger (global
uniqueness, simplicity, and a real nonprincipal exceptional character). -/
abbrev McCurleyTheorem11RealException : Prop :=
  ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (s : ℂ),
    MAPMcCurleyHighImaginaryBridge.mccurleyBoundary
        MAPMcCurleyHighImaginaryBridge.publishedR q s.im < s.re →
    DirichletCharacter.LFunction chi s = 0 →
      s.im = 0

/-- The second assertion of Khale's Appendix-B Corollary, with its printed
level, height, closed-boundary, character, and sign conventions.

Source: T. Khale, *An Explicit Vinogradov--Korobov Zero-Free Region for
Dirichlet L-functions*, Appendix B, Corollary B.2, lines 1328--1341 of the
cached arXiv source. -/
abbrev AppendixBCorollary104 : Prop :=
  ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (t sigma : ℝ),
    3 ≤ q → 3 ≤ |t| →
    1 - 1 / khaleWeakDenominatorAbs q t ≤ sigma →
      DirichletCharacter.LFunction chi
        ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- The first assertion of the same corollary.  It is retained separately
because its coefficient `86` gives slack for a conductor-one zeta reduction
through the principal character modulo three. -/
def khaleStrongDenominatorAbs (q : ℕ) (t : ℝ) : ℝ :=
  18 * Real.log q +
    86 * Real.rpow (Real.log |t|) (2 / 3 : ℝ) *
      Real.rpow (Real.log (Real.log |t|)) (1 / 3 : ℝ)

abbrev AppendixBCorollary86 : Prop :=
  ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (t sigma : ℝ),
    3 ≤ q → Real.exp (Real.exp (Real.exp 23)) ≤ |t| →
    1 - 1 / khaleStrongDenominatorAbs q t ≤ sigma →
      DirichletCharacter.LFunction chi
        ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- There is only one Dirichlet character modulo two.  Mathlib has the
load-bearing `Subsingleton (ZMod 2)ˣ` instance; this proof uses it directly. -/
theorem character_level_two_eq_one (chi : DirichletCharacter ℂ 2) :
    chi = 1 := by
  apply MulChar.ext
  intro x
  have hx : x = 1 := Subsingleton.elim _ _
  subst x
  simp

/-- A primitive nonprincipal Dirichlet character has level at least three.
This is the exact reason Khale's printed `q ≥ 3` scope suffices for the
nonprincipal regular branch. -/
theorem three_le_level_of_isPrimitive_of_ne_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (_hprim : chi.IsPrimitive) (hchi : chi ≠ 1) :
    3 ≤ q := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  by_contra hq
  have hqle : q ≤ 2 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hq)
  have hcases : q = 1 ∨ q = 2 := by omega
  rcases hcases with rfl | rfl
  · exact hchi (DirichletCharacter.level_one' chi rfl)
  · exact hchi (character_level_two_eq_one chi)

/-- Source-faithful high-ordinate nonvanishing for the primitive
nonprincipal characters actually used by MAP.  No conductor-one or level-two
claim is inserted into Khale's theorem. -/
theorem primitive_nonprincipal_absolute_nonvanishing
    (hKhale : AppendixBCorollary104)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {t sigma : ℝ} (ht : 3 ≤ |t|)
    (hsigma : 1 - 1 / khaleWeakDenominatorAbs q t ≤ sigma) :
    DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  exact hKhale q chi t sigma
    (three_le_level_of_isPrimitive_of_ne_one chi hprim hchi) ht hsigma



/-! ## Conductor-one high-height zeta adapter -/

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local instance : NeZero 3 := ⟨by norm_num⟩

/-- At the very-high cutoff in the first half of Corollary B.2, the spare
`104 - 86 = 18` units absorb the level-three Euler-factor lift. -/
theorem strong_level_three_denominator_le_weak_level_one
    {t : ℝ} (ht : Real.exp (Real.exp (Real.exp 23)) ≤ |t|) :
    khaleStrongDenominatorAbs 3 t ≤ khaleWeakDenominatorAbs 1 t := by
  let u : ℝ := |t|
  have huPos : 0 < u := (Real.exp_pos _).trans_le ht
  have hloguLower : Real.exp (Real.exp 23) ≤ Real.log u := by
    have h := Real.log_le_log (Real.exp_pos _) ht
    simpa [u] using h
  have hloguPos : 0 < Real.log u := (Real.exp_pos _).trans_le hloguLower
  have hlogloguLower : Real.exp 23 ≤ Real.log (Real.log u) := by
    have h := Real.log_le_log (Real.exp_pos _) hloguLower
    simpa using h
  have hlogloguPos : 0 < Real.log (Real.log u) :=
    (Real.exp_pos _).trans_le hlogloguLower
  have hlogThreeNonneg : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlogThreeLtTwo : Real.log 3 < 2 := by
    have h := Real.log_lt_sub_one_of_pos (x := (3 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hcube : (Real.log 3) ^ (3 : ℕ) ≤ 8 := by
    have hpow := pow_le_pow_left₀ hlogThreeNonneg hlogThreeLtTwo.le 3
    norm_num at hpow ⊢
    exact hpow
  have height : Real.rpow (Real.log 3) (3 : ℝ) ≤ Real.log (Real.log u) := by
    have heq : Real.rpow (Real.log 3) (3 : ℝ) = (Real.log 3) ^ (3 : ℕ) :=
      Real.rpow_natCast (Real.log 3) 3
    rw [heq]
    have h8exp : (8 : ℝ) ≤ Real.exp 23 := by
      nlinarith [Real.add_one_lt_exp (x := (23 : ℝ)) (by norm_num)]
    exact hcube.trans (h8exp.trans hlogloguLower)
  have hsecond : Real.log 3 ≤
      Real.rpow (Real.log (Real.log u)) (1 / 3 : ℝ) := by
    have hiff := Real.le_rpow_inv_iff_of_pos hlogThreeNonneg hlogloguPos.le
      (show (0 : ℝ) < 3 by norm_num)
    rw [show (3 : ℝ)⁻¹ = 1 / 3 by norm_num] at hiff
    exact hiff.mpr height
  have hfirst : 1 ≤ Real.rpow (Real.log u) (2 / 3 : ℝ) := by
    have hbase : 1 ≤ Real.log u := by
      exact (show (1 : ℝ) ≤ Real.exp (Real.exp 23) by
        exact (Real.one_le_exp (Real.exp_pos 23).le)).trans hloguLower
    simpa using Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num)
      hbase (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  have hproduct : Real.log 3 ≤
      Real.rpow (Real.log u) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log u)) (1 / 3 : ℝ) := by
    calc
      Real.log 3 = 1 * Real.log 3 := by ring
      _ ≤ Real.rpow (Real.log u) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log u)) (1 / 3 : ℝ) := by
        exact mul_le_mul hfirst hsecond hlogThreeNonneg
          (Real.rpow_nonneg hloguPos.le _)
  dsimp [khaleStrongDenominatorAbs, khaleWeakDenominatorAbs,
    khaleWeakDenominator]
  simp only [Nat.cast_one, Real.log_one, mul_zero, zero_add]
  have hproduct' : Real.log 3 ≤
      Real.rpow (Real.log |t|) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log |t|)) (1 / 3 : ℝ) := by
    simpa [u] using hproduct
  calc
    18 * Real.log 3 + 86 *
        Real.rpow (Real.log |t|) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log |t|)) (1 / 3 : ℝ) =
      18 * Real.log 3 + 86 *
        (Real.rpow (Real.log |t|) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log |t|)) (1 / 3 : ℝ)) := by ring
    _ ≤ 104 *
        (Real.rpow (Real.log |t|) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log |t|)) (1 / 3 : ℝ)) := by
      nlinarith
    _ = 104 * Real.rpow (Real.log |t|) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log |t|)) (1 / 3 : ℝ) := by ring



/-- Literal finite conductor-one support below Khale's first very-high cutoff. -/
def principalPreKhaleSupport : Finset ℂ :=
  DirichletZeros.zeroSupport (1 : DirichletCharacter ℂ 1) (4 / 5)
    (Real.exp (Real.exp (Real.exp 23)))

/-- Compactness fills the conductor-one interval below the first source
cutoff.  This theorem asserts no numerical zero-free constant. -/
theorem exists_principalPreKhaleGap :
    ∃ c : ℝ, 0 < c ∧
      ∀ rho ∈ principalPreKhaleSupport, c ≤ 1 - rho.re := by
  classical
  by_cases hnonempty : principalPreKhaleSupport.Nonempty
  · obtain ⟨rho, hrho, hmin⟩ :=
      Finset.exists_min_image principalPreKhaleSupport
        (fun z : ℂ => 1 - z.re) hnonempty
    refine ⟨1 - rho.re, ?_, ?_⟩
    · have hre := MAPMellinDetectorLeaf.re_lt_one_of_mem_zeroSupport
        (1 : DirichletCharacter ℂ 1) hrho
      linarith
    · intro z hz
      exact hmin z hz
  · refine ⟨1, by norm_num, ?_⟩
    intro rho hrho
    exact (hnonempty ⟨rho, hrho⟩).elim

/-- Primitive-principal supported zeros below the first Khale cutoff belong
to the fixed compact support above. -/
theorem primitive_principal_preKhale_gap
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi = 1)
    {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ DirichletZeros.zeroSupport chi 0 T)
    (hbeta : 4 / 5 < rho.re)
    (hheight : |rho.im| < Real.exp (Real.exp (Real.exp 23))) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 - rho.re := by
  obtain ⟨c, hc, hgap⟩ := exists_principalPreKhaleGap
  refine ⟨c, hc, ?_⟩
  have hq : q = 1 := by
    have hcond : chi.conductor = q := hprim
    rw [hchi, DirichletCharacter.conductor_one] at hcond
    exact hcond.symm
  subst q
  subst chi
  have hglobalRect : rho ∈ DirichletZeros.zeroRectangle 0 T :=
    (DirichletZeros.zeroDivisor (1 : DirichletCharacter ℂ 1) 0 T).supportWithinDomain
      ((DirichletZeros.zeroSupport_mem_iff
        (1 : DirichletCharacter ℂ 1) 0 T rho).mp hrho)
  have htargetRect : rho ∈ DirichletZeros.zeroRectangle (4 / 5)
      (Real.exp (Real.exp (Real.exp 23))) := by
    rw [DirichletZeros.zeroRectangle, Complex.mem_reProdIm]
    exact ⟨⟨hbeta.le, hglobalRect.1.2⟩, abs_le.mp hheight.le⟩
  have hzero := DirichletZeros.regularizedLFunction_eq_zero_of_mem_zeroSupport
    (1 : DirichletCharacter ℂ 1) 0 T hrho
  have htarget : rho ∈ principalPreKhaleSupport := by
    unfold principalPreKhaleSupport
    exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      (1 : DirichletCharacter ℂ 1) (4 / 5)
      (Real.exp (Real.exp (Real.exp 23))) htargetRect).mpr hzero
  exact hgap rho htarget



/-- Uniform fixed compact gap for every primitive-principal presentation of
the conductor-one L-function below the first Khale cutoff. -/
theorem exists_primitive_principal_preKhale_gap :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
        chi.IsPrimitive → chi = 1 →
        ∀ (T : ℝ) (rho : ℂ),
          rho ∈ DirichletZeros.zeroSupport chi 0 T →
          4 / 5 < rho.re →
          |rho.im| < Real.exp (Real.exp (Real.exp 23)) →
            c ≤ 1 - rho.re := by
  obtain ⟨c, hc, hgap⟩ := exists_principalPreKhaleGap
  refine ⟨c, hc, ?_⟩
  intro q _inst chi hprim hchi T rho hrho hbeta hheight
  have hq : q = 1 := by
    have hcond : chi.conductor = q := hprim
    rw [hchi, DirichletCharacter.conductor_one] at hcond
    exact hcond.symm
  subst q
  subst chi
  have hglobalRect : rho ∈ DirichletZeros.zeroRectangle 0 T :=
    (DirichletZeros.zeroDivisor (1 : DirichletCharacter ℂ 1) 0 T).supportWithinDomain
      ((DirichletZeros.zeroSupport_mem_iff
        (1 : DirichletCharacter ℂ 1) 0 T rho).mp hrho)
  have htargetRect : rho ∈ DirichletZeros.zeroRectangle (4 / 5)
      (Real.exp (Real.exp (Real.exp 23))) := by
    rw [DirichletZeros.zeroRectangle, Complex.mem_reProdIm]
    exact ⟨⟨hbeta.le, hglobalRect.1.2⟩, abs_le.mp hheight.le⟩
  have hzero := DirichletZeros.regularizedLFunction_eq_zero_of_mem_zeroSupport
    (1 : DirichletCharacter ℂ 1) 0 T hrho
  have htarget : rho ∈ principalPreKhaleSupport := by
    unfold principalPreKhaleSupport
    exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      (1 : DirichletCharacter ℂ 1) (4 / 5)
      (Real.exp (Real.exp (Real.exp 23))) htargetRect).mpr hzero
  exact hgap rho htarget

/-- Exact change-of-level identity used to read conductor-one zeta
nonvanishing from the principal character modulo three.  No assertion about
Euler-factor nonvanishing is needed: if the conductor-one factor vanished,
the level-three product would vanish. -/
theorem principal_one_nonzero_of_principal_three_nonzero
    {s : ℂ} (hs : s ≠ 1)
    (hthree : DirichletCharacter.LFunction
      (1 : DirichletCharacter ℂ 3) s ≠ 0) :
    DirichletCharacter.LFunction
      (1 : DirichletCharacter ℂ 1) s ≠ 0 := by
  intro hone
  have hchange := DirichletCharacter.LFunction_changeLevel
    (M := 1) (N := 3) (one_dvd 3)
    (1 : DirichletCharacter ℂ 1) (s := s) (Or.inr hs)
  rw [DirichletCharacter.changeLevel_one] at hchange
  apply hthree
  rw [hchange, hone, zero_mul]

/-- The first (`86`) region of Khale's exact q≥3 corollary supplies the
separate conductor-one zeta theorem required above its printed very-high
cutoff.  The level-three L-function identity is checked literally. -/
theorem conductor_one_high_nonvanishing_of_appendixB86
    (hKhale : AppendixBCorollary86)
    {t sigma : ℝ}
    (ht : Real.exp (Real.exp (Real.exp 23)) ≤ |t|)
    (hsigma : 1 - 1 / khaleWeakDenominatorAbs 1 t ≤ sigma) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
      ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have hdenLe := strong_level_three_denominator_le_weak_level_one ht
  have htThree : (3 : ℝ) ≤ |t| := by
    have hinner : 2 < Real.exp (Real.exp 23) := by
      exact Real.exp_one_gt_two.trans
        (Real.exp_lt_exp.mpr (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 23)))
    have houter : Real.exp (Real.exp 23) + 1 <
        Real.exp (Real.exp (Real.exp 23)) :=
      Real.add_one_lt_exp (Real.exp_pos (Real.exp 23)).ne'
    linarith
  have hstrongPos : 0 < khaleStrongDenominatorAbs 3 t := by
    unfold khaleStrongDenominatorAbs
    have hlogThree : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hlogAbsOne : 1 < Real.log |t| := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      exact Real.exp_one_lt_d9.trans (by linarith : (2.7182818286 : ℝ) < |t|)
    have hheightNonneg : 0 ≤
        Real.rpow (Real.log |t|) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log |t|)) (1 / 3 : ℝ) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (Real.log_nonneg hlogAbsOne.le) _)
    nlinarith
  have hinv : 1 / khaleWeakDenominatorAbs 1 t ≤
      1 / khaleStrongDenominatorAbs 3 t :=
    one_div_le_one_div_of_le hstrongPos hdenLe
  have hsigmaStrong :
      1 - 1 / khaleStrongDenominatorAbs 3 t ≤ sigma := by
    linarith
  have hthree := hKhale 3 (1 : DirichletCharacter ℂ 3) t sigma
    (by norm_num) ht hsigmaStrong
  apply principal_one_nonzero_of_principal_three_nonzero
  · intro hs
    have him := congrArg Complex.im hs
    simp at him
    rw [him] at htThree
    norm_num at htThree
  · exact hthree



/-- Conductor-one zeta nonvanishing from the *same* `104` source region at
level three.  The price is that the denominator remains the level-three
denominator; this is harmless for MAP because level three is eventually inside
every positive polylogarithmic conductor range. -/
theorem conductor_one_nonvanishing_via_level_three_of_appendixB104
    (hKhale : AppendixBCorollary104)
    {t sigma : ℝ} (ht : 3 ≤ |t|)
    (hsigma : 1 - 1 / khaleWeakDenominatorAbs 3 t ≤ sigma) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
      ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have hthree := hKhale 3 (1 : DirichletCharacter ℂ 3) t sigma
    (by norm_num) ht hsigma
  apply principal_one_nonzero_of_principal_three_nonzero
  · intro hs
    have him := congrArg Complex.im hs
    simp at him
    rw [him] at ht
    norm_num at ht
  · exact hthree

/-- The literal `104` half of Khale's Appendix-B Corollary implies
exactly the uniform weak-VK gap needed by MAP's primitive regular
high-ordinate range.

For primitive nonprincipal characters, the source's `q ≥ 3` restriction is
automatic.  For the primitive principal character, the proof changes level
from one to three exactly and applies the same source region there.  Thus no
all-level Khale statement and no separate `86` source premise is required. -/
theorem exists_eventually_primitive_regular_high_gap_of_appendixB
    (hKhale104 : AppendixBCorollary104)
    (K : ℝ) (hK : 0 < K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
          chi.IsPrimitive →
          (q : ℝ) ≤ Real.rpow (Real.log X) K →
          ∀ (T : ℝ) (rho : ℂ),
            rho ∈ DirichletZeros.zeroSupport chi 0 T →
            4 / 5 < rho.re → 3 ≤ |rho.im| → |rho.im| ≤ X →
            c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤
              1 - rho.re := by
  let c : ℝ := 1 / (18 * K + 104)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hsourceGap :=
    weakGap_le_of_one_div_khaleWeakDenominatorAbs_le K hK.le
  have hthreeLevel : ∀ᶠ X : ℝ in atTop,
      (3 : ℝ) ≤ Real.rpow (Real.log X) K :=
    ((tendsto_rpow_atTop hK).comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop 3)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hsourceGap, hthreeLevel,
      eventually_gt_atTop (Real.exp 1)] with X hgap hthreeX hX
  intro q _inst chi hprim hqX T rho hrho _hbeta hheight himX
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hlogOne : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt hXpos]
    exact hX
  have hzero : DirichletCharacter.LFunction chi
      ((rho.re : ℂ) + (rho.im : ℂ) * Complex.I) = 0 := by
    simpa [Complex.re_add_im] using
      (MAPAPPrimitiveRegularLowGap.LFunction_eq_zero_of_mem_zeroSupport
        chi hrho)
  by_cases hchi : chi = 1
  · have hq : q = 1 := by
      have hcond : chi.conductor = q := hprim
      rw [hchi, DirichletCharacter.conductor_one] at hcond
      exact hcond.symm
    subst q
    subst chi
    have hnonzero :
        1 - 1 / khaleWeakDenominatorAbs 3 rho.im ≤ rho.re →
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
            ((rho.re : ℂ) + (rho.im : ℂ) * Complex.I) ≠ 0 := by
      intro hsigma
      exact conductor_one_nonvanishing_via_level_three_of_appendixB104
        hKhale104 hheight hsigma
    have hrecip :
        1 / khaleWeakDenominatorAbs 3 rho.im ≤ 1 - rho.re := by
      by_contra hnot
      have hsigma :
          1 - 1 / khaleWeakDenominatorAbs 3 rho.im ≤ rho.re := by
        linarith
      exact (hnonzero hsigma) hzero
    have hweak := hgap 3 rho.im rho.re (by norm_num) hthreeX
      hheight himX hrecip
    simpa [c] using hweak
  · have hnonzero :
        1 - 1 / khaleWeakDenominatorAbs q rho.im ≤ rho.re →
          DirichletCharacter.LFunction chi
            ((rho.re : ℂ) + (rho.im : ℂ) * Complex.I) ≠ 0 := by
      intro hsigma
      exact primitive_nonprincipal_absolute_nonvanishing hKhale104 chi
        hprim hchi hheight hsigma
    have hrecip :=
      one_div_khaleWeakDenominatorAbs_le_one_sub_sigma_of_zero
        chi (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hheight
        hnonzero hzero
    have hweak := hgap q rho.im rho.re
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hqX
      hheight himX hrecip
    simpa [c] using hweak


end
end MAPKhaleAppendixBSource

#print axioms MAPKhaleAppendixBSource.exists_principalPreKhaleGap
#print axioms MAPKhaleAppendixBSource.exists_primitive_principal_preKhale_gap
#print axioms MAPKhaleAppendixBSource.exists_eventually_primitive_regular_high_gap_of_appendixB
#print axioms MAPKhaleAppendixBSource.strong_level_three_denominator_le_weak_level_one
#print axioms MAPKhaleAppendixBSource.principal_one_nonzero_of_principal_three_nonzero
#print axioms MAPKhaleAppendixBSource.conductor_one_high_nonvanishing_of_appendixB86
#print axioms MAPKhaleAppendixBSource.conductor_one_nonvanishing_via_level_three_of_appendixB104
#print axioms MAPKhaleAppendixBSource.character_level_two_eq_one
#print axioms MAPKhaleAppendixBSource.three_le_level_of_isPrimitive_of_ne_one
#print axioms MAPKhaleAppendixBSource.primitive_nonprincipal_absolute_nonvanishing
