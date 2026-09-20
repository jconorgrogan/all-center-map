import APFoundation
import APZeroDensityCertificate
import LowBetaMeshClosure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# The maximal explicit-formula bridge in Proposition 2.2

This module isolates the deterministic conversion after the weighted zero-mass
estimate.  It does not assume or assert `SimultaneousShortIntervalAP`.

The first part is the literal finite character projector with the principal
main term removed.  The second part records the exact square-mean inequality
which prevents a loss by the number of characters.  The final interfaces are
strictly source-facing: a truncated primitive explicit formula and the
one-sided Hardy--Littlewood maximal theorem remain visible analytic inputs.
-/

namespace APMaximalExplicitFormulaBridge

open MeasureTheory Set
open scoped BigOperators ENNReal ArithmeticFunction

noncomputable section

open APFoundation

variable {q : ℕ} [NeZero q]

/-- The ambient-character short-window error before passage to the primitive
inducer.  The principal character has the literal real main term `Y` removed. -/
def ambientCharacterWindowError
    (χ : DirichletCharacter ℂ q) (S : Finset ℕ) (Y : ℝ) : ℂ :=
  twistedMangoldtSum χ S - if χ = 1 then Y else 0

theorem residueClass_nat_apply (q a k : ℕ) [NeZero q] :
    ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) k =
      if k % q = a % q then ArithmeticFunction.vonMangoldt k else 0 := by
  change ({n : ℕ | (n : ZMod q) = (a : ZMod q)}.indicator
    (fun n => ArithmeticFunction.vonMangoldt n)) k = _
  rw [Set.indicator_apply]
  simp only [Set.mem_setOf_eq]
  have hiff : ((k : ZMod q) = (a : ZMod q)) ↔ k % q = a % q :=
    ZMod.natCast_eq_natCast_iff' k a q
  by_cases h : k % q = a % q
  · simp [h, hiff.mpr h]
  · have hz : ¬ ((k : ZMod q) = (a : ZMod q)) := mt hiff.mp h
    simp [h, hz]

/-- The elementary prefix used in `progressionPsi` is literally mathlib's
residue-class von Mangoldt sum.  This also fixes the open/closed endpoint
convention: both sides include exactly `1 ≤ k ≤ floor x`. -/
theorem progressionPsi_eq_residueClassPrefix
    (x : ℝ) (q a : ℕ) [NeZero q] :
    (progressionPsi x q a : ℂ) =
      residueClassWindow (a : ZMod q) 0 ⌊x⌋₊ := by
  classical
  have hsets : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  unfold progressionPsi residueClassWindow
  rw [hsets]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  change ((if k % q = a % q then ArithmeticFunction.vonMangoldt k else 0 : ℝ) : ℂ) =
    (ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) k : ℂ)
  rw [residueClass_nat_apply]

/-- Exact subtraction of two real endpoints.  The half-open arithmetic window
is `floor x < k ≤ floor (x+Y)`. -/
theorem progressionPsi_interval_eq_residueClassWindow
    {x Y : ℝ} (hY : 0 ≤ Y) (q a : ℕ) [NeZero q] :
    ((progressionPsi (x + Y) q a - progressionPsi x q a : ℝ) : ℂ) =
      residueClassWindow (a : ZMod q) ⌊x⌋₊ ⌊x + Y⌋₊ := by
  classical
  have hfloor : ⌊x⌋₊ ≤ ⌊x + Y⌋₊ :=
    Nat.floor_mono (by linarith)
  push_cast
  rw [progressionPsi_eq_residueClassPrefix,
    progressionPsi_eq_residueClassPrefix]
  unfold residueClassWindow
  have hsubset : Finset.Ioc 0 ⌊x⌋₊ ⊆ Finset.Ioc 0 ⌊x + Y⌋₊ := by
    intro k hk
    simp only [Finset.mem_Ioc] at hk ⊢
    exact ⟨hk.1, hk.2.trans hfloor⟩
  have hsdiff :
      Finset.Ioc 0 ⌊x + Y⌋₊ \ Finset.Ioc 0 ⌊x⌋₊ =
        Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊ := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Ioc]
    omega
  rw [← hsdiff]
  exact (Finset.sum_sdiff_eq_sub
    (f := fun k => (ArithmeticFunction.vonMangoldt.residueClass
      (a : ZMod q) k : ℂ)) hsubset).symm

/-- Exact character projector after the principal main term is removed.  This
is the finite algebra used before any explicit formula or zero estimate. -/
theorem residueClassWindow_sub_main_eq_sum_characterErrors
    {a : ZMod q} (ha : IsUnit a) (m n : ℕ) (Y : ℝ) :
    residueClassWindow a m n - (Y : ℂ) / (q.totient : ℂ) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * ambientCharacterWindowError χ (Finset.Ioc m n) Y := by
  classical
  rw [residueClassWindow_eq_sum_characters ha]
  have hprincipal :
      ∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * ((if χ = 1 then Y else 0 : ℝ) : ℂ) = Y := by
    have hainv : IsUnit a⁻¹ :=
      isUnit_of_dvd_one ⟨a, (ZMod.inv_mul_of_unit a ha).symm⟩
    rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q)]
    · rw [MulChar.one_apply hainv, one_mul]
      simp
    · intro b _ hb
      simp [hb]
    · simp
  have hsum :
      (∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * ambientCharacterWindowError χ (Finset.Ioc m n) Y) =
        (∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * twistedMangoldtSum χ (Finset.Ioc m n)) - Y := by
    simp_rw [ambientCharacterWindowError, mul_sub]
    rw [Finset.sum_sub_distrib, hprincipal]
  rw [hsum]
  simp only [twistedMangoldtSum]
  have hphi : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne'
  field_simp

/-- The real normalized AP error is exactly the normalized character error
before any supremum, maximal operator, or zero estimate is applied. -/
theorem normalizedAPError_eq_sum_characterErrors
    {x Y : ℝ} (hY : 0 < Y) {q a : ℕ} [NeZero q]
    (ha : a.Coprime q) :
    (normalizedAPError x Y q a : ℂ) =
      ((q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ *
            ambientCharacterWindowError χ (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y) / Y := by
  have haunit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  have hinterval := progressionPsi_interval_eq_residueClassWindow
    (x := x) (Y := Y) hY.le q a
  calc
    (normalizedAPError x Y q a : ℂ) =
        (((progressionPsi (x + Y) q a - progressionPsi x q a : ℝ) : ℂ) -
          (Y : ℂ) / (q.totient : ℂ)) / (Y : ℂ) := by
      unfold normalizedAPError
      push_cast
      rfl
    _ = (residueClassWindow (a : ZMod q) ⌊x⌋₊ ⌊x + Y⌋₊ -
          (Y : ℂ) / (q.totient : ℂ)) / (Y : ℂ) := by
      rw [hinterval]
    _ = _ := by
      rw [residueClassWindow_sub_main_eq_sum_characterErrors haunit]

/-- A Cauchy--Schwarz inequality for the normalized character projector.  At a
reduced residue the character phases have norm one, and the number of
characters is exactly `φ(q)`. -/
theorem norm_sq_normalized_character_sum_le_mean_sq
    {a : ZMod q} (ha : IsUnit a)
    (E : DirichletCharacter ℂ q → ℂ) :
    ‖(q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * E χ‖ ^ 2 ≤
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, ‖E χ‖ ^ 2 := by
  classical
  have hphiNat : 0 < q.totient := Nat.totient_pos.mpr q.pos_of_neZero
  have hphi : 0 < (q.totient : ℝ) := by exact_mod_cast hphiNat
  have hphase (χ : DirichletCharacter ℂ q) : ‖χ a⁻¹‖ = 1 := by
    have ha_inv : ((↑(ha.unit⁻¹) : ZMod q)) = a⁻¹ := by
      calc
        ((↑(ha.unit⁻¹) : ZMod q)) = ((↑ha.unit : ZMod q))⁻¹ :=
          (ZMod.inv_coe_unit ha.unit).symm
        _ = a⁻¹ := congrArg Inv.inv ha.unit_spec
    rw [← ha_inv]
    exact χ.unit_norm_eq_one (ha.unit⁻¹)
  have hnorm :
      ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * E χ‖ ≤
        ∑ χ : DirichletCharacter ℂ q, ‖E χ‖ := by
    calc
      ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * E χ‖ ≤
          ∑ χ : DirichletCharacter ℂ q, ‖χ a⁻¹ * E χ‖ := norm_sum_le _ _
      _ = ∑ χ : DirichletCharacter ℂ q, ‖E χ‖ := by
        apply Finset.sum_congr rfl
        intro χ _
        rw [norm_mul, hphase, one_mul]
  have hnormsq :
      ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * E χ‖ ^ 2 ≤
        (∑ χ : DirichletCharacter ℂ q, ‖E χ‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcs :
      (∑ χ : DirichletCharacter ℂ q, ‖E χ‖) ^ 2 ≤
        ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, ‖E χ‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rw [mul_pow, inv_pow]
  calc
    ((q.totient : ℝ) ^ 2)⁻¹ *
        ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * E χ‖ ^ 2 ≤
        ((q.totient : ℝ) ^ 2)⁻¹ *
          (((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) *
            ∑ χ : DirichletCharacter ℂ q, ‖E χ‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact hnormsq.trans hcs
      · positivity
    _ = (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, ‖E χ‖ ^ 2 := by
      rw [Finset.card_univ, hcard]
      field_simp

/-- Pointwise character bounds may be inserted after Cauchy--Schwarz.  This is
the legal replacement for the manuscript's invalid attempt to use exact
orthogonality after taking a supremum in `Y`. -/
theorem norm_sq_normalized_character_sum_le_mean_majorant_sq
    {a : ZMod q} (ha : IsUnit a)
    (E : DirichletCharacter ℂ q → ℂ)
    (G : DirichletCharacter ℂ q → ℝ)
    (hEG : ∀ χ, ‖E χ‖ ≤ G χ) :
    ‖(q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * E χ‖ ^ 2 ≤
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, (G χ) ^ 2 := by
  have hbase := norm_sq_normalized_character_sum_le_mean_sq ha E
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro χ _
    exact pow_le_pow_left₀ (norm_nonneg _) (hEG χ) 2
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Source-faithful pointwise maximal conversion for one legal modulus and
residue.  `G χ` is intended to be `M⁺F_χ(x)` plus the explicit-formula
remainder.  It is independent of `a` and of the later supremum over `Y`. -/
theorem normalizedAPError_sq_le_mean_characterMajorants
    {x Y : ℝ} (hY : 0 < Y) {q a : ℕ} [NeZero q]
    (ha : a.Coprime q)
    (G : DirichletCharacter ℂ q → ℝ)
    (hmajor : ∀ χ,
      ‖ambientCharacterWindowError χ (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y‖ ≤ G χ) :
    |normalizedAPError x Y q a| ^ 2 ≤
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, (G χ) ^ 2 := by
  have haunit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  have hnormalize :
      ((q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ (a : ZMod q)⁻¹ *
              ambientCharacterWindowError χ (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y) / Y =
        (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ (a : ZMod q)⁻¹ *
              (ambientCharacterWindowError χ
                (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y) := by
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [← Finset.sum_mul]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real,
    normalizedAPError_eq_sum_characterErrors hY ha,
    hnormalize]
  exact norm_sq_normalized_character_sum_le_mean_majorant_sq
    haunit (fun χ => ambientCharacterWindowError χ
      (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y) G hmajor

/-! ## The two nonlinear suprema -/

/-- The exact inner part of `simultaneousAPMax` at one positive modulus. -/
def fixedModulusAPMax (q : ℕ) [NeZero q]
    (ε X x : ℝ) : ℝ≥0∞ :=
  ⨆ (a : ℕ) (_haq : a < q) (_ha : a.Coprime q)
      (Y : ℝ) (_hYlow : Real.rpow X (2 / 15 + ε) ≤ Y)
      (_hYhigh : Y ≤ X),
    ENNReal.ofReal |normalizedAPError x Y q a| ^ 2

/-- A per-character majorant independent of `a` and `Y` controls the full
supremum over every reduced residue and every real legal aperture. -/
theorem fixedModulusAPMax_le_mean_characterMajorants
    {q : ℕ} [NeZero q] {ε X x : ℝ} (hX : 0 < X)
    (G : DirichletCharacter ℂ q → ℝ)
    (hmajor : ∀ (a : ℕ), a < q → a.Coprime q →
      ∀ (Y : ℝ), Real.rpow X (2 / 15 + ε) ≤ Y → Y ≤ X →
        ∀ χ : DirichletCharacter ℂ q,
          ‖ambientCharacterWindowError χ
              (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y‖ ≤ G χ) :
    fixedModulusAPMax q ε X x ≤
      ENNReal.ofReal ((q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, (G χ) ^ 2) := by
  unfold fixedModulusAPMax
  apply iSup_le
  intro a
  apply iSup_le
  intro haq
  apply iSup_le
  intro ha
  apply iSup_le
  intro Y
  apply iSup_le
  intro hYlow
  apply iSup_le
  intro hYhigh
  have hY : 0 < Y :=
    (Real.rpow_pos_of_pos hX _).trans_le hYlow
  rw [← ENNReal.ofReal_pow (abs_nonneg _) 2]
  exact ENNReal.ofReal_le_ofReal
    (normalizedAPError_sq_le_mean_characterMajorants hY ha G
      (hmajor a haq ha Y hYlow hYhigh))

/-- The maximum over legal moduli is bounded by a finite sum of their
nonnegative majorants.  This is the exact legal replacement for trying to
commute character orthogonality with `max_q`, `max_a`, or `sup_Y`. -/
theorem simultaneousAPMax_le_sum_fixedModulusMajorants
    {K ε X x : ℝ} {Q : ℕ} (B : ℕ → ℝ≥0∞)
    (hcapQ : Real.rpow (Real.log X) K ≤ Q)
    (hfixed : ∀ (q : ℕ) (hqpos : 1 ≤ q)
        (_hqcap : (q : ℝ) ≤ Real.rpow (Real.log X) K),
      letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
      fixedModulusAPMax q ε X x ≤ B q) :
    simultaneousAPMax K ε X x ≤
      ∑ q ∈ Finset.Icc 1 Q, B q := by
  unfold simultaneousAPMax
  apply iSup_le
  intro q
  apply iSup_le
  intro hqpos
  apply iSup_le
  intro hqcap
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  change fixedModulusAPMax q ε X x ≤ _
  have hqQreal : (q : ℝ) ≤ (Q : ℝ) := hqcap.trans hcapQ
  have hqQ : q ≤ Q := by exact_mod_cast hqQreal
  exact (hfixed q hqpos hqcap).trans <|
    Finset.single_le_sum (fun _ _ => bot_le)
      (Finset.mem_Icc.mpr ⟨hqpos, hqQ⟩)

/-- Integrated form of the preceding finite-modulus reduction.  All
measurability is explicit; the only later analytic task is to bound each
per-modulus majorant using the one-sided maximal theorem and the weighted
zero-mass estimate. -/
theorem lintegral_simultaneousAPMax_le_sum_majorants
    {K ε X : ℝ} {Q : ℕ} (B : ℕ → ℝ → ℝ≥0∞)
    (hcapQ : Real.rpow (Real.log X) K ≤ Q)
    (hmeas : ∀ q ∈ Finset.Icc 1 Q, Measurable (B q))
    (hfixed : ∀ (x : ℝ) (q : ℕ) (hqpos : 1 ≤ q)
        (_hqcap : (q : ℝ) ≤ Real.rpow (Real.log X) K),
      letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
      fixedModulusAPMax q ε X x ≤ B q x) :
    (∫⁻ x in Set.Icc (X / 2) (4 * X), simultaneousAPMax K ε X x) ≤
      ∑ q ∈ Finset.Icc 1 Q,
        ∫⁻ x in Set.Icc (X / 2) (4 * X), B q x := by
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X), simultaneousAPMax K ε X x) ≤
        ∫⁻ x in Set.Icc (X / 2) (4 * X),
          ∑ q ∈ Finset.Icc 1 Q, B q x := by
      apply lintegral_mono
      intro x
      exact simultaneousAPMax_le_sum_fixedModulusMajorants
        (fun q => B q x) hcapQ (hfixed x)
    _ = ∑ q ∈ Finset.Icc 1 Q,
        ∫⁻ x in Set.Icc (X / 2) (4 * X), B q x := by
      exact MeasureTheory.lintegral_finsetSum _ (fun q hq => hmeas q hq)

/-! ## The formerly ambiguous lower endpoint -/

/-- At `β = 1/2+δ₀`, the low strip is false and mesh cell zero is true.
Thus the source-faithful half-open split loses and double-counts no zero. -/
theorem proposition22_lower_endpoint_assignment
    {ε : ℝ} (hε : 0 < ε) :
    ¬ (1 / 2 + MAPLowBetaMeshClosure.paperDelta0 ε <
        1 / 2 + MAPLowBetaMeshClosure.paperDelta0 ε) ∧
      0 ∈ Finset.range
          (MAPGuthMaynard.meshCellCount
            (MAPLowBetaMeshClosure.paperDelta0 ε)
            (MAPLowBetaMeshClosure.paperDelta ε)) ∧
      MAPGuthMaynard.meshPoint
          (MAPLowBetaMeshClosure.paperDelta0 ε)
          (MAPLowBetaMeshClosure.paperDelta ε) 0 ≤
        1 / 2 + MAPLowBetaMeshClosure.paperDelta0 ε ∧
      1 / 2 + MAPLowBetaMeshClosure.paperDelta0 ε <
        MAPGuthMaynard.meshPoint
            (MAPLowBetaMeshClosure.paperDelta0 ε)
            (MAPLowBetaMeshClosure.paperDelta ε) 0 +
          MAPLowBetaMeshClosure.paperDelta ε := by
  refine ⟨lt_irrefl _, ?_⟩
  exact MAPLowBetaMeshClosure.lower_endpoint_mem_first_mesh_cell hε

end

end APMaximalExplicitFormulaBridge

#print axioms APMaximalExplicitFormulaBridge.residueClassWindow_sub_main_eq_sum_characterErrors
#print axioms APMaximalExplicitFormulaBridge.norm_sq_normalized_character_sum_le_mean_sq
#print axioms APMaximalExplicitFormulaBridge.normalizedAPError_sq_le_mean_characterMajorants
#print axioms APMaximalExplicitFormulaBridge.fixedModulusAPMax_le_mean_characterMajorants
#print axioms APMaximalExplicitFormulaBridge.lintegral_simultaneousAPMax_le_sum_majorants
#print axioms APMaximalExplicitFormulaBridge.proposition22_lower_endpoint_assignment
