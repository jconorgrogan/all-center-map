import FordLAlignedDiagonal
import FordOffdiagCount
import FordClassEnergyInterpolationActual
import FordLPointLargeModulusComplete
import FordLemma33Dichotomy
import FordLemma33FloorConversion

open scoped BigOperators
open MAPFordLemma32LiteralContract MAPFordCompleteSystemMoment
open FordKPointEnergy FordLPointClassEnergy FordClassEnergyMoment
open FordBoundaryCountGeometry FordLAlignedDiagonal FordOffdiagTensor
open FordPositiveHeightFamily MAPFordDifferenceFamily

noncomputable section
set_option autoImplicit false
namespace FordLemma33Actual

/-- The finite floor form of the actual L-count differencing lemma. All
diagonal, interpolation, signed-profile and selection inputs are internal. -/
theorem exists_difference_count
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (hp : 0 < p) (hq : 0 < q) (hk : 1 ≤ k) (hP : 1 ≤ P) :
    ∃ h : ℤ, 1 ≤ h ∧ h ≤ (P : ℤ) ∧
      (Fintype.card (LPoint s k P Q p q r phi) : ℝ) ≤
        max ((2 * (k : ℝ) * P) ^ k * (completeMoment s k Q : ℝ))
          ((2 : ℝ) ^ (k + 1) * ((P / p ^ r : ℕ) : ℝ) ^ k *
            Real.sqrt ((completeMoment s k Q : ℝ) *
              (Fintype.card (KPoint s k P Q (differencePsi phi h) (p * q)) : ℝ))) := by
  have hm : 0 < p ^ r := pow_pos hp _
  by_cases hH : 0 < P / p ^ r
  · obtain ⟨h0, hoff⟩ := FordOffdiagCount.offdiag_count_selection phi hp hq hk hm hH
    obtain ⟨hlo, hhi⟩ := shift_bounds hm h0
    refine ⟨shift h0, hlo, hhi, ?_⟩
    let f : FordKPointEnergy.PowerWord (s := s) (Q := Q) → Fin k → ℤ := baseFreq (q := p * q)
    let g : FordKPointEnergy.SourcePoint (P := P) → Fin k → ℤ := sourceFreq phi
    let cls : FordKPointEnergy.SourcePoint (P := P) → Fin (P + 1) :=
      positiveResidueClass (p := p) (r := r)
    have hL := lPoint_card_eq_classEnergy (s := s) (k := k) (P := P)
      (Q := Q) (p := p) (q := q) (r := r) phi
    have hJ := FordCompleteMomentBridge.completeMoment_eq_baseZero_card
      (s := s) (k := k) (Q := Q) (q := p * q) (Nat.mul_pos hp hq)
    have hmoment := FordClassEnergyInterpolationActual.classEnergy_card_interpolation_actual
      f g cls hk
    change (Fintype.card (ClassEnergyZero f g cls (k - 1)) : ℝ) ^ k ≤
      (Fintype.card (LClassEnergyZero (s := s) (k := k) (P := P)
        (Q := Q) (p := p) (q := q) (r := r) phi) : ℝ) ^ (k - 1) *
        (Fintype.card (BaseZero f) : ℝ) at hmoment
    rw [← hL, ← hJ] at hmoment
    have hdiagN := lDiag_card_le_classEnergy (s := s) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) hk phi
    have hdiag : (Fintype.card (LDiag s k P Q p q r phi) : ℝ) ≤
        ((k : ℝ) * P) * Fintype.card (ClassEnergyZero f g cls (k - 1)) := by
      exact_mod_cast hdiagN
    have hsplit : (Fintype.card (LPoint s k P Q p q r phi) : ℝ) =
        (Fintype.card (LDiag s k P Q p q r phi) : ℝ) +
          (Fintype.card (LOffdiag s k P Q p q r phi) : ℝ) := by
      exact_mod_cast (lPoint_card_partition (s := s) (P := P) (Q := Q)
        (p := p) (q := q) (r := r) phi)
    have hd := FordLemma33Dichotomy.count_dichotomy hk
      (L := (Fintype.card (LPoint s k P Q p q r phi) : ℝ))
      (D := (Fintype.card (LDiag s k P Q p q r phi) : ℝ))
      (O := (Fintype.card (LOffdiag s k P Q p q r phi) : ℝ))
      (M := (Fintype.card (ClassEnergyZero f g cls (k - 1)) : ℝ))
      (J := (completeMoment s k Q : ℝ))
      (K := (Fintype.card (KPoint s k P Q (differencePsi phi (shift h0)) (p * q)) : ℝ))
      (A := (k : ℝ) * P)
      (B := (2 : ℝ) ^ k * ((P / p ^ r : ℕ) : ℝ) ^ k)
      (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) hsplit hdiag hmoment hoff
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hd
  · have hlarge : P < p ^ r := by
      have hzero : P / p ^ r = 0 := Nat.eq_zero_of_not_pos hH
      exact (Nat.div_eq_zero_iff_lt hm).mp hzero
    have hcount := FordLPointLargeModulusComplete.lPoint_card_eq_completeMoment
      (s := s) (k := k) (P := P) (Q := Q) (p := p) (q := q) (r := r)
      phi hp hq hlarge
    refine ⟨1, le_rfl, by exact_mod_cast hP, ?_⟩
    apply le_trans _ (le_max_left _ _)
    rw [hcount]
    push_cast
    have hbase : (P : ℝ) ≤ 2 * (k : ℝ) * P := by
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have ht : (1 : ℝ) ≤ 2 * k := by linarith
      simpa using mul_le_mul_of_nonneg_right ht (show (0 : ℝ) ≤ P by positivity)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hbase k) (by positivity)

 /-- The source divisor form, with a literal differenced polynomial family and
the next Ford type and scale supplied by the proof. -/
theorem exists_typed_difference_count
    {s k d m P Q p q r : ℕ} {T : ℤ}
    (phi : Fin k → Polynomial ℤ)
    (htype : MAPFordType.FordType k d T m (MAPFordP16Source35Triangular.psiNatSucc phi))
    (hT : 0 < T) (hsize : T.natAbs ≤ P ^ d)
    (hp : 0 < p) (hq : 0 < q) (hk : 1 ≤ k) (hP : 1 ≤ P) (hr : 1 ≤ r) :
    ∃ (upsilon : Fin k → Polynomial ℤ) (T' : ℤ),
      MAPFordType.FordType k (d + 1) T' m
        (MAPFordP16Source35Triangular.psiNatSucc upsilon) ∧
      T ≤ T' ∧ T' ≤ (P : ℤ) * T ∧ T'.natAbs ≤ P ^ (d + 1) ∧
      (Fintype.card (LPoint s k P Q p q r phi) : ℝ) ≤
        (2 * (P : ℝ)) ^ k * max
          ((k : ℝ) ^ k * (completeMoment s k Q : ℝ))
          (2 / (p : ℝ) ^ (r * k) *
            Real.sqrt ((completeMoment s k Q : ℝ) *
              (Fintype.card (KPoint s k P Q upsilon (p * q)) : ℝ))) := by
  obtain ⟨h, hlo, hhi, hcount⟩ := exists_difference_count phi hp hq hk hP
  have hh : 0 < h := by omega
  refine ⟨differencePsi phi h, h * T,
    ford_type_differencePsi phi htype h hh, ?_, ?_,
    natAbs_scaled_step_le hsize hlo hhi, ?_⟩
  · simpa using mul_le_mul_of_nonneg_right hlo (le_of_lt hT)
  · exact mul_le_mul_of_nonneg_right hhi (le_of_lt hT)
  · exact FordLemma33FloorConversion.finite_floor_bound_le_source_scalar
      p P k r hp hP hk hr (by positivity) (by positivity) hcount

end FordLemma33Actual

#print axioms FordLemma33Actual.exists_difference_count
#print axioms FordLemma33Actual.exists_typed_difference_count
