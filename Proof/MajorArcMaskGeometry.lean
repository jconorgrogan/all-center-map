import MajorArcPrimePairWeld

namespace MAPMajorArcMaskGeometry

open AddCircle Metric Set
open Filter Asymptotics
open MAPMajorArcWeld

noncomputable section

/-- Distinct rational centers with positive denominators are separated on the
normalized circle by at least the reciprocal product of their denominators. -/
theorem inv_mul_denominators_le_dist_rationalCenter
    {q r a b : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hne : rationalCenter q a ≠ rationalCenter r b) :
    1 / ((q : ℝ) * (r : ℝ)) ≤
      dist (rationalCenter q a) (rationalCenter r b) := by
  let d : ℝ := (a : ℝ) / (q : ℝ) - (b : ℝ) / (r : ℝ)
  let z : ℤ :=
    (a : ℤ) * (r : ℤ) - (b : ℤ) * (q : ℤ) -
      round d * ((q : ℤ) * (r : ℤ))
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hden : (0 : ℝ) < (q : ℝ) * (r : ℝ) := mul_pos hqR hrR
  have hdscale : ((q : ℝ) * (r : ℝ)) *
      (d - (round d : ℝ)) = (z : ℤ) := by
    dsimp [d, z]
    push_cast
    field_simp
  have hfrac : d - (round d : ℝ) ≠ 0 := by
    intro hz
    apply hne
    have hcoe : (d : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨round d, by simpa [hz] using (sub_eq_zero.mp hz).symm⟩
    unfold rationalCenter
    rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub]
    exact hcoe
  have hz : z ≠ 0 := by
    intro hz
    have : ((q : ℝ) * (r : ℝ)) * (d - (round d : ℝ)) = 0 := by
      rw [hdscale, hz]
      norm_num
    exact hfrac ((mul_eq_zero.mp this).resolve_left hden.ne')
  have hone : (1 : ℝ) ≤ |(z : ℤ)| := by
    exact_mod_cast Int.one_le_abs hz
  unfold rationalCenter
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  change 1 / ((q : ℝ) * (r : ℝ)) ≤ ‖(d : UnitAddCircle)‖
  rw [AddCircle.norm_eq]
  simp only [inv_one, one_mul, mul_one]
  rw [← (div_le_iff₀ hden).symm]
  rw [← abs_of_pos hden, ← abs_mul, mul_comm, hdscale]
  simpa only [Int.cast_abs] using hone

/-- A literal lifted rational arc, expressed as a closed metric ball on the
normalized circle. -/
def rationalArc (R : ℝ) (q a : ℕ) : Set UnitAddCircle :=
  closedBall (rationalCenter q a) R

/-- The explicit union of the lifted rational arcs with exactly the paper's
real denominator cutoff. -/
def rationalArcUnion (X : ℝ) (B D : ℕ) : Set UnitAddCircle :=
  ⋃ q : ℕ, ⋃ a : ℕ,
    if 1 ≤ q ∧ (q : ℝ) ≤ (Real.log X) ^ B ∧ a ∈ reducedResidues q then
      rationalArc ((Real.log X) ^ D / X) q a
    else ∅

/-- The literal manuscript mask is exactly the union of the lifted closed
balls, not merely a superset of the model arcs. -/
theorem majorArcs_eq_rationalArcUnion (X : ℝ) (B D : ℕ) :
    PrimePairEndpoints.majorArcs X B D = rationalArcUnion X B D := by
  ext α
  simp only [PrimePairEndpoints.majorArcs, rationalArcUnion, mem_setOf_eq,
    mem_iUnion, mem_ite_empty_right, rationalArc, mem_closedBall]
  constructor
  · rintro ⟨q, a, hq, hqcut, haq, hacop, hdist⟩
    exact ⟨q, a, ⟨⟨hq, hqcut, (mem_reducedResidues.mpr ⟨haq, hacop⟩)⟩, hdist⟩⟩
  · rintro ⟨q, a, ⟨⟨hq, hqcut, ha⟩, hdist⟩⟩
    rw [mem_reducedResidues] at ha
    exact ⟨q, a, hq, hqcut, ha.1, ha.2, hdist⟩

/-- Reduced representatives in `[0,1)` give unique rational centers on the
circle.  Thus the denominator/residue indexing used by the manuscript has no
hidden duplicate arcs. -/
theorem rationalCenter_eq_iff_of_reduced
    {q r a b : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r)
    (haq : a < q) (hbr : b < r) (ha : a.Coprime q) (hb : b.Coprime r) :
    rationalCenter q a = rationalCenter r b ↔ q = r ∧ a = b := by
  constructor
  · intro heq
    let d : ℝ := (a : ℝ) / (q : ℝ) - (b : ℝ) / (r : ℝ)
    have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hrR : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
    have ha0 : (0 : ℝ) ≤ (a : ℝ) / q := div_nonneg (by positivity) hqR.le
    have hb0 : (0 : ℝ) ≤ (b : ℝ) / r := div_nonneg (by positivity) hrR.le
    have ha1 : (a : ℝ) / q < 1 := (div_lt_one hqR).2 (by exact_mod_cast haq)
    have hb1 : (b : ℝ) / r < 1 := (div_lt_one hrR).2 (by exact_mod_cast hbr)
    have hd0 : (d : UnitAddCircle) = 0 := by
      unfold rationalCenter at heq
      rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub] at heq
      exact heq
    rcases (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hd0 with ⟨n, hn⟩
    have hdn : (n : ℝ) = d := by simpa using hn
    have hn0 : n = 0 := by
      have hnlow : (-1 : ℝ) < n := by dsimp [d] at hdn ⊢; nlinarith
      have hnhigh : (n : ℝ) < 1 := by dsimp [d] at hdn ⊢; nlinarith
      have hnlowZ : (-1 : ℤ) < n := by exact_mod_cast hnlow
      have hnhighZ : n < (1 : ℤ) := by exact_mod_cast hnhigh
      omega
    have hdEq : (a : ℝ) / q = (b : ℝ) / r := by
      dsimp [d] at hdn
      rw [hn0] at hdn
      norm_num at hdn
      linarith
    have hcrossR : (a : ℝ) * r = (b : ℝ) * q := by
      field_simp at hdEq
      simpa [mul_comm] using hdEq
    have hcross : a * r = b * q := by exact_mod_cast hcrossR
    have hq_dvd_r : q ∣ r := by
      apply ha.symm.dvd_of_dvd_mul_left
      exact ⟨b, by simpa [Nat.mul_comm] using hcross⟩
    have hr_dvd_q : r ∣ q := by
      apply hb.symm.dvd_of_dvd_mul_left
      exact ⟨a, by simpa [Nat.mul_comm] using hcross.symm⟩
    have hqr : q = r := Nat.dvd_antisymm hq_dvd_r hr_dvd_q
    subst r
    have hq0 : q ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hab : a = b := by
      exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hq0) hcross
    exact ⟨rfl, hab⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Farey separation makes all distinct denominator-`Q` rational arcs
pairwise disjoint as soon as `2R < Q⁻²`.  This is the quantitative geometry
needed by the MAP logarithmic radius `R=(log X)^D/X`. -/
theorem disjoint_rationalArc_of_denominators_le
    {Q q r a b : ℕ} {R : ℝ}
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hne : rationalCenter q a ≠ rationalCenter r b)
    (hwidth : 2 * R < 1 / ((Q : ℝ) ^ 2)) :
    Disjoint (rationalArc R q a) (rationalArc R r b) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hQR : (0 : ℝ) < Q := by
    exact_mod_cast (lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hq) hqQ)
  have hprod : (q : ℝ) * (r : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hrQR : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
    nlinarith
  have hinv : 1 / ((Q : ℝ) ^ 2) ≤
      1 / ((q : ℝ) * (r : ℝ)) := by
    exact one_div_le_one_div_of_le (mul_pos hqR hrR) hprod
  have hdist : 2 * R < dist (rationalCenter q a) (rationalCenter r b) :=
    hwidth.trans_le (hinv.trans
      (inv_mul_denominators_le_dist_rationalCenter hq hr hne))
  unfold rationalArc
  apply Metric.closedBall_disjoint_closedBall
  simpa [two_mul] using hdist

/-- Literal pairwise-disjointness for two distinct reduced indices from the
paper's denominator mask. -/
theorem disjoint_rationalArc_of_distinct_reduced_indices
    {Q q r a b : ℕ} {R : ℝ}
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (haq : a < q) (hbr : b < r) (ha : a.Coprime q) (hb : b.Coprime r)
    (hidx : q ≠ r ∨ a ≠ b)
    (hwidth : 2 * R < 1 / ((Q : ℝ) ^ 2)) :
    Disjoint (rationalArc R q a) (rationalArc R r b) := by
  apply disjoint_rationalArc_of_denominators_le hq hr hqQ hrQ
  · intro hcenters
    have hqa := (rationalCenter_eq_iff_of_reduced hq hr haq hbr ha hb).mp hcenters
    exact hidx.elim (· hqa.1) (· hqa.2)
  · exact hwidth

/-- A purely real version of the width check, before extracting the eventual
threshold.  It uses the paper's literal radius and real denominator cutoff. -/
theorem disjoint_paper_rationalArcs_of_growth
    {X : ℝ} {B D q r a b : ℕ}
    (hX : 1 < X)
    (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hqcut : (q : ℝ) ≤ (Real.log X) ^ B)
    (hrcut : (r : ℝ) ≤ (Real.log X) ^ B)
    (haq : a < q) (hbr : b < r) (ha : a.Coprime q) (hb : b.Coprime r)
    (hidx : q ≠ r ∨ a ≠ b)
    (hgrowth : 2 * (Real.log X) ^ (D + 2 * B) < X) :
    Disjoint
      (rationalArc ((Real.log X) ^ D / X) q a)
      (rationalArc ((Real.log X) ^ D / X) r b) := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hlogB : 0 < (Real.log X) ^ B := pow_pos hlog _
  have hprod : (q : ℝ) * (r : ℝ) ≤ ((Real.log X) ^ B) ^ 2 := by
    nlinarith
  have hpow : (Real.log X) ^ (2 * B) = ((Real.log X) ^ B) ^ 2 := by
    rw [show 2 * B = B * 2 by omega, pow_mul]
  have hsmall : 2 * ((Real.log X) ^ D / X) <
      1 / (Real.log X) ^ (2 * B) := by
    have hXpos : 0 < X := lt_trans zero_lt_one hX
    have hpowpos : 0 < (Real.log X) ^ (2 * B) := pow_pos hlog _
    rw [show 2 * ((Real.log X) ^ D / X) =
      (2 * (Real.log X) ^ D) / X by ring]
    rw [div_lt_div_iff₀ hXpos hpowpos]
    simpa [pow_add, mul_assoc] using hgrowth
  have hinv : 1 / (Real.log X) ^ (2 * B) ≤
      1 / ((q : ℝ) * (r : ℝ)) := by
    rw [hpow]
    exact one_div_le_one_div_of_le (mul_pos hqR hrR) hprod
  apply Metric.closedBall_disjoint_closedBall
  have hcenter : rationalCenter q a ≠ rationalCenter r b := by
    intro heq
    have hqa := (rationalCenter_eq_iff_of_reduced hq hr haq hbr ha hb).mp heq
    exact hidx.elim (· hqa.1) (· hqa.2)
  simpa [two_mul] using hsmall.trans_le (hinv.trans
    (inv_mul_denominators_le_dist_rationalCenter hq hr hcenter))

/-- The manuscript width inequality is automatic beyond a threshold depending
only on the fixed logarithmic exponents. -/
theorem eventually_two_mul_log_pow_lt_id (B D : ℕ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      1 < X ∧ 2 * (Real.log X) ^ (D + 2 * B) < X := by
  have hbound := (Real.isLittleO_pow_log_id_atTop (n := D + 2 * B)).bound
    (show (0 : ℝ) < 1 / 4 by norm_num)
  have hlarge : ∀ᶠ X : ℝ in atTop, 2 ≤ X := eventually_ge_atTop 2
  have hfinal : ∀ᶠ X : ℝ in atTop,
      1 < X ∧ 2 * (Real.log X) ^ (D + 2 * B) < X := by
    filter_upwards [hbound, hlarge] with X hb hX
    have hlognonneg : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have hpownonneg : 0 ≤ (Real.log X) ^ (D + 2 * B) := pow_nonneg hlognonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hpownonneg, id_eq,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ X)] at hb
    constructor
    · linarith
    · nlinarith
  exact eventually_atTop.mp hfinal

end

end MAPMajorArcMaskGeometry
