import MRTPacketEquation83
import Mathlib.MeasureTheory.Function.L2Space

/-!
# MRT equation (82) from (83) and the off-diagonal packet estimate

The near diagonal is proved by an internal `L²` correlation inequality.  The
two pointwise pieces are then combined by the Cauchy envelope already used for
(83), giving the manuscript denominator
`(1 + |t-t'|/(|β|H))²`.
-/

namespace MAPMRTPacketEquation82

open MeasureTheory Set
open MAPMRTPacketEnergy

noncomputable section

/-- The Hermitian packet correlation occurring in equations (81),(82). -/
def packetCorrelation (J : ℝ → ℝ → ℂ) (t t' : ℝ) : ℂ :=
  ∫ x : ℝ, J t x * star (J t' x)

/-- Cauchy--Schwarz in the symmetric arithmetic-mean form needed near the
diagonal in (82). -/
theorem norm_packetCorrelation_le_average_energy
    {J : ℝ → ℝ → ℂ} {t t' : ℝ}
    (ht : MemLp (J t) 2) (ht' : MemLp (J t') 2) :
    ‖packetCorrelation J t t'‖ ≤
      ((∫ x : ℝ, ‖J t x‖ ^ 2) + (∫ x : ℝ, ‖J t' x‖ ^ 2)) / 2 := by
  have ht'ConjMeas : AEStronglyMeasurable (fun x ↦ star (J t' x)) :=
    Complex.continuous_conj.comp_aestronglyMeasurable ht'.aestronglyMeasurable
  have ht'Conj : MemLp (fun x ↦ star (J t' x)) 2 :=
    ht'.congr_norm ht'ConjMeas (Filter.Eventually.of_forall (fun x ↦ by simp))
  have hprod : Integrable (fun x ↦ J t x * star (J t' x)) := by
    change Integrable ((J t) * fun x ↦ star (J t' x))
    exact ht.integrable_mul ht'Conj
  have htSq : Integrable (fun x ↦ ‖J t x‖ ^ 2) := ht.norm.integrable_sq
  have ht'Sq : Integrable (fun x ↦ ‖J t' x‖ ^ 2) := ht'.norm.integrable_sq
  have hprodNorm : Integrable (fun x ↦ ‖J t x‖ * ‖J t' x‖) := by
    change Integrable ((fun x ↦ ‖J t x‖) * fun x ↦ ‖J t' x‖)
    exact ht.norm.integrable_mul ht'.norm
  have hmajor : Integrable (fun x ↦
      (‖J t x‖ ^ 2 + ‖J t' x‖ ^ 2) / 2) :=
    (htSq.add ht'Sq).div_const 2
  calc
    ‖packetCorrelation J t t'‖ ≤
        ∫ x : ℝ, ‖J t x * star (J t' x)‖ := by
      exact norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖J t x‖ * ‖J t' x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      simp
    _ ≤ ∫ x : ℝ, (‖J t x‖ ^ 2 + ‖J t' x‖ ^ 2) / 2 := by
      apply integral_mono hprodNorm hmajor
      intro x
      nlinarith [sq_nonneg (‖J t x‖ - ‖J t' x‖)]
    _ = ((∫ x : ℝ, ‖J t x‖ ^ 2) +
          (∫ x : ℝ, ‖J t' x‖ ^ 2)) / 2 := by
      rw [integral_div, integral_add htSq ht'Sq]

/-- Equation (82) from the diagonal estimate (83) and the manuscript's
off-diagonal two-integration-by-parts bound.

The constant `4(C83+Coff)` is explicit.  The hard-regime inequality
`1 < |β|H` is used exactly when the far envelope is compared to the diagonal
scale. -/
theorem packet_correlation_equation82
    {X H beta C83 Coff t t' : ℝ} {J : ℝ → ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hhard : 1 < |beta| * H)
    (hC83 : 0 ≤ C83) (hCoff : 0 ≤ Coff)
    (hJ : ∀ s, MemLp (J s) 2)
    (h83 : ∀ s, (∫ x : ℝ, ‖J s x‖ ^ 2) ≤
      C83 * H / (|beta| * X))
    (hoff : ∀ s s', |beta| * H ≤ |s - s'| →
      ‖packetCorrelation J s s'‖ ≤
        Coff * H ^ 2 / (X * |s - s'| ^ 2)) :
    ‖packetCorrelation J t t'‖ ≤
      4 * (C83 + Coff) * H / (|beta| * X) /
        (1 + |t - t'| / (|beta| * H)) ^ 2 := by
  let q : ℝ := |beta|
  let R : ℝ := q * H
  let A : ℝ := (C83 + Coff) * H / (q * X)
  let B : ℝ := Coff * H ^ 2 / X
  let K : ℝ → ℂ := fun h ↦ packetCorrelation J t (t + h)
  have hq : 0 < q := by
    unfold q
    have hbeta : beta ≠ 0 := by
      intro hb
      subst beta
      norm_num at hhard
    exact abs_pos.mpr hbeta
  have hR : 0 < R := mul_pos hq hH
  have hA : 0 ≤ A := by unfold A; positivity
  have hB : 0 ≤ B := by unfold B; positivity
  have hcentral : ∀ h, ‖K h‖ ≤ A := by
    intro h
    have hcorr := norm_packetCorrelation_le_average_energy (hJ t) (hJ (t + h))
    have ht := h83 t
    have hth := h83 (t + h)
    have htq : (∫ x : ℝ, ‖J t x‖ ^ 2) ≤ C83 * H / (q * X) := by
      simpa [q] using ht
    have hthq : (∫ x : ℝ, ‖J (t + h) x‖ ^ 2) ≤
        C83 * H / (q * X) := by
      simpa [q] using hth
    have havg : ((∫ x : ℝ, ‖J t x‖ ^ 2) +
        (∫ x : ℝ, ‖J (t + h) x‖ ^ 2)) / 2 ≤
        C83 * H / (q * X) := by linarith
    have hcoeff : C83 * H / (q * X) ≤ (C83 + Coff) * H / (q * X) := by
      have hscale : 0 ≤ H / (q * X) := by positivity
      calc
        C83 * H / (q * X) = C83 * (H / (q * X)) := by ring
        _ ≤ (C83 + Coff) * (H / (q * X)) := by
          gcongr
          linarith
        _ = (C83 + Coff) * H / (q * X) := by ring
    exact hcorr.trans (havg.trans hcoeff)
  have hfar : ∀ h, R ≤ |(0 : ℝ) + 1 * h| →
      ‖K h‖ ≤ B / |(0 : ℝ) + 1 * h| ^ 2 := by
    intro h hh
    have hoff' := hoff t (t + h) (by simpa [R, q] using hh)
    have habs : |t - (t + h)| = |h| := by
      rw [show t - (t + h) = -h by ring, abs_neg]
    rw [habs] at hoff'
    unfold K B
    convert hoff' using 1 <;> field_simp <;> ring
  have hrelation : B / R ^ 2 ≤ A := by
    unfold A B R q
    have hbetaAbs : 0 < |beta| := hq
    field_simp [hbetaAbs.ne', hH.ne', hX.ne']
    nlinarith [mul_pos hbetaAbs hH]
  have henv := norm_le_cauchy_envelope
    (c := 0) (beta := 1) (R := R) (A := A) (B := B)
    (x := t' - t) (J := K) hR hA hB (hcentral (t' - t))
    (hfar (t' - t)) hrelation
  have hK : K (t' - t) = packetCorrelation J t t' := by
    simp [K]
  rw [hK] at henv
  simp only [zero_add, one_mul] at henv
  have hsq : ((t' - t) / R) ^ 2 = (|t - t'| / R) ^ 2 := by
    rw [← sq_abs]
    simp [abs_div, abs_of_pos hR, abs_sub_comm]
  rw [hsq] at henv
  let y : ℝ := |t - t'| / R
  have hy : 0 ≤ y := by unfold y; positivity
  have hden1 : 0 < 1 + y ^ 2 := by positivity
  have hden2 : 0 < (1 + y) ^ 2 := by positivity
  have hcompare : 2 * A / (1 + y ^ 2) ≤ 4 * A / (1 + y) ^ 2 := by
    apply (div_le_div_iff₀ hden1 hden2).2
    have hyineq : (1 + y) ^ 2 ≤ 2 * (1 + y ^ 2) := by
      nlinarith [sq_nonneg (y - 1)]
    nlinarith [hA]
  calc
    ‖packetCorrelation J t t'‖ ≤ 2 * A / (1 + y ^ 2) := by
      simpa [y] using henv
    _ ≤ 4 * A / (1 + y) ^ 2 := hcompare
    _ = 4 * (C83 + Coff) * H / (|beta| * X) /
        (1 + |t - t'| / (|beta| * H)) ^ 2 := by
      dsimp [A, y, R, q]
      ring

#print axioms MAPMRTPacketEquation82.norm_packetCorrelation_le_average_energy
#print axioms MAPMRTPacketEquation82.packet_correlation_equation82

end
end MAPMRTPacketEquation82
