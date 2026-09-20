import FordDirichletGrowthStrip
import FordGrowthWidth

noncomputable section
namespace FordScaledDiskGrowth
open FordFiniteGrowthBound FordGrowthWidth FordAllLambdaOffsetBound

def diskScale (t : ℝ) : ℝ := widthEta (Real.log (t + 3)) / 16
def diskCenter (t : ℝ) : ℂ := ((1 + diskScale t : ℝ) : ℂ) + Complex.I * (t : ℂ)

theorem disk_geometry {t : ℝ} (ht : 3 ≤ t) :
    1 ≤ Real.log (t + 3) ∧ 0 < diskScale t ∧ diskScale t ≤ 1 / 32 ∧
      ∀ z ∈ Metric.closedBall (diskCenter t) (6 * diskScale t),
        1 - widthEta (Real.log (t + 3)) ≤ z.re ∧ z.re ≤ 2 ∧
        2 ≤ z.im ∧ z.im ≤ t + 3 := by
  have hlog : 1 ≤ Real.log (t + 3) := by
    apply (Real.le_log_iff_exp_le (by linarith)).2
    linarith [Real.exp_one_lt_three]
  obtain ⟨hw, hwhalf, _, _⟩ := width_properties hlog
  have ha : 0 < diskScale t := by unfold diskScale; positivity
  have hah : diskScale t ≤ 1 / 32 := by unfold diskScale; linarith
  refine ⟨hlog, ha, hah, ?_⟩
  intro z hz
  have hn : ‖z - diskCenter t‖ ≤ 6 * diskScale t := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre := (Complex.abs_re_le_norm (z - diskCenter t)).trans hn
  have him := (Complex.abs_im_le_norm (z - diskCenter t)).trans hn
  simp only [Complex.sub_re, Complex.sub_im, diskCenter, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im] at hre him
  norm_num at hre him
  have hrelow := (abs_le.mp hre).1
  have hrehi := (abs_le.mp hre).2
  have himlow := (abs_le.mp him).1
  have himhi := (abs_le.mp him).2
  have hwscale : widthEta (Real.log (t + 3)) = 16 * diskScale t := by
    unfold diskScale
    ring
  constructor
  · rw [hwscale]; linarith
  constructor
  · linarith
  constructor <;> linarith

theorem envelope_le_of_log_le {R T v : ℝ}
    (hT : 1 ≤ T) (hv : 2 ≤ v) (hlog : Real.log v ≤ T) :
    commonEnvelope R v (widthEta T) ≤ R + 273 * Real.exp 1 + 12 * Real.pi := by
  obtain ⟨hw, hwhalf, hfirst, hsecond⟩ := width_properties hT
  have hlv : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  have hpow : (Real.log v) ^ ((4 : ℝ) / 5) ≤ T ^ ((4 : ℝ) / 5) :=
    Real.rpow_le_rpow hlv hlog (by norm_num)
  have hfirst' : 1000 * widthEta T * (Real.log v) ^ ((4 : ℝ) / 5) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hfirst
  have hsecond' : widthEta T * Real.sqrt (widthEta T / savingCoeff) * Real.log v ≤ 1 :=
    (mul_le_mul_of_nonneg_left hlog (by positivity)).trans hsecond
  unfold commonEnvelope
  have he1 := Real.exp_le_exp.mpr hfirst'
  have he2 := Real.exp_le_exp.mpr hsecond'
  linarith

/-- The actual L-function bound on the full six-scale disk needed by Jensen. -/
theorem scaled_disk_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
      (t : ℝ), 3 ≤ t → ∀ z ∈ Metric.closedBall (diskCenter t) (6 * diskScale t),
      ‖DirichletCharacter.LFunction χ z‖ ≤
        (N : ℝ) * ((N : ℝ) ^ 2 + C * Real.log (t + 3)) := by
  obtain ⟨R, hR, hg⟩ := FordDirichletGrowthStrip.dirichlet_growth_strip
  let D : ℝ := R + 273 * Real.exp 1 + 12 * Real.pi
  let C : ℝ := 6 * D + 14
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN χ t ht z hz
  obtain ⟨hT, ha, hah, hcoords⟩ := disk_geometry ht
  obtain ⟨hre, hre2, him, himhi⟩ := hcoords z hz
  obtain ⟨hw, hwhalf, _, _⟩ := width_properties hT
  have hlv : 0 ≤ Real.log z.im := Real.log_nonneg (by linarith)
  have hlog : Real.log z.im ≤ Real.log (t + 3) :=
    Real.log_le_log (by linarith) himhi
  have henv := envelope_le_of_log_le (R := R) hT him hlog
  change commonEnvelope R z.im (widthEta (Real.log (t + 3))) ≤ D at henv
  have hb := hg N χ z.im (widthEta (Real.log (t + 3))) z.re him hw.le hwhalf hre hre2
  have hzid : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    apply Complex.ext <;> simp
  rw [hzid] at hb
  have hscalar :
      6 * Real.log z.im * commonEnvelope R z.im (widthEta (Real.log (t + 3))) + 14 ≤
      C * Real.log (t + 3) := by
    have hmul := mul_le_mul_of_nonneg_left henv (show 0 ≤ 6 * Real.log z.im by positivity)
    have hmul2 := mul_le_mul_of_nonneg_right hlog (show 0 ≤ 6 * D by positivity)
    dsimp [C]
    nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hscalar) (Nat.cast_nonneg N))

end FordScaledDiskGrowth
#print axioms FordScaledDiskGrowth.disk_geometry
#print axioms FordScaledDiskGrowth.envelope_le_of_log_le
#print axioms FordScaledDiskGrowth.scaled_disk_growth
