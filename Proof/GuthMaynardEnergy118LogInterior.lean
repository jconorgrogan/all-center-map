import GuthMaynardEnergy118Coordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
noncomputable section
namespace GuthMaynardEnergy118LogInterior

def logFrequencyMargin : ℝ := (1-Real.log 2)/(2*Real.pi)

theorem logFrequencyMargin_pos : 0 < logFrequencyMargin := by
  have hh := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
  unfold logFrequencyMargin
  apply div_pos
  · linarith
  · positivity

/-- Every dyadic ratio frequency stays a fixed distance from the endpoints of
the compact Fourier interval, including its negative sign. -/
theorem ratio_log_frequency_interior {v r : ℝ}
    (hvlo : (1/2 : ℝ) ≤ v) (hvhi : v ≤ 2)
    (hr : r ≤ logFrequencyMargin) :
    (-1 : ℝ)/(2*Real.pi)+r ≤ Real.log v/(-2*Real.pi) ∧
      Real.log v/(-2*Real.pi) ≤ 1/(2*Real.pi)-r := by
  have hv : 0 < v := by linarith
  have hc : 0 < 2*Real.pi := by positivity
  have hloghi : Real.log v ≤ Real.log 2 := Real.log_le_log hv hvhi
  have hloglo : -Real.log 2 ≤ Real.log v := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ)<1/2) hvlo
    simpa only [one_div,Real.log_inv] using hh
  have hfreq : Real.log v/(-2*Real.pi) = -Real.log v/(2*Real.pi) := by ring
  rw [hfreq]
  have hr' : r*(2*Real.pi) ≤ 1-Real.log 2 :=
    (le_div_iff₀ hc).1 hr
  constructor
  · apply (le_div_iff₀ hc).2
    have hden : ((-1 : ℝ)/(2*Real.pi))*(2*Real.pi) = -1 :=
      div_mul_cancel₀ _ hc.ne'
    rw [add_mul,hden]
    linarith
  · apply (div_le_iff₀ hc).2
    have hden : (1/(2*Real.pi))*(2*Real.pi) = (1 : ℝ) :=
      div_mul_cancel₀ _ hc.ne'
    rw [sub_mul,hden]
    linarith

/-- A sublinear power collar fits inside the fixed logarithmic margin at all
sufficiently large times. The threshold is chosen before T and the ratios. -/
theorem eventually_power_collar {eta : ℝ} (heta : eta < 1) :
    ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      Real.rpow T eta/(3*T) ≤ logFrequencyMargin := by
  let c : ℝ := logFrequencyMargin
  have hc : 0 < c := logFrequencyMargin_pos
  have hgap : 0 < 1-eta := by linarith
  have hp := (tendsto_rpow_atTop hgap).eventually
    (eventually_ge_atTop (1/(3*c)))
  have hevent : ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧
      Real.rpow T eta/(3*T) ≤ c := by
    filter_upwards [hp,eventually_ge_atTop (1 : ℝ)] with T hpow hT
    refine ⟨hT,?_⟩
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hmul := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hTpos.le eta)
    have hid : Real.rpow T (1-eta)*Real.rpow T eta = T := by
      calc
        _ = Real.rpow T ((1-eta)+eta) := (Real.rpow_add hTpos _ _).symm
        _ = T := by rw [sub_add_cancel]; exact Real.rpow_one T
    change 1/(3*c)*Real.rpow T eta ≤ Real.rpow T (1-eta)*Real.rpow T eta at hmul
    rw [hid] at hmul
    have hscale := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ 3*c)
    have hscaleid : (3*c)*(1/(3*c)) = (1 : ℝ) := by field_simp
    rw [← mul_assoc,hscaleid,one_mul] at hscale
    apply (div_le_iff₀ (by positivity : 0 < 3*T)).2
    nlinarith
  obtain ⟨a,ha⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 a,le_max_left _ _,?_⟩
  intro T hT
  exact (ha T ((le_max_right _ _).trans hT)).2

end GuthMaynardEnergy118LogInterior
#print axioms GuthMaynardEnergy118LogInterior.ratio_log_frequency_interior
#print axioms GuthMaynardEnergy118LogInterior.eventually_power_collar
