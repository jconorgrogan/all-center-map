import JutilaLemma6ErrorBound
import JutilaCollarMeshCutoff

/-!
# Exact exponent ledger for Jutila Lemma 6 on the MAP collar

At `delta=1/280`, Jutila chooses

* `R = D^delta`,
* `z2 = D^(1/2+8delta)`,
* `X = D^(1+12delta)`.

The sharp p.48 convexity exponent is `1/2+1/560`.  At the collar endpoint
`beta=279/280`, the Mellin error retains the fixed power saving `51/9800`.
This is separate from, and does not spend, the later A.5 gap reserve.
-/

namespace MAPJutilaLemma6ParameterLedger

open Real
open MAPJutilaCollarMeshCutoff
open MAPJutilaLemma6MellinIntegral

noncomputable section

def lemmaSixRExponent : ℝ := collarDelta
def lemmaSixZ2Exponent : ℝ := 1 / 2 + 8 * collarDelta
def lemmaSixXExponent : ℝ := 1 + 12 * collarDelta
def lemmaSixEndpoint : ℝ := 279 / 280
def lemmaSixPowerSaving : ℝ := 51 / 9800

theorem lemmaSixRExponent_eq : lemmaSixRExponent = 1 / 280 := by
  norm_num [lemmaSixRExponent, collarDelta]

theorem lemmaSixZ2Exponent_eq : lemmaSixZ2Exponent = 37 / 70 := by
  norm_num [lemmaSixZ2Exponent, collarDelta]

theorem lemmaSixXExponent_eq : lemmaSixXExponent = 73 / 70 := by
  norm_num [lemmaSixXExponent, collarDelta]

/-- Exact positive margin left after the sharp Gamma--L integral. -/
theorem lemmaSix_endpoint_margin :
    lemmaSixXExponent * lemmaSixEndpoint -
      (lemmaSixZ2Exponent + lemmaSixRExponent + p48HeightExponent) =
        lemmaSixPowerSaving := by
  norm_num [lemmaSixXExponent, lemmaSixEndpoint, lemmaSixZ2Exponent,
    lemmaSixRExponent, lemmaSixPowerSaving, collarDelta,
    p48HeightExponent, MAPJutilaCollarA5Budget.detectorLogBudget]

theorem lemmaSixPowerSaving_pos : 0 < lemmaSixPowerSaving := by
  norm_num [lemmaSixPowerSaving]

theorem lemmaSix_error_exponent_le
    {beta : ℝ} (hbeta : lemmaSixEndpoint ≤ beta) :
    -lemmaSixXExponent * beta + lemmaSixZ2Exponent +
        lemmaSixRExponent + p48HeightExponent ≤
      -lemmaSixPowerSaving := by
  have hXpos : 0 < lemmaSixXExponent := by
    norm_num [lemmaSixXExponent, collarDelta]
  have hmargin := lemmaSix_endpoint_margin
  nlinarith

/-- Multiplicative real-power form of the endpoint ledger. -/
theorem lemmaSix_error_power_le
    {D beta : ℝ} (hD : 1 ≤ D)
    (hbeta : lemmaSixEndpoint ≤ beta) :
    Real.rpow D (-lemmaSixXExponent * beta) *
        Real.rpow D lemmaSixZ2Exponent *
        Real.rpow D lemmaSixRExponent *
        Real.rpow D p48HeightExponent ≤
      Real.rpow D (-lemmaSixPowerSaving) := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  rw [show
      Real.rpow D (-lemmaSixXExponent * beta) *
          Real.rpow D lemmaSixZ2Exponent *
          Real.rpow D lemmaSixRExponent *
          Real.rpow D p48HeightExponent =
        Real.rpow D
          (-lemmaSixXExponent * beta + lemmaSixZ2Exponent +
            lemmaSixRExponent + p48HeightExponent) by
      calc
        Real.rpow D (-lemmaSixXExponent * beta) *
              Real.rpow D lemmaSixZ2Exponent *
              Real.rpow D lemmaSixRExponent *
              Real.rpow D p48HeightExponent =
              Real.rpow D
                (-lemmaSixXExponent * beta + lemmaSixZ2Exponent) *
              Real.rpow D lemmaSixRExponent *
              Real.rpow D p48HeightExponent := by
                exact congrArg
                  (fun y : ℝ => y * Real.rpow D lemmaSixRExponent *
                    Real.rpow D p48HeightExponent)
                  (Real.rpow_add hDpos
                    (-lemmaSixXExponent * beta) lemmaSixZ2Exponent).symm
        _ = Real.rpow D
                ((-lemmaSixXExponent * beta + lemmaSixZ2Exponent) +
                  lemmaSixRExponent) *
              Real.rpow D p48HeightExponent := by
                exact congrArg
                  (fun y : ℝ => y * Real.rpow D p48HeightExponent)
                  (Real.rpow_add hDpos
                    (-lemmaSixXExponent * beta + lemmaSixZ2Exponent)
                    lemmaSixRExponent).symm
        _ = Real.rpow D
              (((-lemmaSixXExponent * beta + lemmaSixZ2Exponent) +
                lemmaSixRExponent) + p48HeightExponent) := by
                exact (Real.rpow_add hDpos
                  ((-lemmaSixXExponent * beta + lemmaSixZ2Exponent) +
                    lemmaSixRExponent) p48HeightExponent).symm
        _ = Real.rpow D
              (-lemmaSixXExponent * beta + lemmaSixZ2Exponent +
                lemmaSixRExponent + p48HeightExponent) := by ring]
  exact Real.rpow_le_rpow_of_exponent_le hD
    (lemmaSix_error_exponent_le hbeta)

end

end MAPJutilaLemma6ParameterLedger

#print axioms MAPJutilaLemma6ParameterLedger.lemmaSix_endpoint_margin
#print axioms MAPJutilaLemma6ParameterLedger.lemmaSix_error_power_le
