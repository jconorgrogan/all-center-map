import FordScaledZeroFreeAbsolute
import FordScaledGapLogPower
import McCurleyPrimitiveLowPredicate
import MAPPrimitiveRegularHighSavingFixedTheta

noncomputable section
namespace FordPrimitiveRegularHighSaving
open Filter
open MAPPrimitiveRegularHighSavingFixedTheta

/-- The fixed-exponent high-ordinate source, derived from actual L-functions. -/
theorem primitiveRegularHighSavingAt_nineteen_twentieths :
    PrimitiveRegularHighSavingAt (19 / 20) := by
  obtain ⟨D, hD, hgap⟩ := FordScaledZeroFreeAbsolute.actual_zero_gap_absolute
  intro K hK
  obtain ⟨c, hc, hevent⟩ := FordScaledGapLogPower.gap_ge_log_power D K hD hK
  refine ⟨c, hc, ?_⟩
  filter_upwards [hevent] with X hX
  intro q hq χ hprim hqX T ρ hρ hre him himX
  have hzero : DirichletCharacter.LFunction χ ρ = 0 :=
    MAPMcCurleyPrimitiveLowPredicate.LFunction_eq_zero_of_mem_zeroSupport χ hρ
  exact (hX q |ρ.im| (NeZero.one_le : 1 ≤ q) hqX him himX).trans
    (hgap q χ ρ him hzero)

/-- The high-saving input is now a theorem, not an external source premise. -/
theorem fixedThetaWeakHighSaving : FixedThetaWeakHighSaving := by
  refine ⟨19 / 20, by norm_num, by norm_num,
    primitiveRegularHighSavingAt_nineteen_twentieths⟩

end FordPrimitiveRegularHighSaving
#print axioms FordPrimitiveRegularHighSaving.primitiveRegularHighSavingAt_nineteen_twentieths
#print axioms FordPrimitiveRegularHighSaving.fixedThetaWeakHighSaving
