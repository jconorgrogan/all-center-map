import MRTSourcePacketEquation82HalfRange

/-!
# The legal whole-line extension before MRT equation (81)

The source extends the `x` integral at the Cauchy--Schwarz step, before the
packet correlation is formed.  This module records that exact move.  It also
exposes the complementary correlation term which would have to be controlled
if one instead tried to replace the already truncated correlation afterwards.
-/

namespace MAPMRTSourceWholeLineExtension

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTSourcePacketSupport
open MAPMRTPacketEquation82

noncomputable section

/-- On the support of the dual function the restricted and unrestricted
source packets agree pointwise. -/
theorem sourceRestrictedPacket_eq_sourceStationaryPacket
    {X H beta t x : ℝ} {cutoff outer : ℝ → ℝ}
    (hx : x ∈ Set.Icc (X / 2) (4 * X)) :
    sourceRestrictedPacket X H beta t cutoff outer x =
      sourceStationaryPacket X H x beta t cutoff outer := by
  simp [sourceRestrictedPacket, hx]

/-- Multiplication by a dual function supported on `[X/2,4X]` permits the
unrestricted packet to replace the indicator packet before Cauchy--Schwarz. -/
theorem dual_mul_sourceRestrictedPacket_eq_unrestricted
    {X H beta t x : ℝ} {cutoff outer : ℝ → ℝ} {g : ℝ → ℂ}
    (hgSupport : ∀ y, y ∉ Set.Icc (X / 2) (4 * X) → g y = 0) :
    g x * sourceRestrictedPacket X H beta t cutoff outer x =
      g x * sourceStationaryPacket X H x beta t cutoff outer := by
  by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
  · rw [sourceRestrictedPacket_eq_sourceStationaryPacket hx]
  · simp [sourceRestrictedPacket, hx, hgSupport x hx]

/-- Exact source-facing whole-line extension: because `g` vanishes off its
declared support, the pairing is unchanged when the packet indicator is
removed.  No truncation error occurs at this earlier line. -/
theorem integral_dual_mul_sourceRestrictedPacket_eq_unrestricted
    {X H beta t : ℝ} {cutoff outer : ℝ → ℝ} {g : ℝ → ℂ}
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0) :
    (∫ x : ℝ, g x * sourceRestrictedPacket X H beta t cutoff outer x) =
      ∫ x : ℝ, g x * sourceStationaryPacket X H x beta t cutoff outer := by
  apply integral_congr_ae
  filter_upwards with x
  exact dual_mul_sourceRestrictedPacket_eq_unrestricted hgSupport

/-- The exact normalized `L²` Cauchy--Schwarz inequality used when the source
enlarges the nonnegative post-duality energy to the whole real line. -/
theorem norm_sq_integral_mul_le_energy
    {g P : ℝ → ℂ}
    (hg : MemLp g 2) (hP : MemLp P 2)
    (hgNorm : (∫ x : ℝ, ‖g x‖ ^ 2) = 1) :
    ‖∫ x : ℝ, g x * P x‖ ^ 2 ≤ ∫ x : ℝ, ‖P x‖ ^ 2 := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr (by norm_num)
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (p := (2 : ℝ)) (q := (2 : ℝ)) (f := g) (g := P)
    hpq (by simpa using hg) (by simpa using hP)
  have hholder' :
      (∫ x : ℝ, ‖g x‖ * ‖P x‖) ≤
        Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) *
          Real.sqrt (∫ x : ℝ, ‖P x‖ ^ 2) := by
    simpa [Real.sqrt_eq_rpow] using hholder
  have hnorm :
      ‖∫ x : ℝ, g x * P x‖ ≤ Real.sqrt (∫ x : ℝ, ‖P x‖ ^ 2) := by
    calc
      ‖∫ x : ℝ, g x * P x‖ ≤ ∫ x : ℝ, ‖g x * P x‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ x : ℝ, ‖g x‖ * ‖P x‖ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [norm_mul]
      _ ≤ Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) *
          Real.sqrt (∫ x : ℝ, ‖P x‖ ^ 2) := hholder'
      _ = Real.sqrt (∫ x : ℝ, ‖P x‖ ^ 2) := by
        rw [hgNorm, Real.sqrt_one, one_mul]
  have henergy : 0 ≤ ∫ x : ℝ, ‖P x‖ ^ 2 :=
    integral_nonneg fun x ↦ sq_nonneg ‖P x‖
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    ‖∫ x : ℝ, g x * P x‖ ^ 2 ≤
        (Real.sqrt (∫ x : ℝ, ‖P x‖ ^ 2)) ^ 2 := hsquare
    _ = ∫ x : ℝ, ‖P x‖ ^ 2 := Real.sq_sqrt henergy

/-- Source specialization of the legal extension: the original indicator
pairing is bounded by the whole-line packet energy. -/
theorem norm_sq_integral_dual_mul_sourceRestrictedPacket_le_whole_energy
    {X H beta t : ℝ} {cutoff outer : ℝ → ℝ} {g : ℝ → ℂ}
    (hg : MemLp g 2)
    (hpacket : MemLp
      (fun x : ℝ ↦ sourceStationaryPacket X H x beta t cutoff outer) 2)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (hgNorm : (∫ x : ℝ, ‖g x‖ ^ 2) = 1) :
    ‖∫ x : ℝ, g x * sourceRestrictedPacket X H beta t cutoff outer x‖ ^ 2 ≤
      ∫ x : ℝ, ‖sourceStationaryPacket X H x beta t cutoff outer‖ ^ 2 := by
  rw [integral_dual_mul_sourceRestrictedPacket_eq_unrestricted hgSupport]
  exact norm_sq_integral_mul_le_energy hg hpacket hgNorm

/-- The restricted packet correlation is exactly the set integral over the
sharp dual-support interval. -/
theorem packetCorrelation_sourceRestrictedPacket_eq_setIntegral
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ} :
    packetCorrelation
        (fun s x ↦ sourceRestrictedPacket X H beta s cutoff outer x) t t' =
      ∫ x : ℝ in Set.Icc (X / 2) (4 * X),
        sourceStationaryPacket X H x beta t cutoff outer *
          star (sourceStationaryPacket X H x beta t' cutoff outer) := by
  unfold packetCorrelation sourceRestrictedPacket
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (X / 2) (4 * X) <;> simp [hx]

/-- If one waits until after forming the correlation, removing the sharp
indicator creates this literal complementary correlation. -/
def sourcePacketCorrelationExtensionError
    (X H beta t t' : ℝ) (cutoff outer : ℝ → ℝ) : ℂ :=
  ∫ x : ℝ in (Set.Icc (X / 2) (4 * X))ᶜ,
    sourceStationaryPacket X H x beta t cutoff outer *
      star (sourceStationaryPacket X H x beta t' cutoff outer)

/-- Exact decomposition showing why the whole-line extension must occur
before Cauchy--Schwarz.  A post-correlation replacement needs a separate bound
for `sourcePacketCorrelationExtensionError`. -/
theorem packetCorrelation_unrestricted_eq_restricted_add_extensionError
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (hprod : Integrable (fun x : ℝ ↦
      sourceStationaryPacket X H x beta t cutoff outer *
        star (sourceStationaryPacket X H x beta t' cutoff outer))) :
    packetCorrelation
        (fun s x ↦ sourceStationaryPacket X H x beta s cutoff outer) t t' =
      packetCorrelation
          (fun s x ↦ sourceRestrictedPacket X H beta s cutoff outer x) t t' +
        sourcePacketCorrelationExtensionError X H beta t t' cutoff outer := by
  rw [packetCorrelation_sourceRestrictedPacket_eq_setIntegral]
  unfold packetCorrelation sourcePacketCorrelationExtensionError
  simpa only using
    (integral_add_compl
      (s := Set.Icc (X / 2) (4 * X)) measurableSet_Icc hprod).symm

#print axioms sourceRestrictedPacket_eq_sourceStationaryPacket
#print axioms integral_dual_mul_sourceRestrictedPacket_eq_unrestricted
#print axioms norm_sq_integral_mul_le_energy
#print axioms norm_sq_integral_dual_mul_sourceRestrictedPacket_le_whole_energy
#print axioms packetCorrelation_sourceRestrictedPacket_eq_setIntegral
#print axioms packetCorrelation_unrestricted_eq_restricted_add_extensionError

end
end MAPMRTSourceWholeLineExtension
