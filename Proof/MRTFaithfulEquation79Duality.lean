import MRTFaithfulEquation79LocalizedBilinear

/-! Exact faithful half-range outer insertion and equation-(79) duality. -/
namespace MAPMRTFaithfulEquation79Duality
open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTFaithfulSmoothCutoff MAPMRTMediumEq79Parallel
open MAPMRTEquation79PacketBilinearCore MAPMRTVanDerCorputProof
noncomputable section
set_option maxHeartbeats 800000

/-- The faithful support has physical radius `H/8`, so even at `H=X/2`
it stays a positive distance from the logarithmic singularity. -/
theorem faithful_physical_support_half_range
    {X H x w : ℝ} (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hx : x ∈ Icc (X / 2) (4 * X))
    (hc : faithfulCutoff ((X * Real.exp w - x) / H) ≠ 0) :
    7 / 16 < Real.exp w ∧ Real.exp w < 65 / 16 := by
  have ha : |(X * Real.exp w - x) / H| < 1 / 8 := by
    by_contra hn
    exact hc (faithfulCutoff_zero (le_of_not_gt hn))
  rw [abs_div, abs_of_pos hH] at ha
  have hp := (div_lt_iff₀ hH).mp ha
  rw [abs_lt] at hp
  constructor <;> nlinarith [hx.1, hx.2]

theorem faithful_log_support_half_range
    {X H x w : ℝ} (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hx : x ∈ Icc (X / 2) (4 * X))
    (hc : faithfulCutoff ((X * Real.exp w - x) / H) ≠ 0) :
    w ∈ Icc (-10) 10 := by
  have hp := faithful_physical_support_half_range hX hH hHalf hx hc
  have he : 11 < Real.exp (10 : ℝ) := by
    have he' := Real.add_one_lt_exp (by norm_num : (10 : ℝ) ≠ 0)
    linarith
  have hen : Real.exp (-10 : ℝ) < 7 / 16 := by
    rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ (Real.exp_pos 10)]
    nlinarith
  constructor
  · exact (Real.exp_lt_exp.mp (hen.trans hp.1)).le
  · exact (Real.exp_lt_exp.mp (hp.2.trans (by linarith))).le

theorem faithful_sourcePacketAmplitude_eq_withoutOuter_half_range
    {X H x w : ℝ} (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hx : x ∈ Icc (X / 2) (4 * X)) :
    sourcePacketAmplitude X H x faithfulCutoff faithfulCutoff w =
      sourcePacketAmplitude X H x faithfulCutoff (fun _ ↦ 1) w := by
  by_cases hc : faithfulCutoff ((X * Real.exp w - x) / H) = 0
  · simp [sourcePacketAmplitude, hc]
  have hw := faithful_log_support_half_range hX hH hHalf hx hc
  have hs : |w / 100| ≤ (1 : ℝ) / 10 := by
    rw [abs_le]
    constructor <;> linarith [hw.1, hw.2]
  simp [sourcePacketAmplitude, faithfulCutoff_one hs]

theorem faithful_sourceStationaryPacket_eq_withoutOuter_half_range
    {X H x beta t : ℝ} (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hx : x ∈ Icc (X / 2) (4 * X)) :
    sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff =
      sourceStationaryPacket X H x beta t faithfulCutoff (fun _ ↦ 1) := by
  unfold sourceStationaryPacket
  apply integral_congr_ae
  filter_upwards with w
  rw [faithful_sourcePacketAmplitude_eq_withoutOuter_half_range hX hH hHalf hx]

/-- The outer amplitude supplies an integrable majorant for Fubini. -/
theorem faithful_outer_envelope_integrable :
    Integrable (fun w : ℝ ↦ Real.exp (w / 2) * |faithfulCutoff (w / 100)|) := by
  have hc : Continuous (fun w : ℝ ↦
      Real.exp (w / 2) * |faithfulCutoff (w / 100)|) := by
    exact (show Continuous (fun w : ℝ ↦ Real.exp (w / 2)) by fun_prop).mul
      ((faithfulCutoff_continuous.comp (by fun_prop)).abs)
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-100 : ℝ) 100))
  intro w hw
  by_contra hn
  have ha : 1 ≤ |w / 100| := by
    rw [abs_div]
    norm_num
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100)]
    have hn' : ¬ |w| ≤ 100 := by simpa [abs_le] using hn
    linarith [lt_of_not_ge hn']
  exact hw (by simp [faithfulCutoff_zero_of_one_le ha])

/-- The actual `(w,x)` packet/dual integrand is absolutely integrable. -/
theorem faithful_dualPacketKernel_integrable
    (X H beta t : ℝ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun z : ℝ × ℝ ↦ g z.2 *
      (additivePhase (stationaryPacketPhase X beta t z.1) *
        sourcePacketAmplitude X H z.2 faithfulCutoff faithfulCutoff z.1)) := by
  have hmajor := faithful_outer_envelope_integrable.mul_prod hg.norm
  have hadd : Continuous additivePhase := by unfold additivePhase; fun_prop
  have hamp : Continuous (fun z : ℝ × ℝ ↦
      additivePhase (stationaryPacketPhase X beta t z.1) *
        sourcePacketAmplitude X H z.2 faithfulCutoff faithfulCutoff z.1) := by
    have hc1 : Continuous (fun z : ℝ × ℝ ↦
        faithfulCutoff ((X * Real.exp z.1 - z.2) / H)) :=
      faithfulCutoff_continuous.comp (by fun_prop)
    have hc2 : Continuous (fun z : ℝ × ℝ ↦ faithfulCutoff (z.1 / 100)) :=
      faithfulCutoff_continuous.comp (by fun_prop)
    unfold sourcePacketAmplitude
    exact (hadd.comp (by unfold stationaryPacketPhase; fun_prop)).mul
      (((Complex.continuous_ofReal.comp (by fun_prop)).mul
        (Complex.continuous_ofReal.comp hc1)).mul
        (Complex.continuous_ofReal.comp hc2))
  apply hmajor.mono' (hg.aestronglyMeasurable.comp_snd.mul hamp.aestronglyMeasurable)
  filter_upwards with z
  simp only [Pi.mul_apply, norm_mul, norm_additivePhase, one_mul, sourcePacketAmplitude,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hb := abs_faithfulCutoff_le_one ((X * Real.exp z.1 - z.2) / H)
  calc
    _ = |faithfulCutoff ((X * Real.exp z.1 - z.2) / H)| *
        (Real.exp (z.1 / 2) * |faithfulCutoff (z.1 / 100)| * ‖g z.2‖) := by ring
    _ ≤ 1 * (Real.exp (z.1 / 2) * |faithfulCutoff (z.1 / 100)| * ‖g z.2‖) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := one_mul _

theorem stationaryPacketPhase_exact (X beta t w : ℝ) :
    additivePhase (stationaryPacketPhase X beta t w) =
      additivePhase (beta * X * Real.exp w) *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) := by
  unfold additivePhase stationaryPacketPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- Exact Fourier/packet duality, including the source's factor `sqrt X`.
Only integrability and the literal physical support of the dual are assumed. -/
theorem faithful_logarithmicDual_fourier_eq_packet_pairing
    {X H beta t : ℝ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    (∫ w : ℝ, logarithmicDualFunction X H beta faithfulCutoff g w *
      Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I))) =
      (Real.sqrt X : ℂ) * ∫ x : ℝ, g x *
        sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff := by
  let K : ℝ → ℝ → ℂ := fun w x ↦ g x *
    (additivePhase (stationaryPacketPhase X beta t w) *
      sourcePacketAmplitude X H x faithfulCutoff faithfulCutoff w)
  have hK : Integrable (Function.uncurry K) :=
    faithful_dualPacketKernel_integrable X H beta t hg
  have hp (w : ℝ) :
      logarithmicDualFunction X H beta faithfulCutoff g w *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) =
      (Real.sqrt X : ℂ) * ∫ x : ℝ, K w x := by
    unfold logarithmicDualFunction
    rw [← integral_const_mul]
    rw [← integral_mul_const]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (X / 2) (4 * X)
    · dsimp [K]
      rw [faithful_sourcePacketAmplitude_eq_withoutOuter_half_range hX hH hHalf hx,
        stationaryPacketPhase_exact]
      unfold sourcePacketAmplitude
      simp only [Complex.ofReal_one, mul_one]
      ring
    · simp [K, hgSupport x hx]
  simp_rw [hp]
  rw [integral_const_mul, integral_integral_swap hK]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  dsimp [K]
  rw [integral_const_mul]
  rfl

theorem faithful_sourceTilde_integrable
    {N : ℕ} {X beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hetaSmall : eta < 1 / 100) :
    Integrable (sourceTildePolynomial N X beta eta faithfulCutoff f) := by
  apply (MAPMRTFaithfulEquation79Bilinear.sourceTilde_continuous
    N X beta eta f hX hbeta heta).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-(|beta| * X / eta)) (|beta| * X / eta)))
  intro t ht
  by_contra hn
  exact ht (MAPMRTFaithfulEquation79Bilinear.sourceTilde_eq_zero_outside_interval
    hX hbeta heta hetaSmall hn)

theorem faithful_equation79PairingKernel_integrable
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hetaSmall : eta < 1 / 100) (hg : Integrable g) :
    Integrable (fun z : ℝ × ℝ ↦
      sourceTildePolynomial N X beta eta faithfulCutoff f z.1 *
        (g z.2 * sourceStationaryPacket X H z.2 beta z.1
          faithfulCutoff faithfulCutoff)) := by
  have hbase := (faithful_sourceTilde_integrable (N := N) (f := f)
    hX hbeta heta hetaSmall).mul_prod hg
  have hJ := MAPMRTFaithfulEquation79Bilinear.continuous_faithfulSourcePacket_joint
    X H beta
  have h := hbase.bdd_mul hJ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦
      MAPMRTSourcePacketSupport.norm_sourceStationaryPacket_le_outer
        (X := X) (H := H) (x := z.2) (beta := beta) (t := z.1)
        (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
        abs_faithfulCutoff_le_one abs_faithfulCutoff_le_one)
  apply h.congr
  filter_upwards with z
  ring

/-- The literal equation-(79) integral equals the dual pairing with the
faithful packet superposition.  Both Fubini interchanges are discharged and
the full source half range is retained. -/
theorem faithful_equation79Integral_eq_packetSuperposition_pairing
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (heta : 0 < eta) (hetaSmall : eta < 1 / 100)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    equation79Integral N X beta eta faithfulCutoff f
        (logarithmicDualFunction X H beta faithfulCutoff g) =
      (Real.sqrt X : ℂ) * ∫ x : ℝ, g x *
        packetSuperposition (sourceTildePolynomial N X beta eta faithfulCutoff f)
          (fun t x ↦ sourceStationaryPacket X H x beta t
            faithfulCutoff faithfulCutoff) x := by
  let A := sourceTildePolynomial N X beta eta faithfulCutoff f
  let J := fun t x ↦ sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff
  have hK : Integrable (Function.uncurry (fun t x ↦ A t * (g x * J t x))) :=
    faithful_equation79PairingKernel_integrable hX hbeta heta hetaSmall hg
  have hpoint (t : ℝ) :
      (∫ w : ℝ, A t * logarithmicDualFunction X H beta faithfulCutoff g w *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I))) =
      (Real.sqrt X : ℂ) * ∫ x : ℝ, A t * (g x * J t x) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul,
      faithful_logarithmicDual_fourier_eq_packet_pairing hX hH hHalf hg hgSupport,
      integral_const_mul]
    ring
  unfold equation79Integral
  change (∫ t : ℝ, ∫ w : ℝ, A t * _ * _) = _
  simp_rw [hpoint]
  rw [integral_const_mul, integral_integral_swap hK]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  change (∫ t : ℝ, A t * (g x * J t x)) = g x * ∫ t : ℝ, A t * J t x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem faithful_packetSuperposition_continuous
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hetaSmall : eta < 1 / 100) :
    Continuous (packetSuperposition
      (sourceTildePolynomial N X beta eta faithfulCutoff f)
      (fun t x ↦ sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff)) := by
  let A := sourceTildePolynomial N X beta eta faithfulCutoff f
  let J := fun t x ↦ sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff
  have hAc : Continuous A := MAPMRTFaithfulEquation79Bilinear.sourceTilde_continuous
    N X beta eta f hX hbeta heta
  have hAi : Integrable A := faithful_sourceTilde_integrable hX hbeta heta hetaSmall
  have hJc := MAPMRTFaithfulEquation79Bilinear.continuous_faithfulSourcePacket_joint X H beta
  unfold packetSuperposition
  apply MeasureTheory.continuous_of_dominated (bound := fun t ↦ (200 * Real.exp 50) * ‖A t‖)
  · intro x
    exact (hAc.mul (hJc.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · intro x
    filter_upwards with t
    rw [norm_mul]
    have hb := MAPMRTSourcePacketSupport.norm_sourceStationaryPacket_le_outer
      (X := X) (H := H) (x := x) (beta := beta) (t := t)
      (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
      abs_faithfulCutoff_le_one abs_faithfulCutoff_le_one
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hb (norm_nonneg (A t))
  · exact hAi.norm.const_mul _
  · filter_upwards with t
    change Continuous (fun x : ℝ ↦ A t * J t x)
    have hsec : Continuous (fun x : ℝ ↦ J t x) :=
      MAPMRTSourcePacketSupport.continuous_sourceStationaryPacket_in_x
        faithfulCutoff_continuous faithfulCutoff_continuous
        (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
    exact continuous_const.mul hsec

theorem faithful_packetSuperposition_hasCompactSupport
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 < H) :
    HasCompactSupport (packetSuperposition
      (sourceTildePolynomial N X beta eta faithfulCutoff f)
      (fun t x ↦ sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-(X * Real.exp 100 + H)) (X * Real.exp 100 + H)))
  intro x hx
  by_contra hn
  apply hx
  unfold packetSuperposition
  have hz (t : ℝ) : sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff = 0 :=
    MAPMRTWholeLinePacketMemLp.sourceStationaryPacket_eq_zero_outside_compact hX hH
      (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
      (fun y hy ↦ faithfulCutoff_zero_of_one_le hy) hn
  simp_rw [hz, mul_zero]
  simp

theorem faithful_packetSuperposition_memLp_two
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    MemLp (packetSuperposition
      (sourceTildePolynomial N X beta eta faithfulCutoff f)
      (fun t x ↦ sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff)) 2 := by
  have hc := faithful_packetSuperposition_continuous (H := H) (N := N) (f := f)
    hX hbeta heta hetaSmall
  have hs := faithful_packetSuperposition_hasCompactSupport
    (N := N) (beta := beta) (eta := eta) (f := f) hX hH
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
  apply (hc.norm.pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two, Pi.mul_apply] using
    (hs.norm.mul_right : HasCompactSupport (fun x ↦ _ * ‖packetSuperposition
      (sourceTildePolynomial N X beta eta faithfulCutoff f)
      (fun t x ↦ sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff) x‖))

theorem faithful_logarithmicDual_integrable_half_range
    {X H beta : ℝ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    Integrable (logarithmicDualFunction X H beta faithfulCutoff g) := by
  have hinner : Continuous (fun w : ℝ ↦ ∫ x : ℝ,
      (faithfulCutoff ((X * Real.exp w - x) / H) : ℂ) * g x) := by
    apply MeasureTheory.continuous_of_dominated (bound := fun x ↦ ‖g x‖)
    · intro w
      exact ((Complex.continuous_ofReal.comp
        (faithfulCutoff_continuous.comp (by fun_prop))).aestronglyMeasurable).mul
          hg.aestronglyMeasurable
    · intro w
      filter_upwards with x
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_faithfulCutoff_le_one _)
    · exact hg.norm
    · filter_upwards with x
      exact (Complex.continuous_ofReal.comp
        (faithfulCutoff_continuous.comp (by fun_prop))).mul continuous_const
  have hc : Continuous (logarithmicDualFunction X H beta faithfulCutoff g) := by
    unfold logarithmicDualFunction additivePhase
    exact (((continuous_const.mul (Complex.continuous_ofReal.comp (by fun_prop))).mul
      (Complex.continuous_exp.comp (by fun_prop))).mul hinner)
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-10 : ℝ) 10))
  intro w hw
  by_contra hn
  apply hw
  have hz (x : ℝ) : (faithfulCutoff ((X * Real.exp w - x) / H) : ℂ) * g x = 0 := by
    by_cases hx : x ∈ Icc (X / 2) (4 * X)
    · have hz : faithfulCutoff ((X * Real.exp w - x) / H) = 0 := by
        by_contra hc
        exact hn (faithful_log_support_half_range hX hH hHalf hx hc)
      simp [hz]
    · simp [hgSupport x hx]
  unfold logarithmicDualFunction
  simp_rw [hz]
  simp

/-- Exact medium projected sum as a packet pairing in the full half range. -/
theorem faithful_mediumProjectedSum_eq_packet_pairing
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (heta : 0 < eta) (hetaSmall : eta < 1 / 100)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    (∑ n ∈ Finset.Icc 1 N, f n * (Real.sqrt n : ℂ)⁻¹ *
      mediumFrequencyProjection X beta eta faithfulCutoff
        (logarithmicDualFunction X H beta faithfulCutoff g)
        (Real.log n - Real.log X)) =
      (Real.sqrt X : ℂ) * ∫ x : ℝ, g x *
        packetSuperposition (sourceTildePolynomial N X beta eta faithfulCutoff f)
          (fun t x ↦ sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff) x := by
  have hG := faithful_logarithmicDual_integrable_half_range (beta := beta) hX hH hHalf hg hgSupport
  have hp := MAPFinishP51FaithfulIntegrability.faithful_equation79_integrability_package
    (N := N) (f := f) hX hbeta heta hG
  have hi := MAPFinishP51Medium79.oneScaleEquation79Transform_of_integrable
    (show 0 < |beta| * X / eta by positivity) hp.1 hp.2.2.1
  have hlo := MAPFinishP51Medium79.oneScaleEquation79Transform_of_integrable
    (show 0 < 10 * eta * |beta| * X by positivity) hp.2.1 hp.2.2.2.1
  rw [mediumProjectedCriticalSum_eq_equation79Integral heta.ne' hi hlo
    hp.2.2.2.2.1 hp.2.2.2.2.2]
  exact faithful_equation79Integral_eq_packetSuperposition_pairing
    hX hH hHalf hbeta heta hetaSmall hg hgSupport

/-- Cauchy for the non-conjugated dual pairing used by the source. -/
theorem norm_integral_pairing_sq_le_energy
    {g F : ℝ → ℂ} (hg : MemLp g 2) (hF : MemLp F 2)
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1) :
    ‖∫ x : ℝ, g x * F x‖ ^ 2 ≤ ∫ x : ℝ, ‖F x‖ ^ 2 := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr (by norm_num)
  have hgNorm : MemLp (fun x ↦ ‖g x‖) (ENNReal.ofReal (2 : ℝ)) := by simpa using hg.norm
  have hFNorm : MemLp (fun x ↦ ‖F x‖) (ENNReal.ofReal (2 : ℝ)) := by simpa using hF.norm
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (g x))
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (F x)) hgNorm hFNorm
  have hh' : (∫ x : ℝ, ‖g x‖ * ‖F x‖) ≤
      Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) * Real.sqrt (∫ x : ℝ, ‖F x‖ ^ 2) := by
    simpa [Real.sqrt_eq_rpow] using hh
  have hs : Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hgOne
  have hn : ‖∫ x : ℝ, g x * F x‖ ≤ Real.sqrt (∫ x : ℝ, ‖F x‖ ^ 2) := by
    calc
      _ ≤ ∫ x : ℝ, ‖g x * F x‖ := norm_integral_le_integral_norm _
      _ = ∫ x : ℝ, ‖g x‖ * ‖F x‖ := by simp_rw [norm_mul]
      _ ≤ Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) * Real.sqrt (∫ x : ℝ, ‖F x‖ ^ 2) := hh'
      _ ≤ 1 * Real.sqrt (∫ x : ℝ, ‖F x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
      _ = _ := one_mul _
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq
    (Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg _))

/-- The faithful medium branch, with its exact source normalization and no
remaining Fubini, collar, packet-energy, or duality assumption. -/
theorem faithful_mediumProjectedSum_sq_le
    {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (hhard : 1 < |beta| * H)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100)
    (hg : Integrable g) (hgL2 : MemLp g 2)
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    ‖∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊, f n * (Real.sqrt n : ℂ)⁻¹ *
      mediumFrequencyProjection X beta eta faithfulCutoff
        (logarithmicDualFunction X H beta faithfulCutoff g)
        (Real.log n - Real.log X)‖ ^ 2 ≤
      (216 * MAPMRTFaithfulEquation81Weld.faithfulEquation82Constant / beta ^ 2) *
        MAPMRTProposition51Source.proposition51I X H f beta eta := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  rw [faithful_mediumProjectedSum_eq_packet_pairing hX hHpos hHalf hbeta heta hetaSmall hg hgSupport,
    norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg X), Real.sq_sqrt hX.le]
  have hpair := norm_integral_pairing_sq_le_energy hgL2
    (faithful_packetSuperposition_memLp_two (N := ⌊2 * X⌋₊) (f := f)
      hX hHpos hbeta heta hetaSmall) hgOne
  have henergy := MAPMRTFaithfulEquation79LocalizedBilinear.faithful_equation79PacketEnergy_le_stationary_scale
    (f := f) hX hH hHalf hbeta hhard heta hetaSmall
  calc
    _ ≤ X * (∫ x : ℝ, ‖packetSuperposition
        (sourceTildePolynomial ⌊2 * X⌋₊ X beta eta faithfulCutoff f)
        (fun t x ↦ sourceStationaryPacket X H x beta t faithfulCutoff faithfulCutoff) x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hpair hX.le
    _ ≤ X * ((216 * MAPMRTFaithfulEquation81Weld.faithfulEquation82Constant / (beta ^ 2 * X)) *
        MAPMRTProposition51Source.proposition51I X H f beta eta) :=
      mul_le_mul_of_nonneg_left henergy hX.le
    _ = _ := by
      field_simp [hX.ne', hbeta]
      <;> ring

#print axioms faithful_mediumProjectedSum_sq_le
#print axioms faithful_mediumProjectedSum_eq_packet_pairing
#print axioms faithful_equation79Integral_eq_packetSuperposition_pairing
#print axioms faithful_dualPacketKernel_integrable
#print axioms faithful_logarithmicDual_fourier_eq_packet_pairing
#print axioms faithful_physical_support_half_range
#print axioms faithful_sourceStationaryPacket_eq_withoutOuter_half_range
end
end MAPMRTFaithfulEquation79Duality
