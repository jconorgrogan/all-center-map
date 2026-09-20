import JutilaCollarSourceParameters
import JutilaP53SourceScaleEnvelopes
import JutilaTotientLogBound

/-!
# Literal Jutila residue-budget normalization

The floor-defined source parameters are retained through SourceGeometry.
The two logarithms in the reciprocal totient estimate are canceled by the
actual lower bound for log R. The residue harmonic factor and its exact
integer exponential-mass constant remain explicit in the final constant.
-/
namespace MAPJutilaSourceFVBudget
open Real Filter
open MAPJutilaCollarSourceParameters MAPJutilaLemma6GenericTailAbsorption
open MAPJutilaP53SourceScaleEnvelopes MAPJutilaTotientLogBound
open MAPJutilaOneSeparatedExponentialPacking
open scoped BigOperators
noncomputable section

def residueLogConstant : ℝ := 72+48*Real.exp 1*integerExponentialMass

def totientLogConstant : ℝ := 1+(Real.log 2)⁻¹

def sourceFVConstant (δ : ℝ) : ℝ :=
  20*3^4*residueLogConstant*(64*totientLogConstant/δ)^2

theorem integerExponentialMass_nonneg : 0 ≤ integerExponentialMass := by
  unfold integerExponentialMass
  exact tsum_nonneg (fun k => (Real.exp_pos _).le)

theorem residueLogConstant_pos : 0 < residueLogConstant := by
  have h := integerExponentialMass_nonneg
  unfold residueLogConstant
  positivity

theorem totientLogConstant_pos : 0 < totientLogConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold totientLogConstant
  positivity

theorem sourceFVConstant_pos {δ : ℝ} (hδ : 0 < δ) : 0 < sourceFVConstant δ := by
  have hF := residueLogConstant_pos
  have hC := totientLogConstant_pos
  unfold sourceFVConstant
  positivity

/-- Exact signed residue budget bounded using its actual harmonic factor
and source logarithms; no absolute-coefficient substitute is introduced. -/
theorem sourceSharpResidueBudget_le_log_sq {δ D : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlogD : 1 ≤ Real.log D)
    (hgeo : SourceGeometry δ D) :
    sourceSharpResidueBudget (sourceR δ D) δ (sourceZ1 δ D)
      (lemmaSixDirectCutoff δ D : ℝ) ≤ residueLogConstant*(1+Real.log D)^2 := by
  let x : ℝ := lemmaSixDirectCutoff δ D
  let L := 1+Real.log D
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast hgeo.x_one
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogz0 : 0 ≤ Real.log (sourceZ1 δ D) := (Real.log_pos hgeo.z1_one).le
  have hF0 := residueLogConstant_pos.le
  have hM0 := integerExponentialMass_nonneg
  have hH0 : 0 ≤ (harmonic (sourceR δ D) : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  have hfirst : (1+δ)*Real.log x-(1-δ)*Real.log (sourceZ1 δ D) ≤ 6*Real.log D := by
    have hneg : 0 ≤ (1-δ)*Real.log (sourceZ1 δ D) :=
      mul_nonneg (by linarith) hlogz0
    have hxup : Real.log x ≤ 3*Real.log D := hgeo.logx_upper
    nlinarith
  have hfactor : 12*((1+δ)*Real.log x-(1-δ)*Real.log (sourceZ1 δ D))+
      48*Real.exp 1*integerExponentialMass ≤ residueLogConstant*L := by
    have hbase : 0 ≤ 48*Real.exp 1*integerExponentialMass := by positivity
    dsimp [residueLogConstant,L]
    nlinarith
  unfold sourceSharpResidueBudget
  calc
    _ ≤ (residueLogConstant*L)*L :=
      mul_le_mul hfactor hgeo.harmonic_upper hH0 (mul_nonneg hF0 (by dsimp [L]; linarith))
    _ = _ := by dsimp [L]; ring

/-- The literal detector threshold V=(phi(q)/q)log(R)/16 has uniformly
bounded reciprocal square at the source parameters. -/
theorem sourceV_inv_sq_le {δ D : ℝ} (hδ : 0 < δ) (hlogD : 1 ≤ Real.log D)
    (hgeo : SourceGeometry δ D) (q : ℕ) (hq : 0 < q) (hqD : (q:ℝ) ≤ D) :
    let V := (1/16:ℝ)*((Nat.totient q:ℝ)/(q:ℝ))*Real.log (sourceR δ D:ℝ)
    (V⁻¹)^2 ≤ (64*totientLogConstant/δ)^2 := by
  dsimp only
  let r : ℝ := (Nat.totient q:ℝ)/(q:ℝ)
  let lR := Real.log (sourceR δ D:ℝ)
  have hr : 0 < r := by
    have hqp : (0:ℝ)<q := by exact_mod_cast hq
    have hφp : (0:ℝ)<Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
    dsimp [r]; positivity
  have hlR : 0 < lR := by
    have h := hgeo.logR_lower
    have hδlog : 0 < (δ/2)*Real.log D := mul_pos (by linarith) (by linarith)
    exact hδlog.trans_le h
  have htot := inverse_totient_ratio_sq_le_logScale q hq hqD
  change (r⁻¹)^2 ≤ totientLogConstant^2*(1+Real.log D)^2 at htot
  have heq : (((1/16:ℝ)*r*lR)⁻¹)^2 = 256*(r⁻¹)^2/lR^2 := by
    field_simp
    ring
  change (((1/16:ℝ)*r*lR)⁻¹)^2 ≤ _
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos hlR)).mpr
  have hL : (1+Real.log D)^2 ≤ 4*(Real.log D)^2 := by nlinarith
  have hlog : ((δ/2)*Real.log D)^2 ≤ lR^2 :=
    pow_le_pow_left₀ (by positivity) hgeo.logR_lower 2
  calc
    256*(r⁻¹)^2 ≤ 256*(totientLogConstant^2*(1+Real.log D)^2) :=
      mul_le_mul_of_nonneg_left htot (by norm_num)
    _ ≤ 256*(totientLogConstant^2*(4*(Real.log D)^2)) := by gcongr
    _ = (64*totientLogConstant/δ)^2*((δ/2)*Real.log D)^2 := by
      field_simp
      ring
    _ ≤ (64*totientLogConstant/δ)^2*lR^2 :=
      mul_le_mul_of_nonneg_left hlog (sq_nonneg _)

/-- Scalar normalization with the exact Q, signed F and threshold V.
The loss is six logarithmic powers, with every numerical source constant
visible in sourceFVConstant. -/
theorem sourceFVBudget_at_geometry {δ D sigma : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlogD : 1 ≤ Real.log D)
    (hgeo : SourceGeometry δ D) (q : ℕ) (hq : 0 < q) (hqD : (q:ℝ) ≤ D) :
    let x := lemmaSixDirectCutoff δ D
    let R := sourceR δ D
    let Q := 10*Real.rpow (x:ℝ) (2-2*sigma)*(1+Real.log (x:ℝ))^4
    let F := sourceSharpResidueBudget R δ (sourceZ1 δ D) (x:ℝ)
    let V := (1/16:ℝ)*((Nat.totient q:ℝ)/(q:ℝ))*Real.log (R:ℝ)
    2*Q*F/V^2 ≤ sourceFVConstant δ*Real.rpow (x:ℝ) (2-2*sigma)*(1+Real.log D)^6 := by
  dsimp only
  let x : ℝ := lemmaSixDirectCutoff δ D
  let L := 1+Real.log D
  let V := (1/16:ℝ)*((Nat.totient q:ℝ)/(q:ℝ))*Real.log (sourceR δ D:ℝ)
  let F := sourceSharpResidueBudget (sourceR δ D) δ (sourceZ1 δ D) x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast hgeo.x_one
  have hx0 : 0 ≤ x := by linarith
  have hpow0 : 0 ≤ Real.rpow x (2-2*sigma) := Real.rpow_nonneg hx0 _
  have hlogx0 : 0 ≤ 1+Real.log x := by linarith [Real.log_nonneg hx1]
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hlogx : 1+Real.log x ≤ 3*L := by
    have h := hgeo.logx_upper
    dsimp [L]
    linarith
  have hF := sourceSharpResidueBudget_le_log_sq hδ.le hδ1 hlogD hgeo
  have hV := sourceV_inv_sq_le hδ hlogD hgeo q hq hqD
  have hC0 := residueLogConstant_pos.le
  change (V⁻¹)^2 ≤ (64*totientLogConstant/δ)^2 at hV
  change F ≤ residueLogConstant*L^2 at hF
  change 2*(10*Real.rpow x (2-2*sigma)*(1+Real.log x)^4)*F/V^2 ≤ _
  rw [div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ 2*(10*Real.rpow x (2-2*sigma)*(1+Real.log x)^4)*
        (residueLogConstant*L^2)*(V⁻¹)^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hF (by positivity)) (sq_nonneg _)
    _ ≤ 2*(10*Real.rpow x (2-2*sigma)*(3*L)^4)*
        (residueLogConstant*L^2)*(64*totientLogConstant/δ)^2 := by
      gcongr
    _ = _ := by dsimp [sourceFVConstant,L]; ring

/-- Uniform eventual source budget at every positive modulus q≤D. The
floor-defined R and x are unchanged, and the statement is independent of
zeros or any desired density conclusion. -/
theorem exists_eventually_sourceFVBudget {δ : ℝ}
    (hlo : 1/560 ≤ δ) (hhi : δ ≤ 1/280) :
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∀ᶠ D : ℝ in atTop,
      ∀ q : ℕ, 0 < q → (q:ℝ) ≤ D → ∀ sigma : ℝ, sigma ≤ 1 →
      let x := lemmaSixDirectCutoff δ D
      let R := sourceR δ D
      let Q := 10*Real.rpow (x:ℝ) (2-2*sigma)*(1+Real.log (x:ℝ))^4
      let F := sourceSharpResidueBudget R δ (sourceZ1 δ D) (x:ℝ)
      let V := (1/16:ℝ)*((Nat.totient q:ℝ)/(q:ℝ))*Real.log (R:ℝ)
      2*Q*F/V^2 ≤ Cδ*Real.rpow (x:ℝ) (2-2*sigma)*(1+Real.log D)^6 := by
  have hδ : 0<δ := by linarith
  refine ⟨sourceFVConstant δ,sourceFVConstant_pos hδ,?_⟩
  filter_upwards [eventually_sourceGeometry hlo hhi,eventually_ge_atTop (Real.exp 1)] with D hgeo hD
  intro q hq hqD sigma hsigma
  have hlogD : 1 ≤ Real.log D := by
    have h := Real.log_le_log (Real.exp_pos 1) hD
    simpa using h
  exact sourceFVBudget_at_geometry hδ (by linarith) hlogD hgeo q hq hqD

end
end MAPJutilaSourceFVBudget
#print axioms MAPJutilaSourceFVBudget.sourceFVBudget_at_geometry
#print axioms MAPJutilaSourceFVBudget.exists_eventually_sourceFVBudget
