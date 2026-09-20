import JutilaGappedCollarSourceAdapter
import PostA5CrowdingDeterministic
import PrincipalZetaCompactCrowding

/-!
# Finite occupied-box aggregation for the live Jutila collar

This module removes the finite source-box aggregation from the remaining
analytic p.53 leaf.  The regular collar divisor is thinned into one parity
class of occupied unit ordinate boxes.  Appendix A.5 bounds the complete
analytic multiplicity in every occupied box, and the selected representatives
are genuinely one-separated.

Unit boxes are a legal strengthening of Jutila's `1 / log D` boxes: their
parity representatives are farther apart, while the A.5 logarithmic cap is
uniform.  No density or detector estimate is asserted here.
-/

namespace MAPJutilaGappedCollarFiniteAggregation

open scoped BigOperators
open DirichletZeros MAPLocalZeroWindow MAPPaperWindowVKBypass
open MAPMellinDetectorLeaf MAPAPZeroDensityCert
open PostA5CrowdingDeterministic
open MAPJutilaGappedCollarSourceAdapter

noncomputable section

/-- The literal regular collar support at left edge `sigma`. -/
def regularCollarSupport {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma T : ℝ) : Finset ℂ :=
  (zeroSupport chi sigma T).filter fun rho =>
    4 / 5 < rho.re ∧
      ¬ (chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0)

/-- Uniform natural A.5 cap for both nonprincipal primitive characters and
the conductor-one zeta function. -/
def regularCollarNatCap {q : ℕ} [NeZero q] (T : ℝ) : ℕ :=
  ⌈1683 * Real.log ((q : ℝ) * (T + 5))⌉₊

/-- A zero in the full rectangle whose real part is beyond `sigma` belongs
to the left-edge support.  Exposed for source adapters that must translate
between the manuscript's full-rectangle and selected-system conventions. -/
theorem mem_zeroSupport_sigma_of_mem_full
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T : ℝ} {rho : ℂ}
    (hfull : rho ∈ zeroSupport chi 0 T) (hre : sigma ≤ rho.re) :
    rho ∈ zeroSupport chi sigma T := by
  have hfullRect : rho ∈ zeroRectangle 0 T :=
    (zeroDivisor chi 0 T).supportWithinDomain
      ((zeroSupport_mem_iff chi 0 T rho).mp hfull)
  have hinnerRect : rho ∈ zeroRectangle sigma T := by
    rw [zeroRectangle, Complex.mem_reProdIm] at hfullRect ⊢
    exact ⟨⟨hre, hfullRect.1.2⟩, hfullRect.2⟩
  apply (mem_zeroSupport_iff_eq_zero chi sigma T hinnerRect).mpr
  exact regularizedLFunction_eq_zero_of_mem_zeroSupport chi 0 T hfull

/-- The full-rectangle formulation used by the MAP mass and the left-edge
formulation used by A.5 have exactly the same multiplicity-weighted content. -/
theorem primitiveRegularCumulativeCount_eq_regularCollarSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T : ℝ} (hsigma : 0 ≤ sigma) :
    primitiveRegularCumulativeCount chi sigma T =
      ∑ rho ∈ regularCollarSupport chi sigma T,
        zeroMultiplicity chi sigma T rho := by
  classical
  let Sfull := (zeroSupport chi 0 T).filter fun rho =>
    (4 / 5 < rho.re ∧
      ¬ (chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0)) ∧
    sigma ≤ rho.re
  let Sinner := regularCollarSupport chi sigma T
  have hsets : Sfull = Sinner := by
    ext rho
    simp only [Sfull, Sinner, regularCollarSupport, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨mem_zeroSupport_sigma_of_mem_full chi h.1 h.2.2,
        h.2.1⟩
    · intro h
      have houter := zeroSupport_mono chi hsigma le_rfl h.1
      have hrect := (zeroDivisor chi sigma T).supportWithinDomain
        ((zeroSupport_mem_iff chi sigma T rho).mp h.1)
      exact ⟨houter, h.2, (Complex.mem_reProdIm.mp hrect).1.1⟩
  unfold primitiveRegularCumulativeCount
  change ∑ rho ∈ Sfull, zeroMultiplicity chi 0 T rho = _
  rw [hsets]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hinner : rho ∈ zeroSupport chi sigma T :=
    (Finset.mem_filter.mp hrho).1
  have houter : rho ∈ zeroSupport chi 0 T :=
    zeroSupport_mono chi hsigma le_rfl hinner
  exact zeroMultiplicity_eq_of_mem_rectangles chi
    ((zeroDivisor chi 0 T).supportWithinDomain
      ((zeroSupport_mem_iff chi 0 T rho).mp houter))
    ((zeroDivisor chi sigma T).supportWithinDomain
      ((zeroSupport_mem_iff chi sigma T rho).mp hinner))

private theorem occupied_floorBin_weight_cap_nonprincipal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma T : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 1 ≤ T)
    {n : ℤ} (hn : n ∈ occupiedFloorBins (regularCollarSupport chi sigma T)) :
    ∑ rho ∈ regularCollarSupport chi sigma T with Int.floor rho.im = n,
        zeroMultiplicity chi sigma T rho ≤ regularCollarNatCap (q := q) T := by
  classical
  let S := regularCollarSupport chi sigma T
  obtain ⟨rho0, hrho0, hfloor0⟩ := Finset.mem_image.mp hn
  have hrho0Support : rho0 ∈ zeroSupport chi sigma T :=
    (Finset.mem_filter.mp hrho0).1
  have hrect := (zeroDivisor chi sigma T).supportWithinDomain
    ((zeroSupport_mem_iff chi sigma T rho0).mp hrho0Support)
  have him : |rho0.im| ≤ T :=
    abs_le.mpr (Complex.mem_reProdIm.mp hrect).2
  have hfloorAbs := abs_floor_le_abs_add_one rho0.im
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hscalePos : 0 < arithmeticScale q (n : ℝ) := by
    unfold arithmeticScale
    positivity
  have hscale : arithmeticScale q (n : ℝ) ≤ (q : ℝ) * (T + 5) := by
    rw [← hfloor0]
    unfold arithmeticScale
    apply mul_le_mul_of_nonneg_left _ hqpos.le
    linarith
  have hlogScale := Real.log_le_log hscalePos hscale
  have hlocal := globalUnitWindowCount_le_log chi hchi
    (T := T) (t := (n : ℝ)) hsigma
  have hfiberSub :
      S.filter (fun rho => Int.floor rho.im = n) ⊆
        globalUnitWindowSupport chi sigma T n := by
    intro rho hrho
    have hrhoS := (Finset.mem_filter.mp hrho).1
    have hfloor := (Finset.mem_filter.mp hrho).2
    rw [globalUnitWindowSupport, Finset.mem_filter]
    refine ⟨(Finset.mem_filter.mp hrhoS).1, ?_, ?_⟩
    · have := Int.floor_le rho.im
      exact_mod_cast (hfloor ▸ this)
    · have hlt := Int.lt_floor_add_one rho.im
      rw [hfloor] at hlt
      exact hlt.le
  have hsumReal :
      ((∑ rho ∈ S with Int.floor rho.im = n,
          zeroMultiplicity chi sigma T rho : ℕ) : ℝ) ≤
        1683 * Real.log ((q : ℝ) * (T + 5)) := by
    push_cast
    calc
      ∑ rho ∈ S.filter (fun rho => Int.floor rho.im = n),
          (zeroMultiplicity chi sigma T rho : ℝ) ≤
        ∑ rho ∈ globalUnitWindowSupport chi sigma T n,
          (zeroMultiplicity chi sigma T rho : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hfiberSub
              (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ 153 * Real.log (arithmeticScale q (n : ℝ)) := hlocal
      _ ≤ 153 * Real.log ((q : ℝ) * (T + 5)) := by
        gcongr
      _ ≤ 1683 * Real.log ((q : ℝ) * (T + 5)) := by
        have hqone : (1 : ℝ) ≤ q := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
        have hbase : 1 ≤ (q : ℝ) * (T + 5) := by nlinarith
        have hlog0 := Real.log_nonneg hbase
        nlinarith
  exact_mod_cast hsumReal.trans (Nat.le_ceil _)

private theorem occupied_floorBin_weight_cap_principal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi = 1)
    {sigma T : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 1 ≤ T)
    {n : ℤ} (hn : n ∈ occupiedFloorBins (regularCollarSupport chi sigma T)) :
    ∑ rho ∈ regularCollarSupport chi sigma T with Int.floor rho.im = n,
        zeroMultiplicity chi sigma T rho ≤ regularCollarNatCap (q := q) T := by
  subst chi
  have hq : q = 1 := by
    rw [DirichletCharacter.isPrimitive_def,
      DirichletCharacter.conductor_one] at hprim
    exact hprim.symm
  subst q
  let Z := regularCollarSupport (1 : DirichletCharacter ℂ 1) sigma T
  have hnFull : n ∈ occupiedFloorBins
      (zeroSupport (1 : DirichletCharacter ℂ 1) sigma T) := by
    obtain ⟨rho, hrho, hfloor⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨rho, (Finset.mem_filter.mp hrho).1, hfloor⟩
  have hcap := MAPPrincipalZetaCompactCrowding.principal_floorBin_weight_cap
    (by linarith : 0 ≤ sigma) n hnFull
  have hsub : Z.filter (fun rho => Int.floor rho.im = n) ⊆
      (zeroSupport (1 : DirichletCharacter ℂ 1) sigma T).filter
        (fun rho => Int.floor rho.im = n) := by
    intro rho hrho
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hrho).1).1,
        (Finset.mem_filter.mp hrho).2⟩
  have hsum :
      ∑ rho ∈ Z with Int.floor rho.im = n,
          zeroMultiplicity (1 : DirichletCharacter ℂ 1) sigma T rho ≤
        MAPLocalZeroWindow.closedUnitWindowCount
          (1 : DirichletCharacter ℂ 1) 0 n := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => Nat.zero_le _)).trans hcap
  have hlog := MAPPrincipalZetaFullStrip.principal_fullStrip_count_le_log n
  have hrectWitness : ∃ rho ∈ Z, Int.floor rho.im = n := by
    obtain ⟨rho, hrho, hfloor⟩ := Finset.mem_image.mp hn
    exact ⟨rho, hrho, hfloor⟩
  obtain ⟨rho0, hrho0, hfloor0⟩ := hrectWitness
  have hrect := (zeroDivisor (1 : DirichletCharacter ℂ 1) sigma T).supportWithinDomain
    ((zeroSupport_mem_iff (1 : DirichletCharacter ℂ 1) sigma T rho0).mp
      (Finset.mem_filter.mp hrho0).1)
  have him : |rho0.im| ≤ T := abs_le.mpr (Complex.mem_reProdIm.mp hrect).2
  have hfloorAbs := abs_floor_le_abs_add_one rho0.im
  have hscale : arithmeticScale 1 (n : ℝ) ≤ T + 5 := by
    rw [← hfloor0]
    simp only [arithmeticScale, Nat.cast_one, one_mul]
    linarith
  have hscalePos : 0 < arithmeticScale 1 (n : ℝ) := by
    unfold arithmeticScale
    positivity
  have hlogScale := Real.log_le_log hscalePos hscale
  have hreal :
      ((∑ rho ∈ Z with Int.floor rho.im = n,
          zeroMultiplicity (1 : DirichletCharacter ℂ 1) sigma T rho : ℕ) : ℝ) ≤
        1683 * Real.log (T + 5) := by
    have hsumCast :
        ((∑ rho ∈ Z with Int.floor rho.im = n,
          zeroMultiplicity (1 : DirichletCharacter ℂ 1) sigma T rho : ℕ) : ℝ) ≤
          (MAPLocalZeroWindow.closedUnitWindowCount
            (1 : DirichletCharacter ℂ 1) 0 n : ℝ) := by
      exact_mod_cast hsum
    exact hsumCast.trans <| hlog.trans
      (mul_le_mul_of_nonneg_left hlogScale (by norm_num))
  simpa [Z, regularCollarNatCap] using (show
    ∑ rho ∈ Z with Int.floor rho.im = n,
      zeroMultiplicity (1 : DirichletCharacter ℂ 1) sigma T rho ≤
        ⌈1683 * Real.log (T + 5)⌉₊ by
      exact_mod_cast hreal.trans (Nat.le_ceil _))

/-- Every occupied floor bin of the regular collar has the uniform A.5 cap,
with the conductor-one principal case supplied by the certified zeta count. -/
theorem occupied_floorBin_weight_cap
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) {sigma T : ℝ}
    (hsigma : 1 / 2 ≤ sigma) (hT : 1 ≤ T)
    {n : ℤ} (hn : n ∈ occupiedFloorBins (regularCollarSupport chi sigma T)) :
    ∑ rho ∈ regularCollarSupport chi sigma T with Int.floor rho.im = n,
        zeroMultiplicity chi sigma T rho ≤ regularCollarNatCap (q := q) T := by
  by_cases hchi : chi = 1
  · exact occupied_floorBin_weight_cap_principal chi hprim hchi hsigma hT hn
  · exact occupied_floorBin_weight_cap_nonprincipal chi hchi hsigma hT hn

/-- Exact deterministic source reduction: one separated selected system
controls the entire regular multiplicity-weighted collar divisor. -/
theorem exists_selected_regularCollar
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) {sigma T : ℝ}
    (hsigma : 1 / 2 ≤ sigma) (hT : 1 ≤ T) :
    ∃ W : Finset ℂ,
      W ⊆ regularCollarSupport chi sigma T ∧
      CGLProofDAG.OneSeparated (W.image Complex.im) ∧
      (W.image Complex.im).card = W.card ∧
      primitiveRegularCumulativeCount chi sigma T ≤
        2 * regularCollarNatCap (q := q) T * W.card := by
  have hextract := exists_oneSeparated_ordinates_of_floorBin_weight_cap
    (regularCollarSupport chi sigma T)
    (zeroMultiplicity chi sigma T)
    (regularCollarNatCap (q := q) T)
    (fun n hn => occupied_floorBin_weight_cap chi hprim hsigma hT hn)
  obtain ⟨W, hW, hsep, hcard, hcount⟩ := hextract
  refine ⟨W, hW, hsep, hcard, ?_⟩
  rw [primitiveRegularCumulativeCount_eq_regularCollarSum chi
    (by linarith : 0 ≤ sigma)]
  exact hcount

/-- The natural A.5 cap is at most a fixed multiple of the live scale
logarithm.  The ceiling costs one extra copy of `log(qT)`. -/
theorem regularCollarNatCap_cast_le_log
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 1 ≤ T)
    (hD : 6 ≤ (q : ℝ) * T) :
    (regularCollarNatCap (q := q) T : ℝ) ≤
      3367 * Real.log ((q : ℝ) * T) := by
  let D : ℝ := (q : ℝ) * T
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hscale0 : 0 ≤ 1683 * Real.log ((q : ℝ) * (T + 5)) := by
    have hqone : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hbase : 1 ≤ (q : ℝ) * (T + 5) := by nlinarith
    exact mul_nonneg (by norm_num) (Real.log_nonneg hbase)
  have hceil := Nat.ceil_lt_add_one hscale0
  have hqshift : (q : ℝ) * (T + 5) ≤ 6 * D := by
    dsimp [D]
    nlinarith
  have hDsq : 6 * D ≤ D ^ 2 := by
    dsimp [D] at hD ⊢
    nlinarith
  have hargPos : 0 < (q : ℝ) * (T + 5) :=
    mul_pos hqpos (by linarith)
  have hlogScale : Real.log ((q : ℝ) * (T + 5)) ≤
      Real.log (D ^ 2) :=
    Real.log_le_log hargPos (hqshift.trans hDsq)
  have hD0 : 0 < D := by dsimp [D]; nlinarith
  have hlogScale' : Real.log ((q : ℝ) * (T + 5)) ≤
      2 * Real.log D := by
    simpa [Real.log_pow] using hlogScale
  have hexpD : Real.exp 1 ≤ D := by
    exact (calc
      Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < 6 := by norm_num
      _ ≤ D := hD).le
  have hlogD : 1 ≤ Real.log D := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hexpD
  change (⌈1683 * Real.log ((q : ℝ) * (T + 5))⌉₊ : ℝ) ≤ _
  calc
    (⌈1683 * Real.log ((q : ℝ) * (T + 5))⌉₊ : ℝ) ≤
        1683 * Real.log ((q : ℝ) * (T + 5)) + 1 := hceil.le
    _ ≤ 3366 * Real.log D + 1 := by nlinarith
    _ ≤ 3367 * Real.log D := by nlinarith
    _ = 3367 * Real.log ((q : ℝ) * T) := rfl

end

end MAPJutilaGappedCollarFiniteAggregation

#print axioms MAPJutilaGappedCollarFiniteAggregation.primitiveRegularCumulativeCount_eq_regularCollarSum
#print axioms MAPJutilaGappedCollarFiniteAggregation.occupied_floorBin_weight_cap
#print axioms MAPJutilaGappedCollarFiniteAggregation.exists_selected_regularCollar
