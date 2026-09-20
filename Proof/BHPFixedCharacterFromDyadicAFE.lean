import FixedCharacterFourthMomentFromAFE
import BHPRamachandraMeanValueFromDyadicAFE

/-!
# Fixed-character separated fourth moments from the shared Ramachandra AFE

The same literal dyadic AFE object used for BHP Lemma 7 also gives the
fixed-character discrete fourth moment required by Appendix A.4.  This file
proves the deterministic translation, character-twist energy bound, and
selected-ordinate mean-square weld.
-/

namespace BHPFixedCharacterFromDyadicAFE

open scoped BigOperators
open CGLProofDAG
open MAPMRTLemma210OrthogonalityReduction
open MontgomeryVaughanFiniteReduction
open BHPAllCharacterDyadicBudget
open BHPRamachandraMeanValueFromDyadicAFE
open FixedCharacterFourthMomentFromAFE
open MAPMRTLemma211AllCharacterSource

noncomputable section

/-- Character and phase modulation that translates a block on `[-U,U]` to
the selected-ordinate mean-square interval `[0,2U]`. -/
def shiftedRamachandraCoefficient
    {q : ℕ} (b : ℕ → ℂ) (dual : Bool)
    (chi : DirichletCharacter ℂ q) (U : ℝ) (n : ℕ) : ℂ :=
  b n * (if dual then star chi else chi) n * twistedPhase n U

/-- Exact identity between the literal Ramachandra block and the standard
Dirichlet polynomial at the oriented ordinate. -/
theorem ramachandraDyadicBlock_eq_dirichletPolynomial
    (q N : ℕ) [NeZero q] (b : ℕ → ℂ) (dual : Bool)
    (chi : DirichletCharacter ℂ q) (U t : ℝ) :
    ramachandraDyadicBlock q N b dual chi t =
      dirichletPolynomial (shiftedRamachandraCoefficient b dual chi U) N
        (orientedTime dual U t) := by
  cases dual
  · change twistedFinitePolynomial q (dyadicSupport N) b chi t =
      dirichletPolynomial (shiftedRamachandraCoefficient b false chi U) N (U - t)
    unfold shiftedRamachandraCoefficient twistedFinitePolynomial twistedPhase
      dirichletPolynomial dyadicSupport
    apply Finset.sum_congr rfl
    intro n hn
    have hexp :
        Complex.exp (((-(U * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (Complex.I * (((U - t) * Real.log (n : ℝ) : ℝ) : ℂ)) =
          Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [Bool.false_eq, Bool.true_eq_false, if_false]
    have hv :
        Complex.exp (Complex.I * (((U - t : ℝ) : ℂ) *
            ((Real.log (n : ℝ) : ℝ) : ℂ))) =
          Complex.exp (Complex.I * (((U - t) * Real.log (n : ℝ) : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [hv, ← hexp]
    ring
  · change twistedFinitePolynomial q (dyadicSupport N) b (star chi) (-t) =
      dirichletPolynomial (shiftedRamachandraCoefficient b true chi U) N (t + U)
    unfold shiftedRamachandraCoefficient twistedFinitePolynomial twistedPhase
      dirichletPolynomial dyadicSupport
    apply Finset.sum_congr rfl
    intro n hn
    have hexp :
        Complex.exp (((-(U * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (Complex.I * (((t + U) * Real.log (n : ℝ) : ℝ) : ℂ)) =
          Complex.exp (((-(-t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [if_true]
    have hv :
        Complex.exp (Complex.I * (((t + U : ℝ) : ℂ) *
            ((Real.log (n : ℝ) : ℝ) : ℂ))) =
          Complex.exp (Complex.I * (((t + U) * Real.log (n : ℝ) : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [hv, ← hexp]
    ring

/-- Character values and the translating phase both have norm at most one,
so twisting never increases the dyadic coefficient energy. -/
theorem shiftedRamachandraCoefficient_energy_le
    (q : ℕ) (b : ℕ → ℂ) (dual : Bool)
    (chi : DirichletCharacter ℂ q) (U : ℝ) (N : ℕ) :
    DiscreteMeanValueSourceLeaf.coefficientEnergy
        (shiftedRamachandraCoefficient b dual chi U) N ≤
      coefficientEnergy b N := by
  unfold DiscreteMeanValueSourceLeaf.coefficientEnergy coefficientEnergy
    shiftedRamachandraCoefficient
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, norm_mul, norm_twistedPhase, mul_one]
  have hc : ‖(if dual then star chi else chi) (n : ZMod q)‖ ≤ 1 := by
    split_ifs <;> exact DirichletCharacter.norm_le_one _ _
  have hprod :
      ‖b n‖ * ‖(if dual then star chi else chi) (n : ZMod q)‖ ≤ ‖b n‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hc
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hprod

/-- The fixed-character selected mean-square cost is bounded by the same
all-character dyadic cost.  This is where the two consumers meet. -/
theorem selected_block_mass_le_of_discreteMeanSquare
    {q N : ℕ} [NeZero q] (b : ℕ → ℂ) (dual : Bool)
    (chi : DirichletCharacter ℂ q)
    {U eta C T₀ : ℝ} (W : Finset ℝ)
    (hsource : 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (S : ℝ) (N' : ℕ) (b' : ℕ → ℂ) (W' : Finset ℝ),
        T₀ ≤ S → 1 ≤ N' → OneSeparated W' →
        (∀ u ∈ W', 0 ≤ u ∧ u ≤ S) →
        (∑ u ∈ W', ‖dirichletPolynomial b' N' u‖ ^ 2) ≤
          C * Real.rpow S eta * ((N' : ℝ) + S) *
            DiscreteMeanValueSourceLeaf.coefficientEnergy b' N')
    (hU : 0 ≤ U) (hT₀ : T₀ ≤ 2 * U) (hN : 1 ≤ N)
    (hsep : OneSeparated W) (hheight : ∀ t ∈ W, |t| ≤ U) :
    (∑ t ∈ W, ‖ramachandraDyadicBlock q N b dual chi t‖ ^ 2) ≤
      C * Real.rpow (2 * U) eta * ramachandraDyadicCost q N U b := by
  let W' := orientedOrdinateSet dual W U
  let c := shiftedRamachandraCoefficient b dual chi U
  have hsep' : OneSeparated W' :=
    orientedOrdinateSet_oneSeparated dual hsep
  have hheight' : ∀ u ∈ W', 0 ≤ u ∧ u ≤ 2 * U :=
    orientedOrdinateSet_height dual hheight
  have hraw := hsource.2.2 (2 * U) N c W' hT₀ hN hsep' hheight'
  have hreindex :
      (∑ t ∈ W, ‖ramachandraDyadicBlock q N b dual chi t‖ ^ 2) =
        ∑ u ∈ W', ‖dirichletPolynomial c N u‖ ^ 2 := by
    rw [sum_orientedOrdinateSet dual (W := W) (T := U)
      (fun u => ‖dirichletPolynomial c N u‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [ramachandraDyadicBlock_eq_dirichletPolynomial]
  rw [hreindex]
  have henergy := shiftedRamachandraCoefficient_energy_le
    q b dual chi U N
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hpi : (1 : ℝ) ≤ 8 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hfactor : (N : ℝ) + 2 * U ≤
      (q : ℝ) * (2 * U) + 8 * Real.pi * (N : ℝ) := by
    have hqU : 2 * U ≤ (q : ℝ) * (2 * U) := by
      have := mul_le_mul_of_nonneg_right hq
        (show 0 ≤ 2 * U by positivity)
      simpa only [one_mul] using this
    have hNpi : (N : ℝ) ≤ 8 * Real.pi * (N : ℝ) := by
      have := mul_le_mul_of_nonneg_right hpi
        (show 0 ≤ (N : ℝ) by positivity)
      simpa only [one_mul] using this
    linarith
  have hfactor0 : 0 ≤ (N : ℝ) + 2 * U := by positivity
  have htargetFactor0 :
      0 ≤ (q : ℝ) * (2 * U) + 8 * Real.pi * (N : ℝ) := by positivity
  have hcost :
      ((N : ℝ) + 2 * U) *
          DiscreteMeanValueSourceLeaf.coefficientEnergy c N ≤
        ramachandraDyadicCost q N U b := by
    calc
      ((N : ℝ) + 2 * U) *
          DiscreteMeanValueSourceLeaf.coefficientEnergy c N ≤
          ((N : ℝ) + 2 * U) * coefficientEnergy b N :=
        mul_le_mul_of_nonneg_left henergy hfactor0
      _ ≤ ((q : ℝ) * (2 * U) + 8 * Real.pi * (N : ℝ)) *
          coefficientEnergy b N :=
        mul_le_mul_of_nonneg_right hfactor (by
          unfold coefficientEnergy
          positivity)
      _ = ramachandraDyadicCost q N U b := rfl
  have hscale : 0 ≤ C * Real.rpow (2 * U) eta := by
    exact mul_nonneg (le_of_lt hsource.1)
      (Real.rpow_nonneg (by linarith : 0 ≤ 2 * U) _)
  exact hraw.trans <| by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcost hscale

/-- Exact finite-family fixed-character consequence of one AFE witness. -/
theorem selected_fourth_mass_le_dyadicFamilyCost
    {q : ℕ} [NeZero q]
    {U x0 C₀ : ℝ} {B : ℕ}
    (data : RamachandraSquaredDyadicAFEData q U x0 C₀ B)
    (chi : DirichletCharacter ℂ q) (W : Finset ℝ)
    {eta Cmv Tmv : ℝ}
    (hmean : 0 < Cmv ∧ 2 ≤ Tmv ∧
      ∀ (S : ℝ) (N' : ℕ) (b' : ℕ → ℂ) (W' : Finset ℝ),
        Tmv ≤ S → 1 ≤ N' → OneSeparated W' →
        (∀ u ∈ W', 0 ≤ u ∧ u ≤ S) →
        (∑ u ∈ W', ‖dirichletPolynomial b' N' u‖ ^ 2) ≤
          Cmv * Real.rpow S eta * ((N' : ℝ) + S) *
            DiscreteMeanValueSourceLeaf.coefficientEnergy b' N')
    (hU : 0 ≤ U) (hTmv : Tmv ≤ 2 * U)
    (hsep : OneSeparated W) (hheight : ∀ t ∈ W, |t| ≤ U) :
    (∑ t ∈ W, criticalLineLFourth chi t) ≤
      Cmv * Real.rpow (2 * U) eta *
        (data.A * ramachandraDyadicFamilyCost q U data.N data.b) := by
  have hpoint :
      (∑ t ∈ W, criticalLineLFourth chi t) ≤
        data.A * ∑ j : Fin data.J,
          ∑ t ∈ W,
            ‖ramachandraDyadicBlock q (data.N j) (data.b j)
              (data.dual j) chi t‖ ^ 2 := by
    calc
      (∑ t ∈ W, criticalLineLFourth chi t) ≤
          ∑ t ∈ W, data.A * ramachandraDyadicFamily
            data.dual data.N data.b chi t := by
        exact Finset.sum_le_sum fun t ht => data.pointwise chi t (hheight t ht)
      _ = data.A * ∑ j : Fin data.J,
          ∑ t ∈ W,
            ‖ramachandraDyadicBlock q (data.N j) (data.b j)
              (data.dual j) chi t‖ ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        unfold ramachandraDyadicFamily
        rw [Finset.sum_comm]
  have hblocks :
      (∑ j : Fin data.J,
        ∑ t ∈ W,
          ‖ramachandraDyadicBlock q (data.N j) (data.b j)
            (data.dual j) chi t‖ ^ 2) ≤
        Cmv * Real.rpow (2 * U) eta *
          ramachandraDyadicFamilyCost q U data.N data.b := by
    calc
      _ ≤ ∑ j : Fin data.J,
          Cmv * Real.rpow (2 * U) eta *
            ramachandraDyadicCost q (data.N j) U (data.b j) := by
        exact Finset.sum_le_sum fun j hj =>
          selected_block_mass_le_of_discreteMeanSquare
            (b := data.b j) (dual := data.dual j) chi W hmean hU hTmv
            (data.block_nonempty j) hsep hheight
      _ = Cmv * Real.rpow (2 * U) eta *
          ramachandraDyadicFamilyCost q U data.N data.b := by
        unfold ramachandraDyadicFamilyCost
        rw [Finset.mul_sum]
  calc
    (∑ t ∈ W, criticalLineLFourth chi t) ≤
        data.A * ∑ j : Fin data.J,
          ∑ t ∈ W,
            ‖ramachandraDyadicBlock q (data.N j) (data.b j)
              (data.dual j) chi t‖ ^ 2 := hpoint
    _ ≤ data.A * (Cmv * Real.rpow (2 * U) eta *
          ramachandraDyadicFamilyCost q U data.N data.b) :=
      mul_le_mul_of_nonneg_left hblocks data.A_nonneg
    _ = Cmv * Real.rpow (2 * U) eta *
          (data.A * ramachandraDyadicFamilyCost q U data.N data.b) := by ring

/-- The same Ramachandra Lemmas 3--6 dyadic witness used for the
all-character BHP integral also supplies the fixed-character separated fourth
moment needed by Appendix A.4.  No second approximate functional equation is
required: the certified discrete mean square is applied blockwise, while the
source's aggregate length-energy budget is retained intact. -/
theorem nonprincipalFixedCharacterDiscreteFourthMoment_of_dyadicAFE
    (hAFE : RamachandraLemma3To6AllCharacterDyadicAFE) :
    NonprincipalFixedCharacterDiscreteFourthMoment := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / 4
  let theta : ℝ := epsilon / 4
  have heta : 0 < eta := by dsimp [eta]; linarith
  have htheta : 0 < theta := by dsimp [theta]; linarith
  have hmean : DiscreteMeanValueSourceLeaf.DiscreteDirichletMeanSquare :=
    RecenteredSampling.discreteDirichletMeanSquare_of_hilbert
      MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
  obtain ⟨Cmv, Tmv, hCmv, hTmv, hmv⟩ := hmean eta heta
  obtain ⟨C₀, hC₀, B, hsource⟩ := hAFE
  have hpoly := ZeroDensityArithmetic.polylog_absorption (B : ℝ) theta htheta
  obtain ⟨Xlog, hXlog⟩ := Filter.eventually_atTop.1 hpoly
  let C : ℝ := Cmv * C₀ * Real.rpow 2 eta
  let T₀ : ℝ := max Tmv (max 2 Xlog)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hT₀ : 2 ≤ T₀ := by
    dsimp [T₀]
    exact le_max_left 2 Xlog |>.trans (le_max_right Tmv (max 2 Xlog))
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T r _inst chi W hT _hprimitive _hnonprincipal hsep hheight
  have hTmv' : Tmv ≤ T :=
    (le_max_left Tmv (max 2 Xlog)).trans hT
  have hTtwo : 2 ≤ T :=
    (le_max_left 2 Xlog).trans
      ((le_max_right Tmv (max 2 Xlog)).trans hT)
  have hXlogT : Xlog ≤ T :=
    (le_max_right 2 Xlog).trans
      ((le_max_right Tmv (max 2 Xlog)).trans hT)
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTtwo
  have hrNat : 0 < r := NeZero.pos r
  have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrNat
  let S : ℝ := (r : ℝ) * T
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have hSone : 1 ≤ S := by
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_right hr hTpos.le]
  have hTleS : T ≤ S := by
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_right hr hTpos.le]
  have hrleS : (r : ℝ) ≤ S := by
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_left hTtwo (by positivity : 0 ≤ (r : ℝ))]
  have hXlogS : Xlog ≤ S := hXlogT.trans hTleS
  obtain ⟨data⟩ := hsource r T S hTtwo hrleS hTleS
  have hmean' : 0 < Cmv ∧ 2 ≤ Tmv ∧
      ∀ (S' : ℝ) (N' : ℕ) (b' : ℕ → ℂ) (W' : Finset ℝ),
        Tmv ≤ S' → 1 ≤ N' → OneSeparated W' →
        (∀ u ∈ W', 0 ≤ u ∧ u ≤ S') →
        (∑ u ∈ W', ‖dirichletPolynomial b' N' u‖ ^ 2) ≤
          Cmv * Real.rpow S' eta * ((N' : ℝ) + S') *
            DiscreteMeanValueSourceLeaf.coefficientEnergy b' N' :=
    ⟨hCmv, hTmv, hmv⟩
  have hraw := selected_fourth_mass_le_dyadicFamilyCost
    data chi W hmean' hTpos.le (by linarith) hsep hheight
  have hlogAbs : Real.rpow (Real.log S) (B : ℝ) ≤
      Real.rpow S theta := hXlog S hXlogS
  have hlogPow : Real.log S ^ B ≤ Real.rpow S theta := by
    rw [← Real.rpow_natCast]
    exact hlogAbs
  have hsourcePower :
      C₀ * (r : ℝ) * T * Real.log S ^ B ≤
        C₀ * Real.rpow S (1 + theta) := by
    have hone : Real.rpow S (1 : ℝ) = S := Real.rpow_one S
    calc
      C₀ * (r : ℝ) * T * Real.log S ^ B =
          C₀ * S * Real.log S ^ B := by dsimp [S]; ring
      _ ≤ C₀ * S * Real.rpow S theta :=
        mul_le_mul_of_nonneg_left hlogPow
          (mul_nonneg hC₀.le hSpos.le)
      _ = C₀ * Real.rpow S (1 + theta) := by
        calc
          C₀ * S * Real.rpow S theta =
              C₀ * (Real.rpow S 1 * Real.rpow S theta) := by
                rw [hone]
                ring
          _ = C₀ * Real.rpow S (1 + theta) :=
            congrArg (fun y : ℝ => C₀ * y)
              (Real.rpow_add hSpos 1 theta).symm
  have haggregate :
      data.A * ramachandraDyadicFamilyCost r T data.N data.b ≤
        C₀ * Real.rpow S (1 + theta) :=
    data.aggregate_budget.trans hsourcePower
  have htwoTle : 2 * T ≤ 2 * S := by linarith
  have hrpowTwoT : Real.rpow (2 * T) eta ≤ Real.rpow (2 * S) eta :=
    Real.rpow_le_rpow (by positivity) htwoTle heta.le
  have hscale0 : 0 ≤ Cmv * Real.rpow (2 * T) eta :=
    mul_nonneg hCmv.le (Real.rpow_nonneg (by positivity) _)
  have htarget0 : 0 ≤ C₀ * Real.rpow S (1 + theta) :=
    mul_nonneg hC₀.le (Real.rpow_nonneg hSpos.le _)
  have hcombined :
      Cmv * Real.rpow (2 * T) eta *
          (data.A * ramachandraDyadicFamilyCost r T data.N data.b) ≤
        Cmv * Real.rpow (2 * S) eta *
          (C₀ * Real.rpow S (1 + theta)) := by
    calc
      Cmv * Real.rpow (2 * T) eta *
          (data.A * ramachandraDyadicFamilyCost r T data.N data.b) ≤
          Cmv * Real.rpow (2 * T) eta *
            (C₀ * Real.rpow S (1 + theta)) :=
        mul_le_mul_of_nonneg_left haggregate hscale0
      _ ≤ Cmv * Real.rpow (2 * S) eta *
            (C₀ * Real.rpow S (1 + theta)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpowTwoT hCmv.le) htarget0
  have hmulTwo : Real.rpow (2 * S) eta =
      Real.rpow 2 eta * Real.rpow S eta :=
    Real.mul_rpow (by norm_num) hSpos.le
  have hpowCombine : Real.rpow S eta * Real.rpow S (1 + theta) =
      Real.rpow S (1 + eta + theta) := by
    calc
      Real.rpow S eta * Real.rpow S (1 + theta) =
          Real.rpow S (eta + (1 + theta)) :=
        (Real.rpow_add hSpos eta (1 + theta)).symm
      _ = Real.rpow S (1 + eta + theta) := by congr 1 <;> ring
  have hexponent : 1 + eta + theta ≤ 1 + epsilon := by
    dsimp [eta, theta]
    linarith
  have hpowMono : Real.rpow S (1 + eta + theta) ≤
      Real.rpow S (1 + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hSone hexponent
  calc
    (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) =
        ∑ t ∈ W, criticalLineLFourth chi t := by
      rfl
    _ ≤ Cmv * Real.rpow (2 * T) eta *
          (data.A * ramachandraDyadicFamilyCost r T data.N data.b) := hraw
    _ ≤ Cmv * Real.rpow (2 * S) eta *
          (C₀ * Real.rpow S (1 + theta)) := hcombined
    _ = C * Real.rpow S (1 + eta + theta) := by
      rw [hmulTwo]
      calc
        Cmv * (Real.rpow 2 eta * Real.rpow S eta) *
            (C₀ * Real.rpow S (1 + theta)) =
            C * (Real.rpow S eta * Real.rpow S (1 + theta)) := by
              dsimp [C]
              ring
        _ = C * Real.rpow S (1 + eta + theta) := by rw [hpowCombine]
    _ ≤ C * Real.rpow S (1 + epsilon) :=
      mul_le_mul_of_nonneg_left hpowMono hC.le
    _ = C * Real.rpow ((r : ℝ) * T) (1 + epsilon) := by rfl

/-- One source theorem, two load-bearing consumers: Ramachandra's literal
dyadic Lemmas 3--6 budget supplies both BHP Lemma 7 for the MRT/far branch and
the fixed-character fourth moment for Appendix A.4. -/
theorem shared_bhp_and_fixedCharacter_consequences_of_dyadicAFE
    (hAFE : RamachandraLemma3To6AllCharacterDyadicAFE) :
    BHPLemma7RamachandraAllCharacterMeanValue ∧
      NonprincipalFixedCharacterDiscreteFourthMoment :=
  ⟨bhpLemma7RamachandraAllCharacterMeanValue_of_dyadicAFE hAFE,
    nonprincipalFixedCharacterDiscreteFourthMoment_of_dyadicAFE hAFE⟩

end
end BHPFixedCharacterFromDyadicAFE

#print axioms BHPFixedCharacterFromDyadicAFE.ramachandraDyadicBlock_eq_dirichletPolynomial
#print axioms BHPFixedCharacterFromDyadicAFE.shiftedRamachandraCoefficient_energy_le
#print axioms BHPFixedCharacterFromDyadicAFE.selected_block_mass_le_of_discreteMeanSquare
#print axioms BHPFixedCharacterFromDyadicAFE.selected_fourth_mass_le_dyadicFamilyCost
#print axioms BHPFixedCharacterFromDyadicAFE.nonprincipalFixedCharacterDiscreteFourthMoment_of_dyadicAFE
#print axioms BHPFixedCharacterFromDyadicAFE.shared_bhp_and_fixedCharacter_consequences_of_dyadicAFE
