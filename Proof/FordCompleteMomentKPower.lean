import FordCompleteMomentBridge
import FordKPointEnergy
import FordTypeCenteredDifference

open scoped BigOperators
open FordBoundaryCountGeometry
open MAPFordCompleteSystemMoment
open MAPFordP16SourceCountBridge MAPFordP16FiniteFourierBridge
open MAPFordLemma32LiteralContract
open FordKPointEnergy
open MAPFordType MAPFordP16Source35Triangular

noncomputable section
namespace FordCompleteMomentKPower

def powerFamily {k : ℕ} : Fin k → Polynomial ℤ :=
  fun j => Polynomial.X ^ (j.val + 1)

def splitPowerWord {s k P : ℕ}
    (u : FordKPointEnergy.PowerWord (s := s + k) (Q := P)) :
    (FordKPointEnergy.PowerWord (s := s) (Q := P)) ×
      (Fin k → FordKPointEnergy.SourcePoint (P := P)) :=
  (fun i => u (Fin.castAdd k i), fun j => u (Fin.natAdd s j))

def joinPowerWord {s k P : ℕ}
    (x : FordKPointEnergy.PowerWord (s := s) (Q := P))
    (z : Fin k → FordKPointEnergy.SourcePoint (P := P)) :
    FordKPointEnergy.PowerWord (s := s + k) (Q := P) :=
  fun i => Fin.addCases (fun j => x j) (fun j => z j) i

def splitJoinEquiv {s k P : ℕ} :
    FordKPointEnergy.PowerWord (s := s + k) (Q := P) ≃
      (FordKPointEnergy.PowerWord (s := s) (Q := P)) ×
        (Fin k → FordKPointEnergy.SourcePoint (P := P)) :=
  { toFun := splitPowerWord
    invFun := fun x => joinPowerWord x.1 x.2
    left_inv := by
      intro u
      funext i
      refine Fin.addCases ?_ ?_ i <;> intro j
      · simp [splitPowerWord, joinPowerWord]
      · simp [splitPowerWord, joinPowerWord]
    right_inv := by
      intro x
      apply Prod.ext
      · funext i
        simp [splitPowerWord, joinPowerWord]
      · funext j
        simp [splitPowerWord, joinPowerWord] }

lemma baseFreq_split
    {s k P : ℕ} (u : FordKPointEnergy.PowerWord (s := s + k) (Q := P))
    (j : Fin k) :
    FordKPointEnergy.baseFreq (q := 1) u j =
      (∑ i : Fin s, ((splitPowerWord u).1 i).1.val ^ (j.val + 1) : ℤ) +
        (∑ i : Fin k, (((splitPowerWord u).2 i).1.val : ℤ) ^ (j.val + 1)) := by
  simp only [FordKPointEnergy.baseFreq, fordQFrequencyAt,
    fordQScalarFrequency]
  rw [Fin.sum_univ_add]
  simp [splitPowerWord]

def baseZeroToKPoint {s k P : ℕ} :
    BaseZero (FordKPointEnergy.baseFreq (s := s + k) (k := k) (Q := P) (q := 1)) ≃
      KPoint s k P P (powerFamily (k := k)) 1 := by
  let toFun : BaseZero
      (FordKPointEnergy.baseFreq (s := s + k) (k := k) (Q := P) (q := 1)) →
      KPoint s k P P (powerFamily (k := k)) 1 := fun r => by
    let xy := splitPowerWord r.1.1
    let zw := splitPowerWord r.1.2
    refine ⟨(fun i => (xy.2 i).1), (fun i => (zw.2 i).1),
      (fun i => (xy.1 i).1), (fun i => (zw.1 i).1),
      (fun i => (xy.2 i).2), (fun i => (zw.2 i).2),
      (fun i => (xy.1 i).2), (fun i => (zw.1 i).2), ?_⟩
    intro j
    have hr := congrFun r.2 j
    have hsplitL := baseFreq_split r.1.1 j
    have hsplitR := baseFreq_split r.1.2 j
    simp only [powerFamily, fordSourceFrequencyAt, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow] at *
    rw [hsplitL, hsplitR] at hr
    change
      (∑ i : Fin k, (((xy.2 i).1.val : ℤ) ^ (j.val + 1) -
        ((zw.2 i).1.val : ℤ) ^ (j.val + 1))) +
        (1 : ℤ) ^ (j.val + 1) *
          (∑ i : Fin s, (((xy.1 i).1.val : ℤ) ^ (j.val + 1) -
            ((zw.1 i).1.val : ℤ) ^ (j.val + 1))) = 0
    simp only [Finset.sum_sub_distrib, one_pow, one_mul]
    dsimp [xy, zw] at hr ⊢
    linear_combination hr
  let invFun : KPoint s k P P (powerFamily (k := k)) 1 →
      BaseZero (FordKPointEnergy.baseFreq (s := s + k) (k := k) (Q := P) (q := 1)) :=
    fun a => by
      let x : FordKPointEnergy.PowerWord (s := s) (Q := P) :=
        fun i => ⟨a.x i, a.x_pos i⟩
      let y : FordKPointEnergy.PowerWord (s := s) (Q := P) :=
        fun i => ⟨a.y i, a.y_pos i⟩
      let z : Fin k → FordKPointEnergy.SourcePoint (P := P) :=
        fun i => ⟨a.z i, a.z_pos i⟩
      let w : Fin k → FordKPointEnergy.SourcePoint (P := P) :=
        fun i => ⟨a.w i, a.w_pos i⟩
      refine ⟨(joinPowerWord x z, joinPowerWord y w), ?_⟩
      funext j
      have ha := a.equation j
      have hsplitL := baseFreq_split (joinPowerWord x z) j
      have hsplitR := baseFreq_split (joinPowerWord y w) j
      simp [splitPowerWord, joinPowerWord] at hsplitL hsplitR
      simp only [powerFamily, fordSourceFrequencyAt, Polynomial.eval_pow,
        Polynomial.eval_X, one_pow] at ha hsplitL hsplitR ⊢
      rw [hsplitL, hsplitR]
      simp only [Finset.sum_sub_distrib, one_pow, one_mul] at *
      dsimp [x, y, z, w] at ha ⊢
      linear_combination ha
  refine Equiv.mk toFun invFun
    (by
      intro r
      apply Subtype.ext
      apply Prod.ext
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j
        · simp [toFun, invFun, splitPowerWord, joinPowerWord]
        · simp [toFun, invFun, splitPowerWord, joinPowerWord]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j
        · simp [toFun, invFun, splitPowerWord, joinPowerWord]
        · simp [toFun, invFun, splitPowerWord, joinPowerWord])
    (by
      intro a
      cases a
      simp [toFun, invFun, splitPowerWord, joinPowerWord])

theorem completeMoment_eq_kPoint_power
    (s k P : ℕ) :
    completeMoment (s + k) k P =
      Fintype.card (KPoint s k P P (powerFamily (k := k)) 1) := by
  have hmoment := FordCompleteMomentBridge.completeMoment_eq_baseZero_card
    (s := s + k) (k := k) (Q := P) (q := 1) (by norm_num : (0 : ℕ) < 1)
  rw [hmoment]
  exact Fintype.card_congr baseZeroToKPoint

theorem powerFamily_fordType {k : ℕ} :
    FordType k 0 1 0 (MAPFordP16Source35Triangular.psiNatSucc (powerFamily (k := k))) := by
  intro j hj
  constructor
  · intro hj0
    have hj_eq : j = 0 := by omega
    subst j
    simp [MAPFordP16Source35Triangular.psiNatSucc]
  · intro hjd
    have hjpos : 1 ≤ j := by omega
    have hjlt : j - 1 < k := by omega
    have hjne : j ≠ 0 := by omega
    simp only [MAPFordP16Source35Triangular.psiNatSucc, dif_neg hjne]
    rw [MAPFordP16Source35Triangular.psiNat_eq (powerFamily (k := k)) hjlt]
    simp [powerFamily, Polynomial.natDegree_X_pow,
      Polynomial.leadingCoeff_X_pow]
    constructor
    · omega
    · have hfac : (j.factorial : ℤ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_ne_zero j)
      rw [Int.ediv_self hfac]

end FordCompleteMomentKPower

#print axioms FordCompleteMomentKPower.completeMoment_eq_kPoint_power
#print axioms FordCompleteMomentKPower.powerFamily_fordType
