import FordRawGroupedToL
import FordRealizedClassBound

open scoped BigOperators
open MAPFordP18FixedTargetInjection MAPFordP18MixedInjection
open MAPFordMixedSourceCount MAPFordScaledPowerCongruence
open MAPFordP16FiniteFourierBridge MAPFordP16LiteralResidueBridge
open MAPFordP16SourceCountBridge MAPFordRawStateGeometry MAPFordRawGroupedToL
open MAPFordLemma32LiteralContract MAPFordRawCongruenceToL

noncomputable section
namespace FordActualGroupedToL

abbrev actualRawFrequencyCarrier {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (phi : Fin k → Polynomial ℤ) : Type :=
  fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k) (d := d)
    (Q := Q) (P := P) (q := q) hdk hp phi

abbrev actualCorrectLPoint := LPoint

private lemma intResidue_val_eq_mod {p r : ℕ} (hp : p.Prime) (a : ℕ) :
    (intResidue (p ^ r) (Nat.pow_pos (n := r) hp.pos) (a : ℤ)).val =
      a % (p ^ r) := by
  change ((a : ℤ) % (p ^ r : ℤ)).toNat = a % (p ^ r)
  apply Int.natCast_inj.mp
  have hq : (p ^ r : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.pow_pos (n := r) hp.pos))
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hq)]
  exact (Int.natCast_emod a (p ^ r)).symm

theorem actual_card_le_L
    {p r k d s P Q q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (hR : 1 ≤ r) (hr : r ≤ k)
    (phi : Fin k → Polynomial ℤ) :
    Fintype.card (actualRawFrequencyCarrier (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := p*q) hdk hp phi) ≤
      p ^ ((r-d) * (r-d-1) / 2 + r*d + (k-d)) *
        Fintype.card (actualCorrectLPoint s k P Q p q r phi) := by
  let C : ℕ := p ^ ((r-d) * (r-d-1) / 2 + r*d + (k-d))
  have hC : ∀ t : Fin k → ℤ,
      ((Finset.univ.filter (fun a : RawState (s := s) (Q := Q) (P := P)
          hdk hp phi => total hdk hp phi q a = t)).image
        (residue hdk hp phi r)).card ≤ C := by
    intro t
    let S := Finset.univ.filter (fun a : RawState (s := s) (Q := Q) (P := P)
      hdk hp phi => total hdk hp phi q a = t)
    let I := S.image (residue hdk hp phi r)
    let R : Type := {c : Fin k → Fin (p ^ r) // c ∈ I}
    let mapClass : R → {c : Fin k → Fin (p ^ r) //
        ∃ z : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P)
            hdk hp phi,
          ∃ u : Fin s → Fin (Q + 1),
            (∀ j, fordSourceFrequencyAt phi z.1 j +
              fordQFrequencyAt (q := p*q) u j = t j) ∧
            (∀ j, c j = intResidue (p ^ r)
              (Nat.pow_pos (n := r) hp.pos) (z.1 j).val)} := by
      intro c
      have hmI := c.2
      change c.1 ∈ I at hmI
      change c.1 ∈ S.image (residue hdk hp phi r) at hmI
      have hex := Finset.mem_image.mp hmI
      let a := Classical.choose hex
      have ha := Classical.choose_spec hex
      have hres := ha.2
      let u : Fin s → Fin (Q + 1) := fun i => (a.2 i).1
      refine ⟨c.1, ⟨a.1, u, ?_, ?_⟩⟩
      · intro j
        have ht : total hdk hp phi q a = t := by
          simpa [S, a] using ha.1
        exact congrFun ht j
      · intro j
        apply Fin.ext
        have hval := congrArg (fun w => (w j).val) hres
        rw [intResidue_val_eq_mod hp (a.1.1 j).val]
        exact hval.symm
    have hfval : ∀ c : R, (mapClass c).val = c.1 := by
      intro c
      dsimp [mapClass]
    have hfinj : Function.Injective mapClass := by
      intro c c' h
      apply Subtype.ext
      have hv := congrArg Subtype.val h
      rw [hfval c, hfval c'] at hv
      exact hv
    have hcard := Fintype.card_le_of_injective mapClass hfinj
    have hreal := FordRealizedClassBound.realized_class_card_le
      (p := p) (r := r) (k := k) (d := d) (s := s) (Q := Q) (P := P)
      (q := q) hdk hp hR hr phi t
    have hi : I.card ≤ C := by
      rw [← Fintype.card_coe I]
      exact hcard.trans hreal
    simpa [C, S, I] using hi
  have hraw := MAPFordRawGroupedToL.raw_card_le_L_of_class_cap
    (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P) (q := q) (r := r)
    hdk hp phi C hC
  simpa [actualRawFrequencyCarrier, actualCorrectLPoint, C] using hraw

end FordActualGroupedToL

#print axioms FordActualGroupedToL.actual_card_le_L
