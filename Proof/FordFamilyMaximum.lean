import FordMaskedKToRaw
import FordTypeCenteredDifference
import FordLemma32LiteralContract
import FordP16Source35Triangular

open scoped BigOperators
open MAPFordType MAPFordMaskedKToRaw MAPFordLemma32LiteralContract
open MAPFordP16Source35Triangular

noncomputable section
namespace FordFamilyMaximum

abbrev FordFamily (k d : ℕ) (T : ℤ) :=
  {x : ℕ × (Fin k → Polynomial ℤ) //
    FordType k d T x.1 (psiNatSucc x.2)}

lemma kpoint_card_le {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ) :
    Fintype.card (KPoint s k P Q psi q) ≤
      (P + 1) ^ (2*k) * (Q + 1) ^ (2*s) := by
  let proj : KPoint s k P Q psi q →
      (Fin k → Fin (P + 1)) × (Fin k → Fin (P + 1)) ×
        (Fin s → Fin (Q + 1)) × (Fin s → Fin (Q + 1)) :=
    fun a => (a.z, a.w, a.x, a.y)
  have hinj : Function.Injective proj := by
    intro a b h
    cases a with
    | mk az aw ax ay azp awp axp ayp ae =>
      cases b with
      | mk bz bw bx by' bzp bwp bxp byp be =>
        change (az, aw, ax, ay) = (bz, bw, bx, by') at h
        cases h
        rfl
  have hc := Fintype.card_le_of_injective proj hinj
  calc
    Fintype.card (KPoint s k P Q psi q) ≤
        (P + 1) ^ k * ((P + 1) ^ k * ((Q + 1) ^ s * (Q + 1) ^ s)) := by
      simpa [proj, Fintype.card_prod, Fintype.card_fun] using hc
    _ = (P + 1) ^ (2*k) * (Q + 1) ^ (2*s) := by
      rw [show 2*k = k+k by omega, show 2*s = s+s by omega,
        pow_add, pow_add]
      ring

theorem exists_maximal_ford_family_member
    {s k d P Q q : ℕ} {T : ℤ}
    (m0 : ℕ) (psi0 : Fin k → Polynomial ℤ)
    (h0 : FordType k d T m0 (psiNatSucc psi0)) :
    ∃ (m : ℕ) (psi : Fin k → Polynomial ℤ),
      FordType k d T m (psiNatSucc psi) ∧
      ∀ (m' : ℕ) (psi' : Fin k → Polynomial ℤ),
        FordType k d T m' (psiNatSucc psi') →
          Fintype.card (KPoint s k P Q psi' q) ≤
            Fintype.card (KPoint s k P Q psi q) := by
  let B : ℕ := (P + 1) ^ (2*k) * (Q + 1) ^ (2*s)
  let counts : Set ℕ := {n | ∃ x : FordFamily k d T,
      Fintype.card (KPoint s k P Q x.1.2 q) = n}
  have hcounts_nonempty : counts.Nonempty := by
    refine ⟨Fintype.card (KPoint s k P Q psi0 q), ?_⟩
    exact ⟨⟨(m0, psi0), h0⟩, rfl⟩
  have hcounts_sub : counts ⊆ Set.Iic B := by
    intro n hn
    rcases hn with ⟨x, rfl⟩
    exact kpoint_card_le x.1.2 q
  have hcounts_finite : counts.Finite :=
    (Set.finite_Iic B).subset hcounts_sub
  obtain ⟨nmax, hnmax, hmax⟩ :=
    Set.exists_max_image counts id hcounts_finite hcounts_nonempty
  rcases hnmax with ⟨xmax, hxmax⟩
  rcases xmax with ⟨xmax, hxm⟩
  refine ⟨xmax.1, xmax.2, hxm, ?_⟩
  intro m' psi' hpsi'
  have hmember : Fintype.card (KPoint s k P Q psi' q) ∈ counts := by
    exact ⟨⟨(m', psi'), hpsi'⟩, rfl⟩
  have hle := hmax _ hmember
  simpa [id, ← hxmax] using hle

end FordFamilyMaximum

#print axioms FordFamilyMaximum.kpoint_card_le
#print axioms FordFamilyMaximum.exists_maximal_ford_family_member
