import FordLemma32GeometricRange
import FordLPointLargeModulusComplete

open MAPFordType MAPFordP16Source35Triangular
open MAPFordLemma32LiteralContract MAPFordCompleteSystemMoment
open MAPFordLemma32GeometricRange
open FordLPointLargeModulusComplete

noncomputable section
set_option autoImplicit false
namespace FordTerminalKCount

/-- The terminal large-modulus specialization of Lemma 3.2.  The geometric
prime selector gives `M < p`; the explicit terminal range hypothesis gives
`P < p^r`, so the exact large-modulus identity removes the residual L-count. -/
theorem exists_terminal_K_bound
    {s k d P Q q r M : ℕ} {T : ℤ}
    (hk : 2 ≤ k) (hd : d ≤ k) (hds : d ≤ s) (hs : 1 ≤ s)
    (hr1 : 1 ≤ r) (hrk : r ≤ k) (hlarge : 16 * k^4 < P) (hM : k ≤ M)
    (hP : P ≤ (M+1)^(k+1))
    (hnative : (4*s)^2*(2^(k^3)*M) ≤ Q) (hq : 0 < q)
    (hterminal : P < (M+1)^r)
    (hT : 0 < T) (hTsize : T.natAbs ≤ P^d)
    (m0 : ℕ) (psi0 : Fin k → Polynomial ℤ)
    (h0 : FordType k d T m0 (psiNatSucc psi0)) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ M < p ∧ p ≤ 2^(k^3)*M ∧
      (4*s)^2*p ≤ Q ∧
      ∃ (m : ℕ) (phi : Fin k → Polynomial ℤ), FordType k d T m (psiNatSucc phi) ∧
      Fintype.card (KPoint s k P Q psi0 q) ≤
        (4*k^3*Nat.factorial d*p^(2*s-d+(r-d)*(r-d-1)/2+r*d+(k-d))) *
          P^k * completeMoment s k (Q/p) := by
  obtain ⟨p, hp, hkp, hMp, hupper, hnative, m, phi, hphi, hK⟩ :=
    MAPFordLemma32GeometricRange.K_exists_L_geometric_range
      (s := s) (k := k) (d := d) (P := P) (Q := Q) (q := q)
      (r := r) (M := M) (T := T)
      hk hd hds hs hr1 hrk hlarge hM hP hnative hq (by omega) hTsize m0 psi0 h0
  have hMplus : M + 1 ≤ p := by omega
  have hpow : (M + 1)^r ≤ p^r := Nat.pow_le_pow_left hMplus r
  have hPr : P < p^r := hterminal.trans_le hpow
  have hL := FordLPointLargeModulusComplete.lPoint_card_eq_completeMoment
    (s := s) (k := k) (P := P) (Q := Q / p) (p := p) (q := q) (r := r)
    phi hp.pos hq hPr
  refine ⟨p, hp, hkp, hMp, hupper, hnative, m, phi, hphi, ?_⟩
  rw [hL] at hK
  simpa [Nat.mul_assoc] using hK

end FordTerminalKCount
#print axioms FordTerminalKCount.exists_terminal_K_bound
