import GuthMaynardSourceLemmas

/-!
# Guth--Maynard S3 source assembly

This module formalizes the exact deterministic substitution of Guth--Maynard
Proposition 11.1 (the energy bound) into Proposition 10.1 (the refined `S3`
bound).  The result is the four-term Proposition 11.2 contribution used in
equation (12.1).  Constants are retained explicitly.

No analytic estimate is assumed globally or asserted here.  Besides the
Proposition 11.2 assembly, the file certifies the deterministic algebra inside
Propositions 9.1, 10.1, 11.1, and Lemma 11.9.  The remaining analytic leaves
are the uniform profile construction in Lemma 9.2 and the literal factored
energy inequality supplied by Lemmas 11.4, 11.8, and 11.9; the latter
ultimately uses Heath--Brown's Theorem 1.6.
-/

namespace GuthMaynardS3Source

noncomputable section

lemma sqrt_add_two_le {x y : ℝ} (hx:0≤x) (hy:0≤y) : Real.sqrt (x+y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hsx := Real.sq_sqrt hx
    have hsy := Real.sq_sqrt hy
    have hsx0 := Real.sqrt_nonneg x
    have hsy0 := Real.sqrt_nonneg y
    nlinarith

lemma sqrt_rpow {x a:ℝ} (hx:0≤x) :
 Real.sqrt (Real.rpow x a) = Real.rpow x (a/2) := by
  apply (Real.sqrt_eq_iff_eq_sq (Real.rpow_nonneg hx _) (Real.rpow_nonneg hx _)).2
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  congr 1
  ring

lemma sqrt_rpow_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (a b : ℝ) :
    Real.sqrt (Real.rpow x a * Real.rpow y b) =
      Real.rpow x (a/2) * Real.rpow y (b/2) := by
  rw [Real.sqrt_mul (x := Real.rpow x a) (Real.rpow_nonneg hx a) (Real.rpow y b), sqrt_rpow hx, sqrt_rpow hy]

lemma sqrt_energyTerm_one {W N sigma:ℝ} (hW:0≤W) (hN:0≤N) :
 Real.sqrt (W * Real.rpow N (4-4*sigma)) =
 Real.sqrt W * Real.rpow N (2-2*sigma) := by
  rw [Real.sqrt_mul hW, sqrt_rpow hN]
  congr 1
  ring

lemma sqrt_energyTerm_two {W T N sigma:ℝ} (hW:0≤W) (hT:0≤T) (hN:0≤N) :
 Real.sqrt (Real.rpow W (21/8:ℝ) * Real.rpow T (1/4:ℝ) * Real.rpow N (1-2*sigma)) =
 Real.rpow W (21/16:ℝ) * Real.rpow T (1/8:ℝ) * Real.rpow N (1/2-sigma) := by
  rw [Real.sqrt_mul (x := Real.rpow W (21/8:ℝ) * Real.rpow T (1/4:ℝ)) (mul_nonneg (Real.rpow_nonneg hW _) (Real.rpow_nonneg hT _)) (Real.rpow N (1-2*sigma))]
  rw [Real.sqrt_mul (x := Real.rpow W (21/8:ℝ)) (Real.rpow_nonneg hW _) (Real.rpow T (1/4:ℝ))]
  rw [sqrt_rpow hW, sqrt_rpow hT, sqrt_rpow hN]
  congr 1
  all_goals ring_nf

lemma sqrt_energyTerm_three {W N sigma:ℝ} (hW:0≤W) (hN:0≤N) :
 Real.sqrt (Real.rpow W (3:ℝ) * Real.rpow N (1-2*sigma)) =
 Real.rpow W (3/2:ℝ) * Real.rpow N (1/2-sigma) := by
  rw [sqrt_rpow_mul hW hN]
  congr 1
  all_goals ring_nf

lemma multiply_energyTerm_one {T N W sigma:ℝ} (hN:0<N) (hW:0<W) :
 T*N*Real.rpow W (1/2:ℝ) *
   (Real.sqrt W * Real.rpow N (2-2*sigma)) =
 T*W*Real.rpow N (3-2*sigma) := by
  rw [Real.sqrt_eq_rpow]
  have hWadd : Real.rpow W ((1/2:ℝ)+(1/2)) =
      Real.rpow W (1/2:ℝ)*Real.rpow W (1/2:ℝ) := by
    exact Real.rpow_add hW _ _
  have hNadd : Real.rpow N ((1:ℝ)+(2-2*sigma)) =
      Real.rpow N (1:ℝ)*Real.rpow N (2-2*sigma) := by
    exact Real.rpow_add hN _ _
  have hTOne : Real.rpow T (1:ℝ) = T := Real.rpow_one T
  have hNOne : Real.rpow N (1:ℝ) = N := Real.rpow_one N
  have hWOne : Real.rpow W (1:ℝ) = W := Real.rpow_one W
  calc
    T*N*Real.rpow W (1/2:ℝ) *
        (Real.rpow W (1/2:ℝ) * Real.rpow N (2-2*sigma)) =
      Real.rpow T (1:ℝ) *
        (Real.rpow W (1/2:ℝ) * Real.rpow W (1/2:ℝ)) *
        (Real.rpow N (1:ℝ) * Real.rpow N (2-2*sigma)) := by
          rw [hTOne, hNOne]
          ring
    _ = Real.rpow T (1:ℝ) * Real.rpow W ((1/2:ℝ)+(1/2)) *
        Real.rpow N ((1:ℝ)+(2-2*sigma)) := by
          rw [← hWadd, ← hNadd]
    _ = T*W*Real.rpow N (3-2*sigma) := by
          rw [hTOne, show (1/2:ℝ)+(1/2)=1 by norm_num, hWOne]
          congr 1
          ring

lemma multiply_energyTerm_two {T N W sigma:ℝ} (hT:0<T) (hN:0<N) (hW:0<W) :
 T*N*Real.rpow W (1/2:ℝ) *
  (Real.rpow W (21/16:ℝ) * Real.rpow T (1/8:ℝ) * Real.rpow N (1/2-sigma)) =
 Real.rpow T (9/8:ℝ) * Real.rpow W (29/16:ℝ) * Real.rpow N (3/2-sigma) := by
  have hTadd : Real.rpow T ((1:ℝ)+(1/8)) = Real.rpow T (1:ℝ)*Real.rpow T (1/8:ℝ) := Real.rpow_add hT _ _
  have hWadd : Real.rpow W ((1/2:ℝ)+(21/16)) = Real.rpow W (1/2:ℝ)*Real.rpow W (21/16:ℝ) := Real.rpow_add hW _ _
  have hNadd : Real.rpow N ((1:ℝ)+(1/2-sigma)) = Real.rpow N (1:ℝ)*Real.rpow N (1/2-sigma) := Real.rpow_add hN _ _
  have hTOne : Real.rpow T (1:ℝ)=T := Real.rpow_one T
  have hNOne : Real.rpow N (1:ℝ)=N := Real.rpow_one N
  calc
   T*N*Real.rpow W (1/2:ℝ) *
      (Real.rpow W (21/16:ℝ) * Real.rpow T (1/8:ℝ) * Real.rpow N (1/2-sigma)) =
     (Real.rpow T (1:ℝ)*Real.rpow T (1/8:ℝ)) *
     (Real.rpow W (1/2:ℝ)*Real.rpow W (21/16:ℝ)) *
     (Real.rpow N (1:ℝ)*Real.rpow N (1/2-sigma)) := by
       rw [hTOne, hNOne]
       ring
   _ = Real.rpow T ((1:ℝ)+(1/8)) * Real.rpow W ((1/2:ℝ)+(21/16)) *
       Real.rpow N ((1:ℝ)+(1/2-sigma)) := by
       rw [← hTadd, ← hWadd, ← hNadd]
   _ = Real.rpow T (9/8:ℝ)*Real.rpow W (29/16:ℝ)*Real.rpow N (3/2-sigma) := by
       congr 1 <;> ring_nf

lemma multiply_energyTerm_three {T N W sigma:ℝ} (hN:0<N) (hW:0<W) :
 T*N*Real.rpow W (1/2:ℝ) *
  (Real.rpow W (3/2:ℝ) * Real.rpow N (1/2-sigma)) =
 T*(W^2)*Real.rpow N (3/2-sigma) := by
  have hWadd : Real.rpow W ((1/2:ℝ)+(3/2)) = Real.rpow W (1/2:ℝ)*Real.rpow W (3/2:ℝ) := Real.rpow_add hW _ _
  have hNadd : Real.rpow N ((1:ℝ)+(1/2-sigma)) = Real.rpow N (1:ℝ)*Real.rpow N (1/2-sigma) := Real.rpow_add hN _ _
  have hNOne : Real.rpow N (1:ℝ)=N := Real.rpow_one N
  calc
   T*N*Real.rpow W (1/2:ℝ) *
      (Real.rpow W (3/2:ℝ) * Real.rpow N (1/2-sigma)) =
     T * (Real.rpow W (1/2:ℝ)*Real.rpow W (3/2:ℝ)) *
     (Real.rpow N (1:ℝ)*Real.rpow N (1/2-sigma)) := by
       rw [hNOne]
       ring
   _ = T*Real.rpow W ((1/2:ℝ)+(3/2))*Real.rpow N ((1:ℝ)+(1/2-sigma)) := by
       rw [← hWadd, ← hNadd]
   _ = T*(W^2)*Real.rpow N (3/2-sigma) := by
       have hpow2 : Real.rpow W (2:ℝ) = W^2 := by
         exact Real.rpow_natCast W 2
       rw [show (1/2:ℝ)+(3/2)=2 by norm_num, hpow2]
       congr 1 <;> ring_nf

lemma sqrt_add_three_le {x y z:ℝ} (hx:0≤x) (hy:0≤y) (hz:0≤z) :
 Real.sqrt (x+y+z) ≤ Real.sqrt x+Real.sqrt y+Real.sqrt z := by
  calc
   Real.sqrt (x+y+z) ≤ Real.sqrt (x+y)+Real.sqrt z := by
    exact sqrt_add_two_le (add_nonneg hx hy) hz
   _ ≤ (Real.sqrt x+Real.sqrt y)+Real.sqrt z := by
    gcongr
    exact sqrt_add_two_le hx hy
   _ = _ := by ring

lemma proposition11_2_of_10_1_and_11_1
 {T N W sigma E S3 C3 CE:ℝ}
 (hT:0<T) (hN:0<N) (hW:0<W) (hC3:0≤C3) (hCE:0≤CE)
 (henergy : E ≤ CE *
   (W*Real.rpow N (4-4*sigma) +
    Real.rpow W (21/8:ℝ)*Real.rpow T (1/4:ℝ)*Real.rpow N (1-2*sigma) +
    Real.rpow W (3:ℝ)*Real.rpow N (1-2*sigma)))
 (hrefined : S3 ≤ C3*(T^2*Real.rpow W (3/2:ℝ) +
    T*N*Real.rpow W (1/2:ℝ)*Real.sqrt E)) :
 S3 ≤ C3*((1+Real.sqrt CE)*
   (T^2*Real.rpow W (3/2:ℝ) +
    (T*W*Real.rpow N (3-2*sigma) +
    Real.rpow T (9/8:ℝ)*Real.rpow W (29/16:ℝ)*Real.rpow N (3/2-sigma) +
    T*(W^2)*Real.rpow N (3/2-sigma)))) := by
 let e1 := W*Real.rpow N (4-4*sigma)
 let e2 := Real.rpow W (21/8:ℝ)*Real.rpow T (1/4:ℝ)*Real.rpow N (1-2*sigma)
 let e3 := Real.rpow W (3:ℝ)*Real.rpow N (1-2*sigma)
 have he10:0≤e1 := mul_nonneg hW.le (Real.rpow_nonneg hN.le _)
 have he20:0≤e2 := mul_nonneg (mul_nonneg (Real.rpow_nonneg hW.le _) (Real.rpow_nonneg hT.le _)) (Real.rpow_nonneg hN.le _)
 have he30:0≤e3 := mul_nonneg (Real.rpow_nonneg hW.le _) (Real.rpow_nonneg hN.le _)
 have hsqrtSum : Real.sqrt (e1+e2+e3) ≤ Real.sqrt e1+Real.sqrt e2+Real.sqrt e3 :=
   sqrt_add_three_le he10 he20 he30
 have hroot : Real.sqrt E ≤ Real.sqrt CE *
   (Real.sqrt e1+Real.sqrt e2+Real.sqrt e3) := by
  calc
   Real.sqrt E ≤ Real.sqrt (CE*(e1+e2+e3)) := Real.sqrt_le_sqrt (by simpa [e1,e2,e3] using henergy)
   _ = Real.sqrt CE*Real.sqrt (e1+e2+e3) := Real.sqrt_mul hCE _
   _ ≤ Real.sqrt CE*(Real.sqrt e1+Real.sqrt e2+Real.sqrt e3) :=
     mul_le_mul_of_nonneg_left hsqrtSum (Real.sqrt_nonneg _)
 have hse1 : Real.sqrt e1 = Real.sqrt W*Real.rpow N (2-2*sigma) := by
   dsimp [e1]
   exact sqrt_energyTerm_one hW.le hN.le
 have hse2 : Real.sqrt e2 = Real.rpow W (21/16:ℝ)*Real.rpow T (1/8:ℝ)*Real.rpow N (1/2-sigma) := by
   dsimp [e2]
   exact sqrt_energyTerm_two hW.le hT.le hN.le
 have hse3 : Real.sqrt e3 = Real.rpow W (3/2:ℝ)*Real.rpow N (1/2-sigma) := by
   dsimp [e3]
   exact sqrt_energyTerm_three hW.le hN.le
 let factor := T*N*Real.rpow W (1/2:ℝ)
 have hfactor0 : 0≤factor := by dsimp [factor]; positivity
 have hfactorRoot : factor*Real.sqrt E ≤ Real.sqrt CE *
   (T*W*Real.rpow N (3-2*sigma) +
    Real.rpow T (9/8:ℝ)*Real.rpow W (29/16:ℝ)*Real.rpow N (3/2-sigma) +
    T*(W^2)*Real.rpow N (3/2-sigma)) := by
  calc
   factor*Real.sqrt E ≤ factor*(Real.sqrt CE*(Real.sqrt e1+Real.sqrt e2+Real.sqrt e3)) :=
    mul_le_mul_of_nonneg_left hroot hfactor0
   _ = Real.sqrt CE * (factor*Real.sqrt e1+factor*Real.sqrt e2+factor*Real.sqrt e3) := by ring
   _ = _ := by
    rw [hse1,hse2,hse3]
    rw [show factor*(Real.sqrt W*Real.rpow N (2-2*sigma)) = T*W*Real.rpow N (3-2*sigma) by
      exact multiply_energyTerm_one hN hW]
    rw [show factor*(Real.rpow W (21/16:ℝ)*Real.rpow T (1/8:ℝ)*Real.rpow N (1/2-sigma)) =
      Real.rpow T (9/8:ℝ)*Real.rpow W (29/16:ℝ)*Real.rpow N (3/2-sigma) by exact multiply_energyTerm_two hT hN hW]
    rw [show factor*(Real.rpow W (3/2:ℝ)*Real.rpow N (1/2-sigma)) = T*(W^2)*Real.rpow N (3/2-sigma) by exact multiply_energyTerm_three hN hW]
 have hA0 : 0≤T^2*Real.rpow W (3/2:ℝ) := mul_nonneg (sq_nonneg T) (Real.rpow_nonneg hW.le _)
 have hB0 : 0≤T*W*Real.rpow N (3-2*sigma) := mul_nonneg (mul_nonneg hT.le hW.le) (Real.rpow_nonneg hN.le _)
 have hC0 : 0≤Real.rpow T (9/8:ℝ)*Real.rpow W (29/16:ℝ)*Real.rpow N (3/2-sigma) := mul_nonneg (mul_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg hW.le _)) (Real.rpow_nonneg hN.le _)
 have hD0 : 0≤T*(W^2)*Real.rpow N (3/2-sigma) := mul_nonneg (mul_nonneg hT.le (sq_nonneg W)) (Real.rpow_nonneg hN.le _)
 calc
  S3 ≤ C3*(T^2*Real.rpow W (3/2:ℝ)+factor*Real.sqrt E) := by simpa [factor] using hrefined
  _ ≤ C3*(T^2*Real.rpow W (3/2:ℝ)+Real.sqrt CE*(
      T*W*Real.rpow N (3-2*sigma)+
      Real.rpow T (9/8:ℝ)*Real.rpow W (29/16:ℝ)*Real.rpow N (3/2-sigma)+
      T*(W^2)*Real.rpow N (3/2-sigma))) := by
    gcongr
  _ ≤ C3*((1+Real.sqrt CE)*(
      T^2*Real.rpow W (3/2:ℝ)+
      (T*W*Real.rpow N (3-2*sigma)+
      Real.rpow T (9/8:ℝ)*Real.rpow W (29/16:ℝ)*Real.rpow N (3/2-sigma)+
      T*(W^2)*Real.rpow N (3/2-sigma)))) := by
    have hsCE0 := Real.sqrt_nonneg CE
    let A := T^2*Real.rpow W (3/2:ℝ)
    let X := T*W*Real.rpow N (3-2*sigma)+
      Real.rpow T (9/8:ℝ)*Real.rpow W (29/16:ℝ)*Real.rpow N (3/2-sigma)+
      T*(W^2)*Real.rpow N (3/2-sigma)
    have hX0 : 0 ≤ X := by dsimp [X]; positivity
    have hinner : A+Real.sqrt CE*X ≤ (1+Real.sqrt CE)*(A+X) := by
      have : 0 ≤ X+Real.sqrt CE*A := add_nonneg hX0 (mul_nonneg hsCE0 (by simpa [A] using hA0))
      nlinarith
    exact mul_le_mul_of_nonneg_left hinner hC3


/-! ## One layer upstream: the algebra of Proposition 10.1 -/

/-- The deterministic core of Guth--Maynard Proposition 10.1 after
Proposition 9.1 and the L2/L4 estimates have supplied the bound on `S32`.
The hypothesis `M ≤ T/N` is then used exactly once to replace the internal
frequency scale by the ambient aperture. -/
theorem proposition10_1_of_affine_secondMoment
 {T N M W E S30 S31 S32:ℝ}
 (hT:0<T) (hN:0<N) (hM:0<M) (hW:0<W) (hE:0≤E)
 (hS320:0≤S32)
 (hS31:S31≤W)
 (hS32:S32≤Real.rpow M (6:ℝ)*Real.rpow W (2:ℝ)+Real.rpow M (4:ℝ)*E)
 (hS30:S30≤(N^2/M)*Real.sqrt (S31*S32))
 (hMT:M≤T/N) :
 S30≤T^2*Real.rpow W (3/2:ℝ)+T*N*Real.sqrt W*Real.sqrt E := by
 let A:=Real.rpow M (6:ℝ)*Real.rpow W (2:ℝ)+Real.rpow M (4:ℝ)*E
 have hA0:0≤A:=by dsimp[A]; positivity
 have hprod:S31*S32≤W*A:=mul_le_mul hS31 (by simpa[A] using hS32) hS320 hW.le
 have hsqrtprod:Real.sqrt (S31*S32)≤Real.sqrt (W*A):=Real.sqrt_le_sqrt hprod
 have hsqrt1:Real.sqrt (Real.rpow M (6:ℝ)*Real.rpow W (3:ℝ))=
   Real.rpow M (3:ℝ)*Real.rpow W (3/2:ℝ):=by
   rw[sqrt_rpow_mul hM.le hW.le]
   congr 1 <;> ring_nf
 have hsqrt2:Real.sqrt (Real.rpow M (4:ℝ)*W*E)=
   Real.rpow M (2:ℝ)*Real.sqrt W*Real.sqrt E:=by
   rw[Real.sqrt_mul (x:=Real.rpow M (4:ℝ)*W) (mul_nonneg (Real.rpow_nonneg hM.le _) hW.le) E]
   rw[Real.sqrt_mul (x:=Real.rpow M (4:ℝ)) (Real.rpow_nonneg hM.le _) W]
   rw[sqrt_rpow hM.le]
   congr 1 <;> ring_nf
 have hW2 : Real.rpow W (2:ℝ)=W^2:=by exact Real.rpow_natCast W 2
 have hW3 : Real.rpow W (3:ℝ)=W^3:=by exact Real.rpow_natCast W 3
 have hWW2 : W*Real.rpow W (2:ℝ)=Real.rpow W (3:ℝ):=by
   rw[hW2,hW3]
   ring
 have hWA:W*A=Real.rpow M (6:ℝ)*Real.rpow W (3:ℝ)+Real.rpow M (4:ℝ)*W*E:=by
   calc
    W*A=Real.rpow M (6:ℝ)*(W*Real.rpow W (2:ℝ))+Real.rpow M (4:ℝ)*W*E:=by dsimp[A]; ring
    _=_:=by rw[hWW2]
 have hsqrtWA:Real.sqrt (W*A)≤Real.rpow M (3:ℝ)*Real.rpow W (3/2:ℝ)+
   Real.rpow M (2:ℝ)*Real.sqrt W*Real.sqrt E:=by
   rw[hWA]
   calc
    Real.sqrt (Real.rpow M 6 * Real.rpow W 3 + Real.rpow M 4 * W * E) ≤
      Real.sqrt (Real.rpow M 6 * Real.rpow W 3)+Real.sqrt (Real.rpow M 4*W*E):=by
       apply sqrt_add_two_le
       · exact mul_nonneg (Real.rpow_nonneg hM.le _) (Real.rpow_nonneg hW.le _)
       · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hM.le _) hW.le) hE
    _=_:=by rw[hsqrt1,hsqrt2]
 have hpre:S30≤(N^2/M)*(Real.rpow M (3:ℝ)*Real.rpow W (3/2:ℝ)+
   Real.rpow M (2:ℝ)*Real.sqrt W*Real.sqrt E):=
   hS30.trans (mul_le_mul_of_nonneg_left (hsqrtprod.trans hsqrtWA) (div_nonneg (sq_nonneg N) hM.le))
 have hM2:Real.rpow M (2:ℝ)=M^2:=by exact Real.rpow_natCast M 2
 have hM3:Real.rpow M (3:ℝ)=M^3:=by exact Real.rpow_natCast M 3
 have hcancel:(N^2/M)*(Real.rpow M (3:ℝ)*Real.rpow W (3/2:ℝ)+
   Real.rpow M (2:ℝ)*Real.sqrt W*Real.sqrt E)=
   N^2*M^2*Real.rpow W (3/2:ℝ)+N^2*M*Real.sqrt W*Real.sqrt E:=by
   rw[hM2,hM3]
   field_simp
 have hMN:M*N≤T:=(le_div_iff₀ hN).mp hMT
 have hNM:N*M≤T:=by simpa [mul_comm] using hMN
 have hsq:(N*M)^2≤T^2:=(sq_le_sq₀ (mul_nonneg hN.le hM.le) hT.le).2 hNM
 have hfirst:N^2*M^2*Real.rpow W (3/2:ℝ)≤T^2*Real.rpow W (3/2:ℝ):=by
   have heq:N^2*M^2=(N*M)^2:=by ring
   rw[heq]
   exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hW.le _)
 have hsecond:N^2*M*Real.sqrt W*Real.sqrt E≤T*N*Real.sqrt W*Real.sqrt E:=by
   have hNMN:N*(N*M)≤N*T:=mul_le_mul_of_nonneg_left hNM hN.le
   have hcoef:N^2*M≤T*N:=by
    calc
     N^2*M=N*(N*M):=by ring
     _≤N*T:=hNMN
     _=T*N:=by ring
   have hcoefW := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg W)
   exact mul_le_mul_of_nonneg_right hcoefW (Real.sqrt_nonneg E)
 have hpre':S30≤N^2*M^2*Real.rpow W (3/2:ℝ)+N^2*M*Real.sqrt W*Real.sqrt E:=by
   rw[←hcancel]
   exact hpre
 exact hpre'.trans (add_le_add hfirst hsecond)

/-! ## Scalar core of the Proposition 9.1 iteration -/

/-- Once Lemma 9.2 has been made uniform over its smoothing orbit, its
iteration reduces to a scalar inequality `X ≤ A + B*sqrt X`.  This lemma
closes that recurrence with the exact two shapes in Proposition 9.1:
`X ≤ 2*A + B^2`.  Thus the remaining work in Proposition 9.1 is analytic:
prove Lemma 9.2 and show that smoothing preserves the admissible class and
its L1/L2 budgets. -/
theorem affine_iteration_scalar_absorption
    {X A B : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrec : X ≤ A + B * Real.sqrt X) :
    X ≤ 2 * A + B ^ 2 := by
  have hsqrtSq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX
  have hyoung : 2 * B * Real.sqrt X ≤ B ^ 2 + (Real.sqrt X) ^ 2 := by
    nlinarith [sq_nonneg (B - Real.sqrt X)]
  rw [hsqrtSq] at hyoung
  nlinarith

/-- Finite logical core of the source's "downwards induction on epsilon".
Starting at `epsilon*(3/2)^n`, repeated use of the uniform smoothing step
reaches `epsilon`. -/
theorem three_halves_epsilon_descent
    (P : ℝ → Prop)
    (hstep : ∀ e, 0 < e → P (3 * e / 2) → P e)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ n : ℕ, P (epsilon * (3 / 2 : ℝ) ^ n) → P epsilon := by
  intro n
  induction n generalizing epsilon with
  | zero => simpa
  | succ n ih =>
      intro hlarge
      apply hstep epsilon hepsilon
      apply ih (epsilon := 3 * epsilon / 2) (by positivity)
      convert hlarge using 1
      rw [pow_succ]
      ring

/-- Every positive epsilon reaches the crude base exponent `100` after
finitely many multiplications by `3/2`. -/
theorem exists_three_halves_depth
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, 100 ≤ epsilon * (3 / 2 : ℝ) ^ n := by
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (100 / epsilon) (by norm_num : (1 : ℝ) < 3 / 2)
  refine ⟨n, ?_⟩
  have hmul : 100 < (3 / 2 : ℝ) ^ n * epsilon :=
    (div_lt_iff₀ hepsilon).mp hn
  nlinarith

/-- Source-faithful closure of the downward-epsilon induction once the
Lemma 9.2 smoothing step is uniform over the admissible profile class. -/
theorem epsilon_induction_of_three_halves_step
    (P : ℝ → Prop)
    (hbase : ∀ e, 100 ≤ e → P e)
    (hstep : ∀ e, 0 < e → P (3 * e / 2) → P e)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) : P epsilon := by
  obtain ⟨n, hn⟩ := exists_three_halves_depth hepsilon
  exact three_halves_epsilon_descent P hstep hepsilon n (hbase _ hn)

/-! ## Exact rearrangement in Proposition 11.1 -/

/-- Constant-explicit square-root absorption.  This is the algebraic content
of the source's phrase "This rearranges to give" immediately before (11.1). -/
theorem absorb_sqrt_energy
    {E A B Q C : ℝ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hraw : E ≤ C * (A + B + Q * Real.sqrt E)) :
    E ≤ 2 * C * (A + B) + (C * Q) ^ 2 := by
  have hrec : E ≤ C * (A + B) + (C * Q) * Real.sqrt E := by
    calc
      E ≤ C * (A + B + Q * Real.sqrt E) := hraw
      _ = C * (A + B) + (C * Q) * Real.sqrt E := by ring
  simpa only [mul_add, mul_assoc] using
    (affine_iteration_scalar_absorption
      hE (mul_nonneg hC (add_nonneg hA hB)) (mul_nonneg hC hQ) hrec)

/-- The square of the coefficient of `sqrt E` is exactly the first monomial
in (11.1). -/
theorem energy_sqrt_coefficient_sq
    {W N sigma : ℝ} (hW : 0 < W) (hN : 0 < N) :
    (Real.sqrt W * Real.rpow N (2 - 2 * sigma)) ^ 2 =
      W * Real.rpow N (4 - 4 * sigma) := by
  have hsqrt : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hW.le
  have hrpow : (Real.rpow N (2 - 2 * sigma)) ^ 2 =
      Real.rpow N (4 - 4 * sigma) := by
    calc
      (Real.rpow N (2 - 2 * sigma)) ^ 2 =
          Real.rpow N (2 - 2 * sigma) *
            Real.rpow N (2 - 2 * sigma) := by ring
      _ = Real.rpow N ((2 - 2 * sigma) + (2 - 2 * sigma)) := by
        exact (Real.rpow_add hN _ _).symm
      _ = Real.rpow N (4 - 4 * sigma) := by ring_nf
  calc
    (Real.sqrt W * Real.rpow N (2 - 2 * sigma)) ^ 2 =
        (Real.sqrt W) ^ 2 * (Real.rpow N (2 - 2 * sigma)) ^ 2 := by ring
    _ = W * Real.rpow N (4 - 4 * sigma) := by rw [hsqrt, hrpow]

/-- Literal normalization of the display obtained after Lemmas 11.4, 11.8,
and 11.9.  This keeps the source's outer `N^(-2 sigma)` visible and proves
that distributing it produces exactly the three terms consumed below. -/
theorem postLemma11_9_normalization_identity
    {E W T N sigma : ℝ} (hN : 0 < N) :
    Real.rpow N (-2 * sigma) *
        (N * Real.rpow W (3 : ℝ) +
          N * Real.rpow T (1 / 4 : ℝ) * Real.rpow W (21 / 8 : ℝ) +
          Real.sqrt E * Real.sqrt W * N ^ 2) =
      Real.rpow W (3 : ℝ) * Real.rpow N (1 - 2 * sigma) +
        Real.rpow W (21 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
          Real.rpow N (1 - 2 * sigma) +
        (Real.sqrt W * Real.rpow N (2 - 2 * sigma)) * Real.sqrt E := by
  have hNone : Real.rpow N (1 : ℝ) = N := Real.rpow_one N
  have hNtwo : Real.rpow N (2 : ℝ) = N ^ 2 := Real.rpow_natCast N 2
  have hshiftOne :
      Real.rpow N (1 - 2 * sigma) = N * Real.rpow N (-2 * sigma) := by
    calc
      Real.rpow N (1 - 2 * sigma) =
          Real.rpow N ((1 : ℝ) + (-2 * sigma)) := by ring_nf
      _ = Real.rpow N (1 : ℝ) * Real.rpow N (-2 * sigma) :=
        Real.rpow_add hN _ _
      _ = N * Real.rpow N (-2 * sigma) := by rw [hNone]
  have hshiftTwo :
      Real.rpow N (2 - 2 * sigma) = N ^ 2 * Real.rpow N (-2 * sigma) := by
    calc
      Real.rpow N (2 - 2 * sigma) =
          Real.rpow N ((2 : ℝ) + (-2 * sigma)) := by ring_nf
      _ = Real.rpow N (2 : ℝ) * Real.rpow N (-2 * sigma) :=
        Real.rpow_add hN _ _
      _ = N ^ 2 * Real.rpow N (-2 * sigma) := by rw [hNtwo]
  rw [hshiftOne, hshiftTwo]
  ring

/-- Exact constant-sensitive form of Proposition 11.1 from the normalized
post-Lemma-11.9 inequality.  The source's `lesssim` hides the explicit output
constant `2*C + C^2`.  Consequently the remaining analytic content of
Proposition 11.1 is the displayed premise, supplied in the paper by Lemmas
11.4, 11.8, and 11.9. -/
theorem proposition11_1_of_postLemma11_9
    {E W T N sigma C : ℝ}
    (hE : 0 ≤ E) (hW : 0 < W) (hT : 0 ≤ T)
    (hN : 0 < N) (hC : 0 ≤ C)
    (hraw :
      E ≤ C *
        (Real.rpow W (3 : ℝ) * Real.rpow N (1 - 2 * sigma) +
          Real.rpow W (21 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
            Real.rpow N (1 - 2 * sigma) +
          (Real.sqrt W * Real.rpow N (2 - 2 * sigma)) * Real.sqrt E)) :
    E ≤ (2 * C + C ^ 2) *
      (W * Real.rpow N (4 - 4 * sigma) +
        Real.rpow W (21 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
          Real.rpow N (1 - 2 * sigma) +
        Real.rpow W (3 : ℝ) * Real.rpow N (1 - 2 * sigma)) := by
  let A := Real.rpow W (3 : ℝ) * Real.rpow N (1 - 2 * sigma)
  let B := Real.rpow W (21 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
    Real.rpow N (1 - 2 * sigma)
  let Q := Real.sqrt W * Real.rpow N (2 - 2 * sigma)
  let P := W * Real.rpow N (4 - 4 * sigma)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hCQ : (C * Q) ^ 2 = C ^ 2 * P := by
    calc
      (C * Q) ^ 2 = C ^ 2 * Q ^ 2 := by ring
      _ = C ^ 2 * P := by
        rw [show Q ^ 2 = P by
          dsimp [Q, P]
          exact energy_sqrt_coefficient_sq hW hN]
  have habs : E ≤ 2 * C * (A + B) + (C * Q) ^ 2 :=
    absorb_sqrt_energy hE hA hB hQ hC (by simpa [A, B, Q] using hraw)
  have htarget :
      2 * C * (A + B) + C ^ 2 * P ≤
        (2 * C + C ^ 2) * (P + B + A) := by
    have hextra : 0 ≤ 2 * C * P + C ^ 2 * B + C ^ 2 * A := by
      positivity
    calc
      2 * C * (A + B) + C ^ 2 * P ≤
          2 * C * (A + B) + C ^ 2 * P +
            (2 * C * P + C ^ 2 * B + C ^ 2 * A) :=
        le_add_of_nonneg_right hextra
      _ = (2 * C + C ^ 2) * (P + B + A) := by ring
  calc
    E ≤ 2 * C * (A + B) + (C * Q) ^ 2 := habs
    _ = 2 * C * (A + B) + C ^ 2 * P := by rw [hCQ]
    _ ≤ (2 * C + C ^ 2) * (P + B + A) := htarget
    _ = (2 * C + C ^ 2) *
        (W * Real.rpow N (4 - 4 * sigma) +
          Real.rpow W (21 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
            Real.rpow N (1 - 2 * sigma) +
          Real.rpow W (3 : ℝ) * Real.rpow N (1 - 2 * sigma)) := by
      rfl

/-- Proposition 11.1 from the literally factored source display, before the
outer `N^(-2 sigma)` is distributed. -/
theorem proposition11_1_of_literal_postLemma11_9
    {E W T N sigma C : ℝ}
    (hE : 0 ≤ E) (hW : 0 < W) (hT : 0 ≤ T)
    (hN : 0 < N) (hC : 0 ≤ C)
    (hraw :
      E ≤ C * (Real.rpow N (-2 * sigma) *
        (N * Real.rpow W (3 : ℝ) +
          N * Real.rpow T (1 / 4 : ℝ) * Real.rpow W (21 / 8 : ℝ) +
          Real.sqrt E * Real.sqrt W * N ^ 2))) :
    E ≤ (2 * C + C ^ 2) *
      (W * Real.rpow N (4 - 4 * sigma) +
        Real.rpow W (21 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
          Real.rpow N (1 - 2 * sigma) +
        Real.rpow W (3 : ℝ) * Real.rpow N (1 - 2 * sigma)) := by
  apply proposition11_1_of_postLemma11_9 hE hW hT hN hC
  rw [← postLemma11_9_normalization_identity hN]
  exact hraw

/-! ## Endpoint check inside Lemma 11.9 -/

/-- Exact inequality used in the low-cardinality case of (11.6).  The source
uses `E >= W^2`, `W <= T^(2/3)`, and `N >= T^(3/4)` to absorb the residual
factor.  This theorem certifies the endpoint exponents, including equality at
all three boundaries. -/
theorem lemma11_9_lowW_residual_absorption
    {T W E N : ℝ}
    (hT : 0 < T) (hW : 0 < W) (hE : 0 < E) (hN : 0 < N)
    (hWupper : W ≤ Real.rpow T (2 / 3 : ℝ))
    (henergyLower : Real.rpow W (2 : ℝ) ≤ E)
    (hNlower : Real.rpow T (3 / 4 : ℝ) ≤ N) :
    Real.rpow T (1 / 2 : ℝ) * Real.rpow W (5 / 8 : ℝ) ≤
      Real.rpow E (1 / 8 : ℝ) * N := by
  have hW38 : Real.rpow W (3 / 8 : ℝ) ≤ Real.rpow T (1 / 4 : ℝ) := by
    calc
      Real.rpow W (3 / 8 : ℝ) ≤
          Real.rpow (Real.rpow T (2 / 3 : ℝ)) (3 / 8 : ℝ) :=
        Real.rpow_le_rpow hW.le hWupper (by norm_num)
      _ = Real.rpow T ((2 / 3 : ℝ) * (3 / 8 : ℝ)) :=
        (Real.rpow_mul hT.le _ _).symm
      _ = Real.rpow T (1 / 4 : ℝ) := by norm_num
  have hWE : Real.rpow W (1 / 4 : ℝ) ≤ Real.rpow E (1 / 8 : ℝ) := by
    calc
      Real.rpow W (1 / 4 : ℝ) =
          Real.rpow W ((2 : ℝ) * (1 / 8 : ℝ)) := by norm_num
      _ = Real.rpow (Real.rpow W (2 : ℝ)) (1 / 8 : ℝ) :=
        Real.rpow_mul hW.le _ _
      _ ≤ Real.rpow E (1 / 8 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hW.le _) henergyLower (by norm_num)
  have hTW :
      Real.rpow T (1 / 2 : ℝ) * Real.rpow W (3 / 8 : ℝ) ≤
        Real.rpow T (3 / 4 : ℝ) := by
    calc
      Real.rpow T (1 / 2 : ℝ) * Real.rpow W (3 / 8 : ℝ) ≤
          Real.rpow T (1 / 2 : ℝ) * Real.rpow T (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hW38 (Real.rpow_nonneg hT.le _)
      _ = Real.rpow T ((1 / 2 : ℝ) + (1 / 4 : ℝ)) :=
        (Real.rpow_add hT _ _).symm
      _ = Real.rpow T (3 / 4 : ℝ) := by norm_num
  calc
    Real.rpow T (1 / 2 : ℝ) * Real.rpow W (5 / 8 : ℝ) =
        (Real.rpow T (1 / 2 : ℝ) * Real.rpow W (3 / 8 : ℝ)) *
          Real.rpow W (1 / 4 : ℝ) := by
      have hWsplit : Real.rpow W (5 / 8 : ℝ) =
          Real.rpow W (3 / 8 : ℝ) * Real.rpow W (1 / 4 : ℝ) := by
        calc
          Real.rpow W (5 / 8 : ℝ) =
              Real.rpow W ((3 / 8 : ℝ) + (1 / 4 : ℝ)) := by norm_num
          _ = Real.rpow W (3 / 8 : ℝ) * Real.rpow W (1 / 4 : ℝ) :=
            Real.rpow_add hW _ _
      rw [hWsplit]
      ring
    _ ≤ Real.rpow T (3 / 4 : ℝ) * Real.rpow W (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hTW (Real.rpow_nonneg hW.le _)
    _ ≤ N * Real.rpow E (1 / 8 : ℝ) :=
      mul_le_mul hNlower hWE (Real.rpow_nonneg hW.le _) hN.le
    _ = Real.rpow E (1 / 8 : ℝ) * N := by ring

/-- The two preliminary low-`W` dominance comparisons used to simplify
(11.4) into (11.6). -/
theorem lemma11_9_lowW_factor_absorptions
    {T W E N : ℝ}
    (hT : 1 ≤ T) (hW : 1 ≤ W) (hE : 0 < E) (hN : 0 ≤ N)
    (hWupper : W ≤ Real.rpow T (2 / 3 : ℝ))
    (henergyUpper : E ≤ Real.rpow W (3 : ℝ))
    (hNlower : Real.rpow T (3 / 4 : ℝ) ≤ N) :
    Real.rpow W (2 : ℝ) ≤
        Real.rpow W (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) ∧
      E * T ≤ Real.rpow E (3 / 4 : ℝ) * W *
        Real.rpow T (1 / 2 : ℝ) * N := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hW34T12 : Real.rpow W (3 / 4 : ℝ) ≤ Real.rpow T (1 / 2 : ℝ) := by
    calc
      Real.rpow W (3 / 4 : ℝ) ≤
          Real.rpow (Real.rpow T (2 / 3 : ℝ)) (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hWpos.le hWupper (by norm_num)
      _ = Real.rpow T ((2 / 3 : ℝ) * (3 / 4 : ℝ)) :=
        (Real.rpow_mul hTpos.le _ _).symm
      _ = Real.rpow T (1 / 2 : ℝ) := by norm_num
  have hE14W34 : Real.rpow E (1 / 4 : ℝ) ≤ Real.rpow W (3 / 4 : ℝ) := by
    calc
      Real.rpow E (1 / 4 : ℝ) ≤
          Real.rpow (Real.rpow W (3 : ℝ)) (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hE.le henergyUpper (by norm_num)
      _ = Real.rpow W ((3 : ℝ) * (1 / 4 : ℝ)) :=
        (Real.rpow_mul hWpos.le _ _).symm
      _ = Real.rpow W (3 / 4 : ℝ) := by norm_num
  have hT12N : Real.rpow T (1 / 2 : ℝ) ≤ N :=
    (Real.rpow_le_rpow_of_exponent_le hT (by norm_num)).trans hNlower
  have hW34W : Real.rpow W (3 / 4 : ℝ) ≤ W := by
    calc
      Real.rpow W (3 / 4 : ℝ) ≤ Real.rpow W (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hW (by norm_num)
      _ = W := Real.rpow_one W
  constructor
  · calc
      Real.rpow W (2 : ℝ) =
          Real.rpow W (5 / 4 : ℝ) * Real.rpow W (3 / 4 : ℝ) := by
        calc
          Real.rpow W (2 : ℝ) =
              Real.rpow W ((5 / 4 : ℝ) + (3 / 4 : ℝ)) := by norm_num
          _ = Real.rpow W (5 / 4 : ℝ) * Real.rpow W (3 / 4 : ℝ) :=
            Real.rpow_add hWpos _ _
      _ ≤ Real.rpow W (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hW34T12 (Real.rpow_nonneg hWpos.le _)
  · have hEsplit : E =
        Real.rpow E (3 / 4 : ℝ) * Real.rpow E (1 / 4 : ℝ) := by
      calc
        E = Real.rpow E (1 : ℝ) := (Real.rpow_one E).symm
        _ = Real.rpow E ((3 / 4 : ℝ) + (1 / 4 : ℝ)) := by norm_num
        _ = Real.rpow E (3 / 4 : ℝ) * Real.rpow E (1 / 4 : ℝ) :=
          Real.rpow_add hE _ _
    have hTsplit : T =
        Real.rpow T (1 / 2 : ℝ) * Real.rpow T (1 / 2 : ℝ) := by
      calc
        T = Real.rpow T (1 : ℝ) := (Real.rpow_one T).symm
        _ = Real.rpow T ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by norm_num
        _ = Real.rpow T (1 / 2 : ℝ) * Real.rpow T (1 / 2 : ℝ) :=
          Real.rpow_add hTpos _ _
    calc
      E * T =
        (Real.rpow E (3 / 4 : ℝ) * Real.rpow E (1 / 4 : ℝ)) *
          (Real.rpow T (1 / 2 : ℝ) * Real.rpow T (1 / 2 : ℝ)) := by
        exact congrArg₂ (fun x y : ℝ => x * y) hEsplit hTsplit
      _ ≤
        (Real.rpow E (3 / 4 : ℝ) * Real.rpow W (3 / 4 : ℝ)) *
          (Real.rpow T (1 / 2 : ℝ) * N) := by
        have hleft :
            Real.rpow E (3 / 4 : ℝ) * Real.rpow E (1 / 4 : ℝ) ≤
              Real.rpow E (3 / 4 : ℝ) * Real.rpow W (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hE14W34 (Real.rpow_nonneg hE.le _)
        have hright :
            Real.rpow T (1 / 2 : ℝ) * Real.rpow T (1 / 2 : ℝ) ≤
              Real.rpow T (1 / 2 : ℝ) * N :=
          mul_le_mul_of_nonneg_left hT12N (Real.rpow_nonneg hTpos.le _)
        exact mul_le_mul hleft hright
          (mul_nonneg (Real.rpow_nonneg hTpos.le _) (Real.rpow_nonneg hTpos.le _))
          (mul_nonneg (Real.rpow_nonneg hE.le _) (Real.rpow_nonneg hWpos.le _))
      _ ≤ (Real.rpow E (3 / 4 : ℝ) * W) *
          (Real.rpow T (1 / 2 : ℝ) * N) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hW34W (Real.rpow_nonneg hE.le _)
        · exact mul_nonneg (Real.rpow_nonneg hTpos.le _) hN
      _ = Real.rpow E (3 / 4 : ℝ) * W *
          Real.rpow T (1 / 2 : ℝ) * N := by ring

/-- The two dominance comparisons used in the high-cardinality case of
Lemma 11.9.  They certify the source's transition from (11.4) to (11.5). -/
theorem lemma11_9_highW_factor_absorptions
    {T W E N : ℝ}
    (hT : 0 < T) (hW : 0 < W) (hE : 0 ≤ E) (hN : 0 ≤ N)
    (hWlower : Real.rpow T (2 / 3 : ℝ) ≤ W)
    (henergyUpper : E ≤ Real.rpow W (3 : ℝ)) :
    Real.rpow W (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) ≤
        Real.rpow W (2 : ℝ) ∧
      Real.rpow E (3 / 4 : ℝ) * W * Real.rpow T (1 / 2 : ℝ) * N ≤
        N * Real.rpow W (4 : ℝ) := by
  have hT12 : Real.rpow T (1 / 2 : ℝ) ≤ Real.rpow W (3 / 4 : ℝ) := by
    calc
      Real.rpow T (1 / 2 : ℝ) =
          Real.rpow (Real.rpow T (2 / 3 : ℝ)) (3 / 4 : ℝ) := by
        calc
          Real.rpow T (1 / 2 : ℝ) =
              Real.rpow T ((2 / 3 : ℝ) * (3 / 4 : ℝ)) := by norm_num
          _ = Real.rpow (Real.rpow T (2 / 3 : ℝ)) (3 / 4 : ℝ) :=
            Real.rpow_mul hT.le _ _
      _ ≤ Real.rpow W (3 / 4 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hT.le _) hWlower (by norm_num)
  have hE34 : Real.rpow E (3 / 4 : ℝ) ≤ Real.rpow W (9 / 4 : ℝ) := by
    calc
      Real.rpow E (3 / 4 : ℝ) ≤
          Real.rpow (Real.rpow W (3 : ℝ)) (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hE henergyUpper (by norm_num)
      _ = Real.rpow W ((3 : ℝ) * (3 / 4 : ℝ)) :=
        (Real.rpow_mul hW.le _ _).symm
      _ = Real.rpow W (9 / 4 : ℝ) := by norm_num
  constructor
  · calc
      Real.rpow W (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) ≤
          Real.rpow W (5 / 4 : ℝ) * Real.rpow W (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hT12 (Real.rpow_nonneg hW.le _)
      _ = Real.rpow W ((5 / 4 : ℝ) + (3 / 4 : ℝ)) :=
        (Real.rpow_add hW _ _).symm
      _ = Real.rpow W (2 : ℝ) := by norm_num
  · have hprod :
        Real.rpow E (3 / 4 : ℝ) * W * Real.rpow T (1 / 2 : ℝ) ≤
          Real.rpow W (9 / 4 : ℝ) * W * Real.rpow W (3 / 4 : ℝ) := by
      have hEW : Real.rpow E (3 / 4 : ℝ) * W ≤
          Real.rpow W (9 / 4 : ℝ) * W :=
        mul_le_mul_of_nonneg_right hE34 hW.le
      exact mul_le_mul hEW hT12 (Real.rpow_nonneg hT.le _)
        (mul_nonneg (Real.rpow_nonneg hW.le _) hW.le)
    have hWproduct :
        Real.rpow W (9 / 4 : ℝ) * W * Real.rpow W (3 / 4 : ℝ) =
          Real.rpow W (4 : ℝ) := by
      calc
        Real.rpow W (9 / 4 : ℝ) * W * Real.rpow W (3 / 4 : ℝ) =
            (Real.rpow W (9 / 4 : ℝ) * Real.rpow W (3 / 4 : ℝ)) * W := by
          ring
        _ = Real.rpow W ((9 / 4 : ℝ) + (3 / 4 : ℝ)) * W := by
          have hadd : Real.rpow W (9 / 4 : ℝ) * Real.rpow W (3 / 4 : ℝ) =
              Real.rpow W ((9 / 4 : ℝ) + (3 / 4 : ℝ)) :=
            (Real.rpow_add hW _ _).symm
          rw [hadd]
        _ = Real.rpow W (3 : ℝ) * W := by norm_num
        _ = Real.rpow W (3 : ℝ) * Real.rpow W (1 : ℝ) := by
          congr 1
          exact (Real.rpow_one W).symm
        _ = Real.rpow W ((3 : ℝ) + (1 : ℝ)) :=
          (Real.rpow_add hW _ _).symm
        _ = Real.rpow W (4 : ℝ) := by norm_num
    calc
      Real.rpow E (3 / 4 : ℝ) * W * Real.rpow T (1 / 2 : ℝ) * N ≤
          (Real.rpow W (9 / 4 : ℝ) * W * Real.rpow W (3 / 4 : ℝ)) * N :=
        mul_le_mul_of_nonneg_right hprod hN
      _ = N * Real.rpow W (4 : ℝ) := by rw [hWproduct]; ring

/-- The remaining high-`W` comparison in Lemma 11.9:
`E*T <= N*W^4`.  The paper uses `E <= W^3`, `W >= T^(2/3)`, and
`N >= T^(3/4)` (more than the needed `T^(1/3)`). -/
theorem lemma11_9_highW_energy_time_absorption
    {T W E N : ℝ}
    (hT : 1 ≤ T) (hW : 0 < W) (hE : 0 ≤ E) (hN : 0 ≤ N)
    (hWlower : Real.rpow T (2 / 3 : ℝ) ≤ W)
    (hNlower : Real.rpow T (3 / 4 : ℝ) ≤ N)
    (henergyUpper : E ≤ Real.rpow W (3 : ℝ)) :
    E * T ≤ N * Real.rpow W (4 : ℝ) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hNthird : Real.rpow T (1 / 3 : ℝ) ≤ N := by
    exact (Real.rpow_le_rpow_of_exponent_le hT (by norm_num)).trans hNlower
  have hTN : T ≤ N * W := by
    have hmul :
        Real.rpow T (1 / 3 : ℝ) * Real.rpow T (2 / 3 : ℝ) ≤ N * W :=
      mul_le_mul hNthird hWlower (Real.rpow_nonneg hTpos.le _) hN
    calc
      T = Real.rpow T ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := by
        norm_num
      _ = Real.rpow T (1 / 3 : ℝ) * Real.rpow T (2 / 3 : ℝ) :=
        Real.rpow_add hTpos _ _
      _ ≤ N * W := hmul
  calc
    E * T ≤ Real.rpow W (3 : ℝ) * T :=
      mul_le_mul_of_nonneg_right henergyUpper hTpos.le
    _ ≤ Real.rpow W (3 : ℝ) * (N * W) :=
      mul_le_mul_of_nonneg_left hTN (Real.rpow_nonneg hW.le _)
    _ = N * (Real.rpow W (3 : ℝ) * Real.rpow W (1 : ℝ)) := by
      have haux : Real.rpow W (3 : ℝ) * W =
          Real.rpow W (3 : ℝ) * Real.rpow W (1 : ℝ) :=
        congrArg (fun x : ℝ => Real.rpow W (3 : ℝ) * x)
          (Real.rpow_one W).symm
      calc
        Real.rpow W (3 : ℝ) * (N * W) =
            N * (Real.rpow W (3 : ℝ) * W) := by ring
        _ = N * (Real.rpow W (3 : ℝ) * Real.rpow W (1 : ℝ)) :=
          congrArg (fun x : ℝ => N * x) haux
    _ = N * Real.rpow W ((3 : ℝ) + (1 : ℝ)) := by
      exact congrArg (fun x : ℝ => N * x) (Real.rpow_add hW _ _).symm
    _ = N * Real.rpow W (4 : ℝ) := by norm_num

/-! ## Arithmetic spacing input in Lemma 11.8 -/

/-- Distinct rational numbers with positive natural denominators are separated
by the reciprocal product of their denominators.  This is the exact
arithmetic fact behind the source's `d^2/N^2` spacing assertion for reduced
fractions in Lemma 11.8. -/
theorem distinct_nat_fraction_separation
    {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hcross : a * d ≠ c * b) :
    (1 : ℝ) / ((b : ℝ) * (d : ℝ)) ≤
      |(a : ℝ) / (b : ℝ) - (c : ℝ) / (d : ℝ)| := by
  let k : ℤ := (a : ℤ) * (d : ℤ) - (c : ℤ) * (b : ℤ)
  have hk : k ≠ 0 := by
    intro hk0
    apply hcross
    have hkEq : (a : ℤ) * (d : ℤ) = (c : ℤ) * (b : ℤ) :=
      sub_eq_zero.mp hk0
    exact_mod_cast hkEq
  have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  have hden : 0 < (b : ℝ) * (d : ℝ) := by positivity
  have hfrac : (1 : ℝ) / ((b : ℝ) * (d : ℝ)) ≤
      |(k : ℝ)| / ((b : ℝ) * (d : ℝ)) :=
    div_le_div_of_nonneg_right hkabs hden.le
  calc
    (1 : ℝ) / ((b : ℝ) * (d : ℝ)) ≤
        |(k : ℝ)| / ((b : ℝ) * (d : ℝ)) := hfrac
    _ = |(k : ℝ) / ((b : ℝ) * (d : ℝ))| := by
      rw [abs_div, abs_of_pos hden]
    _ = |(a : ℝ) / (b : ℝ) - (c : ℝ) / (d : ℝ)| := by
      congr 1
      dsimp [k]
      push_cast
      field_simp

/-- Uniform denominator-box form used for packing the fractions in a
`1/T`-window. -/
theorem distinct_nat_fraction_separation_of_denominator_le
    {a b c d : ℕ} {B : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hB : 0 < B)
    (hbB : (b : ℝ) ≤ B) (hdB : (d : ℝ) ≤ B)
    (hcross : a * d ≠ c * b) :
    (1 : ℝ) / B ^ 2 ≤
      |(a : ℝ) / (b : ℝ) - (c : ℝ) / (d : ℝ)| := by
  have hden : 0 < (b : ℝ) * (d : ℝ) := by positivity
  have hprod : (b : ℝ) * (d : ℝ) ≤ B ^ 2 := by
    calc
      (b : ℝ) * (d : ℝ) ≤ B * B :=
        mul_le_mul hbB hdB (Nat.cast_nonneg _) hB.le
      _ = B ^ 2 := by ring
  exact (one_div_le_one_div_of_le hden hprod).trans
    (distinct_nat_fraction_separation hb hd hcross)

/-- Exact cutoff arithmetic following Lemma 11.8: choosing `D=N^2/T`
turns `D*T+N^2` into `2*N^2`, with no hidden loss. -/
theorem lemma11_8_cutoff_identity {N T : ℝ} (hT : 0 < T) :
    (N ^ 2 / T) * T + N ^ 2 = 2 * N ^ 2 := by
  field_simp [hT.ne']
  ring


/-! ## Exact S3 exponents in equation (12.1) -/

/-- Solving the first Proposition 11.2 term
`T^2 W^(3/2)` against the left side `W^3 N^(6*sigma-3)` gives
`T^(4/3) N^(2-4*sigma)`. -/
theorem s3_first_equation12_1_exponents (sigma : ℝ) :
    (2 : ℝ) / (3 - 3 / 2) = 4 / 3 ∧
      -(6 * sigma - 3) / (3 - 3 / 2) = 2 - 4 * sigma := by
  constructor <;> ring

/-- The second Proposition 11.2 term gives
`T^(1/2) N^(3-4*sigma)`. -/
theorem s3_second_equation12_1_exponents (sigma : ℝ) :
    (1 : ℝ) / (3 - 1) = 1 / 2 ∧
      ((3 - 2 * sigma) - (6 * sigma - 3)) / (3 - 1) =
        3 - 4 * sigma := by
  constructor <;> ring

/-- The third Proposition 11.2 term gives
`T N^(9/2-7*sigma)`. -/
theorem s3_third_equation12_1_exponents (sigma : ℝ) :
    (1 : ℝ) / (3 - 2) = 1 ∧
      ((3 / 2 - sigma) - (6 * sigma - 3)) / (3 - 2) =
        9 / 2 - 7 * sigma := by
  constructor <;> ring

/-- The affine/energy term gives the last term in equation (12.1),
`T^(18/19) N^(72/19-112*sigma/19)`. -/
theorem s3_fourth_equation12_1_exponents (sigma : ℝ) :
    (9 / 8 : ℝ) / (3 - 29 / 16) = 18 / 19 ∧
      ((3 / 2 - sigma) - (6 * sigma - 3)) / (3 - 29 / 16) =
        72 / 19 - 112 * sigma / 19 := by
  constructor <;> ring


end

end GuthMaynardS3Source

#print axioms GuthMaynardS3Source.sqrt_energyTerm_two
#print axioms GuthMaynardS3Source.proposition11_2_of_10_1_and_11_1
#print axioms GuthMaynardS3Source.proposition10_1_of_affine_secondMoment
#print axioms GuthMaynardS3Source.affine_iteration_scalar_absorption
#print axioms GuthMaynardS3Source.three_halves_epsilon_descent
#print axioms GuthMaynardS3Source.exists_three_halves_depth
#print axioms GuthMaynardS3Source.epsilon_induction_of_three_halves_step
#print axioms GuthMaynardS3Source.absorb_sqrt_energy
#print axioms GuthMaynardS3Source.energy_sqrt_coefficient_sq
#print axioms GuthMaynardS3Source.postLemma11_9_normalization_identity
#print axioms GuthMaynardS3Source.proposition11_1_of_postLemma11_9
#print axioms GuthMaynardS3Source.proposition11_1_of_literal_postLemma11_9
#print axioms GuthMaynardS3Source.lemma11_9_lowW_residual_absorption
#print axioms GuthMaynardS3Source.lemma11_9_lowW_factor_absorptions
#print axioms GuthMaynardS3Source.lemma11_9_highW_factor_absorptions
#print axioms GuthMaynardS3Source.lemma11_9_highW_energy_time_absorption
#print axioms GuthMaynardS3Source.distinct_nat_fraction_separation
#print axioms GuthMaynardS3Source.distinct_nat_fraction_separation_of_denominator_le
#print axioms GuthMaynardS3Source.lemma11_8_cutoff_identity
#print axioms GuthMaynardS3Source.s3_fourth_equation12_1_exponents
