import GuthMaynardS3CubicHorizonMomentTail

open scoped Real
noncomputable section
namespace GuthMaynardS3BlockTailLedger

open GuthMaynardS3CubicHorizonTail
open GuthMaynardS3CubicHorizonMomentTail

/-- Literal ledger for the two cubic-horizon error tails.  The only input to
this adapter is the scalar geometry of the selected block; all source and
horizon tails are supplied by the preceding certified lemmas. -/
theorem block_tail_ledger
    {T epsilon rho n K R L D C A B : ℝ}
    (hT : 1 ≤ T) (heps : epsilon ≤ 1)
    (hr0 : 0 ≤ rho) (hr : rho ≤ T)
    (hn0 : 0 ≤ n) (hn : n ≤ T)
    (hKpos : 0 < K) (hK : K ≤ T^2)
    (hR0 : 0 ≤ R) (hR : R ≤ 2*T)
    (hL0 : 0 ≤ L) (hL : L ≤ 8*K)
    (hD0 : 0 ≤ D) (hC0 : 0 ≤ C) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    8*(16*D*rho*n^2/K)^2*A*R*L^2*C*(64*T^3)^epsilon *
      ((4*K)^4*(B*T^(-400 : ℝ)) + (4*K)^4/(64*T^3)^100) ≤
      (2^19*D^2*C*A)*(128+8192*B)*T^(-282 : ℝ) := by
  let P : ℝ := rho^2*n^4*K^2*R*L^2
  have hP0 : 0 ≤ P := by
    dsimp [P]
    positivity
  have hP : P ≤ 128*T^15 := by
    dsimp [P]
    exact block_error_prefactor_le hT hr0 hr hn0 hn hKpos.le hK hR0 hR hL0 hL
  have hpoly := polynomial_prefactor_cubic_tail hT heps hP0 hP
  have hmom := source_moment_tail_after_cubic_prefactor hT heps hP0 hP
  have hT382 : T^(-382 : ℝ) ≤ T^(-282 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hfirst : B*(P*(64*T^3)^epsilon*T^(-400 : ℝ)) ≤
      8192*B*T^(-282 : ℝ) := by
    calc
      B*(P*(64*T^3)^epsilon*T^(-400 : ℝ)) ≤
          B*(8192*T^(-382 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmom hB0
      _ ≤ 8192*B*T^(-282 : ℝ) := by
        have hh : 8192*T^(-382 : ℝ) ≤ 8192*T^(-282 : ℝ) :=
          mul_le_mul_of_nonneg_left hT382 (by norm_num)
        have hh' := mul_le_mul_of_nonneg_left hh hB0
        nlinarith
  have hsecond : P*(64*T^3)^epsilon*(1/(64*T^3)^100) ≤
      128*T^(-282 : ℝ) := by
    calc
      P*(64*T^3)^epsilon*(1/(64*T^3)^100) =
          P*((64*T^3)^epsilon/(64*T^3)^100) := by ring
      _ ≤ 128*T^(-282 : ℝ) := hpoly
  have htail : P*(64*T^3)^epsilon *
      (B*T^(-400 : ℝ) + 1/(64*T^3)^100) ≤
      (128+8192*B)*T^(-282 : ℝ) := by
    calc
      P*(64*T^3)^epsilon *
          (B*T^(-400 : ℝ) + 1/(64*T^3)^100) =
          B*(P*(64*T^3)^epsilon*T^(-400 : ℝ)) +
            P*(64*T^3)^epsilon*(1/(64*T^3)^100) := by ring
      _ ≤ 8192*B*T^(-282 : ℝ) + 128*T^(-282 : ℝ) :=
        add_le_add hfirst hsecond
      _ = (128+8192*B)*T^(-282 : ℝ) := by ring
  have hfactor : 0 ≤ (2^19 : ℝ)*D^2*C*A := by positivity
  calc
    8*(16*D*rho*n^2/K)^2*A*R*L^2*C*(64*T^3)^epsilon *
        ((4*K)^4*(B*T^(-400 : ℝ)) + (4*K)^4/(64*T^3)^100) =
        ((2^19 : ℝ)*D^2*C*A) *
          (P*(64*T^3)^epsilon *
            (B*T^(-400 : ℝ) + 1/(64*T^3)^100)) := by
          dsimp [P]
          field_simp [ne_of_gt hKpos]
          ring
    _ ≤ ((2^19 : ℝ)*D^2*C*A) *
          ((128+8192*B)*T^(-282 : ℝ)) :=
      mul_le_mul_of_nonneg_left htail hfactor
    _ = (2^19*D^2*C*A)*(128+8192*B)*T^(-282 : ℝ) := by ring

end GuthMaynardS3BlockTailLedger

#print axioms GuthMaynardS3BlockTailLedger.block_tail_ledger
