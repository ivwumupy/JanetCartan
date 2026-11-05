module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Literal
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Interpolation

/-!
# Additive differential commutator bound on compact tests

The scalar Euclidean estimate `app:ch_background:eq:bg-commutator`. The fixed
low budget includes the first physical derivative. Interpolation of the actual
transferred amplitudes is combined with datum interpolation, so the high budget
multiplies only L². The continuum normal producer must supply these primitive
budgets; these hypotheses are not bounds on the commutator itself.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

private theorem norm_list_sum_le (l : List (Lp ℂ 2 (volume : Measure E))) :
    ‖l.sum‖ ≤ (l.map norm).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simpa only [List.sum_cons, List.map_cons] using
      (norm_add_le a l.sum).trans (add_le_add le_rfl ih)

/-- `app:ch_background:eq:bg-commutator`: each surviving actual L² branch
satisfies the additive estimate after joint interpolation. -/
theorem norm_commutator_branch_le
    (hd : 0 < d) (R : ℝ) (n : ℕ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A K H : ℝ) (hK : 0 ≤ K)
    (is : List (Fin d)) (hlen : is.length = n + 1)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) A)
    (hbudget : ∀ j, j ≤ n → HasAmplitudeDerivativeBound b (2 * (d + 1) + 1 + j)
      (K * (max 1 H) ^ ((j : ℝ) / n)))
    (p : {p // p ∈ differentialCommutatorTerms is})
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    let f := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
    ‖orderedTransferTermL2Operator hd R b hb hs A is hA
        ⟨p.val, differentialCommutatorTerms_mem_transfer is p.val p.property⟩
        (((contDiff_euclideanCoordinateDerivList hu p.val.2).continuous.memLp_of_hasCompactSupport
          (hasCompactSupport_euclideanCoordinateDerivList hus p.val.2)).toLp
            (euclideanCoordinateDerivList p.val.2 u))‖ ≤
      (fixedBoxAmplitudeConstant d R * (2 ^ (n + 1) * K) *
        (1 + 2 * Real.pi) ^ (n + 1)) *
          (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  dsimp only
  let f : L² := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
  let g : L² := ((contDiff_euclideanCoordinateDerivList hu p.val.2).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_euclideanCoordinateDerivList hus p.val.2)).toLp
      (euclideanCoordinateDerivList p.val.2 u)
  let W := (max 1 H) ^ (((p.val.1.length - 1 : ℕ) : ℝ) / n)
  let S := fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖
  have hp := differentialCommutatorTerms_spec is p.val p.property
  have hb' : ∀ ξ, ContDiff ℝ ∞ (b ξ) :=
    fun _ => hb.comp (contDiff_const.prodMk contDiff_id)
  have ht := commutator_transfer_geometric_bound n b hb' K H hbudget is hlen p.val p.property
  have hop := norm_twoPositionL2Operator_apply_le hd R (iteratedTransferAmplitude b p.val.1)
    (contDiff_uncurry_iteratedTransferAmplitude hb p.val.1)
    (supportedInCenteredBox_iteratedTransferAmplitude b R hs p.val.1) _ ht g
  have hg : ‖g‖ ≤ (2 * Real.pi) ^ p.val.2.length *
      fourierSobolevNorm (p.val.2.length : ℝ) f := by
    simpa only [Nat.cast_zero, zero_add, fourierSobolevNorm_zero] using
      fourierSobolevNorm_coordinateDerivList_toLp_le p.val.2 0 u hu hus
  have hj : W * fourierSobolevNorm (p.val.2.length : ℝ) f ≤ S :=
    commutator_geometric_weight_mul_sobolev_le n p.val.1.length p.val.2.length
      hp.1 (by omega) H f (memFourierSobolev_nat_toLp n u hu hus)
  have hW : 0 ≤ W := Real.rpow_nonneg (by positivity) _
  have hS : 0 ≤ S := add_nonneg (fourierSobolevNorm_nonneg _ _) (by positivity)
  have hC := fixedBoxAmplitudeConstant_nonneg d R
  have hr : (2 : ℝ) ^ p.val.1.length ≤ 2 ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hk : (2 * Real.pi) ^ p.val.2.length ≤ (1 + 2 * Real.pi) ^ (n + 1) :=
    (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith [Real.pi_pos]) (by omega))
  calc
    _ ≤ (fixedBoxAmplitudeConstant d R * (2 ^ p.val.1.length * (K * W))) * ‖g‖ := hop
    _ ≤ (fixedBoxAmplitudeConstant d R * (2 ^ p.val.1.length * (K * W))) *
        ((2 * Real.pi) ^ p.val.2.length * fourierSobolevNorm (p.val.2.length : ℝ) f) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (fixedBoxAmplitudeConstant d R * (2 ^ p.val.1.length * K) *
        (2 * Real.pi) ^ p.val.2.length) *
        (W * fourierSobolevNorm (p.val.2.length : ℝ) f) := by ring
    _ ≤ (fixedBoxAmplitudeConstant d R * (2 ^ p.val.1.length * K) *
        (2 * Real.pi) ^ p.val.2.length) * S :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hS
      apply mul_le_mul _ hk (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hK) hC

/-- `app:ch_background:eq:bg-commutator` on smooth compact tests, with
`|α| = n + 1`. A single shift `B = 2 * (d + 1)` works for every order; the
constant is chosen before the amplitude, high budget, derivative word, and datum.
The high primitive bound is additive, multiplying only the input L² norm. -/
theorem exists_differentialCommutatorCompactL2_tame_constant
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ),
        HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M →
        ∀ (is : List (Fin d)) (_hlen : is.length = n + 1)
          (hH : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) H)
          (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u),
          let f := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
          ‖differentialCommutatorCompactL2 hd R b hb hs H is hH u hu hus‖ ≤
            C * (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨K, hK, hbudget⟩ := exists_commutator_geometric_budget d n M
  let L := fixedBoxAmplitudeConstant d R * (2 ^ (n + 1) * K) *
    (1 + 2 * Real.pi) ^ (n + 1)
  have hC := fixedBoxAmplitudeConstant_nonneg d R
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨(2 : ℝ) ^ (n + 1) * L, by positivity, ?_⟩
  intro b hb hs H hM is hlen hH u hu hus
  dsimp only
  let f : L² := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
  let S := fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖
  have hS : 0 ≤ S := add_nonneg (fourierSobolevNorm_nonneg _ _) (by positivity)
  have hB := hbudget b (fun _ => hb.comp (contDiff_const.prodMk contDiff_id)) H hM
    (by simpa only [hlen] using hH)
  have he := fun p => norm_commutator_branch_le hd R n b hb hs H K H hK.le is hlen hH hB p u hu hus
  have hcard : ((differentialCommutatorTerms is).length : ℝ) ≤ 2 ^ (n + 1) := by
    have hc := differentialCommutatorTerms_length is
    have : (differentialCommutatorTerms is).length ≤ 2 ^ (n + 1) := by rw [hlen] at hc; omega
    exact_mod_cast this
  unfold differentialCommutatorCompactL2
  calc
    _ ≤ _ := norm_list_sum_le _
    _ ≤ ((differentialCommutatorTerms is).attach.map fun _ => L * S).sum := by
      rw [List.map_map]
      exact List.sum_le_sum (fun p _ => he p)
    _ = (differentialCommutatorTerms is).length * (L * S) := by simp
    _ ≤ (2 : ℝ) ^ (n + 1) * (L * S) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hL hS)
    _ = _ := by ring

end JanetCartan.Pseudodifferential
