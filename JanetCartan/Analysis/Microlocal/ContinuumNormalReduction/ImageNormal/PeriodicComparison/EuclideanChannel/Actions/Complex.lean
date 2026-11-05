module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.EuclideanChannel.Basic
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.TestL2

/-!
# Schwartz actions of the concrete complex Euclidean channel

The bounded matrix operator realizes `μ P J χ` on Schwartz families, and
its literal Hilbert adjoint realizes `χ J P* μ`. These identities supply
the real channel actions in `normal_schwartz_action_of_channel_actions`
(`app:ch_background:prop:bg-frame`, Step 1).
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open JanetCartan.ContinuumNormal JanetCartan.PeriodicLocalL2
namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => 𝓢(E, ℂ)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin d)) 2 (volume : Measure E)
local notation "R²" => EuclideanL2 d E

private theorem multiplier_toLp (c : E → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcc : HasCompactSupport c) (u : S) :
    freezingPhysicalMultiplier c hc.continuous hcc (u.toLp 2) =
      (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (c x : ℂ)) u).toLp 2 := by
  have ht := hcc.hasTemperateGrowth hc
  have htc : (fun x ↦ (c x : ℂ)).HasTemperateGrowth := by fun_prop
  apply Lp.ext
  filter_upwards [freezingPhysicalMultiplier_coeFn c hc.continuous hcc (u.toLp 2),
    u.coeFn_toLp 2,
    (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (c x : ℂ)) u).coeFn_toLp 2] with x hx hu hv
  rw [hx, hu, hv, SchwartzMap.smulLeftCLM_apply_apply htc, Complex.real_smul,
    smul_eq_mul]

variable (A : EuclideanSpace ℝ (Fin d) → Fin d → Matrix (Fin d) (Fin d) ℝ)
  (Z : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (χ μ : EuclideanSpace ℝ (Fin d) → ℝ)
  (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
  (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
  (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
  (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)

/-- The concrete bounded channel acts as the literal Schwartz factor
`μ P J χ` (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexEuclideanChannel_toLp (v : Fin d → S) :
    complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc (imageSchwartzFamilyToLp v) =
      imageSchwartzFamilyToLp (channelSchwartz A Z χ μ v) := by
  apply (finiteL2CoordinateIsometry volume).injective
  ext i : 1
  simp only [complexEuclideanChannel, finiteL2CoordinateIsometry_vectorMatrixL2Operator,
    matrixOperator_apply, imageSchwartzFamilyToLp_coordinates,
    euclideanChannelBlock, ContinuousLinearMap.comp_apply, add_apply, sum_apply,
    multiplier_toLp χ hχ hχc, imageDerivativeBesselL2Operator_toLp,
    imageBesselL2Operator_toLp]
  simp only [← imageBesselSchwartzCLM_apply,
    multiplier_toLp _ (hμ.mul (hA _ _ _)) hμc.mul_right,
    multiplier_toLp _ (hμ.mul (hZ _ _)) hμc.mul_right,
    channelSchwartz, maskedCoefficientSchwartzCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.pi_apply, add_apply, sum_apply, ContinuousLinearMap.proj_apply,
    LineDeriv.lineDerivOpCLM_apply]
  simp only [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_add, map_sum]
  rw [Finset.sum_add_distrib, Finset.sum_comm]

private theorem realMask_pairing (c : E → ℝ) (hc : c.HasTemperateGrowth) (u v : S) :
    imageSchwartzPairing (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (c x : ℂ)) u) v =
      imageSchwartzPairing u (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (c x : ℂ)) v) := by
  have htc : (fun x ↦ (c x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [imageSchwartzPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply htc, smul_eq_mul, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  ring

include hA hZ hχ hχc hμ hμc in
/-- Integration by parts retains the full divergence-form adjoint
`χ J P* μ` (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem channelSchwartz_pairing (u v : Fin d → S) :
    (∑ i, imageSchwartzPairing (channelSchwartz A Z χ μ u i) (v i)) =
      ∑ i, imageSchwartzPairing (u i) (channelAdjointSchwartz A Z χ μ v i) := by
  change (∑ i, imageSchwartzPairing (maskedCoefficientSchwartzCLM A Z μ
    (fun j ↦ imageBesselSchwartzCLM (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) (u j))) i)
    (v i)) = _
  rw [maskedCoefficientSchwartzCLM_pairing A Z μ hA hZ hμ hμc]
  simp_rw [imageBesselSchwartzCLM_pairing, realMask_pairing χ (hχc.hasTemperateGrowth hχ)]
  rfl

/-- The Hilbert adjoint of the same bounded channel has the literal
reversed Schwartz action (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexEuclideanChannel_adjoint_toLp (v : Fin d → S) :
    (complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc).adjoint
        (imageSchwartzFamilyToLp v) =
      imageSchwartzFamilyToLp (channelAdjointSchwartz A Z χ μ v) := by
  apply denseRange_imageSchwartzFamilyToLp.eq_of_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, complexEuclideanChannel_toLp,
    imageSchwartzFamilyToLp_inner, imageSchwartzFamilyToLp_inner]
  exact channelSchwartz_pairing A Z χ μ hA hZ hχ hχc hμ hμc u v
end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
