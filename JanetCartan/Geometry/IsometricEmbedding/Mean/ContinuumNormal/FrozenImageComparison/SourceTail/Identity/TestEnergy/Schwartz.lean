module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Identity.KernelAction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Identity.TestSpace
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.FourierEnergy.Reality

/-!
# Compact-test adjoints for the source-square energy

These are the Schwartz adjoint and plateau-removal inputs to
`fixedSourceTail_energy_eq_inner_of_test`, for `paper-v2.tex`,
`app:ch_background:prop:bg-frame`. The adjoint is identified by the existing
Lebesgue integration-by-parts theorem, without a Fourier-energy identity.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter LineDeriv
open scoped ContDiff SchwartzMap Topology
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open JanetCartan.ContinuumRow
open JanetCartan.ContinuumNormalReduction.ImageNormal
open JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

namespace JanetCartan.ContinuumNormal.FrozenImageComparison.SourceTailTestEnergy
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "S" => 𝓢(E, ℂ)

/-- The uncut constant differential channel on Schwartz families, used to
identify its bounded adjoint (`app:ch_background:prop:bg-frame`). -/
def uncutSchwartz (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → S) (i : Fin n) : S :=
  ∑ j, ∑ a, (A a i j : ℂ) •
    lineDerivOp (EuclideanSpace.single a (1 : ℝ)) (imageBesselSchwartzCLM (v j))

/-- The actual compact differential source factor `P* (χ v)`
(`app:ch_background:prop:bg-frame`). -/
def adjointFactor (hR : 0 < R) (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → S) : Fin n → S :=
  maskedCoefficientAdjointSchwartzCLM (fun _ ↦ A) (fun _ ↦ 0)
    (FixedCutoffs.physical hR 0) v

/-- The existing bounded channel realizes the displayed Schwartz action
(`app:ch_background:prop:bg-frame`). -/
theorem uncutSchwartz_toLp (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → S) :
    uncutComplexChannel A (imageSchwartzFamilyToLp v) =
      imageSchwartzFamilyToLp (uncutSchwartz A v) := by
  apply (finiteL2CoordinateIsometry volume).injective
  ext i : 1
  simp only [uncutComplexChannel, finiteL2CoordinateIsometry_vectorMatrixL2Operator,
    matrixOperator_apply, imageSchwartzFamilyToLp_coordinates,
    sum_apply, smul_apply, imageDerivativeBesselL2Operator_toLp, uncutSchwartz]
  simp only [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_sum, map_smul]

private theorem uncutSchwartz_apply (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → S) (x : E) (i : Fin n) :
    uncutSchwartz A v i x = coefficientOperator (fun _ ↦ A) (fun _ ↦ 0)
      (fun y j ↦ imageBesselSchwartzCLM (v j) y) x i := by
  simp only [uncutSchwartz, sum_apply, smul_apply, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, coefficientOperator, partialDeriv,
    Matrix.zero_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, add_zero]
  exact Finset.sum_comm

/-- On plateau-supported tests the literal Hilbert adjoint is `J P* (χ v)`.
This is the adjoint identification consumed by the source-tail energy proof
(`app:ch_background:prop:bg-frame`). -/
theorem uncutComplexChannel_adjoint_toLp (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → S)
    (hv : ∀ i x, v i x ≠ 0 → FixedCutoffs.physical hR 0 x = 1) :
    (uncutComplexChannel A).adjoint (imageSchwartzFamilyToLp v) =
      imageSchwartzFamilyToLp (fun j ↦ imageBesselSchwartzCLM (adjointFactor hR A v j)) := by
  apply denseRange_imageSchwartzFamilyToLp.eq_of_inner_right ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, uncutSchwartz_toLp,
    imageSchwartzFamilyToLp_inner, imageSchwartzFamilyToLp_inner]
  calc
    _ = ∑ i, imageSchwartzPairing
        (maskedCoefficientSchwartzCLM (fun _ ↦ A) (fun _ ↦ 0)
          (FixedCutoffs.physical hR 0) (fun j ↦ imageBesselSchwartzCLM (w j)) i) (v i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [imageSchwartzPairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [uncutSchwartz_apply, maskedCoefficientSchwartzCLM_apply
        (fun _ ↦ A) (fun _ ↦ 0) (FixedCutoffs.physical hR 0)
        (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
        (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport]
      by_cases hx : v i x = 0
      · simp [hx]
      · rw [hv i x hx, Complex.ofReal_one, one_mul]
    _ = _ := by
      rw [maskedCoefficientSchwartzCLM_pairing
        (fun _ ↦ A) (fun _ ↦ 0) (FixedCutoffs.physical hR 0)
        (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
        (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport]
      simp only [imageBesselSchwartzCLM_pairing, adjointFactor]

/-- The open plateau removes the auxiliary square even after applying the
full differential source factor (`app:ch_background:prop:bg-frame`). -/
theorem adjointFactor_mask_sq (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → S)
    (hv : ∀ i, tsupport (v i : E → ℂ) ⊆
      interior {x | FixedCutoffs.physical hR 0 x = 1}) (j : Fin n) :
    SchwartzMap.smulLeftCLM ℂ (fun x ↦ ((FixedCutoffs.physical hR 0 x) ^ 2 : ℂ))
      (adjointFactor hR A v j) = adjointFactor hR A v j := by
  have ht := (FixedCutoffs.physical (n := n) hR 0).hasCompactSupport.hasTemperateGrowth
    (FixedCutoffs.physical hR 0).contDiff
  have hsq : (fun x : E ↦ ((FixedCutoffs.physical hR 0 x) ^ 2 : ℂ)).HasTemperateGrowth := by
    fun_prop
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hsq]
  by_cases hx : FixedCutoffs.physical hR 0 x = 1
  · simp [hx]
  · have hz (i : Fin n) : (v i : E → ℂ) =ᶠ[𝓝 x] 0 := by
      apply notMem_tsupport_iff_eventuallyEq.mp
      intro hi
      have hp : x ∈ {y : E | FixedCutoffs.physical hR 0 y = 1} :=
        interior_subset (hv i hi)
      exact hx hp
    have hd (a : Fin n) (i : Fin n) : partialDeriv
        (fun y ↦ (A a i j : ℂ) * ((FixedCutoffs.physical hR 0 y : ℂ) * v i y)) x a = 0 := by
      have he : (fun y ↦ (A a i j : ℂ) *
          ((FixedCutoffs.physical hR 0 y : ℂ) * v i y)) =ᶠ[𝓝 x] 0 := by
        filter_upwards [hz i] with y hy
        simp [show v i y = 0 from hy]
      rw [partialDeriv, he.fderiv_eq]
      simp
    have hq : adjointFactor hR A v j x = 0 := by
      rw [adjointFactor, maskedCoefficientAdjointSchwartzCLM_apply
        (fun _ ↦ A) (fun _ ↦ 0) (FixedCutoffs.physical hR 0)
        (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
        (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport]
      simp [coefficientFormalAdjoint, hd]
    rw [hq, smul_zero]

end JanetCartan.ContinuumNormal.FrozenImageComparison.SourceTailTestEnergy
