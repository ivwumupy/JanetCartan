module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Realization
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Tests

/-!
# The matrix normal estimate for graph regularizations

For `app:ch_regular_base:eq:actual-normal-amplitude`, the scalar two-position
PDO estimate is applied entrywise with Frobenius derivative bounds. The normal
identity is a producer input: it must describe the complete amplitude, including
source masks. No source-independent formula is asserted for a full amplitude.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential

namespace JanetCartan.FourierIntegral

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
local notation "H₀" => Lp ℂ 2 (volume : Measure E)

/-- Matrix PDO acting on vector-valued Lebesgue L² in Step 1 of
`app:ch_regular_base:thm:actual-calculus`. -/
def graphMatrixL2Operator (B : Fin r → Fin r → H₀ →L[ℂ] H₀) : H →L[ℂ] H :=
  ∑ i, ∑ j, ((coordinateInjection i).toContinuousLinearMap.compLpL 2 volume).comp
    ((B i j).comp ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).compLpL 2 volume))

/-- The finite matrix factor in `app:ch_regular_base:eq:fio-input` is fixed
before higher derivative indices. -/
theorem norm_graphMatrixL2Operator_le (B : Fin r → Fin r → H₀ →L[ℂ] H₀)
    {K : ℝ} (hK : 0 ≤ K) (hB : ∀ i j, ‖B i j‖ ≤ K) :
    ‖graphMatrixL2Operator B‖ ≤ (r : ℝ) * r * K := by
  let I : Fin r → H₀ →L[ℂ] H := fun i ↦
    (coordinateInjection i : ℂ →ₗᵢ[ℂ] V).toContinuousLinearMap.compLpL 2 volume
  let P : Fin r → H →L[ℂ] H₀ := fun j ↦
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).compLpL 2 volume
  have hi (i : Fin r) : ‖I i‖ ≤ 1 := by
    apply (ContinuousLinearMap.norm_compLpL_le (p := 2) (μ := (volume : Measure E))
      (coordinateInjection i : ℂ →ₗᵢ[ℂ] V).toContinuousLinearMap).trans
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp
  have hj (j : Fin r) : ‖P j‖ ≤ 1 := by
    apply (ContinuousLinearMap.norm_compLpL_le (p := 2) (μ := (volume : Measure E))
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j)).trans
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa using PiLp.norm_apply_le z j
  have hterm (i j : Fin r) : ‖(I i).comp ((B i j).comp (P j))‖ ≤ K := by
    calc
      _ ≤ ‖I i‖ * ‖(B i j).comp (P j)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (K * 1) := mul_le_mul (hi i)
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hB i j) (hj j) (norm_nonneg _) hK)) (norm_nonneg _) zero_le_one
      _ = K := by ring
  change ‖∑ i, ∑ j, (I i).comp ((B i j).comp (P j))‖ ≤ _
  calc
    _ ≤ ∑ i : Fin r, ∑ j : Fin r, ‖(I i).comp ((B i j).comp (P j))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _i : Fin r, ∑ _j : Fin r, K :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hterm i j
    _ = _ := by simp [mul_assoc]

/-- Primitive normal-amplitude hypotheses in
`app:ch_regular_base:eq:actual-normal-amplitude`. The derivative reserve is
exactly `2 * (n + 1)` physical derivatives, measured in Frobenius norm. The
frequency argument uses Mathlib's cycles-per-unit PDO convention: producers
must perform the physical-covector change `ξ_phys = 2π ξ` in the exact identity. -/
structure GraphNormalAmplitudeBounds
    (b : E → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ) (R M : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (Function.uncurry b)
  support : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)
  derivative : ∀ ξ is, is.length ≤ 2 * (n + 1) → ∀ z,
    ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M

/-- Scalar entry derivative bounds extracted without changing the Frobenius
budget (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem GraphNormalAmplitudeBounds.entry_bound
    {b : E → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ} {R M : ℝ}
    (hb : GraphNormalAmplitudeBounds b R M) (i j : Fin r) :
    HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) M := by
  intro ξ is hi z
  exact (norm_matrixEntry_le_frobenius _ i j).trans (hb.derivative ξ is hi z)

/-- The complete normal PDO of `app:ch_regular_base:eq:actual-normal-amplitude`,
constructed from the existing two-position L² realization, with both physical
positions independent. -/
def graphNormalL2Operator (hn : 0 < n) (R : ℝ)
    (b : E → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ)
    (M : ℝ) (hb : GraphNormalAmplitudeBounds b R M) : H →L[ℂ] H :=
  graphMatrixL2Operator (fun i j ↦ twoPositionL2Operator hn R
    (fun ξ z ↦ b ξ z i j) ((matrixEntryEvaluation i j).contDiff.comp hb.smooth)
    (fun ξ ↦ hb.support ξ i j) M (hb.entry_bound i j))

/-- The finite low normal estimate in Step 1 of
`app:ch_regular_base:thm:actual-calculus`. -/
theorem norm_graphNormalL2Operator_le (hn : 0 < n) (R : ℝ)
    (b : E → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hb : GraphNormalAmplitudeBounds b R M) :
    ‖graphNormalL2Operator hn R b M hb‖ ≤
      (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * M) := by
  apply norm_graphMatrixL2Operator_le _
    (mul_nonneg (fixedBoxAmplitudeConstant_nonneg n R) hM)
  intro i j
  exact norm_twoPositionL2Operator_le ..

/-- The exact `TT*` identification yields the graph bound by the Hilbert
C*-identity (`app:ch_regular_base:eq:actual-normal-kernel`). The premise is the
complete normal identity, not a graph norm estimate. -/
theorem norm_graphRegularization_le (hn : 0 < n) (R : ℝ)
    (b : E → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hb : GraphNormalAmplitudeBounds b R M)
    (T : H →L[ℂ] H) (hN : T.comp T.adjoint = graphNormalL2Operator hn R b M hb) :
    ‖T‖ ≤ Real.sqrt ((r : ℝ) * r * (fixedBoxAmplitudeConstant n R * M)) := by
  apply (Real.le_sqrt (norm_nonneg _) (by
    have := fixedBoxAmplitudeConstant_nonneg n R
    positivity)).mpr
  have he := ContinuousLinearMap.norm_adjoint_comp_self T.adjoint
  simp only [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map] at he
  rw [sq, ← he, hN]
  exact norm_graphNormalL2Operator_le hn R b hM hb

end JanetCartan.FourierIntegral
