module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Operators
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.VectorKernel
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Channels

/-!
# Physical canonical PDOs in cycle frequency

The connection required by `CompleteResidual.maskedPhysicalPDO` in
`app:ch_regular_base:eq:energy-complete-residual`. The physical covector is
`2 * π` times the Mathlib frequency. Source integration remains first, both
positions remain independent, and the matrix norm is the Frobenius norm.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.PdoRealization
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential AmplitudeBound
open NormalComparison
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean (2 * n)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The exact symbol of a physical canonical graph in Mathlib's frequency and
paired-position coordinates. Consumer: `canonicalGraph_eq_vectorTwoPositionL2Operator`,
for `app:ch_regular_base:eq:energy-complete-residual`. -/
def physicalPDOCycleSymbol (A : FullAmplitude n r) (ξ : E) (z : P) : Mat :=
  A (splitPhysicalPositions z).1 (splitPhysicalPositions z).2 ((2 * Real.pi) • ξ)

/-- Both physical positions are retained in the frequency conversion for
`app:ch_regular_base:eq:energy-complete-residual`. -/
@[simp] theorem physicalPDOCycleSymbol_pairedPosition (A : FullAmplitude n r) (ξ x y : E) :
    physicalPDOCycleSymbol A ξ (pairedPosition x y) = A x y ((2 * Real.pi) • ξ) := by
  simp only [physicalPDOCycleSymbol, splitPhysicalPositions_pairedPosition]

/-- The physical normalization cancels the frequency Jacobian exactly once.
This is the literal integral connection used in
`app:ch_regular_base:eq:energy-complete-residual`; it needs no integrability
premise because it is only a linear change of variables. -/
theorem canonicalGraph_eq_cycleIntegral (A : FullAmplitude n r)
    (u : E → Fin r → ℂ) (x : E) :
    graphOperator (fun x η ↦ inner ℝ x η) A u x =
      ∫ ξ, Real.fourierChar (inner ℝ ξ x) •
        ∫ y, Real.fourierChar (-inner ℝ y ξ) •
          (A x y ((2 * Real.pi) • ξ)).mulVec (u y) := by
  have hscale := Measure.integral_comp_smul_of_nonneg volume
    (fun η ↦ ∫ y, graphOscillation (fun x η ↦ inner ℝ x η) x y η •
      (A x y η).mulVec (u y)) (2 * Real.pi) (hR := by positivity)
  simp only [Euclidean, finrank_euclideanSpace_fin] at hscale
  have hphase (ξ y : E) :
      graphOscillation (fun x η ↦ inner ℝ x η) x y ((2 * Real.pi) • ξ) =
        (Real.fourierChar (inner ℝ ξ x) : ℂ) *
          (Real.fourierChar (-inner ℝ y ξ) : ℂ) := by
    simp only [graphOscillation, Real.fourierChar_apply, real_inner_smul_right,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg, ← Complex.exp_add]
    congr 1
    rw [real_inner_comm ξ x]
    ring
  unfold graphOperator
  rw [show ((2 * Real.pi) ^ n : ℂ)⁻¹ = (((2 * Real.pi) ^ n)⁻¹ : ℝ) by push_cast; rfl]
  rw [Complex.coe_smul, ← hscale]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ξ
  simp_rw [hphase]
  change (∫ y, ((Real.fourierChar (inner ℝ ξ x) : ℂ) *
    (Real.fourierChar (-inner ℝ y ξ) : ℂ)) • (A x y ((2 * Real.pi) • ξ)).mulVec (u y)) =
    (Real.fourierChar (inner ℝ ξ x) : ℂ) •
      ∫ y, (Real.fourierChar (-inner ℝ y ξ) : ℂ) • (A x y ((2 * Real.pi) • ξ)).mulVec (u y)
  simp only [mul_smul, integral_smul]

/-- The finite physical derivative reserve proves frequency integrability on
compact smooth tests. Consumer: the literal canonical PDO identification for
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem integrable_cycleSourceTransform
    (b : E → P → Mat) (hb : ContDiff ℝ ∞ (Function.uncurry b)) (M : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) M)
    (u : graphTestSpace n r) (x : E) (i j : Fin r) :
    Integrable (sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y) i j)
      (fun y ↦ u.val y j) x) := by
  have hb' := (matrixEntryEvaluation i j).contDiff.comp hb
  have hu : ContDiff ℝ ∞ (fun y ↦ u.val y j) :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).restrictScalars ℝ).contDiff.comp u.property.1
  refine integrable_sourceAmplitudeTransform_of_sourceSymbolBounds _ _ x 0 ?_ ?_ ?_ ?_
    (fun k ↦ ((2 * n : ℕ) : ℝ) ^ k * M * ‖physicalSourceInclusion n‖ ^ k) ?_
  · exact hb'.continuous.comp (continuous_fst.prodMk
      (continuous_pairedPosition.comp (continuous_const.prodMk continuous_snd)))
  · exact hu.of_le (by simp)
  · exact u.property.2.comp_left (g := fun v : EuclideanSpace ℂ (Fin r) ↦ v j) rfl
  · intro ξ
    exact (hb'.comp (contDiff_const.prodMk
      (contDiff_pairedPosition.comp (contDiff_const.prodMk contDiff_id)))).of_le (by simp)
  · intro k hk y ξ
    simp only [pow_zero, mul_one]
    apply norm_iteratedFDeriv_source_le_physicalBudget
      (fun ξ ↦ hb'.comp (contDiff_const.prodMk contDiff_id)) (hM i j)
    simp only [Euclidean, finrank_euclideanSpace_fin, zero_add] at hk
    omega

/-- The literal source-first canonical graph equals the matrix PDO on compact
smooth tests; the finite source budget justifies the coordinate sums.
Consumer: `canonicalGraph_eq_vectorTwoPositionL2Operator`, for
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem canonicalGraph_eq_matrixFullAmplitudeOperator
    (A : FullAmplitude n r)
    (hb : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol A))) (M : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ physicalPDOCycleSymbol A ξ z i j) (2 * (n + 1)) M)
    (u : graphTestSpace n r) (x : E) :
    graphOperator (fun x η ↦ inner ℝ x η) A (fun y ↦ (u.val y).ofLp) x =
      matrixFullAmplitudeOperator
        (fun x y ξ ↦ physicalPDOCycleSymbol A ξ (pairedPosition x y))
        (fun y j ↦ u.val y j) x := by
  rw [matrixFullAmplitudeOperator_eq_integral]
  · simpa only [physicalPDOCycleSymbol_pairedPosition] using
      canonicalGraph_eq_cycleIntegral A (fun y ↦ (u.val y).ofLp) x
  · intro i j ξ
    have hc : Continuous (fun y ↦ physicalPDOCycleSymbol A ξ (pairedPosition x y) i j) :=
      ((matrixEntryEvaluation i j).contDiff.comp hb).continuous.comp
      (continuous_const.prodMk (continuous_pairedPosition.comp
        (continuous_const.prodMk continuous_id)))
    exact (((continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp
      u.property.1.continuous)).mul hc).integrable_of_hasCompactSupport
      ((u.property.2.comp_left (g := fun v : EuclideanSpace ℂ (Fin r) ↦ v j) rfl).mul_right)
  · exact integrable_cycleSourceTransform _ hb M hM u x

/-- The SAME choice-defined full graph is the proved vector PDO on Euclidean
Lebesgue L². Literal compact-test integrals and density establish equality;
no realization or operator identity is assumed. Consumer:
`CompleteResidual.maskedPhysicalPDO`, in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem canonicalGraph_eq_vectorTwoPositionL2Operator
    (hn : 0 < n) (R : ℝ) (A : FullAmplitude n r)
    (hb : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol A)))
    (hs : ∀ ξ i j, SupportedInCenteredBox R
      (fun z ↦ physicalPDOCycleSymbol A ξ z i j)) (M : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ physicalPDOCycleSymbol A ξ z i j) (2 * (n + 1)) M) :
    fullGraphOperator (fun x η ↦ inner ℝ x η) A =
      vectorTwoPositionL2Operator hn R (physicalPDOCycleSymbol A) hb hs M hM := by
  apply fullGraphOperator_eq_of_realizes
  intro u
  refine (vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hn R _ hb hs M hM
    u.val (graphTest_memLp u)
    (fun j ↦ (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).restrictScalars ℝ).contDiff.comp
      u.property.1).of_le (by simp))
    (fun j ↦ u.property.2.comp_left (g := fun v : EuclideanSpace ℂ (Fin r) ↦ v j) rfl)).trans ?_
  exact Filter.Eventually.of_forall fun x ↦ congrArg (WithLp.toLp 2)
    (canonicalGraph_eq_matrixFullAmplitudeOperator A hb M hM u x).symm

end JanetCartan.RegularSector.Characteristic.PdoRealization
