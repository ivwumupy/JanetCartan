module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.BandBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Continuity

/-!
# Actual annular sampling operators

This constructs the operators in `app:ch_waves:eq:sampling-operator-bounds`
from their phase, mask and measured amplitude. All input and output measures
are literal Euclidean Lebesgue measures. The fields in `BandKernelData` are
analytic inputs from the actual wave producers, not operator estimates.
The sharper oscillatory bound of order `K` is a separate obligation.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace JanetCartan.SamplingKernelBounds
open RawInputRealization

/-- Continuous phase and measured amplitude with fixed compact physical support
and uniform low bounds, for `app:ch_waves:eq:sampling-operator-bounds`.
The parameter may include color and carrier coordinates. The actual WKB and
leading-wave producers must instantiate these fields. -/
structure BandKernelData (P : Type*) [TopologicalSpace P] (n : ℕ) where
  phase : (P × Euclidean (n - 1)) × Euclidean n → ℝ
  phase_continuous : Continuous phase
  mask : Euclidean (n - 1) → ℂ
  mask_continuous : Continuous mask
  amplitude : (P × Euclidean (n - 1)) × Euclidean n → EuclideanSpace ℂ (Fin n)
  amplitude_continuous : Continuous amplitude
  physicalSupport : Set (Euclidean n)
  physicalSupport_compact : IsCompact physicalSupport
  amplitude_eq_zero : ∀ p η x, x ∉ physicalSupport → amplitude ((p, η), x) = 0
  amplitudeBound : ℝ
  amplitudeBound_nonneg : 0 ≤ amplitudeBound
  amplitude_le : ∀ p η x, ‖amplitude ((p, η), x)‖ ≤ amplitudeBound
  maskBound : ℝ
  maskBound_nonneg : 0 ≤ maskBound
  mask_le : ∀ η, ‖mask η‖ ≤ maskBound

namespace BandKernelData
variable {P : Type*} [TopologicalSpace P] {n : ℕ} (D : BandKernelData P n)

/-- Literal measured oscillatory kernel (`app:ch_waves:eq:sampling-operator-bounds`). -/
def kernel (p : P) (η : Euclidean (n - 1)) (x : Euclidean n) :=
  bandKernel (fun η x ↦ D.phase ((p, η), x)) D.mask
    (fun η x ↦ D.amplitude ((p, η), x)) η x

/-- Joint kernel continuity before passing to L²
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_kernel : Continuous (fun q : (P × Euclidean (n - 1)) × Euclidean n ↦
    D.kernel q.1.1 q.1.2 q.2) := by
  unfold kernel bandKernel
  have hp := D.phase_continuous
  have hm := D.mask_continuous
  have ha := D.amplitude_continuous
  fun_prop

/-- The physical measurement support is retained literally
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem kernel_eq_zero (p : P) (η : Euclidean (n - 1)) (x : Euclidean n)
    (hx : x ∉ D.physicalSupport) : D.kernel p η x = 0 := by
  simp [kernel, bandKernel, D.amplitude_eq_zero p η x hx]

/-- Each physical column lies in the full output L² space
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem memLp_kernel (p : P) (η : Euclidean (n - 1)) :
    MemLp (D.kernel p η) 2 volume :=
  memLp_compact_column (P := P × Euclidean (n - 1)) (d := n)
    (K := fun q x ↦ D.kernel q.1 q.2 x) D.continuous_kernel D.physicalSupport_compact
    (fun (q : P × Euclidean (n - 1)) ↦ D.kernel_eq_zero q.1 q.2) (p, η)

/-- Actual physical L² column (`app:ch_waves:eq:sampling-operator-bounds`). -/
def column (p : P) (η : Euclidean (n - 1)) : Output n :=
  (D.memLp_kernel p η).toLp (D.kernel p η)

/-- The L² column has the specified oscillatory representative
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem column_coe (p : P) (η : Euclidean (n - 1)) :
    (D.column p η : Euclidean n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume] D.kernel p η :=
  MemLp.coeFn_toLp _

/-- The column norm is its literal physical squared-kernel integral
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_column_sq (p : P) (η : Euclidean (n - 1)) :
    ‖D.column p η‖ ^ 2 = ∫ x, ‖D.kernel p η x‖ ^ 2 := by
  rw [l2_vector_norm_sq_eq_integral (𝕜 := ℂ)]
  exact integral_congr_ae ((D.column_coe p η).mono
    (fun _ hx ↦ congrArg (fun v ↦ ‖v‖ ^ 2) hx))

variable [FirstCountableTopology P] [LocallyCompactSpace P]

/-- Joint parameter/frequency continuity into physical L² follows from the
squared-kernel dominated-convergence argument
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_column : Continuous (Function.uncurry D.column) :=
  continuous_compact_column (P := P × Euclidean (n - 1)) (d := n)
    (K := fun q x ↦ D.kernel q.1 q.2 x) D.continuous_kernel D.physicalSupport_compact
    (fun (q : P × Euclidean (n - 1)) ↦ D.kernel_eq_zero q.1 q.2)

/-- Actual annular columns are square integrable in the initial frequency
measure (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem memLp_column (R : ℝ) (p : P) : MemLp (D.column p) 2 (annularMeasure n R) :=
  memLp_restrict_compact_column
    (D.continuous_column.comp (continuous_const.prodMk continuous_id))
    ((isCompact_closedBall (0 : Euclidean (n - 1)) R).diff Metric.isOpen_ball)

/-- Construct the actual annular operator into the entire complex output space
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def operator (R : ℝ) (p : P) : AnnularL2 n R →L[ℂ] Output n :=
  kernelSynthesis (D.memLp_column R p)

/-- Literal L²-valued synthesis formula (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem operator_apply (R : ℝ) (p : P) (f : AnnularL2 n R) :
    D.operator R p f = ∫ η, f η • D.column p η ∂annularMeasure n R :=
  kernelSynthesis_apply (D.memLp_column R p) f

/-- The constructed operator satisfies the actual adjoint kernel formula
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem operator_hasAdjointKernel (R : ℝ) (p : P) :
    HasAdjointKernel (D.operator R p) (D.column p) :=
  kernelSynthesis_hasAdjointKernel (D.memLp_column R p)

/-- The adjoint is integration against the conjugate physical kernel, with
no finite-dimensional output projection (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem operator_adjoint_ae (R : ℝ) (p : P) (v : Output n) :
    ∀ᵐ η ∂annularMeasure n R, (D.operator R p).adjoint v η =
      ∫ x, inner ℂ (D.kernel p η x) (v x) := by
  filter_upwards [D.operator_hasAdjointKernel R p v] with η hη
  rw [hη, L2.inner_def]
  exact integral_congr_ae ((D.column_coe p η).mono (fun x hx ↦ congrArg (fun v₁ ↦ inner ℂ v₁ (v x)) hx))

/-- The actual annular operators depend continuously on their parameters in
operator norm (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_operator (R : ℝ) : Continuous (D.operator R) :=
  continuous_kernelSynthesis_compact D.continuous_column
    ((isCompact_closedBall (0 : Euclidean (n - 1)) R).diff Metric.isOpen_ball)

/-- Uniform squared-kernel constant; it contains only the physical support
volume, amplitude/mask bounds, and initial unit-ball volume
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def squaredKernelConstant : ℝ :=
  volume.real D.physicalSupport * D.maskBound ^ 2 * D.amplitudeBound ^ 2 * unitBallVolume n

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
/-- Nonnegativity of the uniform constant in
`app:ch_waves:eq:sampling-operator-bounds`. -/
theorem squaredKernelConstant_nonneg : 0 ≤ D.squaredKernelConstant := by
  unfold squaredKernelConstant unitBallVolume
  positivity

/-- Continuity of the squared-kernel integral, used to integrate the actual
sampling trace in `app:ch_waves:eq:sampling-operator-bounds`. -/
theorem continuous_integral_norm_column_sq (R : ℝ) :
    Continuous (fun p ↦ ∫ η, ‖D.column p η‖ ^ 2 ∂annularMeasure n R) :=
  continuous_parametric_integral_of_continuous (D.continuous_column.norm.pow 2)
    ((isCompact_closedBall (0 : Euclidean (n - 1)) R).diff Metric.isOpen_ball)

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
/-- The actual squared-kernel estimate has power `n`, because frequency has
dimension `n-1` and the half derivative contributes one power
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem integral_norm_column_sq_le (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R) (p : P) :
    (∫ η, ‖D.column p η‖ ^ 2 ∂annularMeasure n R) ≤ D.squaredKernelConstant * R ^ n := by
  simp_rw [D.norm_column_sq]
  exact double_integral_norm_bandKernel_sq_le hn _ _ _ D.physicalSupport_compact hR
    D.amplitudeBound_nonneg D.maskBound_nonneg D.mask_le (D.amplitude_le p)
    (D.amplitude_eq_zero p)

variable {ι κ : Type*} [Countable ι]

/-- Hilbert–Schmidt summability and the `K^n` bound for the constructed annular
operator (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem operator_hilbertSchmidt_bound (b : HilbertBasis ι ℂ (Output n))
    (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R)
    (c : HilbertBasis κ ℂ (AnnularL2 n R)) (p : P) :
    IsHilbertSchmidt c (D.operator R p) ∧
      hilbertSchmidtSq c (D.operator R p) ≤ D.squaredKernelConstant * R ^ n := by
  obtain ⟨hs, he⟩ := (D.operator_hasAdjointKernel R p).hilbertSchmidtSq_eq_integral
    (D.memLp_column R p) b c
  exact ⟨hs, he.trans_le (D.integral_norm_column_sq_le hn hR p)⟩

/-- The squared Hilbert–Schmidt norm varies continuously, so the compact
sampling weights can be integrated against it
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_hilbertSchmidtSq_operator (b : HilbertBasis ι ℂ (Output n))
    (R : ℝ) (c : HilbertBasis κ ℂ (AnnularL2 n R)) :
    Continuous (fun p ↦ hilbertSchmidtSq c (D.operator R p)) := by
  have he (p : P) := ((D.operator_hasAdjointKernel R p).hilbertSchmidtSq_eq_integral
    (D.memLp_column R p) b c).2
  simp_rw [he]
  exact D.continuous_integral_norm_column_sq R

/-- Compactness on the full output space (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem isCompactOperator_operator (b : HilbertBasis ι ℂ (Output n)) (R : ℝ) (p : P) :
    IsCompactOperator (D.operator R p) :=
  (D.operator_hasAdjointKernel R p).isCompactOperator (D.memLp_column R p) b

/-- The normal trace bound on the full output space
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem positiveTrace_operator_normal_le (b : HilbertBasis ι ℂ (Output n))
    (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R) (p : P) :
    positiveTrace b (D.operator R p ∘L (D.operator R p).adjoint) ≤
      D.squaredKernelConstant * R ^ n := by
  rw [(D.operator_hasAdjointKernel R p).positiveTrace_normal_eq_integral
    (D.memLp_column R p) b]
  exact D.integral_norm_column_sq_le hn hR p

/-- Every finite compression has the same trace bound
(`app:ch_waves:eq:sampling-operator-bounds`), as required by
`HilbertOperatorBernstein`. -/
theorem trace_finiteCompression_operator_normal_le (b : HilbertBasis ι ℂ (Output n))
    (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R) (p : P)
    (U : Submodule ℂ (Output n)) [FiniteDimensional ℂ U] :
    RCLike.re (LinearMap.trace ℂ U
      (finiteCompression U (D.operator R p ∘L (D.operator R p).adjoint)).toLinearMap) ≤
        D.squaredKernelConstant * R ^ n :=
  ((D.operator_hasAdjointKernel R p).trace_finiteCompression_normal_le_integral
    (D.memLp_column R p) b U).trans (D.integral_norm_column_sq_le hn hR p)

end BandKernelData
end JanetCartan.SamplingKernelBounds
