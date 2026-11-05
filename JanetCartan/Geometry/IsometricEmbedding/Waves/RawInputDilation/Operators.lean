module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputDilation.Isometry
public import JanetCartan.Analysis.Operator.NormalPerturbation.Weighted

/-!
# Adjoint and output normals under the annular input dilation

The operator identities preceding `app:ch_waves:eq:sampling-prefix-normal`
apply to the entire output Hilbert space. The input operators are actual bounded
operators supplied by the raw-primary/masked-normal producers. Their boundedness
is not inferred from a formal kernel. Finite rows use the shared Hilbert-sum row
and all prefixes keep the same indices, cutoffs, and weights.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RawInputDilation
open RawInputRealization NormalPerturbation
variable {n : ℕ} {K : ℝ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The same raw operator expressed on the unit annulus, as in
`app:ch_waves:thm:sampling`. The output space and operator values are unchanged. -/
def dilatedOperator (hK : 0 < K) (T : AnnularL2 n K →L[ℂ] H) :
    AnnularL2 n 1 →L[ℂ] H := T.comp (annularDilation n K hK).symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace H] in
/-- An input and its dilation give the identical output in
`app:ch_waves:thm:sampling`. -/
theorem dilatedOperator_apply_dilation (hK : 0 < K) (T : AnnularL2 n K →L[ℂ] H)
    (f : AnnularL2 n K) : dilatedOperator hK T (annularDilation n K hK f) = T f := by
  simp [dilatedOperator]

/-- The transformed adjoint is `D_K T*`, as used in
`app:ch_waves:eq:sampling-prefix-normal`. -/
theorem dilatedOperator_adjoint (hK : 0 < K) (T : AnnularL2 n K →L[ℂ] H) :
    (dilatedOperator hK T).adjoint =
      (annularDilation n K hK).toContinuousLinearEquiv.toContinuousLinearMap.comp
        T.adjoint := by
  unfold dilatedOperator
  rw [ContinuousLinearMap.adjoint_comp, (annularDilation n K hK).symm.adjoint_eq_symm]
  rfl

/-- The entire output normal is exactly preserved by the actual input unitary
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem normal_dilatedOperator (hK : 0 < K) (T : AnnularL2 n K →L[ℂ] H) :
    normal (dilatedOperator hK T) = normal T := by
  rw [normal, dilatedOperator_adjoint]
  ext x
  simp [dilatedOperator, normal]

/-- Explicit almost-everywhere adjoint transformation on the unit annulus
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem dilatedOperator_adjoint_ae (hK : 0 < K) (T : AnnularL2 n K →L[ℂ] H)
    (g : H) : (dilatedOperator hK T).adjoint g =ᵐ[annularMeasure n 1]
      fun θ ↦ (Real.sqrt (K ^ (n - 1)) : ℂ) * T.adjoint g (K • θ) := by
  rw [dilatedOperator_adjoint]
  exact annularDilation_apply_ae hK (T.adjoint g)

variable {ι : Type*} [Fintype ι] {radius : ι → ℝ}

/-- The actual componentwise unitary on the finite annular input sum of
`app:ch_waves:thm:individual`. -/
def inputDilation (hR : ∀ i, 0 < radius i) :
    Input n radius ≃ₗᵢ[ℂ] Input n (fun _ : ι ↦ 1) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i ↦ annularDilation n (radius i) (hR i))

/-- Coordinate formula for the finite input dilation
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem inputDilation_apply (hR : ∀ i, 0 < radius i) (f : Input n radius) (i : ι) :
    inputDilation hR f i = annularDilation n (radius i) (hR i) (f i) := rfl

/-- Coordinate formula for its inverse, keeping the same channel index
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem inputDilation_symm_apply (hR : ∀ i, 0 < radius i)
    (f : Input n (fun _ : ι ↦ 1)) (i : ι) :
    (inputDilation hR).symm f i = (annularDilation n (radius i) (hR i)).symm (f i) := rfl

/-- Componentwise normalization is the unitary change of input of the whole
finite row. Arbitrary weights include all unchanged prefix selections
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem weightedRow_dilatedOperator (hR : ∀ i, 0 < radius i)
    (w : ι → ℝ) (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] H) :
    weightedRow w (fun i ↦ dilatedOperator (hR i) (T i)) =
      (weightedRow w T).comp (inputDilation hR).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  ext f
  simp only [ContinuousLinearMap.comp_apply, weightedRow_apply,
    dilatedOperator]
  rfl

/-- The adjoint of the entire normalized finite row is the dilation of the
original adjoint (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem weightedRow_dilatedOperator_adjoint (hR : ∀ i, 0 < radius i)
    (w : ι → ℝ) (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] H) :
    (weightedRow w (fun i ↦ dilatedOperator (hR i) (T i))).adjoint =
      (inputDilation hR).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (weightedRow w T).adjoint := by
  rw [weightedRow_dilatedOperator]
  rw [ContinuousLinearMap.adjoint_comp, (inputDilation (n := n) hR).symm.adjoint_eq_symm]
  rfl

/-- Full output normals of finite rows are unchanged, including weighted rows
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem normal_weightedRow_dilatedOperator (hR : ∀ i, 0 < radius i)
    (w : ι → ℝ) (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] H) :
    normal (weightedRow w (fun i ↦ dilatedOperator (hR i) (T i))) =
      normal (weightedRow w T) := by
  rw [normal, weightedRow_dilatedOperator_adjoint, weightedRow_dilatedOperator]
  ext x
  simp [normal]

/-- Every literal radial prefix has the same full output normal before and after
input dilation. The condition `radius i ≤ cutoff` and each index are unchanged
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem normal_prefix_dilatedOperator (hR : ∀ i, 0 < radius i)
    (cutoff : ℝ) (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] H) :
    normal (weightedRow (fun i ↦ if radius i ≤ cutoff then 1 else 0)
      (fun i ↦ dilatedOperator (hR i) (T i))) =
    normal (weightedRow (fun i ↦ if radius i ≤ cutoff then 1 else 0) T) :=
  normal_weightedRow_dilatedOperator hR _ T

/-- Sample weights and finite sums of prefix normals are unchanged by the input
normalization (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_normal_prefix_dilatedOperator {σ : Type*} (samples : Finset σ)
    (hR : ∀ i, 0 < radius i) (cutoff : ℝ) (weight : σ → ℝ)
    (T : σ → ∀ i, AnnularL2 n (radius i) →L[ℂ] H) :
    (∑ j ∈ samples, weight j •
      normal (weightedRow (fun i ↦ if radius i ≤ cutoff then 1 else 0)
        (fun i ↦ dilatedOperator (hR i) (T j i)))) =
    ∑ j ∈ samples, weight j •
      normal (weightedRow (fun i ↦ if radius i ≤ cutoff then 1 else 0) (T j)) := by
  simp only [normal_prefix_dilatedOperator]

/-- The continuum integral of every prefix normal is unchanged, with the same
parameter measure and weight (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_normal_prefix_dilatedOperator {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (hR : ∀ i, 0 < radius i) (cutoff : ℝ) (weight : Z → ℝ)
    (T : Z → ∀ i, AnnularL2 n (radius i) →L[ℂ] H) :
    (∫ z, weight z •
      normal (weightedRow (fun i ↦ if radius i ≤ cutoff then 1 else 0)
        (fun i ↦ dilatedOperator (hR i) (T z i))) ∂μ) =
    ∫ z, weight z •
      normal (weightedRow (fun i ↦ if radius i ≤ cutoff then 1 else 0) (T z)) ∂μ := by
  simp only [normal_prefix_dilatedOperator]

end JanetCartan.RawInputDilation
