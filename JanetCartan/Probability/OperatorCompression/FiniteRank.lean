module

public import JanetCartan.Probability.OperatorCompression.Variance
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Compression to a subspace

The finite-dimensional realization of the compressions in
`app:ch_waves:thm:sampling` of `paper.tex`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology InnerProductSpace BigOperators

namespace JanetCartan.OperatorCompression

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The operator on the subspace itself associated to orthogonal compression
(`app:ch_waves:thm:sampling`). -/
def restrictCompression (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (T : H →L[𝕜] H) : U →L[𝕜] U :=
  U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL

/-- The ambient compression is the extension of the subspace operator
(`app:ch_waves:thm:sampling`). -/
theorem coe_restrictCompression (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (T : H →L[𝕜] H) (x : H) :
    (restrictCompression U T (U.orthogonalProjectionOnto x) : H) =
      compress U.starProjection T x := rfl

/-- Passing to the range of an orthogonal projection preserves the compressed
operator norm (`app:ch_waves:thm:sampling`). -/
theorem norm_restrictCompression (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (T : H →L[𝕜] H) : ‖restrictCompression U T‖ = ‖compress U.starProjection T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (compress U.starProjection T).le_opNorm (x : H)
    simpa only [← coe_restrictCompression, U.orthogonalProjectionOnto_mem_subspace_eq_self,
      Submodule.norm_coe] using h
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← coe_restrictCompression, Submodule.norm_coe]
    exact ((restrictCompression U T).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (U.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _))

/-- Compression does not increase the norm, including after restriction to its
range (`app:ch_waves:thm:sampling`). -/
theorem norm_restrictCompression_le (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (T : H →L[𝕜] H) : ‖restrictCompression U T‖ ≤ ‖T‖ := by
  rw [norm_restrictCompression]
  exact norm_compress_le _ _ U.starProjection_norm_le

/-- The quadratic form of the operator on the subspace is the ambient quadratic
form (`app:ch_waves:thm:sampling`). -/
theorem inner_restrictCompression (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (T : H →L[𝕜] H) (x : U) :
    ⟪x, restrictCompression U T x⟫_𝕜 = ⟪(x : H), T x⟫_𝕜 :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left x (T x)

/-- The finite-dimensional and ambient sums have identical norms
(`app:ch_waves:thm:sampling`). -/
theorem norm_sum_restrictCompression (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    {ι : Type*} (s : Finset ι) (Y : ι → H →L[𝕜] H) :
    ‖∑ i ∈ s, restrictCompression U (Y i)‖ =
      ‖∑ i ∈ s, compress U.starProjection (Y i)‖ := by
  have hrestrict : restrictCompression U (∑ i ∈ s, Y i) =
      ∑ i ∈ s, restrictCompression U (Y i) := by
    ext x
    simp [restrictCompression]
  have hcompress : compress U.starProjection (∑ i ∈ s, Y i) =
      ∑ i ∈ s, compress U.starProjection (Y i) := by
    ext x
    simp [compress]
  rw [← hrestrict, ← hcompress, norm_restrictCompression]

/-- Quadratic-form domination implies trace domination in finite dimensions
(`app:ch_waves:thm:sampling`). -/
theorem re_trace_le_of_quadratic_le [FiniteDimensional 𝕜 H]
    (A B : H →L[𝕜] H)
    (h : ∀ x, RCLike.re ⟪x, A x⟫_𝕜 ≤ RCLike.re ⟪x, B x⟫_𝕜) :
    RCLike.re (LinearMap.trace 𝕜 H A.toLinearMap) ≤
      RCLike.re (LinearMap.trace 𝕜 H B.toLinearMap) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis 𝕜 H),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis 𝕜 H), map_sum, map_sum]
  exact Finset.sum_le_sum fun j _ ↦ h (stdOrthonormalBasis 𝕜 H j)

/-- A bound on all finite orthonormal diagonal sums gives the same bound for
the trace of every finite-dimensional compression (`app:ch_waves:thm:sampling`).
For a positive trace-class operator, this hypothesis is the usual trace bound. -/
theorem re_trace_restrictCompression_le
    (U : Submodule 𝕜 H) [FiniteDimensional 𝕜 U] (V : H →L[𝕜] H) (τ : ℝ)
    (htrace : ∀ (m : ℕ) (e : Fin m → H), Orthonormal 𝕜 e →
      ∑ j, RCLike.re ⟪e j, V (e j)⟫_𝕜 ≤ τ) :
    RCLike.re (LinearMap.trace 𝕜 U (restrictCompression U V).toLinearMap) ≤ τ := by
  let b := stdOrthonormalBasis 𝕜 U
  have h := htrace _ (fun j ↦ (b j : H))
    (b.orthonormal.comp_linearIsometry U.subtypeₗᵢ)
  rw [LinearMap.trace_eq_sum_inner _ b, map_sum]
  simpa only [ContinuousLinearMap.coe_coe, inner_restrictCompression] using h

/-- The scalar second moments of the finite-dimensional random operators are
dominated by the compression of the original variance upper operator
(`app:ch_waves:thm:sampling`). -/
theorem sum_integral_restrict_variance_le
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ι)
    (Y : ι → Ω → H →L[𝕜] H) (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (V : H →L[𝕜] H)
    (hint : ∀ i ∈ s, ∀ x, Integrable (fun ω ↦ ‖Y i ω x‖ ^ 2) μ)
    (hV : ∀ x, ∑ i ∈ s, ∫ ω, ‖Y i ω x‖ ^ 2 ∂μ ≤ RCLike.re ⟪x, V x⟫_𝕜)
    (x : U) :
    ∑ i ∈ s, ∫ ω, ‖restrictCompression U (Y i ω) x‖ ^ 2 ∂μ ≤
      RCLike.re ⟪x, restrictCompression U V x⟫_𝕜 := by
  rw [inner_restrictCompression]
  refine (Finset.sum_le_sum (fun i hi ↦ ?_)).trans (hV x)
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (hint i hi x)
  exact Eventually.of_forall fun ω ↦
    pow_le_pow_left₀ (norm_nonneg _) (U.norm_orthogonalProjectionOnto_apply_le (Y i ω x)) 2

/-- A common variance norm bound remains valid for all finite-dimensional
compressions (`app:ch_waves:thm:sampling`). -/
theorem sum_integral_restrict_variance_le_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ι)
    (Y : ι → Ω → H →L[𝕜] H) (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (V : H →L[𝕜] H)
    (hint : ∀ i ∈ s, ∀ x, Integrable (fun ω ↦ ‖Y i ω x‖ ^ 2) μ)
    (hV : ∀ x, ∑ i ∈ s, ∫ ω, ‖Y i ω x‖ ^ 2 ∂μ ≤ RCLike.re ⟪x, V x⟫_𝕜)
    (v : ℝ) (hv : ‖V‖ ≤ v) (x : U) :
    ∑ i ∈ s, ∫ ω, ‖restrictCompression U (Y i ω) x‖ ^ 2 ∂μ ≤ v * ‖x‖ ^ 2 := by
  refine (sum_integral_restrict_variance_le μ s Y U V hint hV x).trans ?_
  rw [inner_restrictCompression]
  calc
    RCLike.re ⟪(x : H), V x⟫_𝕜 ≤ ‖(x : H)‖ * ‖V x‖ := re_inner_le_norm _ _
    _ ≤ ‖(x : H)‖ * (‖V‖ * ‖(x : H)‖) :=
      mul_le_mul_of_nonneg_left (V.le_opNorm x) (norm_nonneg _)
    _ = ‖V‖ * ‖x‖ ^ 2 := by rw [Submodule.norm_coe]; ring
    _ ≤ v * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hv (sq_nonneg _)

/-- A finite sum of compact self-adjoint operators converges in norm under
increasing orthogonal projections with dense union (`app:ch_waves:thm:sampling`).
Finite dimensionality of the subspaces is needed for concentration, not for this limit. -/
theorem tendsto_compress_sum [CompleteSpace H]
    (U : ℕ → Submodule 𝕜 H) [∀ n, (U n).HasOrthogonalProjection]
    (hmono : Monotone U) (hdense : (⨆ n, U n).topologicalClosure = ⊤)
    {ι : Type*} (s : Finset ι) (Y : ι → H →L[𝕜] H)
    (hc : ∀ i ∈ s, IsCompactOperator (Y i)) (hsa : ∀ i ∈ s, IsSelfAdjoint (Y i)) :
    Tendsto (fun n ↦ ∑ i ∈ s, compress (U n).starProjection (Y i)) atTop
      (𝓝 (∑ i ∈ s, Y i)) := by
  apply tendsto_finsetSum
  intro i hi
  exact tendsto_compress (fun n ↦ (U n).starProjection)
    (fun n ↦ (U n).starProjection_norm_le) (fun n ↦ isSelfAdjoint_starProjection (U n))
    (fun x ↦ Submodule.starProjection_tendsto_self U hmono x hdense.ge) (Y i) (hc i hi) (hsa i hi)

end JanetCartan.OperatorCompression
