module

public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Iteration.PhysicalMean.GroupedCurrent
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Measure
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet
public import JanetCartan.Analysis.Fourier.SeparatedSampling
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.SampledRow

/-!
# Exact canonical/native physical identities on the original core

Consumer: the physical full Hermitian profile, then the SAME completed mean.
The canonical correction is identified with the complete native individual
field before taking its tensor square. The original base is retained literally
as its physical periodic lift, so no replacement initializer or base-field
realization hypothesis is introduced. Only the correction's original kernel
and original real-adjoint realization are used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open CurrentMean SmoothPeriodicFamily CanonicalChange PhysicalForwardMean PhysicalSamplingShells
  RawInputRealization RawInputPartition ContinuumRow PeriodicLocalL2

variable {n N J : ℕ} {ν : Type*} [Fintype ν]
    (φ : ν → RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (m : ν → RefinedIndex J × Euclidean (n-1) → ℝ)
    (amp : ν → Fin N → Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (hφ : ∀ i, Continuous (Function.uncurry (φ i)))
    (hm : ∀ i, Continuous (m i)) (hms : ∀ i, HasCompactSupport (m i))
    (hamp : ∀ i a c, Continuous (fun z : (RefinedIndex J × Euclidean (n-1)) × Euclidean n ↦
      amp i a c z.1.1 z.1.2 z.2))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hampK : ∀ i a c j η, tsupport (amp i a c j η) ⊆ K)
    (A : ν → Input n (refinedRadius (J := J)) →L[ℝ] OutputL2 n)
    (An : ν → Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hArep : ∀ i, (A i).comp
      ((annularShellEquiv (V := ℂ) (refinedRadius (J := J))).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      transferOutputOperator (realQuadratureChannel (An i)))
    (G : ν → Input n (refinedRadius (J := J)) →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (hG : ∀ i w z, (G i w).val z () = ∑ j : RefinedIndex J,
      (∫ η, ((fun a c ↦ physicalForwardKernel (fun η ↦ φ i (j,η)) (fun η ↦ m i (j,η)*Real.sqrt ‖η‖)
        (fun η y ↦ amp i a c j η y) (AmplitudeBound.centeredTorusRepresentative z) η*w j η) :
          Matrix (Fin N) (Fin n) ℂ) ∂annularMeasure n (refinedRadius j) : Matrix (Fin N) (Fin n) ℂ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)

include hφ hm hms hamp hK hampK hArep hG

omit [Fintype ν] in
/-- The actual canonical derivative family equals the WHOLE original native
source field of the SAME corrected adjoint and current inverse, at every torus
point. All annular cross terms are retained before squaring (`main:prop:mean`). -/
theorem fixedSourceDerivative_eq_individualNativeField (u : SmoothResidual n) (z : Torus n) (i : ν) :
    (fixedSourceDerivative A G Q₀ u).val z i =
      individualNativeInverseField (φ i) (m i) (amp i) (An i) Q₀ (smoothResidualToL2 n u)
        (AmplitudeBound.centeredTorusRepresentative z) := by
  change (G i ((A i).adjoint (Q₀ (smoothResidualToL2 n u)))).val z () = _
  rw [hG]
  exact congrFun (groupedOriginalCurrentField_eq_individualNativeInverseField
    φ m amp hφ hm hms hamp hK hampK A An hArep Q₀ (smoothResidualToL2 n u) i)
      (AmplitudeBound.centeredTorusRepresentative z)

/-- Exact FULL self tensor of the original initialized base plus the actual
finite-source canonical correction. No measured contraction or shell-diagonal
surrogate replaces this tensor (`main:eq:mean-normal-field`). -/
theorem fixedSourceFullHermitian_eq_native (μ : ν → ℝ)
    (base : SmoothPeriodicFamily n ν (Matrix (Fin N) (Fin n) ℂ))
    (u : SmoothResidual n) (z : Torus n) :
    weightedHermitianTensor μ (base+fixedSourceDerivative A G Q₀ u).val z =
      ∑ i, μ i • hermitianTensor (base.val z i+
        individualNativeInverseField (φ i) (m i) (amp i) (An i) Q₀ (smoothResidualToL2 n u)
          (AmplitudeBound.centeredTorusRepresentative z)) := by
  change (∑ i, μ i • hermitianTensor (base.val z i+(fixedSourceDerivative A G Q₀ u).val z i)) = _
  simp_rw [fixedSourceDerivative_eq_individualNativeField φ m amp hφ hm hms hamp hK hampK A An hArep G hG Q₀]

/-- Every physical C-seminorm of the actual FULL sampled tensor agrees with
the native-field expression on the ORIGINAL core. The centered representative
is removed only in a neighborhood of that core, never globally; the SAME
initialized base is retained as its literal periodic lift (`main:prop:mean`). -/
theorem fixedSourceFullHermitian_cNorm_eq_native_on_core (μ : ν → ℝ)
    (base : SmoothPeriodicFamily n ν (Matrix (Fin N) (Fin n) ℂ))
    (u : SmoothResidual n) {r : ℝ} (hr : r < 1/2) (s : ℕ) :
    cNorm (closedBall 0 r) s
      (periodicLift (weightedHermitianTensor μ (base+fixedSourceDerivative A G Q₀ u).val)) =
    cNorm (closedBall 0 r) s (fun x ↦ ∑ i, μ i • hermitianTensor (base.val (torusQuotient x) i+
      individualNativeInverseField (φ i) (m i) (amp i) (An i) Q₀ (smoothResidualToL2 n u) x)) := by
  apply GeometricProfile.cNorm_eq_of_eventuallyEq
  intro x hx
  have hxball : x ∈ ball (0 : Euclidean n) (1/2) := closedBall_subset_ball hr hx
  filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
  have hyn : ‖y‖ < 1/2 := by simpa only [mem_ball, dist_zero_right] using hy
  have hycell : y ∈ halfOpenCell n := by
    intro i
    have hi : |y i| < 1/2 := (PiLp.norm_apply_le y i).trans_lt hyn
    exact ⟨(abs_lt.mp hi).1.le, by linarith [(abs_lt.mp hi).2]⟩
  have he := fixedSourceFullHermitian_eq_native φ m amp hφ hm hms hamp hK hampK A An hArep G hG Q₀ μ base u (torusQuotient y)
  rw [centeredTorusRepresentative_quotient hycell] at he
  exact he

omit hφ hm hms hamp hK hampK hArep hG in
/-- Exact reindexing of the FULL tensor on the original finite sample family.
Every original weight and field value is retained; no norm/cardinality factor
or sample re-selection occurs (`main:prop:mean`). -/
theorem originalSamples_fullHermitian_sum {I : Type*} [Fintype I]
    (p : ℕ) (B : ℝ) (patch : I → SeparatedSampling.Point → ℝ)
    (window : ℝ → ℝ) (mesh : ℝ) (U : I → SeparatedSampling.Lattice → SeparatedSampling.Point)
    (base change : I → SeparatedSampling.Sample → Euclidean n → Matrix (Fin N) (Fin n) ℂ) :
    let τ := CanonicalRowComparison.SampleIndex p B patch window mesh U
    ∀ x : Euclidean n,
      weightedHermitianTensor (CanonicalRowComparison.sampleWeight (p := p) B patch window mesh U)
        (fun y (ia : τ) ↦ base ia.1 ia.2.1 y+change ia.1 ia.2.1 y) x =
      ∑ i, ∑ a ∈ SeparatedSampling.samples p B (patch i) window mesh (U i),
        SeparatedSampling.weight (patch i) window mesh (U i) a • hermitianTensor (base i a x+change i a x) := by
  classical
  intro τ x
  simp only [weightedHermitianTensor, CanonicalRowComparison.SampleIndex,
    CanonicalRowComparison.sampleWeight, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.sum_subtype (SeparatedSampling.samples p B (patch i) window mesh (U i))
    (fun _ ↦ Iff.rfl)
    (fun a ↦ SeparatedSampling.weight (patch i) window mesh (U i) a •
      hermitianTensor (base i a x+change i a x))).symm

end JanetCartan.PhysicalMean
