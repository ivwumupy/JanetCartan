module

public import JanetCartan.Geometry.IsometricEmbedding.CoordinateTransfer
public import JanetCartan.Geometry.IsometricEmbedding.MetricPreservation
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth positive metrics in inverse coordinates

For Theorem `main:thm:main` of `paper.tex`, the manifold-to-Euclidean reduction
in `CoordinateTransfer/LocalExistence.lean` needs a smooth positive definite
coordinate metric. We prove these properties for the existing
`inverseCoordinateMetric`: smoothness follows by evaluating the smooth bundle
metric on the tangent map, and positivity follows from injectivity of the
inverse-coordinate differential. For a smooth partial-homeomorphism chart,
the inverse chain rule supplies this injectivity on its target.
-/

@[expose] public noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Frobenius
open Bundle TopologicalSpace Set

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- `main:thm:main`: the inverse-coordinate metric is positive definite when
the differential of the inverse coordinates is injective. No regularity of the
metric or coordinate map is needed for this algebraic assertion. -/
theorem posDef_inverseCoordinateMetric {n : ℕ}
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {ψ : Euclidean n → M} {y : Euclidean n}
    (hψ : Function.Injective (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ψ y)) :
    (inverseCoordinateMetric g ψ y).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    exact g.symm (ψ y) _ _
  · intro x hx
    let v : Euclidean n := WithLp.toLp 2 x
    have hv : v ≠ 0 := by
      intro h
      apply hx
      funext i
      exact congrArg (fun z : Euclidean n ↦ z i) h
    let D : Euclidean n →L[ℝ] TangentSpace 𝓘(ℝ, E) (ψ y) :=
      (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ψ y).comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.toContinuousLinearMap
    have hDv : D v ≠ 0 := fun h ↦ hv (hψ (h.trans (map_zero _).symm))
    have hsum : ∑ i, x i • D (EuclideanSpace.single i 1) = D v := by
      simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
        EuclideanSpace.basisFun_apply] using
        congrArg D ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)
    have hpos := g.pos (ψ y) (D v) hDv
    rw [← hsum] at hpos
    simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial,
      inverseCoordinateMetric, map_sum, map_smul, sum_apply, smul_apply,
      smul_eq_mul, Finset.mul_sum] at hpos ⊢
    rw [Finset.sum_comm] at hpos
    convert hpos using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change x i * (g.inner (ψ y) (D (EuclideanSpace.single i 1))
      (D (EuclideanSpace.single j 1)) * x j) =
      x j * (x i * g.inner (ψ y) (D (EuclideanSpace.single i 1))
        (D (EuclideanSpace.single j 1)))
    ring

/-- `main:thm:main`: differentiating the chart followed by its inverse gives a
left inverse to the inverse-chart derivative, hence injectivity on the target. -/
theorem mfderiv_inverseCoordinates_injective {n : ℕ}
    (e : OpenPartialHomeomorph M (Euclidean n))
    (he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) ∞ e e.source)
    (he' : ContMDiffOn 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ∞ e.symm e.target)
    {y : Euclidean n} (hy : y ∈ e.target) :
    Function.Injective (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) e.symm y) := by
  have hed : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) :=
    ⟨he.mdifferentiableOn (by simp), he'.mdifferentiableOn (by simp)⟩
  have hleft : Function.LeftInverse
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) e (e.symm y))
      (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) e.symm y) := by
    intro v
    exact congrArg (fun L ↦ L v) (hed.comp_symm_deriv hy)
  exact hleft.injective

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- `main:thm:main`: pulling back a smooth manifold metric by a smooth inverse
coordinate map gives a smooth matrix field on its open domain. This supplies the
regularity input for `CoordinateTransfer/LocalExistence.lean`. -/
theorem contDiffOn_inverseCoordinateMetric {n : ℕ}
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {ψ : Euclidean n → M} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hψ : ContMDiffOn 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ∞ ψ s) :
    ContDiffOn ℝ ∞ (inverseCoordinateMetric g.toRiemannianMetric ψ) s := by
  -- Assemble the coefficient functions into matrices with the Frobenius norm.
  let ofEntries : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
    { LinearMap.id with cont := continuous_id }
  apply ofEntries.contDiff.comp_contDiffOn
  apply contDiffOn_pi.2
  intro i
  apply contDiffOn_pi.2
  intro j y hy
  have hψy := hψ.contMDiffAt (hs.mem_nhds hy)
  have hv (v : Euclidean n) :
      ContMDiffAt 𝓘(ℝ, Euclidean n) (𝓘(ℝ, E).tangent) ∞
        (fun z ↦ (⟨ψ z, mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ψ z v⟩ :
          TangentBundle 𝓘(ℝ, E) M)) y := by
    have hc : ContMDiffAt 𝓘(ℝ, Euclidean n) (𝓘(ℝ, Euclidean n).tangent) ∞
        (fun z ↦ (⟨z, v⟩ : TangentBundle 𝓘(ℝ, Euclidean n) (Euclidean n))) y :=
      contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
    exact (hψy.contMDiffAt_tangentMap (X := ⟨y, v⟩) (by simp)).comp y hc
  have hg := g.contMDiff.contMDiffAt.comp y hψy
  have happ := hg.clm_bundle_apply₂ (E₃ := Bundle.Trivial M ℝ) (F₃ := ℝ)
    (hv (EuclideanSpace.single i 1)) (hv (EuclideanSpace.single j 1))
  have hscalar := (contMDiffAt_totalSpace.mp happ).2
  exact hscalar.contDiffAt.contDiffWithinAt

/-- `main:thm:main`: the actual inverse-coordinate metric of a smooth
partial-homeomorphism chart is a smooth positive definite metric on the target.
This is the metric input for `CoordinateTransfer/LocalExistence.lean`; smoothness
and positivity of the pullback are conclusions, not additional assumptions. -/
theorem isRiemannianMetricOn_inverseCoordinateMetric {n : ℕ}
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (e : OpenPartialHomeomorph M (Euclidean n))
    (he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) ∞ e e.source)
    (he' : ContMDiffOn 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ∞ e.symm e.target) :
    IsRiemannianMetricOn (inverseCoordinateMetric g.toRiemannianMetric e.symm) e.target :=
  ⟨contDiffOn_inverseCoordinateMetric g e.open_target he',
    fun _ hy ↦ posDef_inverseCoordinateMetric g.toRiemannianMetric
      (mfderiv_inverseCoordinates_injective e he he' hy)⟩

end JanetCartan
