module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Cutoffs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image

/-!
# The actual geometric reduced operator and its periodic realization

These identifications connect the constructed arrays to the existing weak
operator and image channel of `app:ch_background:defn:bg-row`. The physical
operator retains every Christoffel term of `app:ch_waves:eq:reduced-symbol`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.ContinuumRow.ImageGeometry

open GeometricProfile

variable {n : ℕ}

/-- Local agreement of the constructed coefficients identifies the literal
reduced operator, using the actual periodic test jets
(`app:ch_waves:eq:reduced-symbol`). -/
theorem reducedPeriodicFormula_eq_geometric_of_eventuallyEq
    (F : Euclidean n → Euclidean (embeddingDimension n))
    (c : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) {x : Euclidean n}
    (hc : ∀ j, periodicLift (c j) =ᶠ[𝓝 x]
      (fun y ↦ geometricReducedCoefficients F y j)) :
    reducedPeriodicFormula c f (torusQuotient x) =
      WithLp.toLp 2 (NullTransport.reducedOperator F
        (fun y i ↦ (StressFrame.geometricCubeStress F y i).val) (periodicLift f) x) := by
  apply PiLp.ext
  intro i
  exact congr_fun (reducedPeriodicFormula_eq_geometric F c f hf x
    (fun j ↦ (hc j).self_of_nhds)) i

/-- After a fixed supported measurement cutoff, the periodic formula is the
actual physical reduced operator in the centered chart, at every torus point
(`app:ch_background:defn:bg-row`). -/
theorem cutoff_reducedPeriodicFormula_eq_geometric
    (F : Euclidean n → Euclidean (embeddingDimension n))
    (c : ReducedCoefficientIndex n → C(Torus n, ℝ)) {r : ℝ}
    (hc : ∀ j x, x ∈ Metric.closedBall 0 r → periodicLift (c j) =ᶠ[𝓝 x]
      (fun y ↦ geometricReducedCoefficients F y j))
    (ψ : Euclidean n → ℝ) (hs : tsupport ψ ⊆ Metric.closedBall 0 r)
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) (z : Torus n) :
    ψ (AmplitudeBound.centeredTorusRepresentative z) • reducedPeriodicFormula c f z =
      ψ (AmplitudeBound.centeredTorusRepresentative z) •
        WithLp.toLp 2 (NullTransport.reducedOperator F
          (fun y i ↦ (StressFrame.geometricCubeStress F y i).val) (periodicLift f)
          (AmplitudeBound.centeredTorusRepresentative z)) := by
  by_cases hz : ψ (AmplitudeBound.centeredTorusRepresentative z) = 0
  · simp only [hz, zero_smul]
  · congr 1
    simpa only [AmplitudeBound.torusQuotient_centeredTorusRepresentative] using
      reducedPeriodicFormula_eq_geometric_of_eventuallyEq F c f hf
        (fun j ↦ hc j _ (hs (subset_tsupport ψ hz)))

/-- The bounded weak operator, localized by the fixed measurement cutoff, has
exactly the geometric smooth representative on the entire torus
(`app:ch_background:defn:bg-row`). This equality uses torus volume throughout. -/
theorem cutoff_reducedWeakOperator_ofSmooth_ae
    (F : Euclidean n → Euclidean (embeddingDimension n))
    (c : ReducedCoefficientIndex n → C(Torus n, ℝ)) {r : ℝ} (hr : r < 1 / 2)
    (hc : ∀ j x, x ∈ Metric.closedBall 0 r → periodicLift (c j) =ᶠ[𝓝 x]
      (fun y ↦ geometricReducedCoefficients F y j))
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall 0 r)
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    cutoffMultiplier (periodizedImageCutoff hr ψ hψ hs)
      (reducedWeakOperator c (PeriodicSobolevSpace.ofSmooth 1 f hf)) =ᵐ[volume]
      fun z ↦ ψ (AmplitudeBound.centeredTorusRepresentative z) •
        WithLp.toLp 2 (NullTransport.reducedOperator F
          (fun y i ↦ (StressFrame.geometricCubeStress F y i).val) (periodicLift f)
          (AmplitudeBound.centeredTorusRepresentative z)) := by
  filter_upwards [cutoffMultiplier_coeFn (periodizedImageCutoff hr ψ hψ hs)
    (reducedWeakOperator c (PeriodicSobolevSpace.ofSmooth 1 f hf)),
    reducedWeakOperator_ofSmooth_ae c f hf] with z hz hred
  rw [hz, hred, periodizedImageCutoff_apply]
  exact cutoff_reducedPeriodicFormula_eq_geometric F c hc ψ hs f hf z

/-- Coefficient first jets identify the full formal adjoint on the physical
agreement region. Both differentiated principal coefficients and the transposed
zeroth-order connection term occur (`app:ch_waves:eq:reduced-symbol`). -/
theorem reducedFormalAdjoint_eq_geometric_jets
    (F : Euclidean n → Euclidean (embeddingDimension n))
    (c : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j))
    (g : Torus n → Euclidean n) (hg : IsSmoothPeriodic g) {x : Euclidean n}
    (heq : ∀ j, periodicLift (c j) =ᶠ[𝓝 x]
      (fun y ↦ geometricReducedCoefficients F y j)) (k : Fin n) :
    reducedFormalAdjoint c g (torusQuotient x) k =
      -(∑ a, ∑ i, fderiv ℝ (fun y ↦ geometricReducedCoefficients F y (.inl (a, i, k))) x
        (EuclideanSpace.single a 1) * periodicLift g x i) -
      (∑ a, ∑ i, geometricReducedCoefficients F x (.inl (a, i, k)) *
        (fderiv ℝ (periodicLift g) x (EuclideanSpace.single a 1)) i) +
      ∑ i, geometricReducedCoefficients F x (.inr (i, k)) * periodicLift g x i := by
  have hder (a : Fin n) (j : ReducedCoefficientIndex n) :
      periodicCoordinateDeriv a (c j) (torusQuotient x) =
        fderiv ℝ (fun y ↦ geometricReducedCoefficients F y j) x
          (EuclideanSpace.single a 1) := by
    have h := congr_fun (periodicLift_coordinateDeriv (hc j).2 a) x
    change periodicCoordinateDeriv a (c j) (torusQuotient x) = _ at h
    rw [(heq j).fderiv_eq] at h
    exact h
  have htest (a : Fin n) : periodicCoordinateDeriv a g (torusQuotient x) =
      fderiv ℝ (periodicLift g) x (EuclideanSpace.single a 1) :=
    congr_fun (periodicLift_coordinateDeriv hg.2 a) x
  rw [reducedFormalAdjoint_apply_expanded c hc g hg]
  simp only [hder, htest, show ∀ j, c j (torusQuotient x) =
    geometricReducedCoefficients F x j from fun j ↦ (heq j).self_of_nhds,
    periodicLift, Function.comp_apply]

end JanetCartan.ContinuumRow.ImageGeometry
