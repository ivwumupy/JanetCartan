module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Periodization

/-!
# Actual periodic geometric coefficients

The coefficient input of `ContinuumRow.imageChannel` in
`app:ch_background:defn:bg-row` is constructed from the actual reference's
C8 neighborhood. The cutoff and every constant precede the varying map.
The full physical derivative bound retains the reserve two in
`app:ch_background:eq:bg-frame-tame`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace JanetCartan.ContinuumRow.ImageGeometry

open GeometricProfile Periodization

variable {n : ℕ}

/-- Construct every periodic principal and connection coefficient from primitive
C8 closeness to the actual reference (`app:ch_background:defn:bg-row`).
The literal formula retains the negative Christoffel contraction in each
zeroth-order entry. No coefficient estimate or admissible-jet containment is
an input. The constants and cutoff precede both the map and the high order. -/
theorem exists_reference_periodic_coefficients (G : FlatReference n)
    {r₀ r₁ R : ℝ} (hr₀ : 0 < r₀) (h₀₁ : r₀ < r₁) (h₁R : r₁ < R)
    (hRG : R < G.domain.chartRadius) (hR : R < 1 / 2) :
    ∃ (χ : Euclidean n → ℝ) (δ B : ℝ) (C : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.ball 0 r₁ ∧
      Metric.closedBall 0 r₀ ⊆ interior {x | χ x = 1} ∧
      0 < δ ∧ 0 < B ∧ (∀ m, 0 < C m) ∧
      ∀ F : Euclidean n → Euclidean (embeddingDimension n), ContDiff ℝ ∞ F →
        cNorm (Metric.closedBall 0 R) 8 (F - G.map) < δ →
        ∃ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
          (∀ j z, c j z = χ (AmplitudeBound.centeredTorusRepresentative z) *
            geometricReducedCoefficients F (AmplitudeBound.centeredTorusRepresentative z) j) ∧
          (∀ j, IsSmoothPeriodic (c j)) ∧
          (∀ j x, x ∈ Metric.closedBall 0 r₀ →
            periodicLift (c j) =ᶠ[𝓝 x] (fun y ↦ geometricReducedCoefficients F y j)) ∧
          (∀ m j x, ‖iteratedFDeriv ℝ m (periodicLift (c j)) x‖ ≤
            C m * (1 + cNorm (Metric.closedBall 0 R) (m + 2) F)) ∧
          (∀ j z, |c j z| ≤ B) := by
  obtain ⟨χ, D, hχ, hrange, hcompact, hs, hp, hD, hperiod⟩ :=
    exists_cutoff_periodicReducedCoefficients n hr₀ h₀₁ h₁R hR
  obtain ⟨δ, hδ, B, hB, C, hC, hgeom⟩ :=
    exists_reference_reduced_coefficient_estimates G (hr₀.trans h₀₁) h₁R hRG
  refine ⟨χ, δ, B, fun m ↦ D m * C m, hχ, hrange, hcompact, hs, hp,
    hδ, hB, fun m ↦ mul_pos (hD m) (hC m), ?_⟩
  intro F hF hclose
  obtain ⟨hq, hlow, hhigh⟩ := hgeom F hF hclose
  obtain ⟨c, hformula, hc, heq, hderiv, hsup⟩ := hperiod _ hq
  refine ⟨c, hformula, hc, heq, ?_, fun j z ↦ (hsup j z).trans hlow⟩
  intro m j x
  exact (hderiv m j x).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hhigh m) (hD m).le)

/-- Neighborhood agreement of the actual arrays gives agreement of every full
physical jet, including coefficient derivatives in the formal adjoint
(`app:ch_waves:eq:reduced-symbol`). -/
theorem coefficient_jets_eq_of_eventuallyEq
    (F : Euclidean n → Euclidean (embeddingDimension n))
    (c : ReducedCoefficientIndex n → C(Torus n, ℝ)) {x : Euclidean n}
    (hc : ∀ j, periodicLift (c j) =ᶠ[𝓝 x]
      (fun y ↦ geometricReducedCoefficients F y j)) (m : ℕ) (j : ReducedCoefficientIndex n) :
    iteratedFDeriv ℝ m (periodicLift (c j)) x =
      iteratedFDeriv ℝ m (fun y ↦ geometricReducedCoefficients F y j) x :=
  ((hc j).iteratedFDeriv ℝ m).self_of_nhds

end JanetCartan.ContinuumRow.ImageGeometry
