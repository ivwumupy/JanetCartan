module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Periodization
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.HistoryGeometry

/-!
# History image profiles on the initialized coefficient cutoff

The source/history coercivity constructor already supplies its image array.
Its literal formula identifies it with the smooth periodization on the same
coefficient cutoff. The actual history displacement gives the reference
neighborhood, so neither a coefficient estimate nor a new cutoff is assumed.

Consumer: the `hcjet` input of
`ContinuumCommutator.exists_retained_history_elliptic_estimates_with_exterior`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse
open GeometricProfile ContinuumRow.ImageGeometry ContinuumRow.ImageGeometry.Periodization

/-- The literal image array of every admissible history has reserve-two jet
bounds on the supplied initialized coefficient cutoff. The constants precede
all histories and arrays. Equality of the geometric formula transfers both
smoothness and every derivative estimate to the already constructed array
(`app:ch_background:defn:bg-row`, `app:ch_background:eq:bg-frame-tame`,
`app:ch_background:eq:bg-commutator`, `main:eq:displacement-budget`). -/
theorem exists_prescribed_history_image_coefficient_profiles
    {n : ℕ} (G : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (hcell : r < 1 / 2)
    {χ : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ ball 0 r) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ P : ℕ → ℝ, (∀ m, 0 < P m) ∧ ∃ T : ℝ, 2 ≤ T ∧
      ∀ R₀, T ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin stage → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      ∀ coeff : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j x, coeff j x = χ (AmplitudeBound.centeredTorusRepresentative x) *
          geometricReducedCoefficients F (AmplitudeBound.centeredTorusRepresentative x) j) →
        (∀ j, IsSmoothPeriodic (coeff j)) ∧
        ∀ m j x, ‖iteratedFDeriv ℝ m (periodicLift (coeff j)) x‖ ≤
          P m * (1 + cNorm (closedBall (0 : Euclidean n) R) (m + 2) F) := by
  obtain ⟨δ, hδ, _B, _hB, C, hC, hcoeff⟩ :=
    exists_reference_reduced_coefficient_estimates G hr hrR hR
  obtain ⟨T, hT, hnear⟩ :=
    HistoryGeometry.exists_initialScale_for_c8_neighborhood G.map R horder hδ
  refine ⟨fun m ↦ cutoffDerivativeBound χ r m * C m,
    fun m ↦ mul_pos (cutoffDerivativeBound_pos χ r m) (hC m), T, hT, ?_⟩
  intro R₀ hR₀ stage u ell hu F coeff hformula
  obtain ⟨hreg, _hlow, hjets⟩ := hcoeff F
    (hu.contDiff_finiteHistoryMap G.contDiff) (hnear R₀ hR₀ stage u ell hu)
  let selected := periodicReducedCoefficients hrR hcell hχ hs
    (geometricReducedCoefficients F) hreg
  have heq : coeff = selected := by
    funext j
    apply ContinuousMap.ext
    intro x
    exact (hformula j x).trans
      (periodicReducedCoefficients_apply hrR hcell hχ hs
        (geometricReducedCoefficients F) hreg j x).symm
  rw [heq]
  refine ⟨fun j ↦ isSmoothPeriodic_cutCoefficient hrR hcell hχ hs hreg j, ?_⟩
  intro m j x
  exact (norm_iteratedFDeriv_periodicReducedCoefficients_le hrR hcell hχ hs
    (geometricReducedCoefficients F) hreg m j x).trans
      ((mul_le_mul_of_nonneg_left (hjets m) (cutoffDerivativeBound_pos χ r m).le).trans_eq
        (mul_assoc _ _ _).symm)

end JanetCartan.ContinuumInverse
