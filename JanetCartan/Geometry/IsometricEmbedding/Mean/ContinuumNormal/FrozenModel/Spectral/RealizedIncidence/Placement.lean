module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.RootGeometry.Placement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.IncidenceScaling

/-!
# Incidence plateaux for the realized radial representative

The supported carrier constructor uses a small radial representative and returns
smaller conic radii. The roots still belong to the original sphere charts. This
leaf places those SAME roots in the actual smaller angular masks, using the
retained normalized tangential direction. Its consumer is
`exists_constructed_incidence_positive_weights_of_direction`, and then the finite
cover for the realized symbols (`app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

/-- The constructed roots in the original frequency chart lie on the plateaux
of the literal mask with any nonzero reference covector having the retained
tangential direction. In particular, `exists_small_incidence_representative`
supplies `hdir`, and `exists_canonicalFrozen_supported_carrier_unit` supplies
the actual smaller `r` and `a₀`. The new neighborhood and root tolerance are
chosen AFTER these radii and BEFORE extracting a finite cover or constructing
the common root family (`app:ch_seed:eq:seed-actual-detection`,
`app:ch_background:prop:bg-frame`). -/
theorem exists_constructed_incidence_plateau_tolerance_of_direction {n : ℕ} {D : CoverData n}
    {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀) {R : IncidenceRefinement D} (hR : R.IsValid)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (j : Fin R.chartCount) (a : Fin (D.patchCount (R.sourceChart j)))
    {κ₀ : Euclidean n} (hκ₀ : κ₀ ∈ ball (R.center j) (2 * R.radius j))
    (hκ₀ne : κ₀ ≠ 0) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    (hdir : NormedSpace.normalize ηb = NormedSpace.normalize
      ((T ⟨R.sourceChart j, a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint κ₀))
    {r a₀ c εmax : ℝ} (hr : 0 < r) (ha : 0 < a₀)
    (hc : 0 < c) (hεmax : 0 < εmax) :
    let T₀ := T ⟨R.sourceChart j, a⟩
    let z₀ := D.roots (R.sourceChart j) a κ₀
    ∃ ρ ε₀ : ℝ, 0 < ρ ∧ 0 < ε₀ ∧ ε₀ ≤ εmax ∧
      ε₀ / c ≤ a₀ / 8 ∧
      ∀ {s B ε : ℝ}, 0 < s → ε ≤ ε₀ →
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (Θ : (b : Fin D.chartCount) → Fin (D.patchCount b) → Euclidean n → Euclidean 3 → ℝ)
        (g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
          Euclidean n × Euclidean n → ℝ),
      IsConstructedIncidenceRootFamily D R s c B ε Q Θ g →
      ∀ κ ∈ ball κ₀ ρ,
        let z := incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) (g j a (0, κ))
        κ ∈ ball (R.center j) (2 * R.radius j) ∧
        T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ ≠ 0 ∧
        NormedSpace.normalize (T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ) ∈
          closedBall (NormedSpace.normalize ηb) (angularWidth ηb r / 4) ∧
        z 0 ∈ closedBall (z₀ 0) (a₀ / 4) ∧ spectatorCenter z = spectatorCenter z₀ ∧
        angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
          (z 0, spectatorCenter z₀)
          (NormedSpace.normalize (T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ)) = 1 := by
  dsimp only
  let T₀ := T ⟨R.sourceChart j, a⟩
  let η₀ := T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ₀
  have hz := (hD.2.2.2.2.1 (R.sourceChart j) a).2.2.1 κ₀
    (hR.2.1 j (ball_subset_closedBall hκ₀))
  have hη₀ : η₀ ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T₀
    (hD.2.2.2.2.1 (R.sourceChart j) a).1 hz.1 hκ₀ne hz.2.2.2
  let r₀ := r * ‖η₀‖ / ‖ηb‖
  have hr₀ : 0 < r₀ := div_pos (mul_pos hr (norm_pos_iff.mpr hη₀)) (norm_pos_iff.mpr hηb)
  have hwidth : angularWidth η₀ r₀ = angularWidth ηb r := by
    unfold angularWidth
    congr 1
    dsimp only [r₀]
    field_simp
  obtain ⟨hη₀', ρ, ε₀, hρ, hε₀, hεmax, hεc, hplace⟩ :=
    exists_constructed_incidence_plateau_tolerance hD hR T j a hκ₀ hκ₀ne hr₀ ha hc hεmax
  refine ⟨ρ, ε₀, hρ, hε₀, hεmax, hεc, ?_⟩
  intro s B ε hs hε Q Θ g hg κ hκ
  have hp := hplace hs hε Q Θ g hg κ hκ
  change NormedSpace.normalize ηb = NormedSpace.normalize η₀ at hdir
  change _ ∧ _ ∧ _ ∈ closedBall (NormedSpace.normalize η₀) (angularWidth η₀ r₀ / 4) ∧ _ at hp
  rcases hp with ⟨hchart, hne, hθ, hz, hv, _⟩
  have hθ' : NormedSpace.normalize
      (T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ) ∈
      closedBall (NormedSpace.normalize ηb) (angularWidth ηb r / 4) := by
    simpa only [hdir, hwidth] using hθ
  exact ⟨hchart, hne, hθ', hz, hv, angularMask_one _ _ ha (angularWidth_spec hηb hr).1
    hz (mem_closedBall_self (by positivity)) hθ'⟩

end JanetCartan.ContinuumNormal.FrozenModel
