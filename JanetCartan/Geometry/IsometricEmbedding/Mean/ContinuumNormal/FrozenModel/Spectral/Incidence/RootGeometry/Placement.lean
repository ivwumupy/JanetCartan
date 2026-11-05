module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.CanonicalData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence

/-!
# Place the constructed roots in the original angular plateaux

The consumer is `exists_canonicalFrozen_weight_threshold`, specifically its
original-mask premise. All neighborhoods are local to an arbitrary reference
frequency in the SAME refined chart. No assertion about coverage after shrinking
the frequency balls is made (`app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

/-- Continuity of the frozen root and of normalized adapted projection gives
a positive frequency neighborhood inside the retained refined chart. An actual
root within `a₀/8` of the frozen root then lies in the ORIGINAL `a₀/4` incidence
plateau and `angularWidth/4` directional plateau. The zero spectators are retained
(`app:ch_seed:eq:seed-actual-detection`, `app:ch_background:prop:bg-frame`). -/
theorem exists_frozen_incidence_plateau_neighborhood {n : ℕ} {D : CoverData n}
    {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀) {R : IncidenceRefinement D} (hR : R.IsValid)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (j : Fin R.chartCount) (a : Fin (D.patchCount (R.sourceChart j)))
    {κ₀ : Euclidean n} (hκ₀ : κ₀ ∈ ball (R.center j) (2 * R.radius j))
    (hκ₀ne : κ₀ ≠ 0) {r a₀ : ℝ} (hr : 0 < r) (ha : 0 < a₀) :
    let T₀ := T ⟨R.sourceChart j, a⟩
    let z₀ := D.roots (R.sourceChart j) a κ₀
    let ηb := T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ₀
    ∃ hηb : ηb ≠ 0, ∃ ρ > (0 : ℝ),
      ball κ₀ ρ ⊆ ball (R.center j) (2 * R.radius j) ∧
      ∀ κ ∈ ball κ₀ ρ,
        T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ ≠ 0 ∧
        ‖D.roots (R.sourceChart j) a κ - z₀‖ < a₀ / 8 ∧
        NormedSpace.normalize (T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ) ∈
          closedBall (NormedSpace.normalize ηb) (angularWidth ηb r / 4) ∧
        ∀ z : Euclidean 3, ‖z - D.roots (R.sourceChart j) a κ‖ ≤ a₀ / 8 →
          z 1 = 0 → z 2 = 0 →
          z 0 ∈ closedBall (z₀ 0) (a₀ / 4) ∧ spectatorCenter z = spectatorCenter z₀ ∧
          angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
            (z 0, spectatorCenter z₀)
            (NormedSpace.normalize (T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ)) = 1 := by
  dsimp only
  let T₀ := T ⟨R.sourceChart j, a⟩
  let z₀ := D.roots (R.sourceChart j) a κ₀
  let A := T₀.data.adapted.embedding.toContinuousLinearMap.adjoint
  let ηb := A κ₀
  have hdom := hR.2.1 j (ball_subset_closedBall hκ₀)
  have hsection := (hD.2.2.2.2.1 (R.sourceChart j) a).2
  obtain ⟨hz₀, hz₁, hz₂, hinc⟩ := hsection.2.1 κ₀ hdom
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T₀
    (hD.2.2.2.2.1 (R.sourceChart j) a).1 hz₀ hκ₀ne hinc
  have hroot : ContinuousAt (D.roots (R.sourceChart j) a) κ₀ :=
    hsection.1.continuousOn.continuousAt ((hD.2.2.1 _).mem_nhds hdom)
  have hnorm : ContinuousAt (fun κ ↦ NormedSpace.normalize (A κ)) κ₀ := by
    change ContinuousAt (fun κ ↦ ‖A κ‖⁻¹ • A κ) κ₀
    exact (A.continuous.continuousAt.norm.inv₀ (norm_ne_zero_iff.mpr hηb)).smul
      A.continuous.continuousAt
  have hnear : ∀ᶠ κ in 𝓝 κ₀,
      κ ∈ ball (R.center j) (2 * R.radius j) ∧ A κ ≠ 0 ∧
      ‖D.roots (R.sourceChart j) a κ - z₀‖ < a₀ / 8 ∧
      NormedSpace.normalize (A κ) ∈ ball (NormedSpace.normalize ηb) (angularWidth ηb r / 4) := by
    have he₁ := hroot (ball_mem_nhds _ (show 0 < a₀ / 8 by positivity))
    have he₂ := hnorm (ball_mem_nhds _ (show 0 < angularWidth ηb r / 4 by
      have hh := (angularWidth_spec hηb hr).1; positivity))
    have he₃ : ∀ᶠ κ in 𝓝 κ₀, A κ ≠ 0 :=
      A.continuous.continuousAt (isOpen_ne.mem_nhds hηb)
    filter_upwards [isOpen_ball.mem_nhds hκ₀, he₁, he₂, he₃] with κ hκ h₁ h₂ h₃
    exact ⟨hκ, h₃, by simpa only [mem_preimage, mem_ball, dist_eq_norm] using h₁, h₂⟩
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨hηb, ρ, hρ, fun κ hκ ↦ (hsub hκ).1, ?_⟩
  intro κ hκ
  obtain ⟨_, hne, hrootκ, hnormκ⟩ := hsub hκ
  refine ⟨hne, hrootκ, ball_subset_closedBall hnormκ, ?_⟩
  intro z hz h₁ h₂
  have hdist : ‖z - z₀‖ < a₀ / 4 := by
    calc
      ‖z - z₀‖ ≤ ‖z - D.roots (R.sourceChart j) a κ‖ +
          ‖D.roots (R.sourceChart j) a κ - z₀‖ := by
            simpa only [dist_eq_norm] using dist_triangle z (D.roots (R.sourceChart j) a κ) z₀
      _ < a₀ / 4 := by linarith
  have hs : z 0 ∈ closedBall (z₀ 0) (a₀ / 4) := by
    rw [mem_closedBall, Real.dist_eq]
    exact (PiLp.norm_apply_le (z - z₀) 0).trans hdist.le
  have hv : spectatorCenter z = spectatorCenter z₀ := by
    simp only [spectatorCenter, z₀, h₁, h₂, hz₁, hz₂]
  refine ⟨hs, hv, ?_⟩
  apply angularMask_one
  · exact hs
  · exact mem_closedBall_self (by positivity)
  · exact ball_subset_closedBall hnormκ

/-- Choose the explicit smaller root tolerance `min εmax (c * (a₀/8))`
and a positive frequency neighborhood for the SAME `R` and every constructed
root family `g`. The actual producer is the final quantified clause of
`exists_constructed_incidence_roots`: applying that clause at this positive
`ε₀ ≤ εmax` supplies the primitive componentwise frame threshold and `g`.
The parent may first take a finite minimum of these tolerances, then apply
that one producer once; this theorem remains valid for that same `g`
(`app:ch_seed:eq:seed-actual-detection`, `app:ch_background:prop:bg-frame`). -/
theorem exists_constructed_incidence_plateau_tolerance {n : ℕ} {D : CoverData n}
    {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀) {R : IncidenceRefinement D} (hR : R.IsValid)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (j : Fin R.chartCount) (a : Fin (D.patchCount (R.sourceChart j)))
    {κ₀ : Euclidean n} (hκ₀ : κ₀ ∈ ball (R.center j) (2 * R.radius j))
    (hκ₀ne : κ₀ ≠ 0) {r a₀ c εmax : ℝ} (hr : 0 < r) (ha : 0 < a₀)
    (hc : 0 < c) (hεmax : 0 < εmax) :
    let T₀ := T ⟨R.sourceChart j, a⟩
    let z₀ := D.roots (R.sourceChart j) a κ₀
    let ηb := T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ₀
    ∃ hηb : ηb ≠ 0, ∃ ρ ε₀ : ℝ, 0 < ρ ∧ 0 < ε₀ ∧ ε₀ ≤ εmax ∧
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
  obtain ⟨hηb, ρ, hρ, hsub, hplace⟩ :=
    exists_frozen_incidence_plateau_neighborhood hD hR T j a hκ₀ hκ₀ne hr ha
  let ε₀ := min εmax (c * (a₀ / 8))
  have he : ε₀ / c ≤ a₀ / 8 :=
    (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using min_le_right εmax (c * (a₀ / 8)))
  refine ⟨hηb, ρ, ε₀, hρ, lt_min hεmax (by positivity), min_le_left _ _, he, ?_⟩
  intro s B ε hs hε Q Θ g hg κ hκ
  have hv : (0, κ) ∈ ball (0 : Euclidean n) (3 * s) ×ˢ
      ball (R.center j) (2 * R.radius j) := ⟨by simpa using (show 0 < 3 * s by positivity), hsub hκ⟩
  have hz := (hg j a).2.2.1 (0, κ) hv
  have herror := hz.2.2.2.2.2.2.1.trans
    ((div_le_div_of_nonneg_right hε hc.le).trans he)
  have hp := (hplace κ hκ).2.2.2 _ herror hz.2.2.1 hz.2.2.2.1
  exact ⟨hsub hκ, (hplace κ hκ).1, (hplace κ hκ).2.2.1, hp⟩
end JanetCartan.ContinuumNormal.FrozenModel
