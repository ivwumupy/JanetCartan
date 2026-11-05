module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.Freezing

/-!
# Common balls for the literal frozen inverse

The original common balls are contracted once so their output radius is at
most the input radius. The shared `frozenInverse_common_ball` then transfers
domain containment and the inverse range to the frozen inverse. The doubled
output ball leaves an open buffer for the supported constructor.
Consumer: `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`
(`new:lem:scaling`, `app:ch_background:eq:bg-Psi`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Actual input/output balls and frozen augmented half-gap, chosen before
`Q`. The three local analytic premises are precisely the smooth chart,
buffered inverse and transverse outputs of `exists_frozen_conic_inputs`.
No frozen inverse range or frozen differential estimate is assumed
(`new:lem:scaling`, `app:ch_background:eq:bg-Psi`). -/
theorem exists_frozen_primitive_balls {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {r a cap : ℝ} (hr : 0 < r) (ha : 0 < a) (hcap : 0 < cap)
    (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let q₀ := frozenAugmentedChart T p₀
    ∃ ρ > (0 : ℝ), ρ < cap ∧ closedBall p₀ ρ ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧
    ∃ τ > (0 : ℝ), 2 * τ ≤ ρ ∧ ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) →
      ∀ {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
        {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
      (∀ p ∈ physicalParameterSet z₀ (6 * a),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      closedBall q₀ (2 * τ) ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r (6 * a)))
        (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
      (∀ p ∈ closedBall p₀ ρ,
        ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ closedBall p₀ ρ,
        ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
  let q₀ := frozenAugmentedChart T p₀
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  have hcenter : q₀ = ((0, 0, k), spectatorCenter z₀) := frozenAugmentedChart_center T hP hz₀ hinc
  obtain ⟨ρ, hρ, hρcap, hinput, τ₀, hτ₀, δ, hδ, hballs⟩ :=
    exists_common_conic_balls T hP hz₀ hk hinc hd hr ha hcap
  let τ := min τ₀ ρ / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have htτ : 2 * τ ≤ τ₀ := by dsimp [τ]; linarith [min_le_left τ₀ ρ]
  have htρ : 2 * τ ≤ ρ := by dsimp [τ]; linarith [min_le_right τ₀ ρ]
  refine ⟨ρ, hρ, hρcap, hinput, τ, hτ, htρ, δ, hδ, ?_⟩
  intro Q hQ hf b cJ V L G hInv htrans
  obtain ⟨houtput, hrange, hgap⟩ := hballs Q hQ hf hInv htrans
  rw [frozenAugmentedChart_center T hP hz₀ hinc] at houtput hrange
  have hfrozen := frozenInverse_common_ball T Q htρ
    ((closedBall_subset_closedBall htτ).trans houtput)
    (hrange.mono_left (closedBall_subset_closedBall htτ))
  rw [← hcenter] at hfrozen
  exact ⟨hfrozen.1, hfrozen.2,
    frozenAugmented_halfGap_of_original T Q hP hr har hcarrier hz₀ hinc hd hηb
      hinput hf hgap, hgap⟩

end JanetCartan.ContinuumNormal.FrozenModel
