module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Realization.KernelGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.CommonBalls

/-!
# Common balls for the same frozen inverse

Zeroing the physical positions preserves each centered input/output ball.
The original canonical inverse range therefore supplies the frozen inverse
range after capping the output radius by the input radius. The construction
uses the original common-ball producer; no inverse-range premise is added to
the actual fixed geometric data. Consumer: the supported frozen carrier
constructor (`app:ch_background:eq:bg-Psi`, `bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol

variable {n : ℕ}

/-- Erasing the two physical positions cannot leave a ball centered at zero
positions. The carrier and input frequency are retained (`bg-Psi`). -/
theorem originInput_mem_closedBall_centered_at_zero_positions {z : CarrierParameter} {η : Euclidean (n - 1)}
    {ρ : ℝ} {p : InputVariables n} (hp : p ∈ closedBall ((0, 0), z, η) ρ) :
    originInput p ∈ closedBall ((0, 0), z, η) ρ := by
  have hρ := nonneg_of_mem_closedBall hp
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hp ⊢
  exact ⟨⟨by simpa [originInput] using hρ, by simpa [originInput] using hρ⟩, hp.2⟩

/-- The corresponding output projection keeps the physical frequency and
spectator in the original common output ball (`bg-Psi`). -/
private theorem originOutput_mem_centered_closedBall {k : Euclidean n} {v : Euclidean 2}
    {τ : ℝ} {p : Variables n × Euclidean 2}
    (hp : p ∈ closedBall ((0, 0, k), v) τ) :
    originOutput p ∈ closedBall ((0, 0, k), v) τ := by
  have hτ := nonneg_of_mem_closedBall hp
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hp ⊢
  exact ⟨⟨by simpa [originOutput] using hτ,
    by simpa [originOutput] using hτ, hp.1.2.2⟩, hp.2⟩

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}

/-- Transfer the original common output ball and inverse-range estimate to
the frozen domain and SAME inverse. The sole radius restriction makes the
unchanged output positions fit in the input ball; it is discharged by `min`
in `exists_frozen_common_conic_balls` (`bg-full-complex-amplitude`). -/
theorem frozenInverse_common_ball {k : Euclidean n} {ρ τ : ℝ} (hτρ : τ ≤ ρ)
    (houtput : closedBall ((0, 0, k), spectatorCenter z₀) τ ⊆
      symbolDomain T Q z₀ ηb r a)
    (hrange : MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r a))
      (closedBall ((0, 0, k), spectatorCenter z₀) τ)
      (closedBall ((0, 0), (z₀ 0, spectatorCenter z₀), ηb) ρ)) :
    closedBall ((0, 0, k), spectatorCenter z₀) τ ⊆ frozenSymbolDomain T Q z₀ ηb r a ∧
    MapsTo (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r a))
      (closedBall ((0, 0, k), spectatorCenter z₀) τ)
      (closedBall ((0, 0), (z₀ 0, spectatorCenter z₀), ηb) ρ) := by
  refine ⟨fun _ hp ↦ houtput (originOutput_mem_centered_closedBall hp), ?_⟩
  intro p hp
  have hi := hrange (originOutput_mem_centered_closedBall hp)
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hp hi ⊢
  exact ⟨⟨hp.1.1.trans hτρ, hp.1.2.1.trans hτρ⟩, hi.2⟩

omit Q in
/-- Construct common balls for the actual normalized zero-scale inverse from
the retained canonical geometry. The radii and threshold precede the frame;
the buffered inverse and transverse inputs are precisely those produced by
`exists_frozen_conic_inputs`. The original augmented half-gap is retained on the SAME input ball for
`frozenAugmented_derivative_halfGap` to transfer to the normalized map (`new:lem:scaling`, `bg-Psi`). -/
theorem exists_frozen_common_conic_balls {c C : ℝ} (hP : P.IsValid c C)
    (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {cap : ℝ} (hr : 0 < r) (ha : 0 < a) (hcap : 0 < cap) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let q₀ := ((0, 0, k), spectatorCenter z₀)
    ∃ ρ > (0 : ℝ), ρ < cap ∧ closedBall p₀ ρ ⊆ frozenInputDomain z₀ ηb r (6 * a) ∧
    ∃ τ > (0 : ℝ), τ ≤ ρ ∧ ∃ δ > (0 : ℝ), ∀ Q,
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
      closedBall q₀ τ ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r (6 * a)))
        (closedBall q₀ τ) (closedBall p₀ ρ) ∧
      (∀ p ∈ closedBall p₀ ρ,
        ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) := by
  dsimp only
  obtain ⟨ρ, hρ, hρcap, hinput, τ₀, hτ₀, δ, hδ, hballs⟩ :=
    exists_common_conic_balls T hP hz₀ hk hinc hd hr ha hcap
  have hcenter := frozenAugmentedChart_center T hP hz₀ hinc
  refine ⟨ρ, hρ, hρcap, ?_, min τ₀ ρ, lt_min hτ₀ hρ, min_le_right _ _, δ, hδ, ?_⟩
  · intro p hp
    exact hinput (originInput_mem_closedBall_centered_at_zero_positions hp)
  intro Q hQ hf b cJ V L G hInv htrans
  obtain ⟨hout, hrange, hgap⟩ := hballs Q hQ hf hInv htrans
  rw [hcenter] at hout hrange
  have hb := frozenInverse_common_ball T Q (min_le_right τ₀ ρ)
    ((closedBall_subset_closedBall (min_le_left τ₀ ρ)).trans hout)
    (hrange.mono_left (closedBall_subset_closedBall (min_le_left τ₀ ρ)))
  exact ⟨hb.1, hb.2, hgap⟩

end JanetCartan.ContinuumNormal.FrozenModel
