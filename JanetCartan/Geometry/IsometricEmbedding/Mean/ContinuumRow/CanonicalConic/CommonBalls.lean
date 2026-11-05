module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.AugmentedGap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.AugmentedValue
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.JacobianRegularity

/-!
# Common balls for the same canonical conic inverse

The quantitative inverse theorem supplies preimages in a fixed input ball.
Conic injectivity identifies these preimages with the already constructed
inverse. All balls and thresholds precede the current frame (`bg-Psi`).
The local-chart premises are the exact outputs of `exists_actual_local_charts`;
their actual instantiation is retained by `ActualGeometry`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Common input/output balls for the SAME conic inverse. The augmented gap
and central-value comparison are proved from primitive frame closeness; the
remaining local-chart data are produced by `exists_actual_local_charts` and
`exists_supported_transverse_threshold`. The output is chosen before `Q`.
Consumer: the supported global carrier producer (`bg-full-complex-amplitude`). -/
theorem exists_common_conic_balls {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {r a cap : ℝ} (hr : 0 < r) (ha : 0 < a) (hcap : 0 < cap) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let q₀ := frozenAugmentedChart T p₀
    ∃ ρ > (0 : ℝ), ρ < cap ∧ closedBall p₀ ρ ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Q,
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
      closedBall q₀ τ ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
        (closedBall q₀ τ) (closedBall p₀ ρ) ∧
      (∀ p ∈ closedBall p₀ ρ,
        ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
  let q₀ := frozenAugmentedChart T p₀
  let A := augmentedReferenceEquiv T hP hz₀ hinc hd
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  have hp₀ : p₀ ∈ symbolInputDomain z₀ ηb r (6 * a) :=
    ⟨⟨mem_ball_self (by positivity), mem_ball_self (by positivity), mem_ball_self (by positivity)⟩,
      mem_ball_self hr, hηb, mem_ball_self (angularWidth_spec hηb hr).1⟩
  obtain ⟨d, hdpos, hdsub⟩ := Metric.mem_nhds_iff.mp
    ((symbolInputDomain_open z₀ ηb r (6 * a)).mem_nhds hp₀)
  obtain ⟨ρ, hρ, hρcap, δ₀, hδ₀, hgap⟩ := exists_actual_augmented_gap T hP hz₀ hinc hd
    (lt_min hcap hdpos)
  have hinput : closedBall p₀ ρ ⊆ symbolInputDomain z₀ ηb r (6 * a) :=
    (closedBall_subset_ball (hρcap.trans_le (min_le_right _ _))).trans hdsub
  let τ := ρ / (8 * (‖A.symm.toContinuousLinearMap‖ + 1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτeq : (8 * (‖A.symm.toContinuousLinearMap‖ + 1)) * τ = ρ := by
    dsimp [τ]
    field_simp
  obtain ⟨δ₁, hδ₁, hvalue⟩ := exists_augmented_center_threshold T hP hz₀ k hτ
  refine ⟨ρ, hρ, hρcap.trans_le (min_le_left _ _), hinput, τ, hτ,
    min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro Q hQ hf b cJ V L G hInv htrans
  have hgap' := hgap Q (hQ.trans_le (min_le_left _ _))
  have hvalue' := hvalue Q (hQ.trans_le (min_le_right _ _))
  have hdiff : ∀ p ∈ closedBall p₀ ρ,
      DifferentiableAt ℝ (augmentedTransportGradient (transportPosition T Q)) p := by
    intro p hp
    have hg := (transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf).contDiffAt
      ((symbolInputDomain_open z₀ ηb r (6 * a)).mem_nhds (hinput hp))
    exact ((contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk hg)).prodMk
      contDiffAt_snd.fst.snd).differentiableAt (by simp)
  have himage : closedBall q₀ τ ⊆
      augmentedTransportGradient (transportPosition T Q) '' closedBall p₀ ρ := by
    intro q hq
    apply mem_image_closedBall_of_normalized_derivative_gap (convex_closedBall _ _) A
      hdiff hgap' hρ.le Subset.rfl
    apply (A.symm.toContinuousLinearMap.le_opNorm _).trans
    have hdist : ‖q - augmentedTransportGradient (transportPosition T Q) p₀‖ ≤ 2 * τ := by
      calc
        _ ≤ ‖q - q₀‖ + ‖q₀ - augmentedTransportGradient (transportPosition T Q) p₀‖ :=
          by simpa only [dist_eq_norm] using
            dist_triangle q q₀ (augmentedTransportGradient (transportPosition T Q) p₀)
        _ ≤ τ + τ := add_le_add (mem_closedBall_iff_norm.mp hq)
          (by simpa only [norm_sub_rev] using hvalue')
        _ = 2 * τ := by ring
    apply (mul_le_mul_of_nonneg_left hdist (norm_nonneg _)).trans
    nlinarith [norm_nonneg A.symm.toContinuousLinearMap]
  refine ⟨?_, ?_, hgap'⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := himage hq
    exact ⟨(hinput hp).1, (p.2.1.1, p.2.2), (hinput hp).2, rfl⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := himage hq
    rw [symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans (hinput hp)]
    exact hp

end JanetCartan.ContinuumRow.CanonicalConic
