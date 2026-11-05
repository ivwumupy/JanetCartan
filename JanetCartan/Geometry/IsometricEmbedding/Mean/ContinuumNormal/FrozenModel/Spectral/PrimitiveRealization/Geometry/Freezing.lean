module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Realization.CommonBalls

/-!
# Freezing the augmented differential and common balls

The normalized zero-scale frequency is the original frequency at zero physical
positions. The position projection contracts the product norm; the augmented
reference preserves the complementary physical block. These facts transfer
the actual half-gap without identifying the two transport fields.
Centered-ball projection estimates are reused from `Realization.CommonBalls`.
Consumer: the primitive supported carrier construction (`new:lem:scaling`,
`app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol

variable {n : ℕ}

private def originProjection : InputVariables n →L[ℝ] InputVariables n :=
  (0 : InputVariables n →L[ℝ] Euclidean n × Euclidean n).prod
    (ContinuousLinearMap.snd ℝ (Euclidean n × Euclidean n) _)

private def positionInsertion : InputVariables n →L[ℝ] Variables n × Euclidean 2 :=
  ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)).prod 0) |>.prod 0

private theorem originProjection_norm_le : ‖originProjection (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro p
  change max ‖(0 : Euclidean n × Euclidean n)‖ ‖p.2‖ ≤ 1 * ‖p‖
  simpa only [norm_zero, max_eq_right (norm_nonneg _), one_mul] using norm_snd_le p

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

private theorem frozenReference_decomposition : frozenAugmentedChart T = fun p ↦
    positionInsertion p + frozenAugmentedChart T (originProjection p) := by
  funext p
  change ((p.1.1, p.1.2, _), p.2.1.2) = ((p.1.1, p.1.2, 0), 0) + ((0, 0, _), p.2.1.2)
  simp only [Prod.mk_add_mk, add_zero, zero_add]
  rfl

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    {c C : ℝ} (hP : P.IsValid c C) (hr : 0 < r) (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))

include hP hr har hcarrier in
private theorem frozenAugmented_hasFDerivAt {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r a)
    (hf : DifferentiableAt ℝ (augmentedTransportGradient (transportPosition T Q)) (originInput p)) :
    HasFDerivAt (augmentedTransportGradient (normalizedTransportPosition T Q 0))
      (positionInsertion + (fderiv ℝ (augmentedTransportGradient (transportPosition T Q))
        (originInput p)).comp originProjection) p := by
  have he : augmentedTransportGradient (normalizedTransportPosition T Q 0) =ᶠ[𝓝 p]
      (fun q ↦ positionInsertion q +
        augmentedTransportGradient (transportPosition T Q) (originProjection q)) := by
    filter_upwards [(frozenInputDomain_open z₀ ηb r a).mem_nhds hp] with q hq
    have h := frozenForward_eq_origin T Q hP hr har hcarrier hq
    change ((q.1.1, q.1.2, _), q.2.1.2) = ((q.1.1, q.1.2, 0), 0) + ((0, 0, _), q.2.1.2)
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    exact congrArg (fun ξ ↦ ((q.1.1, q.1.2, ξ), q.2.1.2)) h
  exact ((positionInsertion (n := n)).hasFDerivAt.add
    (hf.hasFDerivAt.comp p (originProjection (n := n)).hasFDerivAt)).congr_of_eventuallyEq he

include hP hr har hcarrier in
/-- The actual augmented half-gap survives freezing. The original half-gap
and input ball are produced by `exists_common_conic_balls`; smoothness is an
exact output of `exists_frozen_conic_inputs`. This proves the constructor's
frozen half-gap, including the spectator derivatives (`new:lem:scaling`, `bg-Psi`). -/
theorem frozenAugmented_halfGap_of_original
    (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    (hηb : ηb ≠ 0)
    {ρ : ℝ}
    (hinput : closedBall (augmentedInputCenter T (z₀ := z₀) (k := k)) ρ ⊆
      symbolInputDomain z₀ ηb r a)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)))
    (hgap : ∀ p ∈ closedBall (augmentedInputCenter T (z₀ := z₀) (k := k)) ρ,
      ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) :
    ∀ p ∈ closedBall (augmentedInputCenter T (z₀ := z₀) (k := k)) ρ,
      ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2 := by
  let A := augmentedReferenceEquiv T hP hz₀ hinc hd
  let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
  have hp₀ : carrierParameters (p₀.2.1.2, p₀.2.1.1) ∈ parameterInterior (2 * P.radius) := by
    change carrierParameters (spectatorCenter z₀, z₀ 0) ∈ _
    rw [carrierParameters_spectatorCenter]
    exact parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz₀ i).le)
  have href := (frozenAugmentedChart_contDiffAt T hP hp₀).differentiableAt (by simp)
  have href' := (positionInsertion (n := n)).hasFDerivAt.add
    (href.hasFDerivAt.comp p₀ (originProjection (n := n)).hasFDerivAt)
  have hA : A.toContinuousLinearMap = positionInsertion + A.toContinuousLinearMap.comp originProjection := by
    have he := href'.fderiv
    change fderiv ℝ (fun p ↦ positionInsertion p +
      frozenAugmentedChart T (originProjection p)) p₀ = _ at he
    rw [← frozenReference_decomposition T] at he
    dsimp only [p₀] at he
    simpa only [fderiv_frozenAugmentedChart_center T hP hz₀ hinc hd] using he
  intro p hp
  have hporg : originInput p ∈ closedBall p₀ ρ :=
    originInput_mem_closedBall_centered_at_zero_positions hp
  have hpin : p ∈ frozenInputDomain z₀ ηb r a := hinput hporg
  have hg := (transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf).contDiffAt
    ((symbolInputDomain_open z₀ ηb r a).mem_nhds (hinput hporg))
  have hdiff := ((contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk hg)).prodMk
    contDiffAt_snd.fst.snd).differentiableAt (by simp)
  rw [(frozenAugmented_hasFDerivAt T Q hP hr har hcarrier hpin hdiff).fderiv]
  have he : A.symm.toContinuousLinearMap.comp
        (positionInsertion + (fderiv ℝ (augmentedTransportGradient (transportPosition T Q))
          (originInput p)).comp originProjection) - ContinuousLinearMap.id ℝ (InputVariables n) =
      (A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) (originInput p)) -
          ContinuousLinearMap.id ℝ (InputVariables n)).comp originProjection := by
    have hcancel : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ (InputVariables n) := by
      apply ContinuousLinearMap.ext
      intro v
      exact A.symm_apply_apply v
    conv_lhs => rw [← hcancel]
    conv_lhs => arg 2; arg 2; rw [hA]
    simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.sub_comp,
      ← ContinuousLinearMap.comp_assoc, hcancel]
    abel
  change ‖A.symm.toContinuousLinearMap.comp _ - _‖ ≤ 1 / 2
  rw [he]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (hgap _ hporg) originProjection_norm_le (norm_nonneg _) (by norm_num)).trans
      (by norm_num))

end JanetCartan.ContinuumNormal.FrozenModel
