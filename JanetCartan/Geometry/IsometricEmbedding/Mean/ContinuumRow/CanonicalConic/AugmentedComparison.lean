module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.AugmentedReference

/-!
# Actual joint derivative comparison in original carrier coordinates

The primitive frame comparison is pulled back by fixed linear coordinates.
Only the frequency component changes; all physical and spectator variables
are retained. This is the perturbation input for the augmented half-gap in
the global inverse-jet construction (`bg-Psi`, `bg-mixed-input`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

private abbrev ComparisonVariables (n : ℕ) := Euclidean 2 ×
  (WithLp 2 (ℝ × Euclidean (n - 1)) × WithLp 2 (ℝ × Euclidean (n - 1))) ×
    (ℝ × Euclidean (n - 1))

private def comparisonCoordinates : InputVariables n ≃L[ℝ] ComparisonVariables n :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p ↦ (p.2.1.2, (physicalCoordinates T p.1.1,
        physicalCoordinates T p.1.2), (p.2.1.1, p.2.2))
      invFun := fun q ↦ (((physicalCoordinates T).symm q.2.1.1,
        (physicalCoordinates T).symm q.2.1.2), (q.2.2.1, q.1), q.2.2.2)
      left_inv := fun p ↦ by simp
      right_inv := fun p ↦ by simp
      map_add' := fun _ _ ↦ by simp
      map_smul' := fun _ _ ↦ by simp }

private def frequencyInsertion : (ℝ × Euclidean (n - 1)) →L[ℝ] Variables n × Euclidean 2 :=
  (0 : (ℝ × Euclidean (n - 1)) →L[ℝ] Euclidean n).prod
      ((0 : (ℝ × Euclidean (n - 1)) →L[ℝ] Euclidean n).prod
        (adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap) |>.prod 0

private def baseInsertion : InputVariables n →L[ℝ] Variables n × Euclidean 2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ ((p.1.1, p.1.2, 0), p.2.1.2)
      map_add' := fun _ _ ↦ by simp
      map_smul' := fun _ _ ↦ by simp }

private def comparisonFrozen (q : ComparisonVariables n) : ℝ × Euclidean (n - 1) :=
  frozenChart (fun s ↦ gradient (dispersion T) (spatialCarrier T (q.1, s))) q.2.2

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

private def comparisonActual (q : ComparisonVariables n) : ℝ × Euclidean (n - 1) :=
  Comparison.fullChart (current T Q) (spatialCarrier T) 0 q.1 q.2.1.1 q.2.1.2 q.2.2

private theorem actual_decomposition :
    augmentedTransportGradient (transportPosition T Q) = fun p ↦
      baseInsertion p + frequencyInsertion T (comparisonActual T Q (comparisonCoordinates T p)) := by
  funext p
  have he : comparisonActual T Q (comparisonCoordinates T p) =
      (adaptedSliceCoordinates T).equiv (transportAveragedGradient (transportPosition T Q) p) :=
    (transportAveragedGradient_eq_fullChart T Q p).symm
  rw [he]
  simp only [baseInsertion, frequencyInsertion, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  change ((p.1.1, p.1.2, _), p.2.1.2) = ((p.1.1, p.1.2, 0), p.2.1.2) + ((0, 0, _), 0)
  simp only [Prod.mk_add_mk, zero_add, add_zero]

private theorem frozen_decomposition : frozenAugmentedChart T = fun p ↦
    baseInsertion p + frequencyInsertion T (comparisonFrozen T (comparisonCoordinates T p)) := by
  funext p
  change ((p.1.1, p.1.2, _), p.2.1.2) = ((p.1.1, p.1.2, 0), p.2.1.2) + ((0, 0, _), 0)
  simp only [Prod.mk_add_mk, zero_add, add_zero]
  rfl

private theorem augmented_derivative_difference {p : InputVariables n}
    (hf : DifferentiableAt ℝ (comparisonActual T Q) (comparisonCoordinates T p))
    (hg : DifferentiableAt ℝ (comparisonFrozen T) (comparisonCoordinates T p)) :
    fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p -
      fderiv ℝ (frozenAugmentedChart T) p =
    (frequencyInsertion T).comp
      ((fderiv ℝ (comparisonActual T Q) (comparisonCoordinates T p) -
        fderiv ℝ (comparisonFrozen T) (comparisonCoordinates T p)).comp
          (comparisonCoordinates T).toContinuousLinearMap) := by
  have h₁ := (baseInsertion (n := n)).hasFDerivAt.add
    ((frequencyInsertion T).hasFDerivAt.comp p
      (hf.hasFDerivAt.comp p (comparisonCoordinates T).hasFDerivAt))
  have h₂ := (baseInsertion (n := n)).hasFDerivAt.add
    ((frequencyInsertion T).hasFDerivAt.comp p
      (hg.hasFDerivAt.comp p (comparisonCoordinates T).hasFDerivAt))
  change HasFDerivAt (fun p ↦ baseInsertion p + frequencyInsertion T
    (comparisonActual T Q (comparisonCoordinates T p))) _ p at h₁
  change HasFDerivAt (fun p ↦ baseInsertion p + frequencyInsertion T
    (comparisonFrozen T (comparisonCoordinates T p))) _ p at h₂
  rw [actual_decomposition, frozen_decomposition, h₁.fderiv, h₂.fderiv]
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  abel

omit Q in
/-- Primitive frame closeness gives any requested joint augmented derivative
tolerance on a fixed compact ball. The finite-dimensional coordinate norms
are fixed before `Q`; no augmented gap is assumed (`bg-Psi`). -/
theorem exists_augmented_comparison_threshold {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) {r : ℝ} (hr : 0 < r)
    (hphys : r < T.family.radius / 8)
    (hcarrier : closedBall (spectatorCenter z₀) r ×ˢ closedBall (z₀ 0) r ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ p ∈ closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) (r / 2),
        ‖fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p -
          fderiv ℝ (frozenAugmentedChart T) p‖ ≤ τ := by
  let K := (‖frequencyInsertion T‖ + 1) * (‖(comparisonCoordinates T).toContinuousLinearMap‖ + 1)
  have hK : 0 < K := mul_pos (by positivity) (by positivity)
  obtain ⟨δ, hδ, e, he, hcompare⟩ := exists_frame_comparison_threshold T hP z₀ ηb hphys
    hcarrier (div_pos hτ hK)
  obtain ⟨e₀, he₀, hsmooth⟩ := exists_smooth_chartFamilies T hP z₀ ηb hphys.le hcarrier
  refine ⟨δ, hδ, fun Q hQ p hp ↦ ?_⟩
  have hp' : p.2.1.2 ∈ ball (spectatorCenter z₀) r ∧
      p.1.1 ∈ ball 0 r ∧ p.1.2 ∈ ball 0 r ∧
      p.2.1.1 ∈ ball (z₀ 0) r ∧ p.2.2 ∈ ball ηb r := by
    have h := mem_closedBall.mp hp
    simp only [Prod.dist_eq, max_le_iff] at h
    exact ⟨(h.2.1.2.trans_lt (half_lt_self hr)),
      h.1.1.trans_lt (half_lt_self hr), h.1.2.trans_lt (half_lt_self hr),
      h.2.1.1.trans_lt (half_lt_self hr), h.2.2.trans_lt (half_lt_self hr)⟩
  have hx : physicalCoordinates T p.1.1 ∈ ball 0 r := by
    simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hp'.2.1
  have hy : physicalCoordinates T p.1.2 ∈ ball 0 r := by
    simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hp'.2.2.1
  have hq : comparisonCoordinates T p ∈ closedBall (spectatorCenter z₀) r ×ˢ
      ((closedBall (0 : WithLp 2 (ℝ × Euclidean (n - 1))) r ×ˢ closedBall 0 r) ×ˢ
        (closedBall (z₀ 0) r ×ˢ closedBall ηb r)) :=
    ⟨ball_subset_closedBall hp'.1, ⟨ball_subset_closedBall hx, ball_subset_closedBall hy⟩,
      ball_subset_closedBall hp'.2.2.2.1, ball_subset_closedBall hp'.2.2.2.2⟩
  have hfull : ((0, p.2.1.2, physicalCoordinates T p.1.1, physicalCoordinates T p.1.2),
      (p.2.1.1, p.2.2)) ∈ fullParameterSet z₀ r e₀ ×ˢ dataSet z₀ ηb r :=
    ⟨⟨⟨by linarith, he₀⟩, hp'.1, hx, hy⟩, hp'.2.2.2.1, hp'.2.2.2.2⟩
  have hf : DifferentiableAt ℝ (comparisonActual T Q) (comparisonCoordinates T p) := by
    have hh := ((hsmooth Q).2.1.contDiffAt
      (((isOpen_fullParameterSet z₀ r e₀).prod (isOpen_dataSet z₀ ηb r)).mem_nhds hfull)).comp
        (comparisonCoordinates T p)
        ((contDiffAt_const.prodMk (contDiffAt_fst.prodMk
          (contDiffAt_snd.fst.fst.prodMk contDiffAt_snd.fst.snd))).prodMk contDiffAt_snd.snd)
    exact hh.differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (comparisonFrozen T) (comparisonCoordinates T p) := by
    have hcar : carrierParameters (p.2.1.2, p.2.1.1) ∈ parameterInterior (3 * P.radius / 2) :=
      hcarrier ⟨ball_subset_closedBall hp'.1, ball_subset_closedBall hp'.2.2.2.1⟩
    have hcar' : carrierParameters (p.2.1.2, p.2.1.1) ∈ parameterInterior (2 * P.radius) :=
      (middle_parameter_buffers hP).2 (fun i ↦ (hcar i).le)
    have hc := (ActualInverses.frozenChart_contDiffAt T hP
      (q := (p.2.1.2, p.2.1.1, p.2.2)) hcar').comp
      (comparisonCoordinates T p) (contDiffAt_fst.prodMk contDiffAt_snd.snd)
    exact hc.differentiableAt (by simp)
  have hbound := ((hcompare Q hQ 0 (by simpa using he.le)).1 _ hq).2.1.le
  rw [augmented_derivative_difference T Q hf hg]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans
  have hc₁ : ‖frequencyInsertion T‖ ≤ ‖frequencyInsertion T‖ + 1 := by linarith
  have hc₂ : ‖(comparisonCoordinates T).toContinuousLinearMap‖ ≤
      ‖(comparisonCoordinates T).toContinuousLinearMap‖ + 1 := by linarith
  calc
    _ ≤ (‖frequencyInsertion T‖ + 1) *
        ((τ / K) * (‖(comparisonCoordinates T).toContinuousLinearMap‖ + 1)) :=
      mul_le_mul hc₁ (mul_le_mul hbound hc₂ (norm_nonneg _) (by positivity))
        (by positivity) (by positivity)
    _ = τ := by dsimp [K]; field_simp

end JanetCartan.ContinuumRow.CanonicalConic
