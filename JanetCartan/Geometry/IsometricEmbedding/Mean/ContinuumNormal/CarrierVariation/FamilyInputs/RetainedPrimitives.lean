module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedPhase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Transport

/-!
# Finite norms of the retained normalized Hamilton transport

The literal `FrozenModel.normalizedTransportPosition` is the integral extension
of the SAME retained seed phase. Its joint smoothness gives finite primitive
convergence, and the proved Hamilton matching transfers the estimates to every
actual positive contraction. Consumer: the `m + 2` transport input in
`CarrierVariation.exists_inverseCoordinates_sub_le`, for
`app:ch_background:prop:bg-normalized` and `app:ch_osc:prop:osc-normal`, Step 4'.
The inverse null-flow map used by density evaluation is a separate object.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow FrozenModel
open NormalizedBackground SourceMatching

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Finite primitive convergence of the literal retained normalized transport,
on any fixed compact physical/carrier domain inside the original label buffer.
The seed phase regularity is discharged by the retained Hamilton construction;
no transport continuity is assumed. Source: `app:ch_background:eq:bg-Nsigma`.
Consumer: the `cNorm L (m + 2)` input of the full normal comparison. -/
theorem tendsto_normalizedTransportPosition_sub_cNorm {c C : ℝ} (hP : P.IsValid c C)
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    (hlabel : MapsTo Prod.snd L
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (3 * P.radius / 2))) (m : ℕ) :
    Tendsto (fun σ ↦ cNorm L (m + 2)
      (normalizedTransportPosition T Q₀ σ - normalizedTransportPosition T Q₀ 0))
      (𝓝 0) (𝓝 0) := by
  obtain ⟨B, hB, hLB, r, hr, _, hJ, _⟩ :=
    exists_retained_phase_normalization_bounds T Q₀ hP
      (hL.image continuous_fst) (hL.image continuous_snd)
      (by rintro z ⟨p, hp, rfl⟩; exact hlabel hp)
  exact tendsto_cNorm_slice_sub isOpen_Ioo
    (hB.prod ((isOpen_parameterInterior _).preimage CanonicalCarrier.parameter.continuous))
    hJ.snd.snd hL (fun p hp ↦ ⟨hLB ⟨p, hp, rfl⟩, hlabel hp⟩)
    ⟨by linarith, by linarith⟩ (m + 2)

/-- An explicit positive scale threshold for the SAME actual retained current
transport, with all finite ambient derivatives measured against the zero-scale
seed transport. Phase matching is proved from the primitive projected stress,
the retained transverse gap and Hamilton uniqueness. The seed hypotheses are
produced together by `SourceMatching.exists_source_seed_chart_matching` (or
the finite common-scale assembly), and the domain is fixed before `σ`.
Source: `app:ch_background:prop:bg-normalized`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_current_transportPosition_sub_lt {c C : ℝ} (hP : P.IsValid c C)
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    (hLD : L ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ 1 ∧ ∀ σ ∈ Ioc (0 : ℝ) δ,
      ∀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
        Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ) →
        cNorm L (m + 2)
          (CanonicalCarrier.transportPosition T Qσ - normalizedTransportPosition T Q₀ 0) < ε := by
  have ht := tendsto_normalizedTransportPosition_sub_cNorm T Q₀ hP hL
    (fun _ hp ↦ (hLD hp).2) m
  obtain ⟨e, he, hsmall⟩ := Metric.mem_nhds_iff.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨min (e / 2) 1, lt_min (half_pos he) zero_lt_one, min_le_right _ _, ?_⟩
  intro σ hσ Qσ hscaled
  have hσ1 : σ ≤ 1 := hσ.2.trans (min_le_right _ _)
  have hmatch := (current_transportPosition_source_dilation_on_patch T Q₀ Qσ
    hF hrank hphysical hseed htrans hσ.1 hσ1 hscaled).1
  have hnorm : cNorm L (m + 2)
      (CanonicalCarrier.transportPosition T Qσ - normalizedTransportPosition T Q₀ 0) =
      cNorm L (m + 2)
        (normalizedTransportPosition T Q₀ σ - normalizedTransportPosition T Q₀ 0) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Set.image_congr
    intro p hp
    have hpD : p ∈ ball (0 : Euclidean n) T.physicalRadius ×ˢ
        (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)) :=
      ⟨(hLD hp).1, fun i ↦ ((hLD hp).2 i).trans (by linarith [hP.1])⟩
    have heq : CanonicalCarrier.transportPosition T Qσ =ᶠ[𝓝 p]
        normalizedTransportPosition T Q₀ σ :=
      eventuallyEq_of_mem ((isOpen_ball.prod ((isOpen_parameterInterior _).preimage
        CanonicalCarrier.parameter.continuous)).mem_nhds hpD) (fun q hq ↦ hmatch hq)
    exact congrArg norm (((heq.sub (Filter.EventuallyEq.refl _ _)).iteratedFDeriv ℝ j).eq_of_nhds)
  rw [hnorm]
  apply hsmall
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
  exact (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self he)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
