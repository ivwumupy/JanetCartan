module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedCarrierProfiles.HamiltonPosition
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Transport

/-!
# All-order Hamilton-position profiles of the retained actual source

Transfer the normalized seed position budgets to every admitted source frame
by its exact Hamilton matching identity. The same fixed coefficient chart
and one source interval work for all orders in the full reflected amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier
open ContinuumNormal.FrozenModel ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol

/-- The actual Hamilton position has all-order bounds before the source
scale and before any admitted frame with its prescribed geometric value.
The proof uses source uniqueness and the seed phase's joint smoothness;
no norm of the varying position is assumed. Consumer: the normalized bounded
carrier's full reflected amplitude (`app:ch_background:eq:bg-Nsigma`,
`app:ch_background:prop:bg-normalized`, `app:ch_background:eq:bg-commutator`). -/
theorem exists_actual_source_transportPosition_profiles
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {c C : ℝ} (hP : P.IsValid c C)
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    (hD : D.region ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2))) :
    ∃ s > (0 : ℝ), s ≤ 1 ∧ ∃ B : ℕ → ℝ, (∀ p, 0 < B p) ∧
      ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ) →
      ContDiffOn ℝ ∞ (transportPosition T Qσ) D.region ∧
        ∀ p, cNorm D.carrier p (transportPosition T Qσ) ≤ B p := by
  obtain ⟨s, hs, hs1, B, hB, hposition⟩ :=
    NormalizedCarrierProfiles.exists_normalizedTransportPosition_profiles T Q₀ hP D hD
  refine ⟨s, hs, hs1, B, hB, ?_⟩
  intro σ hσ Qσ hscaled
  have hmatch := (SourceMatching.current_transportPosition_source_dilation_on_patch
    T Q₀ Qσ hF hrank hphysical hseed htrans hσ.1 (hσ.2.trans hs1) hscaled).1
  have heq : EqOn (transportPosition T Qσ) (normalizedTransportPosition T Q₀ σ) D.region := by
    intro q hq
    exact hmatch ⟨(hD hq).1, fun i ↦ ((hD hq).2 i).trans (by linarith [hP.1])⟩
  obtain ⟨hsm, hb⟩ := hposition σ ⟨hσ.1.le, hσ.2⟩
  refine ⟨hsm.congr (fun _ hq ↦ heq hq), ?_⟩
  intro p
  exact (GeometricProfile.cNorm_eq_of_eventuallyEq (fun x hx ↦
    Filter.eventuallyEq_of_mem (D.isOpen_region.mem_nhds (D.ball_subset hx))
      (fun _ hq ↦ heq hq)) p).trans_le (hb p)

end JanetCartan.ContinuumRow.NormalizedSelection
