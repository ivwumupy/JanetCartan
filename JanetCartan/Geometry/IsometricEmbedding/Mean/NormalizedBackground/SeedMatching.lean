module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.SeedAdmission
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Coefficients

/-!
# One seed scale for the retained finite source family

The finite minimum of the actual transverse and frame thresholds gives a cap
valid for every smaller seed scale. This lets the unit-transport and mean
construction choose its seed below the cap, without choosing a second seed
when connecting to the continuum charts (`app:ch_background:eq:bg-Nsigma`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground
open ActualCarriers FrozenMenu CurrentFullPhase HamiltonPhase FrozenPhaseReference
open ProjectedStressFrame SourceGeometry ContinuumRow NullTransport
open ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching

/-- A common cap admits every smaller genuine flat seed and all its positive
contractions to the SAME finite retained charts. The transverse input is the
frozen gap produced by `exists_flat_seed_family`; the current transverse gap,
frame admission, chart, phase, covector and selected-column identities are
outputs. The seed cap and physical/carrier buffers precede every derivative
order. Consumer: `exists_constructed_flat_seed_matched_mean`, connecting its
actual unit transports to the continuum geometry
(`app:ch_background:prop:bg-normalized`, `app:ch_background:eq:bg-Nsigma`). -/
theorem exists_finite_retained_source_matching_scale {n : ℕ} {A : Type} [Fintype A]
    (G : FlatReference n) {U : Set (Euclidean n)} {hU : IsOpen U}
    {P : A → Patch n} (T : (a : A) → PatchQuantitativeFamily (P a) U hU)
    (hbounded : Bornology.IsBounded U)
    (hphysical : ∀ a, closedBall (0 : Euclidean n)
      (T a).data.localReference.stateRadius ⊆ U)
    {c : ℝ} (hc : 0 < c)
    (hgap : ∀ a, ∀ z ∈ closedBall (0, (T a).data.center)
        (T a).data.localReference.stateRadius,
      c ≤ |⟪(frozenSymbol n).hp z, (T a).data.adapted.normal⟫_ℝ|) :
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧ ∀ θ : ℝ, 0 < θ → θ ≤ cap →
      let F := sourceDilation G.map θ
      ∀ a, ∀ Q₀ : {Q : Euclidean n → Fin n → MetricTensor n //
          ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < (T a).family.threshold},
        Q₀.1 = projectedStress F →
        (∀ z ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
          ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z,
            (T a).data.adapted.normal⟫_ℝ ≠ 0) ∧
        ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
          ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n //
              ContDiffOn ℝ ∞ Q U ∧
              cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
                (Q - fun _ ↦ cubeStress n) < (T a).family.threshold},
            Qσ.1 = projectedStress (sourceDilation F σ) ∧
            EqOn ((T a).currentChart Qσ).coordinates
              (sourceCoordinates ((T a).currentChart Q₀).coordinates σ) (T a).target ∧
            EqOn (phase ((T a).currentChart Qσ).coordinates)
              (sourcePhase (phase ((T a).currentChart Q₀).coordinates) σ) (T a).target ∧
            (∀ m : ℕ, EqOn (iteratedFDeriv ℝ m (phase ((T a).currentChart Qσ).coordinates))
              (iteratedFDeriv ℝ m
                (sourcePhase (phase ((T a).currentChart Q₀).coordinates) σ)) (T a).target) ∧
            (let S := fun p : Euclidean n × Euclidean (n - 1) ↦
                phase ((T a).currentChart Q₀).coordinates (p.1, (0, p.2))
             let ζ := fun z ↦ (T a).reference.spatialPatch (CanonicalCarrier.parameter z)
             let B := ball (0 : Euclidean n) (T a).physicalRadius ×ˢ
               (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * (P a).radius))
             EqOn (CanonicalCarrier.transportPosition (T a) Qσ)
               (sourceTransportPosition S ζ σ) B ∧
             ∀ m : ℕ, EqOn (iteratedFDeriv ℝ m (CanonicalCarrier.transportPosition (T a) Qσ))
               (iteratedFDeriv ℝ m (sourceTransportPosition S ζ σ)) B) ∧
            ∀ x ∈ ball (0 : Euclidean n) (T a).physicalRadius,
              ∀ z ∈ parameterCube (2 * (P a).radius),
                (T a).carrier Qσ x z =
                  sourcePhase (fun p ↦ (T a).carrier Q₀ p.1 p.2) σ (x, z) ∧
                (T a).carrierGradient Qσ x z = (T a).carrierGradient Q₀ (σ • x) z ∧
                ∀ col, carrierNullvector (T a) Qσ col (x, z) =
                  carrierNullvector (T a) Q₀ col (σ • x, z) := by
  classical
  choose δ hδ htrans using fun a ↦
    exists_retained_seed_transverse_threshold (T a) (hphysical a) hc (hgap a)
  let d := fun a ↦ min (T a).family.threshold (δ a)
  obtain ⟨ε, hε, hmin⟩ := (finite_range d).isCompact.exists_forall_le' continuousOn_id
    (by rintro x ⟨a, rfl⟩; exact lt_min (T a).family.threshold_pos (hδ a))
  obtain ⟨cap, hcap, hcap1, hscale⟩ := exists_joint_stress_scale_interval G hbounded hε
  have hK : IsCompact (closure U) := hbounded.isCompact_closure
  have hsmall (s : ℝ) (hs : 0 < s) (hscap : s ≤ cap) (a : A) :
      cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (projectedStress (sourceDilation G.map s) - fun _ ↦ cubeStress n) < d a := by
    apply lt_of_le_of_lt (cNorm_mono_set_of_contDiffAt
      ((hphysical a).trans subset_closure) hK ?_)
      ((hscale s hs hscap).2.2.2.trans_le (hmin _ ⟨a, rfl⟩))
    intro x hx
    exact (((hscale s hs hscap).2.2.1 x hx).sub contDiffAt_const).of_le (by simp)
  refine ⟨cap, hcap, hcap1, ?_⟩
  intro θ hθ hθcap F a Q₀ hseed
  have hF : ContDiff ℝ ∞ F := contDiff_sourceDilation G.contDiff
  have hrank : HasFullNormalRankOn F U := (hscale θ hθ hθcap).2.1
  have ht : ∀ z ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z,
        (T a).data.adapted.normal⟫_ℝ ≠ 0 := by
    apply fun z hz ↦ (htrans a Q₀ ?_ z hz).2
    rw [hseed]
    exact (hsmall θ hθ hθcap a).trans_le (min_le_right _ _)
  refine ⟨ht, ?_⟩
  intro σ hσ hσ1
  have hm : 0 < θ * σ := mul_pos hθ hσ
  have hmcap : θ * σ ≤ cap := (mul_le_of_le_one_right hθ.le hσ1).trans hθcap
  have he : sourceDilation F σ = sourceDilation G.map (θ * σ) := by
    funext x
    simp only [F, sourceDilation, smul_smul, mul_inv_rev]
  have hqs : cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
      (projectedStress (sourceDilation F σ) - fun _ ↦ cubeStress n) < (T a).family.threshold := by
    rw [he]
    exact (hsmall (θ * σ) hm hmcap a).trans_le (min_le_left _ _)
  let Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T a).family.threshold} :=
    ⟨projectedStress (sourceDilation F σ), he.symm ▸
      (show ContDiffOn ℝ ∞ (projectedStress (sourceDilation G.map (θ * σ))) U from
        fun x hx ↦ ((hscale (θ * σ) hm hmcap).2.2.1 x (subset_closure hx)).contDiffWithinAt), hqs⟩
  obtain ⟨hcoord, hphase, hjets⟩ := projected_current_chart_source_dilation
    (T a) Q₀ Qσ hF hrank (hphysical a) hseed ht hσ hσ1 rfl
  refine ⟨Qσ, rfl, hcoord, hphase, hjets,
    current_transportPosition_source_dilation_on_patch
      (T a) Q₀ Qσ hF hrank (hphysical a) hseed ht hσ hσ1 rfl, ?_⟩
  intro x hx z hz
  exact ⟨hphase ((T a).target_contains_closed hx hz),
    current_carrierGradient_source_dilation (T a) Q₀ Qσ hF hrank
      (hphysical a) hseed ht hσ hσ1 rfl hx hz,
    fun col ↦ current_carrierNullvector_source_dilation (T a) Q₀ Qσ hF hrank
      (hphysical a) hseed ht hσ hσ1 rfl col hx hz⟩

end JanetCartan.NormalizedBackground
