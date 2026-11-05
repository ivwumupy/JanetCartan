module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.KernelMatching

/-!
# Physical means on the retained normalized scalar family

The normalized selector proves the actual source scalar-transport identity on
one working buffer. Applying it on the full support of the original external
weights identifies the physical tensor mean, including its collar outside the
detector masks. Kernel matching on the detector support alone is not used to
justify that larger integral identity.

The normal, covector and canonical footpoint come from the same seed and
current Hamilton families. The resulting compact source is literally the
source of `NormalizedSourceSobolev`, with the original `-1/2` factor, fixed
source cutoff and product Lebesgue measure. Uniform row coercivity and inverse
estimates are still separate inputs to `SourceInverse`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PositiveBackground
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier
open ContinuumNormal.FrozenModel ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
open NormalizedBackground NormalizedBackground.SourceGeometry
open NullTransport NullTransport.ActualFlow NullTransport.FlowAmplitude HamiltonPhase

variable {n N : ℕ} {A : Type*} [Fintype A]
    {P : A → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (a : A) → PatchQuantitativeFamily (P a) U hU)
    (Q₀ Qσ : (a : A) →
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < (T a).family.threshold})
    (F : Euclidean n → Euclidean N) (row col : A → Fin n)
    (Φ₀ Y₀ Φσ Yσ : A → ℝ × (Euclidean (n - 1) × Euclidean 3) →
      Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : A → CarrierParameter → Euclidean (n - 1) → ℝ) (high : A → ℝ → ℝ)
    (χ : A → CarrierParameter → ℝ) {σ : ℝ}
    {W : Set (Euclidean n)} {c C : ℝ} (hP : ∀ a, (P a).IsValid c C)
    (hχpatch : ∀ a z, z ∈ tsupport (χ a) →
      parameter z ∈ parameterInterior (2 * (P a).radius))

include hP hχpatch in
/-- The physical uncorrected mean of `normalizedCarrierData` is the existing
normalized seed mean, with the SAME squared weights and measure. The actual
phase gradient supplies the covector identity on the full external support,
including at zero scale (`app:ch_background:eq:bg-Hsigma`,
`app:ch_background:prop:bg-normalized`). -/
theorem physicalDensityMean_normalizedCarrierData_zero
    (hscale : ∀ a x, x ∈ W → σ • x ∈ ball (0 : Euclidean n) (T a).physicalRadius) :
    EqOn (physicalDensityMean (fun a ↦ normalizedCarrierData (T a) (Q₀ a) F
      (row a) (col a) (Φ₀ a) (Y₀ a) (fun _ ↦ 1) hr hcell (angular a) (high a) σ) χ 0)
      (normalizedCarrierMean (fun _ ↦ volume.prod volume) (fun a z ↦ χ a z ^ 2)
        (fun a p ↦ normalField (T a) (Q₀ a) F (row a) (col a) (Φ₀ a) (Y₀ a)
          (fun _ ↦ 1) p.1 p.2)
        (fun a p ↦ (T a).carrierGradient (Q₀ a) p.1 (parameter p.2)) σ) W := by
  intro x hx
  rw [physicalDensityMean_zero]
  unfold normalizedCarrierMean carrierMean
  apply Finset.sum_congr rfl
  intro a _
  ext i j
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : χ a z = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul]
  · have hξ := normalizedCovector_eq_retainedCarrierGradient (T a) (Q₀ a)
      (hP a) (hscale a x hx) (hχpatch a z (subset_tsupport _ hz))
    change χ a z ^ 2 * ‖normalizedNormal (T a) (Q₀ a) F (row a) (col a)
      (Φ₀ a) (Y₀ a) (fun _ ↦ 1) σ x z‖ ^ 2 *
        (normalizedCovector (T a) (Q₀ a) σ x z i *
          normalizedCovector (T a) (Q₀ a) σ x z j) = _
    rw [hξ]
    rfl

variable (hF : ContDiff ℝ ∞ F) (hrank : HasFullNormalRankOn F U)
    (hphysical : ∀ a, closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius ⊆ U)
    (hseed : ∀ a, (Q₀ a).1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ a q, q ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius →
      ⟪(normalizedHomogeneousSymbol hU (Q₀ a).1 (Q₀ a).2.1).hp q,
        (T a).data.adapted.normal⟫_ℝ ≠ 0)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : ∀ a, (Qσ a).1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    (hW : ∀ a, W ⊆ ball (0 : Euclidean n) (T a).physicalRadius)
    (hscalar : ∀ a x, x ∈ W → ∀ z ∈ tsupport (χ a),
      carrierScalarAmplitude (T a) (Qσ a) (sourceDilation F σ) (row a) (col a)
        (Φσ a) (Yσ a) (fun _ ↦ σ) (x, parameter z) =
      sourceAmplitude (carrierScalarAmplitude (T a) (Q₀ a) F (row a) (col a)
        (Φ₀ a) (Y₀ a) (fun _ ↦ 1)) σ (x, parameter z))

include hP hχpatch hF hrank hphysical hseed htrans hσ hσ1 hscaled hW hscalar in
/-- The actual current scalar transport identifies the entire physical
affine mean with the normalized carrier mean, for the SAME density `v`.
Its producer is `NormalizedSelection.exists_retained_source_carrier_integrals`
on the fixed scalar-flow buffer; the original weight selection must keep its
full support in that buffer. The proof uses the actual scaled nullvector,
normal completion and Hamilton footpoint, not just equality of supported
kernels (`app:ch_background:eq:bg-affine-mean`,
`app:ch_background:eq:bg-current-identity`, `new:lem:scaling`). -/
theorem physicalDensityMean_eq_normalized_of_scalar_transport
    (v : A → CarrierVariable n → ℝ) :
    EqOn (physicalDensityMean (fun a ↦ data (T a) (Qσ a) (sourceDilation F σ)
      (row a) (col a) (Φσ a) (Yσ a) (fun _ ↦ σ) hr hcell (angular a) (high a)) χ v)
      (physicalDensityMean (fun a ↦ normalizedCarrierData (T a) (Q₀ a) F
        (row a) (col a) (Φ₀ a) (Y₀ a) (fun _ ↦ 1) hr hcell (angular a) (high a) σ) χ v) W := by
  intro x hx
  unfold physicalDensityMean
  apply Finset.sum_congr rfl
  intro a _
  ext i j
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : χ a z = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul]
  · have hzsupport := subset_tsupport (χ a) hz
    have hx' := hW a hx
    have hz' : parameter z ∈ parameterCube (2 * (P a).radius) :=
      fun k ↦ (hχpatch a z hzsupport k).le
    have hsx := (convex_ball (0 : Euclidean n) (T a).physicalRadius).smul_mem_of_zero_mem
      (mem_ball_self (T a).physicalRadius_pos) hx' ⟨hσ.le, hσ1⟩
    have hxU : σ • x ∈ U :=
      (carrierPhase_gradient_mem_domain ((T a).currentChart (Q₀ a)) (T a).reference.spatialPatch
        ((T a).target_contains_closed hsx hz')).1
    have hgrad := current_carrierGradient_source_dilation (T a) (Q₀ a) (Qσ a) hF hrank
      (hphysical a) (hseed a) (htrans a) hσ hσ1 (hscaled a) hx' hz'
    have hnull := current_carrierNullvector_source_dilation (T a) (Q₀ a) (Qσ a) hF hrank
      (hphysical a) (hseed a) (htrans a) hσ hσ1 (hscaled a) (col a) hx' hz'
    have hξ := hgrad.trans (normalizedCovector_eq_retainedCarrierGradient (T a) (Q₀ a)
      (hP a) hsx (hχpatch a z hzsupport)).symm
    have hpos : transportPosition (T a) (Qσ a) (x, z) =
        normalizedTransportPosition (T a) (Q₀ a) σ (x, z) :=
      (current_transportPosition_source_dilation_on_patch (T a) (Q₀ a) (Qσ a)
        hF hrank (hphysical a) (hseed a) (htrans a) hσ hσ1 (hscaled a)).1
        ⟨hx', hχpatch a z hzsupport⟩
    have hnormal : normalField (T a) (Qσ a) (sourceDilation F σ) (row a) (col a)
        (Φσ a) (Yσ a) (fun _ ↦ σ) x z =
      normalizedNormal (T a) (Q₀ a) F (row a) (col a) (Φ₀ a) (Y₀ a) (fun _ ↦ 1) σ x z := by
      rw [normalizedNormal_eq_sourceDilation _ _ _ _ _ _ _ _ hσ hF x z (hrank _ hxU)]
      simp only [normalField, hgrad, hnull, hscalar a x hx z hzsupport, sourceAmplitude,
        smul_smul, smul_eq_mul]
    change (χ a z ^ 2 * (1 + v a (z, transportPosition (T a) (Qσ a) (x, z)))) *
      ‖normalField (T a) (Qσ a) (sourceDilation F σ) (row a) (col a)
        (Φσ a) (Yσ a) (fun _ ↦ σ) x z‖ ^ 2 *
        ((T a).carrierGradient (Qσ a) x (parameter z) i *
          (T a).carrierGradient (Qσ a) x (parameter z) j) = _
    rw [hξ, hpos, hnormal]
    rfl

include hP hχpatch hF hrank hphysical hseed htrans hσ hσ1 hscaled hW hscalar in
/-- The compact source for the actual uncorrected carrier row is literally
the normalized seed source consumed by
`exists_normalized_referenceSource_sobolev_bounds`. Scalar matching is used on
the full external support; outside the original source cutoff both sides
vanish. The reference field, projected stress, weights, measure and sign
`-1/2` stay unchanged (`app:ch_background:eq:bg-current-raising`,
`app:ch_background:eq:bg-positive-profile`). -/
theorem cutReducedSource_eq_normalized_of_scalar_transport
    (H₀ : MetricTensor n) (θ : Euclidean n → ℝ) (hsupport : tsupport θ ⊆ W) :
    let d := fun a ↦ data (T a) (Qσ a) (sourceDilation F σ)
      (row a) (col a) (Φσ a) (Yσ a) (fun _ ↦ σ) hr hcell (angular a) (high a)
    let H := normalizedCarrierMean (fun _ ↦ volume.prod volume) (fun a z ↦ χ a z ^ 2)
      (fun a p ↦ normalField (T a) (Q₀ a) F (row a) (col a) (Φ₀ a) (Y₀ a)
        (fun _ ↦ 1) p.1 p.2)
      (fun a p ↦ (T a).carrierGradient (Q₀ a) p.1 (parameter p.2)) σ
    cutReducedSource θ (ProjectedStressFrame.projectedStress (sourceDilation F σ))
        (referenceMeanResidual (sourceDilation F σ) H₀ (physicalDensityMean d χ 0)) =
      cutReducedSource θ (ProjectedStressFrame.projectedStress (sourceDilation F σ))
        (referenceMeanResidual (sourceDilation F σ) H₀ H) := by
  intro d H
  have hscale (a : A) (x : Euclidean n) (hx : x ∈ W) :
      σ • x ∈ ball (0 : Euclidean n) (T a).physicalRadius :=
    (convex_ball (0 : Euclidean n) (T a).physicalRadius).smul_mem_of_zero_mem
      (mem_ball_self (T a).physicalRadius_pos) (hW a hx) ⟨hσ.le, hσ1⟩
  have ha := physicalDensityMean_eq_normalized_of_scalar_transport T Q₀ Qσ F row col
    Φ₀ Y₀ Φσ Yσ hr hcell angular high χ hP hχpatch hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hW hscalar 0
  have hn := physicalDensityMean_normalizedCarrierData_zero T Q₀ F row col Φ₀ Y₀
    hr hcell angular high χ hP hχpatch hscale
  funext x
  by_cases hx : θ x = 0
  · simp only [cutReducedSource, hx, mul_zero, zero_smul]
  · have hxW := hsupport (subset_tsupport θ hx)
    have hmean : physicalDensityMean d χ 0 x = H x := (ha hxW).trans (hn hxW)
    simp only [cutReducedSource, referenceMeanResidual, Pi.add_apply, hmean]

end JanetCartan.PositiveBackground
