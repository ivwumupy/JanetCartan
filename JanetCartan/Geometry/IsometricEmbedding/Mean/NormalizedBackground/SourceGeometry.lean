module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Normal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Residual
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Fields
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Bounds

/-!
# Concrete deductions for the normalized source geometry

Checked portions of `app:ch_background:prop:bg-normalized` and equations
`app:ch_background:eq:bg-Nsigma`, `app:ch_background:eq:bg-Hsigma`:

* literal projected-frame determinant scaling;
* the constructed determinant Hamilton flow, inverse chart and divided phase,
  its physical and canonical differentials, section value and smooth extension;
* the actual positive characteristic transport with initial scalar `ρ`;
* principal-normal nonvanishing from the actual geometric equation, with a common
  compact lower bound for the normalized pullback;
* one common buffer and scale interval for the mixed derivatives and the
  all-order `O(ρ)` estimate of the actual fixed-measure carrier integral;
* the exact flat reference residual for the same frozen mean.

The seed phase, null amplitude, and their smoothness and geometric hypotheses
must be supplied by HamiltonPhase, ActualCarriers, NullTransport and LeadingWave.
The source-scaled Hamilton flow/chart and positive characteristic solution are
constructed in `Hamilton` and `Transport`. `Bounds` chooses one common physical
buffer and scale interval before all derivative orders, derives normal
nonvanishing and mean smoothness, and proves the exact flat residual identity.
`SmoothPhase` retains the canonical footpoint of the divided phase. This module
does not assert the continuum inverse estimates of the full normalized-background
proposition, nor full normal rank at source scale zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

/-- The actual positive-scale mean, using the physical gradient of the named
source phase and its actual canonical principal normal. The carrier measure
and weights are unchanged (`app:ch_background:eq:bg-Hsigma`). Its zero-scale
extension is supplied by `normalizedCarrierMean`, not by this definition. -/
def sourcePrincipalMean {n N : ℕ} {A Z : Type} [Fintype A] [MeasurableSpace Z]
    (F : Euclidean n → Euclidean N) (μ : A → Measure Z) (w : A → Z → ℝ)
    (S : A → Euclidean n × Z → ℝ) (b : A → Euclidean n × Z → Euclidean n)
    (ρ : ℝ) : Euclidean n → MetricTensor n :=
  carrierMean μ w
    (fun a p ↦ LeadingWave.principalNormal
      (AmbientResponse.canonicalNormalCompletion (sourceDilation F ρ) p.1)
      (gradient (fun y ↦ sourcePhase (S a) ρ (y, p.2)) p.1) (sourceAmplitude (b a) ρ p))
    (fun a p ↦ gradient (fun y ↦ sourcePhase (S a) ρ (y, p.2)) p.1)

/-- Identification of the actual mean with the regular normalized carrier
mean, including the original unrestricted carrier measure. Equality of the
actual phase covector is required only on the fixed weight supports
(`app:ch_background:eq:bg-Hsigma`). -/
theorem sourcePrincipalMean_eq_normalizedCarrierMean {n N : ℕ} {A Z : Type}
    [Fintype A] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiff ℝ ∞ F) (hrank : HasFullNormalRankOn F U)
    (μ : A → Measure Z) (K V : A → Set Z) (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (S : A → Euclidean n × Z → ℝ)
    (b : A → Euclidean n × Z → Euclidean n)
    (hsupp : ∀ a z, z ∉ K a → w a z = 0)
    (hS : ∀ a, ContDiffOn ℝ ∞ (S a) (U ×ˢ V a))
    {ρ : ℝ} (hρ : 0 < ρ) {x : Euclidean n} (hx : ρ • x ∈ U) :
    sourcePrincipalMean F μ w S b ρ x =
    normalizedCarrierMean μ w
      (fun a p ↦ LeadingWave.principalNormal (AmbientResponse.canonicalNormalCompletion F p.1)
        (gradient (fun y ↦ S a (y, p.2)) p.1) (b a p))
      (fun a p ↦ gradient (fun y ↦ S a (y, p.2)) p.1) ρ x := by
  classical
  unfold sourcePrincipalMean normalizedCarrierMean carrierMean
  apply Finset.sum_congr rfl
  intro a _
  ext i j
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ V a
  · have hs : ContDiffOn ℝ ∞ (fun y ↦ S a (y, z)) U :=
      (hS a).comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hz⟩)
    have hd := (hs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    dsimp only
    rw [principalNormal_sourcePhase_sourceAmplitude hF (b a) hρ (hrank _ hx) hd,
      gradient_sourcePhase_position hρ.ne' hd]
    rfl
  · have hw0 : w a z = 0 := hsupp a z (fun hzK ↦ hz (hKV a hzK))
    simp [hw0]

/-- The literal principal-normal mean of the source-scaled geometry is the
published normalized carrier mean, for the explicitly scaled input covectors
and amplitudes (`app:ch_background:eq:bg-Hsigma`). The actual phase-gradient
version is `sourcePrincipalMean_eq_normalizedCarrierMean`. -/
theorem carrierMean_principalNormal_sourceDilation {n N : ℕ} {A Z : Type}
    [Fintype A] [MeasurableSpace Z]
    {F : Euclidean n → Euclidean N} {ρ : ℝ}
    (hρ : 0 < ρ) (hF : ContDiff ℝ ∞ F) (x : Euclidean n)
    (hrank : Set.range (normalMap F (ρ • x)) =
      (normalSpace F (ρ • x) : Set (Euclidean N)))
    (μ : A → Measure Z) (w : A → Z → ℝ)
    (ξ b : A → Euclidean n × Z → Euclidean n) :
    carrierMean μ w
      (fun a p ↦ LeadingWave.principalNormal
        (AmbientResponse.canonicalNormalCompletion (sourceDilation F ρ) p.1)
        (ξ a (ρ • p.1, p.2)) (ρ • b a (ρ • p.1, p.2)))
      (fun a p ↦ ξ a (ρ • p.1, p.2)) x =
    normalizedCarrierMean μ w
      (fun a p ↦ LeadingWave.principalNormal (AmbientResponse.canonicalNormalCompletion F p.1)
        (ξ a p) (b a p)) ξ ρ x := by
  simp only [carrierMean, normalizedCarrierMean, normalizedPullback,
    principalNormal_sourceDilation_scaled_amplitude hρ hF x hrank]

/-- The source phase solves the literal scaled determinant eikonal equation,
derived from the genuine seed Hamilton projection chart
(`app:ch_background:eq:bg-Nsigma`). `sourceNormalizedProjectionChart_phase`
identifies this named phase with the constructed literal determinant chart. -/
theorem sourcePhase_eikonal_of_projectionChart {n N : ℕ}
    {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {F : Euclidean n → Euclidean N} {ρ : ℝ}
    (hρ : 0 < ρ) (hF : ContDiff ℝ ∞ F) {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (hQ : ContDiffOn ℝ ∞ (ProjectedStressFrame.projectedStress F) Ω)
    {Φ : HamiltonPhase.HamiltonFlow
      (ActualCarriers.normalizedHomogeneousSymbol hΩ (ProjectedStressFrame.projectedStress F) hQ) Y}
    (C : HamiltonPhase.ProjectionChart Φ) (x : Euclidean n) (η : ℝ × Y)
    (hz : (ρ • x, η) ∈ C.target)
    (hrank : Set.range (normalMap F (ρ • x)) =
      (normalSpace F (ρ • x) : Set (Euclidean N))) :
    ActualCarriers.normalizedSymbol (ProjectedStressFrame.projectedStress (sourceDilation F ρ))
      (x, gradient (fun y ↦ sourcePhase (HamiltonPhase.phase C.coordinates) ρ (y, η)) x) =
        η.1 := by
  rw [normalizedSymbol_sourceDilation hρ hF x _ hrank]
  exact sourcePhase_eikonal C (ne_of_gt hρ) hz

/-- Assemble the common geometric and mean bounds from the actual selected
seed amplitude (`app:ch_background:prop:bg-normalized`). The scalar `α` is the
seed positive characteristic solution with initial value one; its construction
and the original transport PDE are supplied by NullTransport. This theorem
derives all normal/mean conclusions from that seed's smooth positive scalar,
the actual phase, and its fixed characteristic minor. The constructed scaled
transport is identified with that same scalar in `source_transport_on_buffered_core`.

The source phase, normal and original-measure mean share one open physical
buffer and one scale interval, chosen before every derivative order. The seed
Cauchy value is produced by `seedHamiltonPhase_zero`. Neither the output normal
nor the integral's smoothness or its smallness is a hypothesis. -/
theorem exists_sourcePrincipalMean_and_phase_bounds {n N : ℕ} {A Z : Type}
    [Fintype A] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [MeasurableSpace Z] [BorelSpace Z]
    {F : Euclidean n → Euclidean N} {U D : Set (Euclidean n)}
    (hU : IsOpen U) (hc : Convex ℝ U) (h0 : (0 : Euclidean n) ∈ U) (hD : IsCompact D)
    (hF : ContDiff ℝ ∞ F) (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    (hrank : HasFullNormalRankOn F U)
    (hframe : ∃ e : Module.Basis (Fin n) ℝ (ProjectedStressFrame.symmetricNormalMap F 0).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = ProjectedStressFrame.projectedStress F 0 i)
    (μ : A → Measure Z) (K V : A → Set Z)
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hV : ∀ a, IsOpen (V a)) (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a))
    (hwpos : ∀ a z, 0 ≤ w a z) (hsupp : ∀ a z, z ∉ K a → w a z = 0)
    (S α : A → Euclidean n × Z → ℝ) (row col time : A → Fin n)
    (hS : ∀ a, ContDiffOn ℝ ∞ (S a) (U ×ˢ V a))
    (hzero : ∀ a z, z ∈ V a → S a (0, z) = 0)
    (hα : ∀ a, ContDiffOn ℝ ∞ (α a) (U ×ˢ V a))
    (hpos : ∀ a p, p ∈ U ×ˢ V a → 0 < α a p)
    (hchar : ∀ a p, p ∈ U ×ˢ V a →
      ((projectedPhaseGeometry F (S a) (row a) (col a) (time a)).symbol p).det = 0)
    (hminor : ∀ a p, p ∈ U ×ˢ V a →
      ((projectedPhaseGeometry F (S a) (row a) (col a) (time a)).symbol p).adjugate (row a) (col a) ≠ 0)
    (hξ0 : ∀ a z, z ∈ K a → gradient (fun y ↦ S a (y, z)) 0 ≠ 0) :
    let ξ := fun a p ↦ gradient (fun y ↦ S a (y, p.2)) p.1
    let b := fun a p ↦ α a p • (projectedPhaseGeometry F (S a) (row a) (col a) (time a)).kernel p
    let ν := fun a p ↦ LeadingWave.principalNormal
      (AmbientResponse.canonicalNormalCompletion F p.1) (ξ a p) (b a p)
    let J := fun a q ↦ (normalizedPullback (b a) q,
      normalizedPullback (ξ a) q, normalizedPullback (ν a) q)
    let P := fun a q ↦ (sourcePhaseExtension (S a) q,
      fderiv ℝ (fun z ↦ sourcePhaseExtension (S a) (q.1, (q.2.1, z))) q.2.2)
    ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧ ∃ ρ₀ > 0, ρ₀ ≤ 1 ∧
      (∀ a, ContDiffOn ℝ ∞ (J a) (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V a) ∧
        ContDiffOn ℝ ∞ (P a) (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V a)) ∧
      (∃ c > 0, ∀ a, ∀ ρ ∈ Icc (0 : ℝ) ρ₀, ∀ x ∈ D, ∀ z ∈ K a,
        c ≤ ‖normalizedPullback (ν a) (ρ, (x, z))‖) ∧
      (carrierMean μ w ν ξ 0).PosSemidef ∧
      (∀ ρ ∈ Ioc (0 : ℝ) ρ₀, ∀ x ∈ B,
        sourcePrincipalMean F μ w S b ρ x = normalizedCarrierMean μ w ν ξ ρ x ∧
        PositiveBackground.referenceMeanResidual (sourceDilation F ρ)
          (carrierMean μ w ν ξ 0) (sourcePrincipalMean F μ w S b ρ) x =
          sourcePrincipalMean F μ w S b ρ x - carrierMean μ w ν ξ 0 ∧
        ∀ a z, z ∈ V a → sourcePhase (S a) ρ (x, z) = sourcePhaseExtension (S a) (ρ, (x, z))) ∧
      ∀ s : ℕ, ∃ C > 0, ∀ ρ ∈ Ioc (0 : ℝ) ρ₀,
        cNorm D s (fun x ↦ sourcePrincipalMean F μ w S b ρ x - carrierMean μ w ν ξ 0) ≤ C * ρ ∧
        ∀ a x, x ∈ D → ∀ z ∈ K a,
          ‖iteratedFDeriv ℝ s (J a) (ρ, (x, z))‖ ≤ C ∧
          ‖iteratedFDeriv ℝ s (P a) (ρ, (x, z))‖ ≤ C := by
  classical
  let ξ := fun a (p : Euclidean n × Z) ↦ gradient (fun y ↦ S a (y, p.2)) p.1
  let b := fun a p ↦ α a p • (projectedPhaseGeometry F (S a) (row a) (col a) (time a)).kernel p
  let ν := fun a p ↦ LeadingWave.principalNormal
    (AmbientResponse.canonicalNormalCompletion F p.1) (ξ a p) (b a p)
  let J := fun a q ↦ (normalizedPullback (b a) q,
    normalizedPullback (ξ a) q, normalizedPullback (ν a) q)
  let P := fun a q ↦ (sourcePhaseExtension (S a) q,
    fderiv ℝ (fun z ↦ sourcePhaseExtension (S a) (q.1, (q.2.1, z))) q.2.2)
  have hξ a : ContDiffOn ℝ ∞ (ξ a) (U ×ˢ V a) :=
    contDiffOn_phase_positionGradient hU (hV a) (hS a)
  have hb a := selected_seedAmplitude_properties hU (hV a) hF.contDiffOn hflat hrank
    (hS a) (hα a) (row a) (col a) (time a) (hpos a) (hchar a) (hminor a)
  obtain ⟨B, hB, hDB, r, hr, hr1, hseg, hJ, hlo, hH0, hres, hbound⟩ :=
    exists_common_source_geometry_bounds hU h0 hD hF hflat hrank hframe μ K V hV hK hKV
      w ξ b hw hwpos hsupp hξ (fun a ↦ (hb a).1)
      (fun a z hz ↦ ((hb a).2 (0, z) ⟨h0, hKV a hz⟩).1) hξ0
      (fun a z hz ↦ ((hb a).2 (0, z) ⟨h0, hKV a hz⟩).2)
  have hphase a := sourcePhaseExtension_joint_bounds hU hB (hV a) hr hD hDB
    (hK a) (hKV a) (hS a) hseg
  have hmaps (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) r) {x : Euclidean n} (hx : x ∈ B) : ρ • x ∈ U := by
    simpa using hseg ρ ⟨by linarith [hρ.1], by linarith [hρ.2]⟩ x hx 1 ⟨by norm_num, by norm_num⟩
  have heq (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) r) {x : Euclidean n} (hx : x ∈ B) :
      sourcePrincipalMean F μ w S b ρ x = normalizedCarrierMean μ w ν ξ ρ x :=
    sourcePrincipalMean_eq_normalizedCarrierMean hU hF hrank μ K V hKV w S b hsupp hS
      hρ.1 (hmaps ρ hρ hx)
  refine ⟨B, hB, hDB, r, hr, hr1, fun a ↦ ⟨hJ a, (hphase a).1⟩, hlo, hH0, ?_, ?_⟩
  · intro ρ hρ x hx
    refine ⟨heq ρ hρ hx, ?_, ?_⟩
    · have hh := hres ρ hρ x hx
      change PositiveBackground.referenceMeanResidual (sourceDilation F ρ)
        (carrierMean μ w ν ξ 0) (sourcePrincipalMean F μ w S b ρ) x =
        sourcePrincipalMean F μ w S b ρ x - carrierMean μ w ν ξ 0
      simpa only [PositiveBackground.referenceMeanResidual, Pi.add_apply, heq ρ hρ hx,
        normalizedCarrierMean_zero] using hh
    · intro a z hz
      have hs : ContDiffOn ℝ ∞ (fun y ↦ S a (y, z)) U :=
        (hS a).comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hz⟩)
      exact sourcePhase_eq_extension hU hc (hs.of_le (by simp)) (hzero a z hz)
        h0 (hmaps ρ hρ hx) hρ.1.ne'
  · intro s
    obtain ⟨C₀, hC₀, hC⟩ := hbound s
    choose C hCp hPC using fun a ↦ (hphase a).2 s
    let M := max C₀ (∑ a, (C a + 1))
    have hCM a : C a ≤ M := by
      apply le_trans (le_add_of_nonneg_right zero_le_one)
      exact (Finset.single_le_sum (f := fun a ↦ C a + 1)
        (fun a _ ↦ by linarith [hCp a]) (Finset.mem_univ a)).trans (le_max_right _ _)
    refine ⟨M, hC₀.trans_le (le_max_left _ _), ?_⟩
    intro ρ hρ
    have hρ' : ρ ∈ Icc (0 : ℝ) r := ⟨hρ.1.le, hρ.2⟩
    have hn : cNorm D s (fun x ↦ sourcePrincipalMean F μ w S b ρ x - carrierMean μ w ν ξ 0) =
        cNorm D s (fun x ↦ normalizedCarrierMean μ w ν ξ ρ x - normalizedCarrierMean μ w ν ξ 0 x) := by
      apply GeometricProfile.cNorm_eq_of_eventuallyEq
      intro x hx
      filter_upwards [hB.mem_nhds (hDB hx)] with y hy
      rw [heq ρ hρ hy, normalizedCarrierMean_zero]
    refine ⟨?_, ?_⟩
    · rw [hn]
      exact ((hC ρ hρ').1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.1.le)
    · intro a x hx z hz
      exact ⟨((hC ρ hρ').2 a x hx z hz).trans (le_max_left _ _),
        (hPC a ρ hρ' x hx z hz).trans (hCM a)⟩

end JanetCartan.NormalizedBackground.SourceGeometry
