module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.SmoothPhase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Normal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.MeanBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Residual

/-!
# One common scale for the actual principal normals and mean

The geometric estimates in `app:ch_background:prop:bg-normalized`. The input
covectors and amplitudes are the seed fields supplied by HamiltonPhase and
NullTransport. The output normal is the actual canonical completion, whose
smoothness and nonvanishing are proved, not input assumptions. The fixed compact
carrier supports and original measures are used at every scale.
-/

@[expose] public noncomputable section

open Set MeasureTheory Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

open ProjectedStressFrame

private theorem finite_positive_lower_bound {A : Type} [Finite A]
    (f : A → ℝ) (hf : ∀ a, 0 < f a) : ∃ c > 0, ∀ a, c ≤ f a := by
  obtain ⟨c, hc, h⟩ := (finite_range f).isCompact.exists_forall_le' continuousOn_id
    (by rintro x ⟨a, rfl⟩; exact hf a)
  exact ⟨c, hc, fun a ↦ h _ ⟨a, rfl⟩⟩

/-- Integrability for the original carrier measure, derived from the compact
weight support (`app:ch_background:eq:bg-Hsigma`). -/
theorem integrable_carrierMean_entries_of_weight_support
    {A E Z T : Type} {n : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
    [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    (μ : A → Measure Z) (K V : A → Set Z) {U : Set E}
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (ν : A → E × Z → T) (ξ : A → E × Z → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a))
    (hν : ∀ a, ContDiffOn ℝ ∞ (ν a) (U ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (U ×ˢ V a))
    (hsupp : ∀ a z, z ∉ K a → w a z = 0)
    {x : E} (hx : x ∈ U) (a : A) (i j : Fin n) :
    Integrable (fun z ↦ w a z * ‖ν a (x, z)‖ ^ 2 *
      (ξ a (x, z) i * ξ a (x, z) j)) (μ a) := by
  exact IntegrableOn.integrable_of_forall_notMem_eq_zero
    (integrable_carrierMean_entries μ K V hK hKV w ν ξ hw hν hξ hx a i j)
    (fun z hz ↦ by simp [hsupp a z hz])

/-- Common physical buffer, scale interval, positive normal lower bound and
all-order mean estimate for the literal canonical principal normals
(`app:ch_background:prop:bg-normalized`, `app:ch_background:eq:bg-Hsigma`).

The input pencil-null relation and nonzero covector/amplitude are the seed
Hamilton/selected-adjugate transport data. No nonvanishing or regularity of the
output normal, smoothness of its integral, or scaled equation is assumed.
The same `ρ₀`, physical buffer, weights and measures work for every order. -/
theorem exists_common_source_geometry_bounds {n N : ℕ} {A Z : Type}
    [Fintype A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [BorelSpace Z]
    {F : Euclidean n → Euclidean N} {U D : Set (Euclidean n)}
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U) (hD : IsCompact D)
    (hF : ContDiff ℝ ∞ F) (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    (hrank : HasFullNormalRankOn F U)
    (hframe : ∃ e : Module.Basis (Fin n) ℝ (symmetricNormalMap F 0).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = ProjectedStressFrame.projectedStress F 0 i)
    (μ : A → Measure Z) (K V : A → Set Z)
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hV : ∀ a, IsOpen (V a)) (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (ξ b : A → Euclidean n × Z → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a)) (hwpos : ∀ a z, 0 ≤ w a z)
    (hsupp : ∀ a z, z ∉ K a → w a z = 0)
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (U ×ˢ V a))
    (hb : ∀ a, ContDiffOn ℝ ∞ (b a) (U ×ˢ V a))
    (hnull : ∀ a z, z ∈ K a → ActualCarriers.pencil (ProjectedStressFrame.projectedStress F 0)
      (ξ a (0, z)) *ᵥ (fun j ↦ b a (0, z) j) = 0)
    (hξ0 : ∀ a z, z ∈ K a → ξ a (0, z) ≠ 0)
    (hb0 : ∀ a z, z ∈ K a → b a (0, z) ≠ 0) :
    let ν := fun a p ↦ LeadingWave.principalNormal
      (AmbientResponse.canonicalNormalCompletion F p.1) (ξ a p) (b a p)
    let J := fun a q ↦ (normalizedPullback (b a) q,
      normalizedPullback (ξ a) q, normalizedPullback (ν a) q)
    ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧
      (∀ ρ ∈ Ioo (-2 * ρ₀) (2 * ρ₀), ∀ x ∈ B, ∀ t ∈ Ioo (-1 : ℝ) 2,
        (t * ρ) • x ∈ U) ∧
      (∀ a, ContDiffOn ℝ ∞ (J a) (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V a)) ∧
      (∃ c > 0, ∀ a, ∀ ρ ∈ Icc (0 : ℝ) ρ₀, ∀ x ∈ D, ∀ z ∈ K a,
        c ≤ ‖normalizedPullback (ν a) (ρ, (x, z))‖) ∧
      (carrierMean μ w ν ξ 0).PosSemidef ∧
      (∀ ρ ∈ Ioc (0 : ℝ) ρ₀, ∀ x ∈ B,
        PositiveBackground.referenceMeanResidual (sourceDilation F ρ)
          (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ) x =
          normalizedCarrierMean μ w ν ξ ρ x - normalizedCarrierMean μ w ν ξ 0 x) ∧
      ∀ s : ℕ, ∃ C > 0, ∀ ρ ∈ Icc (0 : ℝ) ρ₀,
        cNorm D s (fun x ↦ normalizedCarrierMean μ w ν ξ ρ x -
          normalizedCarrierMean μ w ν ξ 0 x) ≤ C * ρ ∧
        ∀ a x, x ∈ D → ∀ z ∈ K a, ‖iteratedFDeriv ℝ s (J a) (ρ, (x, z))‖ ≤ C := by
  classical
  let ν := fun a p ↦ LeadingWave.principalNormal
    (AmbientResponse.canonicalNormalCompletion F p.1) (ξ a p) (b a p)
  let J := fun a q ↦ (normalizedPullback (b a) q,
    normalizedPullback (ξ a) q, normalizedPullback (ν a) q)
  change ∃ B, _ ∧ _ ∧ ∃ ρ₀, _ ∧ _ ∧ _ ∧ (∀ a, ContDiffOn ℝ ∞ (J a) _) ∧ _
  have himm : IsImmersionOn F U := isImmersionOn_of_isIsometricOn
    (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one) hflat
  have hν (a : A) : ContDiffOn ℝ ∞ (ν a) (U ×ˢ V a) :=
    contDiffOn_canonicalPrincipalNormal hU hF.contDiffOn himm hrank
      (fun _ hp ↦ hp.1) (hξ a) (hb a)
  have hlo (a : A) := exists_uniform_principalNormal_lower_bound
    hU hF.contDiffOn h0 himm hrank (U := U ×ˢ V a) (fun _ hp ↦ hp.1)
    (hU.prod (hV a)) (hξ a) (hb a) (hD.prod (hK a))
    (fun p hp ↦ ⟨h0, hKV a hp.2⟩) hframe
    (fun p hp ↦ hnull a p.2 hp.2) (fun p hp ↦ hξ0 a p.2 hp.2)
    (fun p hp ↦ hb0 a p.2 hp.2)
  choose c hc δ hδ hlo using hlo
  obtain ⟨c₀, hc₀, hc_le⟩ := finite_positive_lower_bound c hc
  obtain ⟨δ₀, hδ₀, hδ_le⟩ := finite_positive_lower_bound δ hδ
  obtain ⟨W, hW, hDW, ε, hε, hε1, _hWU, hmean⟩ :=
    exists_local_cNorm_normalizedCarrierMean_sub_zero_bounds μ K V hU h0 hD
      hV hK hKV w ν ξ hw hν hξ hsupp
  obtain ⟨B₁, hB₁, hDB₁, r, hr, hseg⟩ := exists_source_phase_buffer hU h0 hD
  let B := B₁ ∩ W
  let ρ₀ := min r (min ε δ₀)
  have hρ₀ : 0 < ρ₀ := lt_min hr (lt_min hε hδ₀)
  have hρr : ρ₀ ≤ r := min_le_left _ _
  have hρε : ρ₀ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ₀ ≤ δ₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hB : IsOpen B := hB₁.inter hW
  have hDB : D ⊆ B := fun _ hx ↦ ⟨hDB₁ hx, hDW hx⟩
  have hseg' : ∀ ρ ∈ Ioo (-2 * ρ₀) (2 * ρ₀), ∀ x ∈ B,
      ∀ t ∈ Ioo (-1 : ℝ) 2, (t * ρ) • x ∈ U := by
    intro ρ hρ x hx t ht
    exact hseg ρ ⟨by linarith [hρ.1], by linarith [hρ.2]⟩ x hx.1 t ht
  have hmaps : ∀ ρ ∈ Ioo (-2 * ρ₀) (2 * ρ₀), MapsTo (fun x ↦ ρ • x) B U := by
    intro ρ hρ x hx
    simpa using hseg' ρ hρ x hx 1 ⟨by norm_num, by norm_num⟩
  have hinc : Icc (0 : ℝ) ρ₀ ⊆ Ioo (-2 * ρ₀) (2 * ρ₀) := by
    intro ρ hρ
    constructor <;> linarith [hρ.1, hρ.2]
  have hJ (a : A) : ContDiffOn ℝ ∞ (J a) (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V a) := by
    have hm : MapsTo (fun q : ℝ × (Euclidean n × Z) ↦ (q.1 • q.2.1, q.2.2))
        (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V a) (U ×ˢ V a) :=
      fun _ hq ↦ ⟨hmaps _ hq.1 hq.2.1, hq.2.2⟩
    exact ((contDiffOn_normalizedPullback (hb a)).mono hm).prodMk
      (((contDiffOn_normalizedPullback (hξ a)).mono hm).prodMk
        ((contDiffOn_normalizedPullback (hν a)).mono hm))
  have hi := integrable_carrierMean_entries_of_weight_support μ K V hK hKV
    w ν ξ hw hν hξ hsupp h0
  refine ⟨B, hB, hDB, ρ₀, hρ₀, hρε.trans hε1, hseg', hJ,
    ⟨c₀, hc₀, ?_⟩, carrierMean_posSemidef μ w ν ξ 0 hwpos hi, ?_, ?_⟩
  · intro a ρ hρ x hx z hz
    exact (hc_le a).trans (hlo a ρ ⟨hρ.1, hρ.2.trans (hρδ.trans (hδ_le a))⟩
      (x, z) ⟨hx, hz⟩)
  · intro ρ hρ x hx
    exact referenceMeanResidual_sourceDilation hρ.1 hF hB hflat
      (hmaps ρ (hinc ⟨hρ.1.le, hρ.2⟩)) μ w ν ξ hwpos hi x hx
  · intro s
    obtain ⟨C₀, hC₀, hCmean⟩ := hmean s
    have hj (a : A) : ∃ C, ∀ q ∈ Icc (0 : ℝ) ρ₀ ×ˢ D ×ˢ K a,
        ‖iteratedFDeriv ℝ s (J a) q‖ ≤ C :=
      (isCompact_Icc.prod (hD.prod (hK a))).exists_bound_of_continuousOn
        ((ContinuousOn.continuousOn_iteratedFDeriv (hJ a)
          (isOpen_Ioo.prod (hB.prod (hV a))) (by simp)).mono
            (fun _ hq ↦ ⟨hinc hq.1, hDB hq.2.1, hKV a hq.2.2⟩))
    choose C hC using hj
    refine ⟨max C₀ (∑ a, (|C a| + 1)), hC₀.trans_le (le_max_left _ _), ?_⟩
    intro ρ hρ
    refine ⟨(hCmean ρ ⟨hρ.1, hρ.2.trans hρε⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.1), ?_⟩
    intro a x hx z hz
    apply (hC a (ρ, (x, z)) ⟨hρ, hx, hz⟩).trans
    apply le_trans ((le_abs_self (C a)).trans (le_add_of_nonneg_right zero_le_one))
    exact (Finset.single_le_sum (f := fun a ↦ |C a| + 1)
      (fun a _ ↦ by positivity) (Finset.mem_univ a)).trans
      (le_max_right _ _)

end JanetCartan.NormalizedBackground.SourceGeometry
