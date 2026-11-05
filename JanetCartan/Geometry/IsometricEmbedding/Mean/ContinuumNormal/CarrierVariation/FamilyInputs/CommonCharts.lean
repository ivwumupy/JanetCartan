module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.SliceJacobian
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.MaskBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.IncidenceScaling
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.SeedAdmission

/-!
# Common normalized conic comparison charts for the explicit source family

For `paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4', the theorems below
construct fixed compact input and target sets, open buffers, actual smooth
inverses and the full augmented differential gap from seed data. The reference
equivalence comes from the named frozen incidence construction. The physical
and scale buffers are constructed before choosing the scale or any density.

`exists_retained_seed_common_conic_charts` derives the zero-section physical
covector identity from the actual Hamilton seed's origin frame and a fixed
primitive frame threshold. The root neighborhood comes from
`exists_frozenRootBuffer`; quantitative phase comparison puts the actual
momentum in it. `projectedStress_flatReference_zero` supplies the exact origin
frame for a flat seed.

The local construction also proves a lower bound for the literal slice
Jacobian. The conic construction uses a fixed output normalization sphere,
a common open conic target and explicit radial extensions of the local
inverses. The original masks are chosen before the scale. Their uncut
transported support has a punctured closure buffer inside the common target,
and both inverse identities hold on that support. No global support is
assumed to fit inside a finite radial shell.

`exists_dilated_flat_seed_common_conic_charts` closes every seed premise by
choosing a genuine source contraction of the supplied flat reference on the
original bounded physical domain. It proves frame admission and the additional
smallness threshold, seed smoothness and the exact covector identity, then
constructs all inverse fields. The seed contraction precedes the later family
scale. Identification with separately chosen positive-scale charts remains the
parent's `SourceMatching` obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open NormalizedBackground.SourceGeometry ContinuumNormalReduction.TransportSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison ContinuumRow.CanonicalConic

variable {n : ℕ} {P : Patch n} {U₀ : Set (Euclidean n)} {hU₀ : IsOpen U₀}
    (T : PatchQuantitativeFamily P U₀ hU₀)

/-- Construct the exact local inverse-comparison inputs for the literal
`sourceTransportPosition` family. Only seed smoothness, its physical covector
on the zero section, and the frozen incidence/transversality are inputs.
All domains, the equivalence, and the positive scale and determinant bounds
precede `σ`. Consumer: `CarrierVariation.exists_inverseCoordinates_sub_le`
in `app:ch_osc:prop:osc-normal`, Step 4'. The common lower bound includes
the literal slice Jacobian. The following conic theorem supplies the
uncut original-mask buffers. -/
theorem exists_source_common_local_charts
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V) (h0 : (0 : Euclidean n) ∈ U)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hVbuffer : V ⊆ ball (covectorCenter T) (2 * T.family.radius))
    (hseed : ∀ η ∈ V, gradient (fun x ↦ S (x, η)) 0 =
      (adaptedSliceCoordinates T).equiv.symm (dispersion T η, η))
    (hzV : spatialCarrier T (spectatorCenter z₀, z₀ 0) ∈ V) :
    let Y := sourceTransportPosition S (fun z ↦ spatialCarrier T (z.2, z.1))
    let A := augmentedReferenceEquiv T hP hz₀ hinc hd
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    ∃ K W : Set (InputVariables n), IsCompact K ∧ Convex ℝ K ∧ IsOpen W ∧ K ⊆ W ∧
      p₀ ∈ interior K ∧
    ∃ Q Ω : Set (Variables n × Euclidean 2), IsCompact Q ∧ IsOpen Ω ∧ Q ⊆ Ω ∧
      augmentedTransportGradient (Y 0) p₀ ∈ interior Q ∧
    ∃ ε > (0 : ℝ), ∃ cJ > (0 : ℝ),
    ∃ u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
      ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
        augmentedTransportGradient (Y q.1) q.2) (Ioo (-ε) ε ×ˢ W) ∧
      ∀ σ ∈ Ioo (-ε) ε,
        ContDiffOn ℝ ∞ (augmentedTransportGradient (Y σ)) W ∧
        ContDiffOn ℝ ∞ (u σ) Ω ∧
        MapsTo (inverseCoordinates (u σ)) Q K ∧
        (∀ q ∈ Ω, transportAveragedGradient (Y σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
        (∀ p ∈ K,
          ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Y σ)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ K,
          cJ ≤ |(A.symm.toContinuousLinearMap.comp
            (fderiv ℝ (augmentedTransportGradient (Y σ)) p)).det|) ∧
        (∀ p ∈ K, cJ ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T) (Y σ) p) ∧
        InjOn (augmentedTransportGradient (Y σ)) K := by
  dsimp only
  let ζ := fun z : ℝ × Euclidean 2 ↦ spatialCarrier T (z.2, z.1)
  let Z := (fun z : ℝ × Euclidean 2 ↦ carrierParameters (z.2, z.1)) ⁻¹'
    parameterInterior (2 * P.radius)
  have hZ : IsOpen Z := (isOpen_parameterInterior _).preimage
    (carrierParameters.continuous.comp (continuous_snd.prodMk continuous_fst))
  have hζ : ContDiffOn ℝ ∞ ζ Z := (spatialCarrier_smooth T hP).comp
    (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hz ↦ hz)
  let Z' := Z ∩ ζ ⁻¹' V
  have hZ' : IsOpen Z' := hζ.continuousOn.isOpen_inter_preimage hZ hV
  have hzZ : (z₀ 0, spectatorCenter z₀) ∈ Z := by
    change carrierParameters (spectatorCenter z₀, z₀ 0) ∈ parameterInterior (2 * P.radius)
    rw [carrierParameters_spectatorCenter]
    exact parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz₀ i).le)
  have hzZ' : (z₀ 0, spectatorCenter z₀) ∈ Z' := ⟨hzZ, hzV⟩
  obtain ⟨B, hB, h6B, r, hr, hscale⟩ := exists_source_phase_buffer hU h0
    (isCompact_closedBall (0 : Euclidean n) 6)
  let W : Set (InputVariables n) := (ball (0 : Euclidean n) 1 ×ˢ ball 0 1) ×ˢ Z' ×ˢ univ
  have hW : IsOpen W := (isOpen_ball.prod isOpen_ball).prod (hZ'.prod isOpen_univ)
  have hseg : ∀ t ∈ Ioo (-1 : ℝ) 2,
      MapsTo (transportSegmentInput n t) W (B ×ˢ Z') := by
    intro t ht p hp
    refine ⟨h6B ?_, hp.2.1⟩
    rw [mem_closedBall_zero_iff]
    change ‖p.1.2 + t • (p.1.1 - p.1.2)‖ ≤ 6
    have hx : ‖p.1.1‖ ≤ 1 := (mem_ball_zero_iff.mp hp.1.1).le
    have hy : ‖p.1.2‖ ≤ 1 := (mem_ball_zero_iff.mp hp.1.2).le
    have ht' : ‖t‖ ≤ 2 := by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1, ht.2]
    calc
      _ ≤ ‖p.1.2‖ + ‖t • (p.1.1 - p.1.2)‖ := norm_add_le _ _
      _ = ‖p.1.2‖ + ‖t‖ * ‖p.1.1 - p.1.2‖ := by rw [norm_smul]
      _ ≤ 1 + 2 * (1 + 1) := add_le_add hy
        (mul_le_mul ht' ((norm_sub_le _ _).trans (add_le_add hx hy)) (norm_nonneg _) (by norm_num))
      _ ≤ 6 := by norm_num
  have hIT : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun _ ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hF := contDiffOn_sourceAugmentedTransport hU hB hV hZ' hW hS
    (hζ.mono inter_subset_left) (fun _ hz ↦ hz.2) hscale isOpen_Ioo hIT hseg
  have hp₀ : augmentedInputCenter T (z₀ := z₀) (k := k) ∈ W :=
    ⟨⟨mem_ball_self zero_lt_one, mem_ball_self zero_lt_one⟩, hzZ', mem_univ _⟩
  let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
  let A := augmentedReferenceEquiv T hP hz₀ hinc hd
  have hA := fderiv_sourceAugmentedTransport_zero_center T hP hz₀ hinc hd
    hU hV h0 hS hVbuffer hseed hzV
  have h0I : (0 : ℝ) ∈ Ioo (-2 * r) (2 * r) := ⟨by linarith, by linarith⟩
  obtain ⟨rJ, hrJ, _, eJ, heJ, _, dJ, hdJ, hjac⟩ :=
    exists_local_positive_transport_jacobian (adaptedSliceCoordinates T)
      isOpen_Ioo hW h0I hp₀ hF A hA
  let W' := W ∩ ball p₀ rJ
  let I' := Ioo (-2 * r) (2 * r) ∩ Ioo (-eJ) eJ
  have hW' : IsOpen W' := hW.inter isOpen_ball
  have hI' : IsOpen I' := isOpen_Ioo.inter isOpen_Ioo
  have h0I' : (0 : ℝ) ∈ I' := ⟨h0I, by constructor <;> linarith⟩
  have hp₀' : p₀ ∈ W' := ⟨hp₀, mem_ball_self hrJ⟩
  have hF' : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (sourceTransportPosition S ζ q.1) q.2) (I' ×ˢ W') :=
    hF.mono (prod_mono inter_subset_left inter_subset_left)
  obtain ⟨ρ, hρ, hKW, ε, hε, hεI, Q, Ω, hQ, hΩ, hQΩ, hcenter, cD, hcD, u, hjoint, hu⟩ :=
    exists_local_common_transport_inverse hI' hW' h0I' hp₀' hF' A hA
  refine ⟨closedBall p₀ ρ, W', isCompact_closedBall _ _, convex_closedBall _ _, hW', hKW,
    ?_, Q, Ω, hQ, hΩ, hQΩ, hcenter, ε, hε, min cD dJ, lt_min hcD hdJ, u, hjoint, ?_⟩
  · exact mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ hρ)
  · intro σ hσ
    obtain ⟨hf, hs, _, hmap, heq, hgap, hdet, hinj⟩ := hu σ hσ
    exact ⟨hf, hs, hmap, heq, hgap,
      fun p hp ↦ (min_le_left _ _).trans (hdet p hp),
      fun p hp ↦ (min_le_right _ _).trans
        (hjac σ (hεI hσ).2 p (ball_subset_closedBall (hKW hp).2)), hinj⟩

/-- Common normalized conic comparison buffers for the explicit source
family. All domains, mask radii, the equivalence and positive bounds precede
`σ`. The same compact input has the full augmented half-gap and the literal
slice-Jacobian lower bound. The output sphere is a normalization section;
the right-inverse equation, scaling law, and original-mask closure buffer
hold at every nonzero radial frequency. Consumer:
`CarrierVariation.exists_inverseCoordinates_sub_le` and the supported normal
amplitude (`app:ch_osc:prop:osc-normal`, Step 4', `bg-Psi`, `bg-jacobian`).
The primitive seed covector identity `hseed` is discharged in
`exists_retained_seed_common_conic_charts` below. -/
theorem exists_source_common_conic_charts
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V) (h0 : (0 : Euclidean n) ∈ U)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hVbuffer : V ⊆ ball (covectorCenter T) (2 * T.family.radius))
    (hseed : ∀ η ∈ V, gradient (fun x ↦ S (x, η)) 0 =
      (adaptedSliceCoordinates T).equiv.symm (dispersion T η, η))
    (hzV : spatialCarrier T (spectatorCenter z₀, z₀ 0) ∈ V) :
    let Y := sourceTransportPosition S (fun z ↦ spatialCarrier T (z.2, z.1))
    let A := augmentedReferenceEquiv T hP hz₀ hinc hd
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ K W : Set (InputVariables n), IsCompact K ∧ Convex ℝ K ∧ IsOpen W ∧ K ⊆ W ∧
      p₀ ∈ interior K ∧
    ∃ Q Ω : Set (Variables n × Euclidean 2), IsCompact Q ∧ IsOpen Ω ∧ Q ⊆ Ω ∧
      augmentedTransportGradient (Y 0) p₀ ∈ Q ∧
      (∀ q ∈ Q, ‖q.1.2.2‖ = ‖k‖) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω) ∧
    ∃ r > (0 : ℝ), ∃ a > (0 : ℝ), a ≤ r ∧
    ∃ ε > (0 : ℝ), ∃ cJ > (0 : ℝ),
    ∃ u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
      ∀ σ ∈ Ioo (-ε) ε,
        ContDiffOn ℝ ∞ (augmentedTransportGradient (Y σ)) W ∧
        ContDiffOn ℝ ∞ (u σ) Ω ∧
        MapsTo (inverseCoordinates (u σ)) Q K ∧
        (∀ q ∈ Ω, transportAveragedGradient (Y σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
        (∀ p ∈ K,
          ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Y σ)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ K, cJ ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T) (Y σ) p) ∧
        (∀ t : ℝ, 0 < t → ∀ q,
          u σ (scaleFrequency t q.1, q.2) = ((u σ q).1, t • (u σ q).2)) ∧
        (∀ p ∈ conicMaskSupport z₀ ηb r a,
          scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ K ∧
          transportAveragedGradient (Y σ) p ≠ 0 ∧
          normalizeOutputRadius ‖k‖ (augmentedTransportGradient (Y σ) p) ∈ Q ∧
          inverseCoordinates (u σ) (augmentedTransportGradient (Y σ) p) = p) ∧
        (closure (augmentedTransportGradient (Y σ) '' conicMaskSupport z₀ ηb r a) ∩
          {q | q.1.2.2 ≠ 0} ⊆ Ω) := by
  dsimp only
  let Y := sourceTransportPosition S (fun z ↦ spatialCarrier T (z.2, z.1))
  let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hk : k ≠ 0 := by
    intro hk
    subst k
    simp [incidence] at hd
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  have hℓ : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have hcenter : augmentedTransportGradient (Y 0) p₀ = ((0, 0, k), spectatorCenter z₀) :=
    (sourceAugmentedTransport_zero_eq_frozen T hU hV h0 hS hVbuffer hseed p₀ hzV).trans
      (frozenAugmentedChart_center T hP hz₀ hinc)
  have hfreq : transportAveragedGradient (Y 0) p₀ = k :=
    congrArg (fun q : Variables n × Euclidean 2 ↦ q.1.2.2) hcenter
  obtain ⟨K, W, hK, hconv, hW, hKW, hp₀, Q, Ω, hQ, hΩ, hQΩ, hq₀,
    ε₀, hε₀, cJ, hcJ, u, hjoint, hu⟩ :=
    exists_source_common_local_charts T hP hz₀ hinc hd hU hV h0 hS hVbuffer hseed hzV
  have hf : ContinuousAt (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (0, p₀) :=
    hjoint.continuousOn.continuousAt ((isOpen_Ioo.prod hW).mem_nhds
      ⟨⟨by linarith, hε₀⟩, hKW (interior_subset hp₀)⟩)
  obtain ⟨r, hr, a, ha, har, ε₁, hε₁, hmask⟩ :=
    exists_source_normalized_mask_buffer hηb hp₀ hf hq₀ (hfreq ▸ hk)
  change ∀ σ ∈ Ioo (-ε₁) ε₁, ∀ p ∈ conicMaskSupport z₀ ηb r a,
    scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ K ∧ transportAveragedGradient (Y σ) p ≠ 0 ∧
    normalizeOutputRadius ‖transportAveragedGradient (Y 0) p₀‖
      (augmentedTransportGradient (Y σ) p) ∈ Q ∧
    scaleInput (‖transportAveragedGradient (Y 0) p₀‖ /
      ‖transportAveragedGradient (Y σ) p‖) p ∈ K at hmask
  rw [hfreq] at hmask
  let Q' := Q ∩ {q : Variables n × Euclidean 2 | ‖q.1.2.2‖ = ‖k‖}
  have hQ'Ω : Q' ⊆ normalizedConicTarget ‖k‖ Ω := by
    intro q hq
    refine ⟨norm_pos_iff.mp (hq.2 ▸ hℓ), ?_⟩
    rw [normalizeOutputRadius_eq_self hℓ hq.2]
    exact hQΩ hq.1
  refine ⟨K, W, hK, hconv, hW, hKW, hp₀, Q', normalizedConicTarget ‖k‖ Ω,
    hQ.inter_right (isClosed_eq continuous_fst.snd.snd.norm continuous_const),
    normalizedConicTarget_isOpen _ hΩ, hQ'Ω,
    ⟨interior_subset hq₀, by change ‖transportAveragedGradient (Y 0) p₀‖ = ‖k‖; rw [hfreq]⟩,
    fun _ hq ↦ hq.2, fun t ht q ↦ normalizedConicTarget_smul_iff _ _ q ht,
    r, hr, a, ha, har, min ε₀ ε₁, lt_min hε₀ hε₁, cJ, hcJ,
    fun σ ↦ radialExtensionInverse ‖k‖ (u σ), ?_⟩
  intro σ hσ
  have hσ₀ : σ ∈ Ioo (-ε₀) ε₀ :=
    ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hσ.1, hσ.2.trans_le (min_le_left _ _)⟩
  have hσ₁ : σ ∈ Ioo (-ε₁) ε₁ :=
    ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hσ.1, hσ.2.trans_le (min_le_right _ _)⟩
  obtain ⟨hY, hs, hmap, heq, hgap, _, hdet, hinj⟩ := hu σ hσ₀
  refine ⟨hY, radialExtensionInverse_smooth _ hΩ hs, ?_,
    fun _ hq ↦ radialExtensionInverse_right_inverse hℓ heq hq,
    hgap, hdet, fun t ht q ↦ radialExtensionInverse_smul _ _ q ht, ?_,
    normalized_mask_image_punctured_buffer hQ.isClosed hQΩ
      (fun p hp ↦ (hmask σ hσ₁ p hp).2.2.1)⟩
  · intro q hq
    have hc : inverseCoordinates (radialExtensionInverse ‖k‖ (u σ)) q =
        inverseCoordinates (u σ) q := by
      simp only [inverseCoordinates, radialExtensionInverse_eq_on_sphere hℓ _ hq.2]
    rw [hc]
    exact hmap hq.1
  · intro p hp
    obtain ⟨hi, hn, ho, hscaled⟩ := hmask σ hσ₁ p hp
    refine ⟨hi, hn, ⟨ho, ?_⟩,
      radialExtensionInverse_left_inverse hℓ hinj hmap hQΩ heq hn ho hscaled⟩
    change ‖(‖k‖ / ‖transportAveragedGradient (Y σ) p‖) •
      transportAveragedGradient (Y σ) p‖ = ‖k‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hℓ (norm_pos_iff.mpr hn)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hn)]


/-- The fixed seed frame threshold for the common normalized conic construction.
The seed is the actual retained Hamilton phase. Seed smoothness, the exact
zero-section covector, and the augmented reference differential are derived;
the origin frame identity is supplied by `projectedStress_flatReference_zero`.
Consumer: the actual-family assembly in `app:ch_osc:prop:osc-normal`, Step 4'.
The following dilation theorem also discharges the primitive frame threshold. -/
theorem exists_retained_seed_common_conic_charts
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0) :
    ∃ δ > (0 : ℝ), ∀ Q₀ : {Q : Euclidean n → Fin n → MetricTensor n //
        ContDiffOn ℝ ∞ Q U₀ ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q₀.1 - fun _ ↦ cubeStress n) < δ → Q₀.1 0 = cubeStress n →
    let S := fun p : Euclidean n × Euclidean (n - 1) ↦
      HamiltonPhase.phase (T.currentChart Q₀).coordinates (p.1, (0, p.2))
    let Y := sourceTransportPosition S (fun z ↦ spatialCarrier T (z.2, z.1))
    let A := augmentedReferenceEquiv T hP hz₀ hinc hd
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ K W : Set (InputVariables n), IsCompact K ∧ Convex ℝ K ∧ IsOpen W ∧ K ⊆ W ∧
      p₀ ∈ interior K ∧
    ∃ Q Ω : Set (Variables n × Euclidean 2), IsCompact Q ∧ IsOpen Ω ∧ Q ⊆ Ω ∧
      augmentedTransportGradient (Y 0) p₀ ∈ Q ∧
      (∀ q ∈ Q, ‖q.1.2.2‖ = ‖k‖) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω) ∧
    ∃ r > (0 : ℝ), ∃ a > (0 : ℝ), a ≤ r ∧
    ∃ ε > (0 : ℝ), ∃ cJ > (0 : ℝ),
    ∃ u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
      ∀ σ ∈ Ioo (-ε) ε,
        ContDiffOn ℝ ∞ (augmentedTransportGradient (Y σ)) W ∧
        ContDiffOn ℝ ∞ (u σ) Ω ∧
        MapsTo (inverseCoordinates (u σ)) Q K ∧
        (∀ q ∈ Ω, transportAveragedGradient (Y σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
        (∀ p ∈ K,
          ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Y σ)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ K, cJ ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T) (Y σ) p) ∧
        (∀ t : ℝ, 0 < t → ∀ q,
          u σ (scaleFrequency t q.1, q.2) = ((u σ q).1, t • (u σ q).2)) ∧
        (∀ p ∈ conicMaskSupport z₀ ηb r a,
          scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ K ∧
          transportAveragedGradient (Y σ) p ≠ 0 ∧
          normalizeOutputRadius ‖k‖ (augmentedTransportGradient (Y σ) p) ∈ Q ∧
          inverseCoordinates (u σ) (augmentedTransportGradient (Y σ) p) = p) ∧
        (closure (augmentedTransportGradient (Y σ) '' conicMaskSupport z₀ ηb r a) ∩
          {q | q.1.2.2 ≠ 0} ⊆ Ω) := by
  obtain ⟨V, hV, hzV, hVbuffer, δ, hδ, hseed⟩ := exists_retained_seed_covector_buffer T hP hz₀
  refine ⟨δ, hδ, fun Q₀ hQ hQzero ↦ ?_⟩
  obtain ⟨hS, hcov⟩ := hseed Q₀ hQ hQzero
  exact exists_source_common_conic_charts T hP hz₀ hinc hd isOpen_ball hV
    (mem_ball_self T.physicalRadius_pos) hS hVbuffer hcov hzV


/-- Actual common normalized conic charts from the fixed incidence data and a
flat reference on a bounded physical domain. Choose one genuine seed contraction
below `cap`, admit its projected frame to the SAME retained Hamilton family, and
construct the inverses for its literal `sourceTransportPosition` family. Every
extra analytic premise of `exists_source_common_conic_charts` is discharged:
seed smoothness, zero-section covector, and the primitive frame threshold.
All comparison domains, masks, normalization and positive bounds precede `σ`,
density and history. Both inverse identities and the punctured support buffer
retain every nonzero frequency (`app:ch_osc:prop:osc-normal`, Step 4',
`app:ch_background:prop:bg-frame`, `bg-Psi`, `bg-jacobian`).
Matching this explicit family to separately retained positive-scale charts
belongs to `FamilyInputs.SourceMatching`. -/
theorem exists_dilated_flat_seed_common_conic_charts
    (G : FlatReference n) (hbounded : Bornology.IsBounded U₀)
    {cap : ℝ} (hcap : 0 < cap)
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < cap ∧ ρ ≤ 1 ∧
    ∃ hQ : ContDiffOn ℝ ∞ (ProjectedStressFrame.projectedStress (sourceDilation G.map ρ)) U₀,
    ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (ProjectedStressFrame.projectedStress (sourceDilation G.map ρ) - fun _ ↦ cubeStress n) <
          T.family.threshold,
    let S := fun p : Euclidean n × Euclidean (n - 1) ↦
      HamiltonPhase.phase (T.currentChart
        ⟨ProjectedStressFrame.projectedStress (sourceDilation G.map ρ), hQ, hlow⟩).coordinates
          (p.1, (0, p.2))
    let Y := sourceTransportPosition S (fun z ↦ spatialCarrier T (z.2, z.1))
    let A := augmentedReferenceEquiv T hP hz₀ hinc hd
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ K W : Set (InputVariables n), IsCompact K ∧ Convex ℝ K ∧ IsOpen W ∧ K ⊆ W ∧
      p₀ ∈ interior K ∧
    ∃ Q Ω : Set (Variables n × Euclidean 2), IsCompact Q ∧ IsOpen Ω ∧ Q ⊆ Ω ∧
      augmentedTransportGradient (Y 0) p₀ ∈ Q ∧
      (∀ q ∈ Q, ‖q.1.2.2‖ = ‖k‖) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω) ∧
    ∃ r > (0 : ℝ), ∃ a > (0 : ℝ), a ≤ r ∧
    ∃ ε > (0 : ℝ), ∃ cJ > (0 : ℝ),
    ∃ u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
      ∀ σ ∈ Ioo (-ε) ε,
        ContDiffOn ℝ ∞ (augmentedTransportGradient (Y σ)) W ∧
        ContDiffOn ℝ ∞ (u σ) Ω ∧
        MapsTo (inverseCoordinates (u σ)) Q K ∧
        (∀ q ∈ Ω, transportAveragedGradient (Y σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
        (∀ p ∈ K,
          ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Y σ)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ K, cJ ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T) (Y σ) p) ∧
        (∀ t : ℝ, 0 < t → ∀ q,
          u σ (scaleFrequency t q.1, q.2) = ((u σ q).1, t • (u σ q).2)) ∧
        (∀ p ∈ conicMaskSupport z₀ ηb r a,
          scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ K ∧
          transportAveragedGradient (Y σ) p ≠ 0 ∧
          normalizeOutputRadius ‖k‖ (augmentedTransportGradient (Y σ) p) ∈ Q ∧
          inverseCoordinates (u σ) (augmentedTransportGradient (Y σ) p) = p) ∧
        (closure (augmentedTransportGradient (Y σ) '' conicMaskSupport z₀ ηb r a) ∩
          {q | q.1.2.2 ≠ 0} ⊆ Ω) := by
  obtain ⟨δ, hδ, hcharts⟩ := exists_retained_seed_common_conic_charts T hP hz₀ hinc hd
  obtain ⟨ρ, hρ, hρcap, hρ1, hQ, hsmall, hzero⟩ :=
    exists_dilated_flat_seed_frame T G hbounded (lt_min T.family.threshold_pos hδ) hcap
  have hlow := hsmall.trans_le (min_le_left T.family.threshold δ)
  refine ⟨ρ, hρ, hρcap, hρ1, hQ, hlow, ?_⟩
  exact hcharts ⟨_, hQ, hlow⟩ (hsmall.trans_le (min_le_right _ _)) hzero

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
