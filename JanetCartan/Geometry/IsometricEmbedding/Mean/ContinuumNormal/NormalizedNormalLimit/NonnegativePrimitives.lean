module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SourcePrimitives

/-!
# Source primitive convergence from nonnegative-scale geometry

The actual retained current carriers are supplied for positive scales, with
a separate literal zero-scale inverse. A square reparameterization applies
the existing conic convergence theorem to these same inverses. No inverse
at a negative source scale or smaller target domain is required.
-/

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open ContinuumNormalReduction.TransportSymbol CarrierVariation.FamilyInputs
open CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity
open CarrierVariation.AmplitudeDifference.PrimitiveDensity

/-- The actual normalized forward, inverse, Jacobian and reciprocal converge
on the SAME retained compact domains using inverse geometry only for
nonnegative source scales. Apply the existing convergence theorem at `t²`,
then return to the original scale by continuity of the square root. Neither
the inverse nor the masks are replaced. Consumer: the primitive-limit input
of the density-uniform full-amplitude comparison
(`app:ch_background:prop:bg-normalized`, `bg-Psi`, `bg-jacobian`). -/
theorem tendsto_source_conic_primitives_nonneg
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (normalizedTransportPosition T Q₀ q.1) q.2)
        (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ico (0 : ℝ) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (normalizedTransportPosition T Q₀ σ)
        (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, δ ≤ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q₀ σ) p)) (m : ℕ) :
    let Z := normalizedTransportPosition T Q₀
    let J := fun σ ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) (Z σ)
    Tendsto (fun σ ↦
      cNorm K m (augmentedTransportGradient (Z σ) - augmentedTransportGradient (Z 0)) +
      cNorm Q m (inverseCoordinates (u σ) - inverseCoordinates (u 0)) +
      cNorm K m (J σ - J 0) +
      cNorm K m ((fun p ↦ (J σ p)⁻¹) - (fun p ↦ (J 0 p)⁻¹)))
        (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
  intro Z J
  let d := min e 1 / 2
  have hd : 0 < d := half_pos (lt_min he zero_lt_one)
  have hsquare (t : ℝ) (ht : t ∈ Ioo (-d) d) : t ^ 2 ∈ Ico (0 : ℝ) e := by
    have hde : d ≤ e := (half_le_self (le_min he.le zero_le_one)).trans (min_le_left _ _)
    have hd1 : d ≤ 1 := (half_le_self (le_min he.le zero_le_one)).trans (min_le_right _ _)
    have habs : |t| < d := abs_lt.mpr ht
    have ht2 : t ^ 2 < d ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    exact ⟨sq_nonneg t, ht2.trans_le (by nlinarith)⟩
  have hsmooth : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Z (q.1 ^ 2)) q.2) (Ioo (-d) d ×ˢ W) :=
    hjoint.comp ((contDiffOn_fst.pow 2).prodMk contDiffOn_snd) (fun q hq ↦
      ⟨⟨(neg_neg_of_pos he).trans_le (hsquare q.1 hq.1).1, (hsquare q.1 hq.1).2⟩, hq.2⟩)
  have hlimit := tendsto_conic_inverse_jacobian_sub_cNorm
    (Y := fun t ↦ Z (t ^ 2)) (u := fun t ↦ u (t ^ 2))
    hK hconv hW hKW hQ hΩ hQΩ A (CanonicalConic.adaptedSliceCoordinates T)
    hd hδ hsmooth (fun t ht ↦ hfamily (t ^ 2) (hsquare t ht)) m
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)] at hlimit
  have hsqrt : Tendsto Real.sqrt (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (show 𝓝[≥] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply (hlimit.comp hsqrt).congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  simp only [Function.comp_apply, Real.sq_sqrt hσ, J]

/-- Both divided ODE footpoints converge after the SAME supplied inverse
using only nonnegative-scale inverse geometry. The fixed-reference
composition estimate applies to the literal footpoint extension and the
already proved inverse limit. The original scalar ranges are separately
retained by `source_footpoint_original_domain_regular`; no density or
footpoint convergence is assumed. Consumer: the two label-error terms in
the density-uniform full-amplitude difference
(`app:ch_background:eq:bg-Nsigma`, `bg-full-complex-amplitude`). -/
theorem tendsto_source_conic_footpoints_nonneg
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hend : ∀ side, MapsTo (densityEndpoint side) K (ball 0 R ×ˢ V))
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (normalizedTransportPosition T Q₀ q.1) q.2)
        (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ico (0 : ℝ) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (normalizedTransportPosition T Q₀ σ)
        (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, δ ≤ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q₀ σ) p)) (m : ℕ) (side : Bool) :
    Tendsto (fun σ ↦ cNorm Q m
      ((fun p ↦ sourceDensityFootpointExtension T Y
        (σ, densityEndpoint side (inverseCoordinates (u σ) p))) -
       (fun p ↦ sourceDensityFootpointExtension T Y
        (0, densityEndpoint side (inverseCoordinates (u 0) p)))))
      (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
  let Z := normalizedTransportPosition T Q₀
  let J := fun σ ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) (Z σ)
  have hgeometry := tendsto_source_conic_primitives_nonneg
    T Q₀ hK hconv hW hKW hQ hΩ hQΩ A he hδ hjoint hfamily m
  have huLimit : Tendsto (fun σ ↦ cNorm Q m
      (inverseCoordinates (u σ) - inverseCoordinates (u 0))) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ cNorm_nonneg ..)
      (Eventually.of_forall fun σ ↦ ?_) hgeometry
    have hforward := cNorm_nonneg K m (augmentedTransportGradient (Z σ) - augmentedTransportGradient (Z 0))
    have hJ := cNorm_nonneg K m (J σ - J 0)
    have hJinv := cNorm_nonneg K m ((fun p ↦ (J σ p)⁻¹) - (fun p ↦ (J 0 p)⁻¹))
    change _ ≤ cNorm K m (augmentedTransportGradient (Z σ) - augmentedTransportGradient (Z 0)) +
      cNorm Q m (inverseCoordinates (u σ) - inverseCoordinates (u 0)) +
      cNorm K m (J σ - J 0) + cNorm K m ((fun p ↦ (J σ p)⁻¹) - (fun p ↦ (J 0 p)⁻¹))
    linarith only [hforward, hJ, hJinv]
  let O := densityEndpoint side ⁻¹' (ball (0 : Euclidean n) R ×ˢ V)
  have hO : IsOpen O := (isOpen_ball.prod hV).preimage (densityEndpoint_contDiff side).continuous
  have hKO : K ⊆ O := hend side
  let f := fun σ (p : InputVariables n) ↦ sourceDensityFootpointExtension T Y (σ, densityEndpoint side p)
  let g := fun σ ↦ inverseCoordinates (u σ)
  have hf : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦ f q.1 q.2)
      (Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ O) :=
    (sourceDensityFootpointExtension_contDiffOn T hV hY).comp
      (contDiffOn_fst.prodMk ((densityEndpoint_contDiff side).comp_contDiffOn contDiffOn_snd))
      (fun q hq ↦ ⟨hq.1, hq.2⟩)
  have h0 : (0 : ℝ) ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) := by constructor <;> norm_num
  have hfAt (σ : ℝ) (hσ : σ ∈ Ioo (-(1 / 4) : ℝ) (1 / 4)) (p) (hp : p ∈ K) :
      ContDiffAt ℝ ∞ (f σ) p :=
    (hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hq ↦ ⟨hσ, hq⟩)).contDiffAt
      (hO.mem_nhds (hKO hp))
  have hgAt (σ : ℝ) (hσ : σ ∈ Ico (0 : ℝ) e) (p) (hp : p ∈ Q) :
      ContDiffAt ℝ ∞ (g σ) p :=
    (inverseCoordinates_contDiffOn (hfamily σ hσ).1).contDiffAt (hΩ.mem_nhds (hQΩ hp))
  have hfLimit := (tendsto_cNorm_slice_sub isOpen_Ioo hO hf hK hKO h0 m).mono_left
    (show 𝓝[≥] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  let B := cNorm Q m (g 0) + 1
  have hB : 0 ≤ B := add_nonneg (cNorm_nonneg ..) zero_le_one
  obtain ⟨C, _, hcompare⟩ := exists_cNorm_comp_sub_le_fixed_reference hQ hK (hfAt 0 h0) m hB
  have hg0 : ∀ p ∈ Q, ContDiffAt ℝ ∞ (g 0) p := hgAt 0 ⟨le_rfl, he⟩
  have hg0B : cNorm Q m (g 0) ≤ B := le_add_of_nonneg_right zero_le_one
  change Tendsto (fun σ ↦ cNorm Q m (f σ ∘ g σ - f 0 ∘ g 0)) _ _
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ cNorm_nonneg ..) ?_
    (by simpa only [add_zero, mul_zero] using (hfLimit.add huLimit).const_mul C)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds he),
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds h0),
    huLimit.eventually (gt_mem_nhds zero_lt_one)] with σ hσ0 hσe hσI hsmall
  have hσ : σ ∈ Ico (0 : ℝ) e := ⟨hσ0, hσe⟩
  have hgB : cNorm Q m (g σ) ≤ B := by
    have hh := cNorm_add_le_of_contDiffAt (r := m) hQ
      (fun p hp ↦ ((hgAt σ hσ p hp).sub (hg0 p hp)).of_le (by simp))
      (fun p hp ↦ (hg0 p hp).of_le (by simp))
    simp only [Pi.add_def, sub_add_cancel] at hh
    change cNorm Q m (g σ) ≤ cNorm Q m (g σ - g 0) + cNorm Q m (g 0) at hh
    exact hh.trans (by dsimp only [B]; linarith only [hsmall])
  exact hcompare (f σ) (g σ) (g 0) _ (add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..))
    (hfAt σ hσI) (hgAt σ hσ) hg0 (hfamily σ hσ).2.1 (hfamily 0 ⟨le_rfl, he⟩).2.1
    hgB hg0B (le_add_of_nonneg_right (cNorm_nonneg ..)) (le_add_of_nonneg_left (cNorm_nonneg ..))

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
