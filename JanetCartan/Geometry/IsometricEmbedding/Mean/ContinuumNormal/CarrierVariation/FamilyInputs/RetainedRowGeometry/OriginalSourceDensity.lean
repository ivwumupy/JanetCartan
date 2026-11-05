module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.SourceComparison

/-!
# Source density comparison on the original retained scalar ball

The actual source ODE labels have the original `L / 16` buffer. Continuity
through scale zero keeps the limiting labels in its closure, hence inside
the original `L / 8` density domain. The density estimate is obtained from
the existing two-endpoint calculus, with constants chosen before the density.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow
open ContinuumRow CanonicalCarrier PositiveReference NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol WideDensity

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The zero-scale ODE labels stay in the closure of the ORIGINAL scalar
buffer. The positive-scale range is supplied by `exists_original_label_region`
for the retained charts, transferred by `RetainedLeading.retained_charts_source_dilation`.
Only continuity of the explicitly constructed integral extension is used.
Consumer: `exists_retained_source_densityPair_comparison` and the source
weighted full amplitude (`app:ch_background:eq:bg-Nsigma`,
`app:ch_background:prop:bg-normalized`). -/
theorem sourceDensityFootpointExtension_zero_mem_original_closedBall
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {S : Set (Euclidean n × CarrierParameter)} (hSV : S ⊆ ball 0 R ×ˢ V)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) S
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16))) :
    MapsTo (fun p ↦ sourceDensityFootpointExtension T Y (0, p)) S
      (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 16)) := by
  intro p hp
  have hf := sourceDensityFootpointExtension_contDiffOn T hV hY
  have hcont : ContinuousAt (fun σ ↦ sourceDensityFootpointExtension T Y (σ, p)) 0 :=
    (hf.continuousOn.continuousAt
      ((isOpen_Ioo.prod (isOpen_ball.prod hV)).mem_nhds
        (show ((0 : ℝ), p) ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ ball 0 R ×ˢ V from
          ⟨⟨by norm_num, by norm_num⟩, hSV hp⟩))).comp
        (f := fun σ : ℝ ↦ (σ, p)) (continuousAt_id.prodMk continuousAt_const)
  apply isClosed_closedBall.mem_of_tendsto
    (hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  filter_upwards [Ioo_mem_nhdsGT (lt_min hs₀ zero_lt_one)] with σ hσ
  have hscaled : (σ • p.1, p.2) ∈ ball (0 : Euclidean n) R ×ˢ V := by
    refine ⟨?_, (hSV hp).2⟩
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hσ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hσ.2.le.trans (min_le_right _ _))).trans_lt
        (by simpa only [mem_ball, dist_zero_right] using (hSV hp).1)
  rw [sourceDensityFootpointExtension_eq T hR hY hzero hparam (ne_of_gt hσ.1) hscaled]
  exact ball_subset_closedBall (hsource σ ⟨hσ.1, hσ.2.le.trans (min_le_left _ _)⟩ hp)

/-- Uniform comparison of BOTH density factors on the ORIGINAL retained
scalar domain. No auxiliary density ball is selected. The positive-scale
label range is the output of `exists_original_label_region` on the same
charts; the source matching is proved by
`exists_retained_chart_source_primitive_convergence_on_outputCylinder`.
The fixed-low reserve and constants precede the varying density. This
instantiates `WideDensity.exists_densityPair_endpoint_sub_bound` for the
retained source, without assuming continuity of a weighted amplitude or
normal operator (`app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_retained_source_densityPair_comparison
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {S : Set (Euclidean n × CarrierParameter)} (hS : IsCompact S)
    (hSV : S ⊆ ball 0 R ×ˢ V)
    {K : Set (InputVariables n)} (hK : IsCompact K)
    (hKS : ∀ side, MapsTo (densityEndpoint side) K S)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) S
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16))) :
    ∀ m : ℕ, ∃ A > (0 : ℝ), ∀ ε > (0 : ℝ),
      ∃ s > (0 : ℝ), s ≤ s₀ ∧ s ≤ 1 ∧ ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      EqOn (densityFootpoint T Yσ) (densityFootpoint T (sourceTransportFlow Y σ))
        (ball 0 R ×ˢ V) →
      ∀ (d₀ : ℕ), m + 1 ≤ d₀ →
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v q) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) d₀ v ≤ 1 →
      cNorm K m (canonicalDensityPair T v Yσ) ≤ A ∧
      cNorm K m (sourceDensityPairLimit T v Y) ≤ A ∧
      cNorm K m (canonicalDensityPair T v Yσ - sourceDensityPairLimit T v Y) < ε := by
  let f := sourceDensityFootpointExtension T Y
  have hf := sourceDensityFootpointExtension_contDiffOn T hV hY
  have hIS : Icc (0 : ℝ) (1 / 8) ×ˢ S ⊆
      Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ ball 0 R ×ˢ V := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hSV hq.2⟩
  have hsmooth (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) (1 / 8)) :
      ∀ p ∈ S, ContDiffAt ℝ ∞ (fun p ↦ f (σ, p)) p := by
    intro p hp
    exact (hf.contDiffAt ((isOpen_Ioo.prod (isOpen_ball.prod hV)).mem_nhds
      (hIS ⟨hσ, hp⟩))).comp p (contDiffAt_const.prodMk contDiffAt_id)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 8) := ⟨le_rfl, by norm_num⟩
  have hrange₀ : MapsTo (fun p ↦ f (0, p)) S
      (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) :=
    (sourceDensityFootpointExtension_zero_mem_original_closedBall T hR hV hY hzero hparam
      hSV hs₀ hsource).mono_right (closedBall_subset_closedBall (by linarith))
  intro m
  let B := cNorm S m (fun p ↦ f (0, p)) + 1
  have hB : 0 ≤ B := add_nonneg (cNorm_nonneg ..) zero_le_one
  obtain ⟨A, hA, hpair⟩ := exists_densityPair_endpoint_sub_bound hK hS
    (isCompact_closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
    (convex_closedBall _ _) hKS m hB
  refine ⟨A, hA, ?_⟩
  intro ε hε
  have htol : 0 < min 1 (ε / A) := lt_min zero_lt_one (div_pos hε hA)
  obtain ⟨e, he, hsmall⟩ := Metric.mem_nhds_iff.mp
    ((tendsto_sourceDensityFootpointExtension_sub_cNorm T hV hY hS hSV m).eventually
      (gt_mem_nhds htol))
  let s := min s₀ (min (e / 2) (1 / 8))
  have hs : 0 < s := lt_min hs₀ (lt_min (half_pos he) (by norm_num))
  have hs₀' : s ≤ s₀ := min_le_left _ _
  have hs8 : s ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hs1 : s ≤ 1 := hs8.trans (by norm_num)
  refine ⟨s, hs, hs₀', hs1, ?_⟩
  intro σ hσ Yσ hmatch d₀ horder v hv hvm
  have hσI : σ ∈ Icc (0 : ℝ) (1 / 8) := ⟨hσ.1.le, hσ.2.trans hs8⟩
  have heq : EqOn (densityFootpoint T Yσ) (fun p ↦ f (σ, p)) (ball 0 R ×ˢ V) := by
    intro p hpp
    rw [hmatch hpp]
    apply (sourceDensityFootpointExtension_eq T hR hY hzero hparam (ne_of_gt hσ.1) ?_).symm
    refine ⟨?_, hpp.2⟩
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hσ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hσ.2.trans hs1)).trans_lt
      (by simpa only [mem_ball, dist_zero_right] using hpp.1)
  have hrange : MapsTo (fun p ↦ f (σ, p)) S
      (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) := by
    intro p hp
    rw [← heq (hSV hp), hmatch (hSV hp)]
    exact closedBall_subset_closedBall (by linarith : L / 16 ≤ L / 8)
      (ball_subset_closedBall (hsource σ ⟨hσ.1, hσ.2.trans hs₀'⟩ hp))
  let d := cNorm S m ((fun p ↦ f (σ, p)) - (fun p ↦ f (0, p)))
  have hd : 0 ≤ d := cNorm_nonneg ..
  have hdiff : d < min 1 (ε / A) := by
    apply hsmall
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
    exact (hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (half_lt_self he)
  have hnorm : cNorm S m (fun p ↦ f (σ, p)) ≤ B := by
    have hh := cNorm_add_le_of_contDiffAt (r := m) hS
      (fun p hp ↦ ((hsmooth σ hσI p hp).sub (hsmooth 0 h0 p hp)).of_le (by simp))
      (fun p hp ↦ (hsmooth 0 h0 p hp).of_le (by simp))
    simp only [Pi.add_def, sub_add_cancel] at hh
    exact hh.trans (by change d + _ ≤ _; dsimp [B]; linarith [hdiff.trans_le (min_le_left 1 (ε / A))])
  have hnorm₀ : cNorm S m (fun p ↦ f (0, p)) ≤ B := by dsimp [B]; linarith
  have hp := hpair v (fun p ↦ f (σ, p)) (fun p ↦ f (0, p)) d hd hv
    ((cNorm_mono_order horder).trans hvm) (hsmooth σ hσI) (hsmooth 0 h0)
    hrange hrange₀ hnorm hnorm₀ le_rfl
  have heqd : ∀ p ∈ K, canonicalDensityPair T v Yσ =ᶠ[𝓝 p]
      densityPair v (fun b ↦ (fun p ↦ f (σ, p)) ∘ densityEndpoint b) := by
    intro p hp
    have hmem (b : Bool) : ∀ᶠ q in 𝓝 p, densityEndpoint b q ∈ ball (0 : Euclidean n) R ×ˢ V :=
      (densityEndpoint_contDiff b).continuous.continuousAt.preimage_mem_nhds
        ((isOpen_ball.prod hV).mem_nhds (hSV (hKS b hp)))
    filter_upwards [hmem false, hmem true] with q hq₀ hq₁
    simp only [canonicalDensityPair, densityPair, Function.comp_apply, heq hq₀, heq hq₁]
  have heqnorm := GeometricProfile.cNorm_eq_of_eventuallyEq (r := m) heqd
  have heqsub := GeometricProfile.cNorm_eq_of_eventuallyEq (r := m)
    (fun p hp ↦ (heqd p hp).sub (Filter.EventuallyEq.rfl (f := sourceDensityPairLimit T v Y)))
  rw [heqnorm, heqsub]
  exact ⟨hp.2.1, hp.2.2.1, hp.2.2.2.trans_lt
    ((mul_lt_mul_of_pos_left (hdiff.trans_le (min_le_right _ _)) hA).trans_eq
      (mul_div_cancel₀ ε (ne_of_gt hA)))⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
