module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.ConicComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalSourceDensity

/-!
# Retained source densities after conic inversion on the original scalar domain

Keep the supplied conic charts, input sets and target sets unchanged. The
retained forward bound gives the original label range at positive scales;
the explicit integral extension retains that range at zero. The existing
conic comparison and two-factor calculus then apply on the original scalar
ball, with constants preceding the varying density.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow
open ContinuumRow CanonicalCarrier PositiveReference NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol AmplitudeDifference.PrimitiveDensity WideDensity

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Both actual divided ODE labels remain in the ORIGINAL scalar ball after
substitution of the supplied conic inverse. The inverse difference comes from
the existing conic equations and half-gap. `exists_original_source_density_region`
produces the source label range on each contained coefficient product;
`SourceCharts` produces the through-zero inverse geometry. All domains and
inverses remain supplied witnesses. Consumer: the source weighted matrix
comparison on retained domains (`app:ch_background:eq:bg-Nsigma`,
`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_source_conic_footpoint_primitives
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    {Z : ℝ → Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hend : ∀ side, MapsTo (densityEndpoint side) K (ball 0 R ×ˢ V))
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) {e : ℝ} (he : 0 < e)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Z q.1) q.2) (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-e) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (Z σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Z σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)) :
    let g := fun t side p ↦ sourceDensityFootpointExtension T Y
      (t, densityEndpoint side (inverseCoordinates (u t) p))
    (∀ m side, Tendsto (fun t ↦ cNorm Q m (g t side - g 0 side)) (𝓝 0) (𝓝 0)) ∧
      ∃ s > (0 : ℝ), s ≤ 1 ∧ ∀ σ ∈ Icc (0 : ℝ) s, ∀ side,
        (∀ p ∈ Q, ContDiffAt ℝ ∞ (g σ side) p) ∧
        MapsTo (g σ side) Q (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) := by
  obtain ⟨_Rv, _hRv, hlim, sg, hsg, hsg1, hregular⟩ :=
    exists_source_conic_footpoint_primitives T hV hY hK hconv hW hKW hQ hΩ hQΩ
      hend A he hjoint hfamily
  have hzeroRange := sourceDensityFootpointExtension_zero_mem_original_closedBall T
    hR hV hY hzero hparam (S := ball 0 R ×ˢ V) Subset.rfl hs₀ hsource
  let s := min sg (min s₀ (e / 2))
  have hs : 0 < s := lt_min hsg (lt_min hs₀ (half_pos he))
  have hs1 : s ≤ 1 := (min_le_left _ _).trans hsg1
  refine ⟨hlim, s, hs, hs1, ?_⟩
  intro σ hσ side
  have hσg : σ ∈ Icc (0 : ℝ) sg := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hσe : σ ∈ Ioo (-e) e := ⟨by linarith [hσ.1],
    (hσ.2.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (half_lt_self he)⟩
  refine ⟨(hregular σ hσg side).1, ?_⟩
  intro p hp
  have harg := hend side ((hfamily σ hσe).2.1 hp)
  apply closedBall_subset_closedBall (by linarith : L / 16 ≤ L / 8)
  change sourceDensityFootpointExtension T Y
    (σ, densityEndpoint side (inverseCoordinates (u σ) p)) ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 16)
  by_cases hσ0 : σ = 0
  · subst σ
    exact hzeroRange harg
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ.1 (Ne.symm hσ0)
    have hscaled : (σ • (densityEndpoint side (inverseCoordinates (u σ) p)).1,
        (densityEndpoint side (inverseCoordinates (u σ) p)).2) ∈ ball (0 : Euclidean n) R ×ˢ V := by
      refine ⟨?_, harg.2⟩
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hσpos]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hσ.2.trans hs1)).trans_lt
        (by simpa only [mem_ball, dist_zero_right] using harg.1)
    rw [sourceDensityFootpointExtension_eq T hR hY hzero hparam hσ0 hscaled]
    exact ball_subset_closedBall (hsource σ
      ⟨hσpos, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ harg)

/-- Uniform source comparison of the two density factors AFTER the same
conic inverse, using only the original fixed-low density norm on `L/8`.
This instantiates the existing density calculus with the preceding original
range theorem; no auxiliary scalar domain or density extension is assumed.
The supplied conic geometry is not changed. Consumer: the retained weighted
matrix comparison (`app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_retained_source_conic_densityPair_comparison
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    {Z : ℝ → Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hend : ∀ side, MapsTo (densityEndpoint side) K (ball 0 R ×ˢ V))
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) {e : ℝ} (he : 0 < e)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Z q.1) q.2) (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-e) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (Z σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Z σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)) :
    ∀ m : ℕ, ∃ C > (0 : ℝ), ∀ ε > (0 : ℝ),
      ∃ s > (0 : ℝ), s ≤ 1 ∧ ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ (d₀ : ℕ), m + 1 ≤ d₀ →
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v q) → cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) d₀ v ≤ 1 →
      let g := fun t side p ↦ sourceDensityFootpointExtension T Y
        (t, densityEndpoint side (inverseCoordinates (u t) p))
      cNorm Q m (densityPair v (g σ)) ≤ C ∧
      cNorm Q m (sourceDensityPairLimit T v Y ∘ inverseCoordinates (u 0)) ≤ C ∧
      cNorm Q m (densityPair v (g σ) -
        sourceDensityPairLimit T v Y ∘ inverseCoordinates (u 0)) < ε := by
  obtain ⟨hlim, sreg, hsreg, hsreg1, hregular⟩ :=
    exists_retained_source_conic_footpoint_primitives T hR hV hY hzero hparam hL hs₀ hsource hK hconv hW hKW hQ hΩ hQΩ
      hend A he hjoint hfamily
  let g := fun t side p ↦ sourceDensityFootpointExtension T Y
    (t, densityEndpoint side (inverseCoordinates (u t) p))
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) sreg := ⟨le_rfl, hsreg.le⟩
  intro m
  let M := cNorm Q m (g 0 false) + cNorm Q m (g 0 true) + 1
  have hM : 0 ≤ M := add_nonneg (add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..)) zero_le_one
  have hnorm₀ (b) : cNorm Q m (g 0 b) + 1 ≤ M := by
    cases b <;> dsimp [M] <;> linarith [cNorm_nonneg Q m (g 0 false), cNorm_nonneg Q m (g 0 true)]
  obtain ⟨C, hC, hpair⟩ := exists_densityPair_sub_bound hQ
    (isCompact_closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (convex_closedBall _ _) m hM
  refine ⟨C, hC, ?_⟩
  intro ε hε
  have htol : 0 < min 1 (ε / C) := lt_min zero_lt_one (div_pos hε hC)
  have hsmall := (hlim m false).add (hlim m true)
  obtain ⟨a, ha, hasmall⟩ := Metric.mem_nhds_iff.mp
    (hsmall.eventually (gt_mem_nhds (show (0 : ℝ) + 0 < min 1 (ε / C) by simpa only [add_zero] using htol)))
  let s := min (a / 2) sreg
  have hs : 0 < s := lt_min (half_pos ha) hsreg
  refine ⟨s, hs, (min_le_right _ _).trans hsreg1, ?_⟩
  intro σ hσ d₀ horder v hv hvm
  have hσs : σ ∈ Icc (0 : ℝ) sreg := ⟨hσ.1.le, hσ.2.trans (min_le_right _ _)⟩
  let d := cNorm Q m (g σ false - g 0 false) + cNorm Q m (g σ true - g 0 true)
  have hd : 0 ≤ d := add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..)
  have hdiff : d < min 1 (ε / C) := by
    apply hasmall
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
    exact (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self ha)
  have hbd (b) : cNorm Q m (g σ b - g 0 b) ≤ d := by
    cases b <;> dsimp [d] <;> linarith [cNorm_nonneg Q m (g σ false - g 0 false),
      cNorm_nonneg Q m (g σ true - g 0 true)]
  have hnorm (b) : cNorm Q m (g σ b) ≤ M := by
    have hh := cNorm_add_le_of_contDiffAt (r := m) hQ
      (fun p hp ↦ (((hregular σ hσs b).1 p hp).sub ((hregular 0 hzero b).1 p hp)).of_le (by simp))
      (fun p hp ↦ ((hregular 0 hzero b).1 p hp).of_le (by simp))
    simp only [Pi.add_def, sub_add_cancel] at hh
    change cNorm Q m (g σ b) ≤ cNorm Q m (g σ b - g 0 b) + cNorm Q m (g 0 b) at hh
    exact hh.trans (by linarith only [hbd b, hnorm₀ b, hdiff.trans_le (min_le_left _ _)])
  have hp := hpair v (g σ) (g 0) d hd hv ((cNorm_mono_order horder).trans hvm)
    (fun b ↦ (hregular σ hσs b).1) (fun b ↦ (hregular 0 hzero b).1)
    (fun b ↦ (hregular σ hσs b).2)
    (fun b ↦ (hregular 0 hzero b).2)
    hnorm (fun b ↦ (le_add_of_nonneg_right zero_le_one).trans (hnorm₀ b)) hbd
  refine ⟨hp.2.1, hp.2.2.1, hp.2.2.2.trans_lt ?_⟩
  exact (mul_lt_mul_of_pos_left (hdiff.trans_le (min_le_right _ _)) hC).trans_eq
    (mul_div_cancel₀ ε (ne_of_gt hC))

/-- Identify the comparison with the literal retained positive ODE inverse,
including both density factors AFTER conic substitution. The matching is
produced by `RetainedLeading.retained_charts_source_dilation` on the same
seed charts; it does not identify the ODE footpoint with Hamilton transport.
The original `L/8` density domain is unchanged and constants precede the
varying density (`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_actual_retained_source_conic_densityPair_comparison
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    {Z : ℝ → Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hend : ∀ side, MapsTo (densityEndpoint side) K (ball 0 R ×ˢ V))
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) {e : ℝ} (he : 0 < e)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Z q.1) q.2) (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-e) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (Z σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Z σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)) :
    ∀ m : ℕ, ∃ C > (0 : ℝ), ∀ ε > (0 : ℝ),
      ∃ s > (0 : ℝ), s ≤ 1 ∧ ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      EqOn (densityFootpoint T Yσ) (densityFootpoint T (sourceTransportFlow Y σ))
        (ball 0 R ×ˢ V) →
      ∀ (d₀ : ℕ), m + 1 ≤ d₀ →
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v q) → cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) d₀ v ≤ 1 →
      cNorm Q m (canonicalDensityPair T v Yσ ∘ inverseCoordinates (u σ)) ≤ C ∧
      cNorm Q m (sourceDensityPairLimit T v Y ∘ inverseCoordinates (u 0)) ≤ C ∧
      cNorm Q m (canonicalDensityPair T v Yσ ∘ inverseCoordinates (u σ) -
        sourceDensityPairLimit T v Y ∘ inverseCoordinates (u 0)) < ε := by
  have hcompare := exists_retained_source_conic_densityPair_comparison T hR hV hY
    hzero hparam hL hs₀ hsource
    hK hconv hW hKW hQ hΩ hQΩ hend A he hjoint hfamily
  intro m
  obtain ⟨C, hC, htol⟩ := hcompare m
  refine ⟨C, hC, ?_⟩
  intro ε hε
  obtain ⟨s₀, hs₀, hs₀1, hs₀bound⟩ := htol ε hε
  refine ⟨min s₀ (e / 2), lt_min hs₀ (half_pos he), (min_le_left _ _).trans hs₀1, ?_⟩
  intro σ hσ Yσ hmatch d₀ horder v hv hvm
  have hσs : σ ∈ Ioc (0 : ℝ) s₀ := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hσ1 : σ ≤ 1 := hσs.2.trans hs₀1
  have hσe : σ ∈ Ioo (-e) e := ⟨by linarith [hσ.1],
    (hσ.2.trans (min_le_right _ _)).trans_lt (half_lt_self he)⟩
  have hp := hs₀bound σ hσs d₀ horder v hv hvm
  let O := {p : InputVariables n | ∀ b, densityEndpoint b p ∈ ball (0 : Euclidean n) R ×ˢ V}
  have hO : IsOpen O := by
    have hh : O = ⋂ b : Bool, densityEndpoint b ⁻¹' (ball (0 : Euclidean n) R ×ˢ V) := by
      ext p; simp only [O, mem_ofPred_eq, mem_iInter, mem_preimage]
    rw [hh]
    exact isOpen_iInter_of_finite fun b ↦
      (isOpen_ball.prod hV).preimage (densityEndpoint_contDiff b).continuous
  have heq (p : Euclidean n × CarrierParameter) (hpp : p ∈ ball (0 : Euclidean n) R ×ˢ V) :
      densityFootpoint T Yσ p = sourceDensityFootpointExtension T Y (σ, p) := by
    rw [hmatch hpp]
    apply (sourceDensityFootpointExtension_eq T hR hY hzero hparam hσ.1.ne' ?_).symm
    refine ⟨?_, hpp.2⟩
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hσ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hσ1).trans_lt
      (by simpa only [mem_ball, dist_zero_right] using hpp.1)
  have hevent (p) (hpp : p ∈ Q) :
      canonicalDensityPair T v Yσ ∘ inverseCoordinates (u σ) =ᶠ[𝓝 p]
        densityPair v (fun b q ↦ sourceDensityFootpointExtension T Y
          (σ, densityEndpoint b (inverseCoordinates (u σ) q))) := by
    have hu := (inverseCoordinates_contDiffOn (hfamily σ hσe).1).contDiffAt
      (hΩ.mem_nhds (hQΩ hpp))
    have hm : inverseCoordinates (u σ) p ∈ O := fun b ↦ hend b ((hfamily σ hσe).2.1 hpp)
    filter_upwards [hu.continuousAt.eventually (hO.mem_nhds hm)] with q hq
    change (1 + v (densityFootpoint T Yσ (densityEndpoint false (inverseCoordinates (u σ) q)))) *
      (1 + v (densityFootpoint T Yσ (densityEndpoint true (inverseCoordinates (u σ) q)))) = _
    rw [heq _ (hq false), heq _ (hq true)]
    rfl
  have hn := GeometricProfile.cNorm_eq_of_eventuallyEq hevent m
  have hd := GeometricProfile.cNorm_eq_of_eventuallyEq
    (fun p hpp ↦ (hevent p hpp).sub (Filter.EventuallyEq.rfl
      (f := sourceDensityPairLimit T v Y ∘ inverseCoordinates (u 0)))) m
  exact ⟨hn.trans_le hp.1, hp.2.1, hd.trans_lt hp.2.2⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
