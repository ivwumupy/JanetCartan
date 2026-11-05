module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.SourceFootpoint

/-!
# Density-uniform convergence of the same source ODE family

The compact density domain, constants and source threshold precede the
initial density. Both factors in the literal normal density are retained.
The seed smoothness, Cauchy value and label identity are produced by
`exists_retained_seed_matched_primitive_convergence`; its positive-scale
matching is the only input concerning the varying flow. Consumer:
`FamilyInputs`, for `paper.tex`, `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow
open ContinuumRow CanonicalCarrier PositiveReference NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The zero-scale density still evaluates the initial density at TWO ODE
labels. These labels are the smooth limit of the divided seed inverse.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:prop:bg-normalized`. -/
def sourceDensityPairLimit
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3) :
    InputVariables n → ℝ :=
  densityPair v (fun b p ↦ sourceDensityFootpointExtension T Y (0, densityEndpoint b p))

/-- Explicit source-to-zero finite-density comparison for the original wider
fixed-low class. The primitive seed data are exported together by
`exists_finite_same_seed_primitive_inputs`; positive-scale matching is
proved there for the very same seed witnesses. The density domain is chosen
before order and scale, and the threshold is chosen before `v`. No inverse,
amplitude or operator continuity is assumed. The reserve `d₀` is the original
fixed low reserve; only `m + 1 ≤ d₀` is needed. Source:
`app:ch_background:prop:bg-normalized`, `app:ch_background:prop:bg-frame`. -/
theorem exists_source_densityPair_comparison
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {S : Set (Euclidean n × CarrierParameter)} (hS : IsCompact S)
    (hSV : S ⊆ ball 0 R ×ˢ V)
    {K : Set (InputVariables n)} (hK : IsCompact K)
    (hKS : ∀ side, MapsTo (densityEndpoint side) K S) :
    ∃ Rv > (0 : ℝ), ∀ m : ℕ, ∃ A > (0 : ℝ), ∀ ε > (0 : ℝ),
      ∃ s > (0 : ℝ), s ≤ 1 ∧ ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      EqOn (densityFootpoint T Yσ) (densityFootpoint T (sourceTransportFlow Y σ))
        (ball 0 R ×ˢ V) →
      ∀ (d₀ : ℕ), m + 1 ≤ d₀ →
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
      (∀ q ∈ closedBall 0 Rv, ContDiffAt ℝ ∞ v q) →
      cNorm (closedBall 0 Rv) d₀ v ≤ 1 →
      cNorm K m (canonicalDensityPair T v Yσ) ≤ A ∧
      cNorm K m (sourceDensityPairLimit T v Y) ≤ A ∧
      cNorm K m (canonicalDensityPair T v Yσ - sourceDensityPairLimit T v Y) < ε := by
  let f := sourceDensityFootpointExtension T Y
  have hf := sourceDensityFootpointExtension_contDiffOn T hV hY
  have hIS : Icc (0 : ℝ) (1 / 8) ×ˢ S ⊆
      Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ ball 0 R ×ˢ V := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hSV hq.2⟩
  obtain ⟨L, hL⟩ := (isCompact_Icc.prod hS).exists_bound_of_continuousOn
    (hf.continuousOn.mono hIS)
  let Rv := |L| + 1
  have hRv : 0 < Rv := by dsimp [Rv]; positivity
  have hrange (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) (1 / 8)) :
      MapsTo (fun p ↦ f (σ, p)) S (closedBall 0 Rv) := by
    intro p hp
    rw [mem_closedBall, dist_zero_right]
    exact (hL (σ, p) ⟨hσ, hp⟩).trans ((le_abs_self L).trans (by dsimp [Rv]; linarith))
  have hsmooth (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) (1 / 8)) :
      ∀ p ∈ S, ContDiffAt ℝ ∞ (fun p ↦ f (σ, p)) p := by
    intro p hp
    exact (hf.contDiffAt ((isOpen_Ioo.prod (isOpen_ball.prod hV)).mem_nhds
      (hIS ⟨hσ, hp⟩))).comp p (contDiffAt_const.prodMk contDiffAt_id)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 8) := ⟨le_rfl, by norm_num⟩
  refine ⟨Rv, hRv, ?_⟩
  intro m
  let B := cNorm S m (fun p ↦ f (0, p)) + 1
  have hB : 0 ≤ B := add_nonneg (cNorm_nonneg ..) zero_le_one
  obtain ⟨A, hA, hpair⟩ := exists_densityPair_endpoint_sub_bound hK hS
    (isCompact_closedBall (0 : Euclidean (n - 1) × Euclidean 3) Rv)
    (convex_closedBall _ _) hKS m hB
  refine ⟨A, hA, ?_⟩
  intro ε hε
  have htol : 0 < min 1 (ε / A) := lt_min zero_lt_one (div_pos hε hA)
  obtain ⟨e, he, hsmall⟩ := Metric.mem_nhds_iff.mp
    ((tendsto_sourceDensityFootpointExtension_sub_cNorm T hV hY hS hSV m).eventually
      (gt_mem_nhds htol))
  let s := min (e / 2) (1 / 8)
  have hs : 0 < s := lt_min (half_pos he) (by norm_num)
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (by norm_num)
  refine ⟨s, hs, hs1, ?_⟩
  intro σ hσ Yσ hmatch d₀ horder v hv hvm
  have hσI : σ ∈ Icc (0 : ℝ) (1 / 8) := ⟨hσ.1.le, hσ.2.trans (min_le_right _ _)⟩
  let d := cNorm S m ((fun p ↦ f (σ, p)) - (fun p ↦ f (0, p)))
  have hd : 0 ≤ d := cNorm_nonneg ..
  have hdiff : d < min 1 (ε / A) := by
    apply hsmall
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
    exact (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self he)
  have hnorm : cNorm S m (fun p ↦ f (σ, p)) ≤ B := by
    have hh := cNorm_add_le_of_contDiffAt (r := m) hS
      (fun p hp ↦ ((hsmooth σ hσI p hp).sub (hsmooth 0 h0 p hp)).of_le (by simp))
      (fun p hp ↦ (hsmooth 0 h0 p hp).of_le (by simp))
    simp only [Pi.add_def, sub_add_cancel] at hh
    exact hh.trans (by change d + _ ≤ _; dsimp [B]; linarith [hdiff.trans_le (min_le_left 1 (ε / A))])
  have hnorm₀ : cNorm S m (fun p ↦ f (0, p)) ≤ B := by dsimp [B]; linarith
  have hp := hpair v (fun p ↦ f (σ, p)) (fun p ↦ f (0, p)) d hd hv
    ((cNorm_mono_order horder).trans hvm) (hsmooth σ hσI) (hsmooth 0 h0)
    (hrange σ hσI) (hrange 0 h0) hnorm hnorm₀ le_rfl
  have heq : EqOn (densityFootpoint T Yσ) (fun p ↦ f (σ, p)) (ball 0 R ×ˢ V) := by
    intro p hpp
    rw [hmatch hpp]
    apply (sourceDensityFootpointExtension_eq T hR hY hzero hparam (ne_of_gt hσ.1) ?_).symm
    refine ⟨?_, hpp.2⟩
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hσ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hσ.2.trans hs1)).trans_lt
      (by simpa only [mem_ball, dist_zero_right] using hpp.1)
  have hevent (p) (hpp : p ∈ K) : canonicalDensityPair T v Yσ =ᶠ[𝓝 p]
      densityPair v (fun b p ↦ f (σ, densityEndpoint b p)) := by
    have hW : IsOpen (ball (0 : Euclidean n) R ×ˢ V) := isOpen_ball.prod hV
    have hleft := (hW.preimage (densityEndpoint_contDiff false).continuous).mem_nhds (hSV (hKS false hpp))
    have hright := (hW.preimage (densityEndpoint_contDiff true).continuous).mem_nhds (hSV (hKS true hpp))
    filter_upwards [hleft, hright] with q hq hq'
    change (1 + v (densityFootpoint T Yσ (densityEndpoint false q))) *
      (1 + v (densityFootpoint T Yσ (densityEndpoint true q))) = _
    rw [heq hq, heq hq']
    rfl
  have hn := GeometricProfile.cNorm_eq_of_eventuallyEq (r := m) hevent
  have hnd := GeometricProfile.cNorm_eq_of_eventuallyEq (r := m)
    (fun p hpp ↦ (hevent p hpp).sub (Filter.EventuallyEq.rfl
      (f := sourceDensityPairLimit T v Y)))
  refine ⟨hn.trans_le hp.2.1, hp.2.2.1, hnd.trans_le hp.2.2.2 |>.trans_lt ?_⟩
  exact (mul_lt_mul_of_pos_left (hdiff.trans_le (min_le_right _ _)) hA).trans_eq
    (mul_div_cancel₀ ε (ne_of_gt hA))

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
