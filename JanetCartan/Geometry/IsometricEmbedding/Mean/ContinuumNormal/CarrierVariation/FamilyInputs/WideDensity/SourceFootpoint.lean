module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.Canonical
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CompactSlices
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.SmoothPhase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Transport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.MatchedCoefficients

/-!
# Smooth extension of the actual divided ODE footpoint

The source ODE inverse has a divided physical component and unchanged carrier
labels. Its extension through zero is obtained componentwise from the integral
of the seed differential. This is the ODE density label, not the Hamilton
canonical footpoint. Consumer: the wider density-class convergence in
`FamilyInputs`, for `app:ch_background:eq:bg-Nsigma` and
`app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow
open ContinuumRow CanonicalCarrier PositiveReference NormalizedBackground.SourceGeometry

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Literal physical dilation of the ODE density footpoint, retaining the
inverse scale on its spatial label and leaving carrier labels untouched.
Source: `app:ch_background:eq:bg-Nsigma`. -/
theorem densityFootpoint_sourceTransportFlow
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (σ : ℝ) (p : Euclidean n × CarrierParameter) :
    densityFootpoint T (sourceTransportFlow Y σ) p =
      (σ⁻¹ • (densityFootpoint T Y (σ • p.1, p.2)).1,
        (densityFootpoint T Y (σ • p.1, p.2)).2) := by
  simp [densityFootpoint, densityCoordinates, sourceTransportFlow, transportLabelDilation,
    transportCoordinateDilation, FlowAmplitude.coordinates_apply, map_smul]

/-- The integral extension of the SAME ODE inverse. Only the spatial label
is divided; the original carrier label and initial density measure remain
fixed. Source: `app:ch_background:eq:bg-Nsigma`. -/
def sourceDensityFootpointExtension
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (q : ℝ × (Euclidean n × CarrierParameter)) : Euclidean (n - 1) × Euclidean 3 :=
  (WithLp.toLp 2 (fun j ↦ sourcePhaseExtension
    (fun p ↦ (densityFootpoint T Y p).1 j) q), parameter q.2.2)

/-- Smoothness through scale zero comes from the seed inverse and its
integral extension. The seed inverse's actual constructor supplies `hY`;
there is no hypothesis about a varying inverse family. Source:
`app:ch_background:prop:bg-normalized`. -/
theorem sourceDensityFootpointExtension_contDiffOn
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V)) :
    ContDiffOn ℝ ∞ (sourceDensityFootpointExtension T Y)
      (Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ ball 0 R ×ˢ V) := by
  apply ContDiffOn.prodMk _ (parameter.contDiff.comp_contDiffOn contDiffOn_snd.snd)
  apply (contDiffOn_piLp 2).mpr
  intro j
  apply contDiffOn_sourcePhaseExtension isOpen_ball hV
    (isOpen_Ioo.prod (isOpen_ball.prod hV)) isOpen_Ioo
    (show Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 from fun _ ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    ((contDiffOn_piLp 2).mp hY.fst j)
  intro q hq t ht
  refine ⟨?_, hq.2.2⟩
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
  have hs : |q.1| ≤ 1 / 4 := abs_le.mpr ⟨hq.1.1.le, hq.1.2.le⟩
  have htt : |t| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2.le⟩
  have hprod : |t * q.1| ≤ 1 := by
    rw [abs_mul]
    have hh := mul_le_mul htt hs (abs_nonneg q.1) (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  exact (mul_le_of_le_one_left (norm_nonneg _) hprod).trans_lt
    (by simpa only [mem_ball, dist_zero_right] using hq.2.1)

/-- At nonzero scale the integral extension equals the actual divided ODE
inverse. The Cauchy value is a consequence of the two seed flow identities,
and the unchanged-parameter identity is exported by the seed constructor.
Source: `app:ch_background:eq:bg-Nsigma`. -/
theorem sourceDensityFootpointExtension_eq
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter}
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {σ : ℝ} (hσ : σ ≠ 0) {p : Euclidean n × CarrierParameter}
    (hp : (σ • p.1, p.2) ∈ ball (0 : Euclidean n) R ×ˢ V) :
    sourceDensityFootpointExtension T Y (σ, p) = densityFootpoint T (sourceTransportFlow Y σ) p := by
  rw [densityFootpoint_sourceTransportFlow]
  apply Prod.ext
  · ext j
    have hs := ((contDiffOn_piLp 2).mp hY.fst j).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ ⟨hx, hp.2⟩)
    have he := sourcePhase_eq_extension
      (S := fun q : Euclidean n × CarrierParameter ↦ (densityFootpoint T Y q).1 j)
      isOpen_ball (convex_ball (0 : Euclidean n) R)
      (hs.of_le (by simp)) (by simpa using congrArg (fun x : Euclidean (n - 1) ↦ x j) (hzero p.2 hp.2))
      (mem_ball_self hR) hp.1 hσ
    simpa only [sourceDensityFootpointExtension, WithLp.ofLp_toLp, PiLp.smul_apply,
      smul_eq_mul, sourcePhase] using he.symm
  · exact (hparam _ hp).symm

/-- Finite primitive `cNorm` convergence of the normalized ODE footpoint on
the prescribed compact field domain. The extension uses the actual seed;
it is independent of the initial density. Source:
`app:ch_background:prop:bg-normalized`. -/
theorem tendsto_sourceDensityFootpointExtension_sub_cNorm
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    {S : Set (Euclidean n × CarrierParameter)} (hS : IsCompact S)
    (hSV : S ⊆ ball 0 R ×ˢ V) (m : ℕ) :
    Tendsto (fun σ ↦ cNorm S m
      ((fun p ↦ sourceDensityFootpointExtension T Y (σ, p)) -
        (fun p ↦ sourceDensityFootpointExtension T Y (0, p)))) (𝓝 0) (𝓝 0) :=
  tendsto_cNorm_slice_sub isOpen_Ioo (isOpen_ball.prod hV)
    (sourceDensityFootpointExtension_contDiffOn T hV hY) hS hSV
    (by constructor <;> norm_num) m

/-- The seed inverse identities determine its physical-zero Cauchy value,
so the divided extension is the actual source family. Positive-scale
matching is exactly the output of `MatchedSeedCoefficients`; no inverse
continuity is a hypothesis. This explicit finite-norm estimate is used by
the original density-class comparison. Source:
`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`. -/
theorem exists_matched_sourceDensityFootpoint_sub_tolerance
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {S : Set (Euclidean n × CarrierParameter)} (hS : IsCompact S)
    (hSV : S ⊆ ball 0 R ×ˢ V) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s > (0 : ℝ), s ≤ 1 ∧ ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      EqOn (densityFootpoint T Yσ) (densityFootpoint T (sourceTransportFlow Y σ))
        (ball 0 R ×ˢ V) →
      cNorm S m (densityFootpoint T Yσ -
        (fun p ↦ sourceDensityFootpointExtension T Y (0, p))) < ε := by
  obtain ⟨e, he, hsmall⟩ := Metric.mem_nhds_iff.mp
    ((tendsto_sourceDensityFootpointExtension_sub_cNorm T hV hY hS hSV m).eventually
      (gt_mem_nhds hε))
  refine ⟨min (e / 2) 1, lt_min (half_pos he) zero_lt_one, min_le_right _ _, ?_⟩
  intro σ hσ Yσ hmatch
  have hσ1 : σ ≤ 1 := hσ.2.trans (min_le_right _ _)
  have heq : EqOn (densityFootpoint T Yσ)
      (fun p ↦ sourceDensityFootpointExtension T Y (σ, p)) (ball 0 R ×ˢ V) := by
    intro p hp
    rw [hmatch hp]
    apply (sourceDensityFootpointExtension_eq T hR hY hzero hparam (ne_of_gt hσ.1) ?_).symm
    refine ⟨?_, hp.2⟩
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hσ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hσ1).trans_lt
      (by simpa only [mem_ball, dist_zero_right] using hp.1)
  have hnorm : cNorm S m (densityFootpoint T Yσ -
        (fun p ↦ sourceDensityFootpointExtension T Y (0, p))) =
      cNorm S m ((fun p ↦ sourceDensityFootpointExtension T Y (σ, p)) -
        (fun p ↦ sourceDensityFootpointExtension T Y (0, p))) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro p hp
    filter_upwards [(isOpen_ball.prod hV).mem_nhds (hSV hp)] with q hq
    exact congrArg (fun z ↦ z - sourceDensityFootpointExtension T Y (0, q)) (heq hq)
  rw [hnorm]
  apply hsmall
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
  exact (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self he)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
