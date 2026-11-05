module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.NormalizedCarrierBaseline.DensityControls
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.SourceFootpoint

/-!
# The divided ODE footpoint in the original low baseline

The footpoint's integral extension supplies a constant before source scale.
The original initial label is not dilated inside the density. This is the
footpoint input of `exists_original_density_normal_controls`, for
`app:ch_background:eq:bg-Nsigma` and `app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumCommutator.NormalizedCarrierBaseline
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ContinuumRow CanonicalCarrier
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference WideDensity
open NormalizedBackground.SourceGeometry ContinuumNormalReduction.TransportSymbol

/-- The original initial scalar factors at the literal inverse ODE label.
No flow, label, scalar scale or canonical normal is reselected
(`app:ch_background:eq:bg-T`, `app:ch_background:eq:bg-Nsigma`). -/
theorem normalField_positiveDensity_eq {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (σ : ℝ) (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (p : Euclidean n × CarrierParameter) :
    normalField T Q F row col Φ Y (fun q ↦ positiveDensityAmplitude σ (v q)) p.1 p.2 =
      Real.sqrt (1 + v (densityFootpoint T Y p)) •
        normalField T Q F row col Φ Y (fun _ ↦ σ) p.1 p.2 := by
  rw [normalField_eq_scalar_smul, normalField_eq_scalar_smul, smul_smul]
  congr 1
  rw [densityFootpoint_eq]
  simp only [carrierScalarAmplitude, transportFromFootpoint,
    characteristicTransport, scalarTransport, positiveDensityAmplitude]
  ring

/-- The actual source ODE inverse has a uniform `μ+1` bound, including its
unchanged carrier label. Seed smoothness and Cauchy identities are outputs of
the selected unit transport. The positive-scale matching premise is the
literal branch of `exists_retained_seed_matched_unit_transport`; no norm of
the source inverse is assumed. This supplies the density composition in the
normalized low baseline (`app:ch_background:prop:bg-normalized`). -/
theorem exists_source_densityFootpoint_low_bound {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    (hD : D.region ⊆ ball (0 : Euclidean n) R ×ˢ V) :
    ∃ G > (0 : ℝ), ∃ s > (0 : ℝ), s ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      EqOn (densityFootpoint T Yσ) (densityFootpoint T (sourceTransportFlow Y σ))
        D.region →
      ContDiffOn ℝ ∞ (densityFootpoint T Yσ) D.region ∧
        cNorm D.carrier (2 * (n + 1) + 1) (densityFootpoint T Yσ) ≤ G := by
  let g := fun σ p ↦ sourceDensityFootpointExtension T Y (σ, p)
  let m := 2 * (n + 1) + 1
  have hK : IsCompact D.carrier := isCompact_closedBall ..
  have hKV : D.carrier ⊆ ball (0 : Euclidean n) R ×ˢ V := D.ball_subset.trans hD
  obtain ⟨e, he, hsmall⟩ := Metric.mem_nhds_iff.mp
    ((tendsto_sourceDensityFootpointExtension_sub_cNorm T hV hY hK hKV m).eventually
      (gt_mem_nhds zero_lt_one))
  let s := min (e / 2) (1 / 8)
  have hs : 0 < s := lt_min (half_pos he) (by norm_num)
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hreg (σ : ℝ) (hσ : σ ∈ Ioo (-(1 / 4) : ℝ) (1 / 4)) :
      ContDiffOn ℝ ∞ (g σ) D.region :=
    (sourceDensityFootpointExtension_contDiffOn T hV hY).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun p hp ↦ ⟨hσ, hD hp⟩)
  have hreg0 := hreg 0 (by constructor <;> norm_num)
  refine ⟨cNorm D.carrier m (g 0) + 1,
    add_pos_of_nonneg_of_pos (cNorm_nonneg ..) zero_lt_one, s, hs, hs1, ?_⟩
  intro σ hσ Yσ hmatch
  have hσ1 : σ ≤ 1 := hσ.2.trans hs1
  have hσI : σ ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) := by
    have hh := hσ.2.trans (min_le_right (e / 2) (1 / 8))
    constructor <;> linarith [hσ.1]
  have hgσ := hreg σ hσI
  have heq : EqOn (densityFootpoint T Yσ) (g σ) D.region := by
    intro p hp
    rw [hmatch hp]
    apply (sourceDensityFootpointExtension_eq T hR hY hzero hparam hσ.1.ne' ?_).symm
    exact ⟨(convex_ball (0 : Euclidean n) R).smul_mem_of_zero_mem
      (mem_ball_self hR) (hD hp).1 ⟨hσ.1.le, hσ1⟩, (hD hp).2⟩
  have hnorm : cNorm D.carrier m (densityFootpoint T Yσ) = cNorm D.carrier m (g σ) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro p hp
    filter_upwards [D.isOpen_region.mem_nhds (D.ball_subset hp)] with q hq
    exact heq hq
  refine ⟨hgσ.congr (fun p hp ↦ heq hp), ?_⟩
  change cNorm D.carrier m (densityFootpoint T Yσ) ≤ _
  rw [hnorm]
  have hdiff : cNorm D.carrier m (g σ - g 0) < 1 := by
    apply hsmall
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
    exact (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self he)
  have hsum := cNorm_add_le_of_contDiffAt (r := m) hK
    (fun p hp ↦ ((hgσ.sub hreg0).contDiffAt
      (D.isOpen_region.mem_nhds (D.ball_subset hp))).of_le (by simp))
    (fun p hp ↦ (hreg0.contDiffAt
      (D.isOpen_region.mem_nhds (D.ball_subset hp))).of_le (by simp))
  simp only [Pi.add_def, sub_add_cancel] at hsum
  change cNorm D.carrier m (g σ) ≤
    cNorm D.carrier m (g σ - g 0) + cNorm D.carrier m (g 0) at hsum
  linarith only [hsum, hdiff]

end JanetCartan.ContinuumCommutator.NormalizedCarrierBaseline
