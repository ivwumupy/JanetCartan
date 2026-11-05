module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.RootGap
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.StressScaling
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents

/-!
# Admission of the genuine source-scaled seed to the retained charts

The component estimates from `Reference.Initialization.StressScaling` imply
the joint frame norm required by the actual Hamilton construction. A single
initial scale admits the seed and all its positive contractions to the same
retained family. The frozen transverse gap then proves chart and phase
matching, including ambient jets, without a matching premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenPhaseReference
open NormalizedBackground.SourceGeometry
open ProjectedStressFrame

/-- On any fixed bounded open working domain, every sufficiently small
source dilation of the actual flat reference has small JOINT projected frame
norm. This supplies the subtype admission and coefficient threshold for
`exists_source_seed_chart_matching`. The cap precedes the varying scale.
Source: `app:ch_background:eq:bg-Nsigma`, `new:lem:scaling`. -/
theorem exists_joint_stress_scale_interval {n : ℕ} (G : FlatReference n)
    {U : Set (Euclidean n)} (hbounded : Bornology.IsBounded U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cap : ℝ, 0 < cap ∧ cap ≤ 1 ∧ ∀ s : ℝ, 0 < s → s ≤ cap →
      IsImmersionOn (sourceDilation G.map s) U ∧
      HasFullNormalRankOn (sourceDilation G.map s) U ∧
      (∀ x ∈ closure U, ContDiffAt ℝ ∞ (projectedStress (sourceDilation G.map s)) x) ∧
      cNorm (closure U) 6
        (projectedStress (sourceDilation G.map s) - fun _ ↦ cubeStress n) < ε := by
  have hK : IsCompact (closure U) := hbounded.isCompact_closure
  obtain ⟨W, hW, hKW, s₀, hs₀, hs₁, _, hgeom, hb⟩ :=
    exists_projectedStress_dilation_bounds G hK
  obtain ⟨C, hC, hbound⟩ := hb 6
  let cap := min s₀ (ε / (14 * C))
  have hcap : 0 < cap := lt_min hs₀ (by positivity)
  refine ⟨cap, hcap, (min_le_left _ _).trans hs₁, ?_⟩
  intro s hs hscap
  have hss₀ : s ≤ s₀ := hscap.trans (min_le_left _ _)
  obtain ⟨hi, hr, hq⟩ := hgeom s ⟨hs, hss₀⟩
  have hframe : ContDiffOn ℝ ∞ (projectedStress (sourceDilation G.map s)) W :=
    contDiffOn_pi.mpr hq
  have hUW : U ⊆ W := subset_closure.trans hKW
  refine ⟨fun x hx ↦ hi x (hUW hx), fun x hx ↦ hr x (hUW hx),
    (fun x hx ↦ hframe.contDiffAt (hW.mem_nhds (hKW hx))), ?_⟩
  have hjoint := frame_cNorm_le_of_componentwise (m := 6) hK
    (f := projectedStress (sourceDilation G.map s) - fun _ ↦ cubeStress n)
    (fun x hx ↦ ((hframe.contDiffAt (hW.mem_nhds (hKW hx))).sub
      contDiffAt_const).of_le (show (6 : ℕ∞ω) ≤ ∞ by simp))
    (mul_nonneg hC.le hs.le) (fun i ↦ by
      simpa only [Pi.sub_apply] using hbound s ⟨hs, hss₀⟩ i)
  have hsmall := (le_div_iff₀ (show 0 < 14 * C by positivity)).mp
    (hscap.trans (min_le_right _ _))
  norm_num only [Nat.cast_ofNat] at hjoint
  have hstrict : (7 : ℝ) * (C * s) < ε := by
    nlinarith only [hsmall, hε]
  exact hjoint.trans_lt hstrict

/-- Choose a genuine smooth flat full-rank seed whose retained charts match
all its positive source contractions on the same open target. The initial
scale is chosen from the frame threshold, the frozen transverse threshold,
and an arbitrary additional coefficient margin `ε`; no chart or trajectory
identity is assumed. The frozen gap is produced by
`exists_transverse_localFrozenReference_in_physical_ball`.
Consumer: `FamilyInputs` source-normalized carrier construction.
Source: `app:ch_background:eq:bg-Nsigma`, `new:lem:scaling`.

The extra margin is on `closure U`, so it can also admit the seed to
`exists_projected_null_coefficients` on any compact subset of `U`. -/
theorem exists_source_seed_chart_matching {n : ℕ} (G : FlatReference n)
    {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (hbounded : Bornology.IsBounded U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hgap : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      c ≤ |⟪(frozenSymbol n).hp z, T.data.adapted.normal⟫_ℝ|) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      let F := sourceDilation G.map ρ
      ContDiff ℝ ∞ F ∧ (∀ x, inducedMetric F x = 1) ∧
      IsImmersionOn F U ∧ HasFullNormalRankOn F U ∧
      cNorm (closure U) 6 (projectedStress F - fun _ ↦ cubeStress n) < ε ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < ε ∧
      ∃ Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
        Q₀.1 = projectedStress F ∧
        (∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
          ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z,
            T.data.adapted.normal⟫_ℝ ≠ 0) ∧
        ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
          IsImmersionOn (sourceDilation F σ) U ∧
          HasFullNormalRankOn (sourceDilation F σ) U ∧
          cNorm (closure U) 6
            (projectedStress (sourceDilation F σ) - fun _ ↦ cubeStress n) < ε ∧
          ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
            cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (Q - fun _ ↦ cubeStress n) < T.family.threshold},
            Qσ.1 = projectedStress (sourceDilation F σ) ∧
            EqOn (T.currentChart Qσ).coordinates
              (sourceCoordinates (T.currentChart Q₀).coordinates σ) T.target ∧
            EqOn (phase (T.currentChart Qσ).coordinates)
              (sourcePhase (phase (T.currentChart Q₀).coordinates) σ) T.target ∧
            ∀ m : ℕ,
              EqOn (iteratedFDeriv ℝ m (phase (T.currentChart Qσ).coordinates))
                (iteratedFDeriv ℝ m
                  (sourcePhase (phase (T.currentChart Q₀).coordinates) σ)) T.target := by
  obtain ⟨δ, hδ, htrans⟩ := exists_retained_seed_transverse_threshold T hphysical hc hgap
  let d := min ε (min T.family.threshold δ)
  have hd : 0 < d := lt_min hε (lt_min T.family.threshold_pos hδ)
  obtain ⟨ρ, hρ, hρ₁, hscale⟩ := exists_joint_stress_scale_interval G hbounded hd
  have hK : IsCompact (closure U) := hbounded.isCompact_closure
  have hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆
      closure U := hphysical.trans subset_closure
  have hlow (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ) := (hscale s hs hsρ).2.2.2
  have hsmall (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ) :
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress (sourceDilation G.map s) - fun _ ↦ cubeStress n) < d := by
    apply (cNorm_mono_set_of_contDiffAt hball hK ?_).trans_lt (hlow s hs hsρ)
    intro x hx
    exact (((hscale s hs hsρ).2.2.1 x hx).sub contDiffAt_const).of_le (by simp)
  let F := sourceDilation G.map ρ
  have hg := hscale ρ hρ le_rfl
  have hq : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold :=
    (hsmall ρ hρ le_rfl).trans_le ((min_le_right ε _).trans (min_le_left _ _))
  let Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨projectedStress F, fun x hx ↦ (hg.2.2.1 x (subset_closure hx)).contDiffWithinAt, hq⟩
  have ht : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z,
        T.data.adapted.normal⟫_ℝ ≠ 0 := fun z hz ↦
    (htrans Q₀ ((hsmall ρ hρ le_rfl).trans_le
      ((min_le_right ε _).trans (min_le_right _ _))) z hz).2
  refine ⟨ρ, hρ, hρ₁, contDiff_sourceDilation G.contDiff,
    inducedMetric_sourceDilation_eq_one hρ G.contDiff G.inducedMetric_eq_one,
    hg.1, hg.2.1, hg.2.2.2.trans_le (min_le_left _ _),
    (hsmall ρ hρ le_rfl).trans_le (min_le_left _ _), Q₀, rfl, ht, ?_⟩
  intro σ hσ hσ₁
  have hm : 0 < ρ * σ := mul_pos hρ hσ
  have hmρ : ρ * σ ≤ ρ := mul_le_of_le_one_right hρ.le hσ₁
  have he : sourceDilation F σ = sourceDilation G.map (ρ * σ) := by
    funext x
    simp only [F, sourceDilation, smul_smul, mul_inv_rev]
  have hgs := hscale (ρ * σ) hm hmρ
  have hqs : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress (sourceDilation F σ) - fun _ ↦ cubeStress n) < T.family.threshold := by
    rw [he]
    exact (hsmall (ρ * σ) hm hmρ).trans_le
      ((min_le_right ε _).trans (min_le_left _ _))
  let Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨projectedStress (sourceDilation F σ),
      he.symm ▸ (show ContDiffOn ℝ ∞ (projectedStress (sourceDilation G.map (ρ * σ))) U from
        fun x hx ↦ (hgs.2.2.1 x (subset_closure hx)).contDiffWithinAt), hqs⟩
  refine ⟨he.symm ▸ hgs.1, he.symm ▸ hgs.2.1,
    he.symm ▸ hgs.2.2.2.trans_le (min_le_left _ _), Qσ, rfl, ?_⟩
  exact projected_current_chart_source_dilation T Q₀ Qσ
    (contDiff_sourceDilation G.contDiff) hg.2.1 hphysical rfl ht hσ hσ₁ rfl

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
