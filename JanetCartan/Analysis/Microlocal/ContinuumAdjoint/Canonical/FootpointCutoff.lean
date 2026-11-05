module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.ExtensionBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Density

/-!
# One fixed physical initial cutoff for the canonical carrier

The cutoff in `app:ch_background:eq:bg-density-adjoint` must equal one at
the core's actual footpoints. A fixed primitive low immersion bound controls
the Hamilton footpoint on the entire supported chart. We choose one bump
on the literal initial product space before the immersion and all Sobolev
orders. Its open plateau contains every such footpoint, including the core.
This discharges the plateau choice required by `Canonical.density`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow PhaseExtension ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual canonical Hamilton footpoints lie in the open plateau of one
fixed compact smooth initial bump. The bump precedes the current immersion,
initial scalar and derivative order. Its only varying inputs are the original
primitive low bounds and projected-frame admissibility; no footpoint-size
estimate is assumed (`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_projected_initialCutoff {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} {r a : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hphys : 4 * a < T.physicalRadius)
    (hcarrier : closedBall (FullPhaseCharts.ActualComparison.spectatorCenter z₀) (3 * r) ×ˢ
        closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ b : ContDiffBump (0 : CarrierVariable n),
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨ProjectedStressFrame.projectedStress F,
          contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        MapsTo (fun p : Euclidean n × CarrierParameter ↦
          (p.2, CanonicalCarrier.transportPosition T Q p))
          (supportedChart z₀ a) (interior {q | b q = 1}) := by
  let L := supportedChart (n := n) z₀ a
  have hL : IsCompact L := supportedChart_compact z₀ a
  have hLO := supportedChart_subset_extensionDomain T ha har hphys hcarrier
  have hLO' : L ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hp
    have hh := hLO hp
    refine ⟨hh.1, fun i ↦ ?_⟩
    have hh' := hh.2 i
    linarith [hP.1]
  obtain ⟨A, hA, hbound⟩ := CanonicalCarrier.exists_projected_transportPosition_bound
    T (N := N) hP hL hLO' hK hKU hball M hκmet hκ
  let Z := CanonicalConic.carrierSupport z₀ (r := a)
  let Bz := cNorm Z 0 (id : CarrierParameter → CarrierParameter)
  let By := A 0 * (1 + max M 0)
  have hBz : 0 ≤ Bz := cNorm_nonneg ..
  have hBy : 0 < By := mul_pos (hA 0) (by linarith [le_max_right M 0])
  let R := 1 + Bz + By
  have hR : 0 < R := by dsimp [R]; linarith
  let b : ContDiffBump (0 : CarrierVariable n) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := by linarith }
  have hplateau : ball (0 : CarrierVariable n) R ⊆ interior {q | b q = 1} := by
    apply interior_maximal _ isOpen_ball
    intro q hq
    exact b.one_of_mem_closedBall (ball_subset_closedBall hq)
  refine ⟨b, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  have hY := transportPosition_contDiffOn_extensionDomain T hP Q
  have hYbound : cNorm L 0 (CanonicalCarrier.transportPosition T Q) ≤ By := by
    apply (hbound F hF hi hrank hFM hmet hnormal hlow 0).trans
    apply mul_le_mul_of_nonneg_left _ (hA 0).le
    exact add_le_add (le_refl 1) (hFM.trans (le_max_left M 0))
  intro p hp
  have hy : ‖CanonicalCarrier.transportPosition T Q p‖ ≤ By := by
    apply le_trans _ hYbound
    simpa only [norm_iteratedFDeriv_zero] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
        (fun q hq ↦ (hY.contDiffAt ((extensionDomain_open T).mem_nhds (hLO hq))).of_le
          (by simp : (0 : ℕ∞ω) ≤ ∞)) hp (le_refl 0)
  have hz : ‖p.2‖ ≤ Bz :=
    norm_le_cNorm (CanonicalConic.carrierSupport_compact z₀) contDiff_id hp.2
  apply hplateau
  rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
  constructor <;> dsimp [R] <;> linarith

end JanetCartan.ContinuumAdjoint.Canonical
