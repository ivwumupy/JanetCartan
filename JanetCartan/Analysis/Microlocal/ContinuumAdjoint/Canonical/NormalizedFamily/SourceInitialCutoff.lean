module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.SourcePhase
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Density

/-!
# Initial cutoff on the literal source-family supported chart

The normalized Hamilton estimate bounds the actual retained footpoint without
using an unnormalized normal-pairing gap or identifying independently chosen
flows. One cutoff on the original carrier/initial space contains every footpoint
of the supplied supported chart, before the source scale varies.

Consumer: the fixed cutoff in `Canonical.density`,
`app:ch_background:eq:bg-density-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier
open PhaseExtension ProjectedStressFrame FullPhaseCharts

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- A single smooth initial-space cutoff for every actual source frame on the
SAME supplied supported chart. The cutoff and source cap precede `σ` and all
Sobolev orders, and the original carrier coordinate order is preserved.
This is the plateau obligation for the raw-adjoint density construction
(`app:ch_background:eq:bg-density-adjoint`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_source_initialCutoff (H : FlatReference n)
    {c C : ℝ} (hP : P.IsValid c C) (hbounded : Bornology.IsBounded U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    {z₀ : Euclidean 3} {r a : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hphys : 4 * a < T.physicalRadius)
    (hcarrier : closedBall (FullPhaseCharts.ActualComparison.spectatorCenter z₀) (3 * r) ×ˢ
        closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧ ∃ χinitial : ContDiffBump (0 : CarrierVariable n),
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      Q.1 = projectedStress (sourceDilation H.map σ) →
        MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.2, transportPosition T Q p))
          (supportedChart z₀ a) (interior {q | χinitial q = 1}) := by
  have hdom := supportedChart_subset_extensionDomain T ha har hphys hcarrier
  have hdom' : supportedChart (n := n) z₀ a ⊆
      ball (0 : Euclidean n) T.physicalRadius ×ˢ
        (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hp
    exact ⟨(hdom hp).1, fun i ↦ ((hdom hp).2 i).trans (by linarith [hP.1])⟩
  obtain ⟨σ₀, hσ₀, hσ₁, B, hB, hb⟩ := exists_source_transportPosition_bounds T H hP
    hbounded hphysical (supportedChart_compact z₀ a) hdom'
  let Z := CanonicalConic.carrierSupport z₀ (r := a)
  let Bz := cNorm Z 0 (id : CarrierParameter → CarrierParameter)
  let R := 1 + Bz + B 0
  have hR : 0 < R := by dsimp [R, Bz]; linarith [hB 0, cNorm_nonneg Z 0 id]
  let χinitial : ContDiffBump (0 : CarrierVariable n) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := by linarith }
  have hplateau : ball (0 : CarrierVariable n) R ⊆ interior {q | χinitial q = 1} := by
    apply interior_maximal _ isOpen_ball
    intro q hq
    exact χinitial.one_of_mem_closedBall (ball_subset_closedBall hq)
  refine ⟨σ₀, hσ₀, hσ₁, χinitial, ?_⟩
  intro σ hσ Q hQ p hp
  have hy : ‖transportPosition T Q p‖ ≤ B 0 := by
    apply le_trans _ (hb σ hσ Q hQ 0)
    simpa only [norm_iteratedFDeriv_zero] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt (supportedChart_compact z₀ a)
        (fun q hq ↦ ((transportPosition_contDiffOn_extensionDomain T hP Q).contDiffAt
          ((extensionDomain_open T).mem_nhds (hdom hq))).of_le (by simp)) hp (le_refl 0)
  have hz : ‖p.2‖ ≤ Bz :=
    norm_le_cNorm (CanonicalConic.carrierSupport_compact z₀) contDiff_id hp.2
  apply hplateau
  rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
  constructor <;> dsimp [R] <;> linarith [cNorm_nonneg Z 0 id, hB 0]

end JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
