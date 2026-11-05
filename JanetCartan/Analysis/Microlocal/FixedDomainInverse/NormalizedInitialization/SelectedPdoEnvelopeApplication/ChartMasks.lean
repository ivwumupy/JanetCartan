module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.Geometry

/-!
# The actual selected chart masks fit the original source box

The output and input are the same masks appearing in
`selectedCommonChartResidualTerm`. Their chart coordinates preserve distance,
so the existing physical supports lie in the original radius-three box.
Consumer: the PDO source envelope in `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
open RegularSector RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic.ResidualCoordinates
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K₀ : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)

/-- The literal common output and chart input have compact supports in the
same source box used by the near and complementary frequency estimates
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_chart_pdo_masks_source_box
    (f : ActualMaskFamily Ω x RQ A₀ K₀ M) (p : f.centers)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) :
    HasCompactSupport (endpointOutputMask f p output) ∧
    HasCompactSupport (chartInputMask f p) ∧
    tsupport (endpointOutputMask f p output) ∪ tsupport (chartInputMask f p) ⊆
      ball ((physicalCoordinates (f.chart p).index).symm x) (3*f.physicalRadius) := by
  refine ⟨(endpointOutputMask_properties f p ho hoc hos).2.1,
    (chartPhysicalMasks_properties f p).2.2.2.1, ?_⟩
  intro y hy
  rcases hy with hy | hy
  · exact (closedBall_subset_ball (by linarith [f.physicalRadius_pos]))
      ((endpointOutputMask_properties f p ho hoc hos).2.2 hy)
  · let e := physicalCoordinates (f.chart p).index
    have hs : e y ∈ tsupport f.inputMask :=
      tsupport_comp_subset Complex.ofReal_zero f.inputMask
        (tsupport_comp_subset_preimage (fun z ↦ (f.inputMask z : ℂ)) e.continuous hy)
    have hd : dist (e y) x = dist y (e.symm x) := by
      conv_lhs => arg 2; rw [← e.apply_symm_apply x]
      rw [dist_eq_norm, ← map_sub, norm_physicalCoordinates, dist_eq_norm]
    have hb := mem_ball.mp (f.inputMask_support hs)
    rw [hd] at hb
    exact mem_ball.mpr hb

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
