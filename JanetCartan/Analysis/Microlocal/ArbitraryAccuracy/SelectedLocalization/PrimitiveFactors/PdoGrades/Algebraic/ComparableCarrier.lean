module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.SourceGerms
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.CommonMasks
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Comparable.SupportedCarrier

/-!
# The exact comparable carrier of the selected algebraic PDO

The `Kpdo` in `CompleteFactor` places its output point in the source plateau
and the original coefficient domain, and its normalized covector in one
fixed compact annulus away from zero. No smaller cover or larger multiplier
threshold is used (`high-amplitude`, `chain-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.FiniteMasks.ActualFamily RegularSector.FinitePdo RegularSector.FiniteAlgebraic FourierIntegral
open FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Comparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- Every point of the actual endpoint mask lies strictly inside the source
plateau and inside the original coefficient ball (`energy-complete-residual`). -/
theorem endpointOutputMask_mem_algebraic_common_ball
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hs : tsupport output ⊆ ball x f.physicalRadius)
    {y : E} (hy : y ∈ tsupport (endpointOutputMask f p output)) :
    physicalCoordinates (f.chart p).index y ∈ ball x (4*f.physicalRadius) ∧
      physicalCoordinates (f.chart p).index y ∈ closedBall x RQ := by
  have ht := tsupport_comp_subset_preimage (fun y ↦ (output y : ℂ))
    (physicalCoordinates (f.chart p).index).continuous hy
  have hb := hs (tsupport_comp_subset Complex.ofReal_zero output ht)
  have hfour : physicalCoordinates (f.chart p).index y ∈ ball x (4*f.physicalRadius) :=
    ball_subset_ball (by linarith [f.physicalRadius_pos]) hb
  exact ⟨hfour, f.physicalBall_coefficientDomain (ball_subset_closedBall hfour)⟩

/-- The literal `Kpdo` of `CompleteFactor` supplies all geometric inputs for
the algebraic inverse and source-germ estimates. In particular, its fixed
normalized annulus excludes zero when the original protected inner radius
is positive (`app:ch_regular:eq:high-amplitude`, `chain-tail`). -/
theorem selected_algebraic_comparable_carrier_inputs
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hs : tsupport output ⊆ ball x f.physicalRadius)
    (a b : ℝ) (ha : 0 < a) :
    let J := frequencyAnnulus (n := d+1) (a / (16*annulusFactor 1 1))
      (4 * max 1 (4*annulusFactor 1 1*b))
    let Z := tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p)
    IsCompact J ∧ (0 : E) ∉ J ∧
      ∀ v ∈ comparableJointCarrier 1 1 a b ((Prod.fst '' Z) ×ˢ J) Z (frequencyAnnulus a b),
        physicalCoordinates (f.chart p).index v.1.1 ∈ ball x (4*f.physicalRadius) ∧
        physicalCoordinates (f.chart p).index v.1.1 ∈ closedBall x RQ ∧ v.2.1 ∈ J := by
  intro J Z
  refine ⟨isCompact_frequencyAnnulus _ _, ?_, ?_⟩
  · intro hz
    have hf : 0 < 16 * annulusFactor 1 1 := by
      have := two_le_annulusFactor 1 1
      positivity
    have hp := div_pos ha hf
    have hl : a / (16*annulusFactor 1 1) ≤ ‖(0 : E)‖ := hz.1
    simp only [norm_zero, not_le.mpr hp] at hl
  · intro v hv
    have hbase : v.1 ∈ Z := hv.1.1
    have hfreq : v.2.1 ∈ J := hv.1.2.1
    exact ⟨(endpointOutputMask_mem_algebraic_common_ball f p output hs hbase.1).1,
      (endpointOutputMask_mem_algebraic_common_ball f p output hs hbase.1).2, hfreq⟩

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
