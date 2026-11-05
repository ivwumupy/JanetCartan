module

public import JanetCartan.Iteration.PhysicalForwardMean.OriginalPhaseProfiles
public import JanetCartan.Iteration.PhysicalForwardMean.SingleScalar

/-!
# The literal retained native phase agrees with the SAME28 phase as a germ

Pointwise agreement on a closed amplitude support would NOT justify replacing
a phase derivative. This leaf proves full neighborhood agreement in physical
space from the original open shift domain and the SAME localized Y germ.
Consequently the original native full phase has the actual28 derivative-trade
identity and all normalized physical jets. No phase, carrier, scalar cutoff,
input mask or inverse is changed. Consumers are mean14's raw adjoint moments
and forward34's complete original phase-profile instantiation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalForwardMean
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open LeadingWave.FullModulation RawPrimary.SliceBounds PhysicalAdjointGeometry
open Sampling.MeasuredAmplitude

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
local notation "E" => Euclidean (m + 1)
local notation "Eta" => Euclidean (m + 1 - 1)
local notation "e" => adaptedSpacetimeEquiv T.data.adapted

/-- The actual full retained native quotient is jointly C∞. This is qualitative
regularity only; no quantitative frequency derivatives are taken. -/
theorem contDiff_retainedRawPhase (ζ : Eta) (τ : ℝ) :
    ContDiff ℝ ∞ (fun q : Eta × E ↦
      rawPrimaryPhaseDifference (extendedRetainedPhase T Q) ζ τ q.2 q.1) := by
  have hS := contDiff_extendedRetainedPhase T Q
  have hplus : ContDiff ℝ ∞ (fun q : Eta × E ↦ (q.2, ζ + τ • q.1)) := by fun_prop
  have hbase : ContDiff ℝ ∞ (fun q : Eta × E ↦ (q.2, ζ)) := contDiff_snd.prodMk contDiff_const
  change ContDiff ℝ ∞ (fun q : Eta × E ↦
    (extendedRetainedPhase T Q q.2 (ζ + τ • q.1) - extendedRetainedPhase T Q q.2 ζ) / τ)
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using
    ((hS.comp hplus).sub (hS.comp hbase)).div_const τ

/-- The original native FULL phase equals the SAME28 physical averaged phase
on a physical neighborhood, not merely pointwise on a closed support. The
original open shift buffer implies both evaluations lie in the ORIGINAL
retained phase plateau (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem retainedRawPhase_eventuallyEq_originalSampledPhysicalPhase
    {Y : Point (Spacetime (m + 1 - 1)) (m + 1 - 1) → Eta}
    {x : E} {ζ η : Eta} {τ : ℝ} (hτ : τ ≠ 0)
    (hq : ((e).symm x, ζ, τ • η) ∈ shiftDomain (covectorCenter T) T.family.radius)
    (heY : Y =ᶠ[𝓝 ((e).symm x, ζ, τ • η)] averagedCovector (current T Q)) :
    (fun y ↦ rawPrimaryPhaseDifference (extendedRetainedPhase T Q) ζ τ y η) =ᶠ[𝓝 x]
      originalSampledPhysicalPhase T Y ζ τ η := by
  let q : E → Point (Spacetime (m + 1 - 1)) (m + 1 - 1) := fun y ↦ ((e).symm y, ζ, τ • η)
  have hqc : Continuous q := (e).symm.continuous.prodMk continuous_const
  have hqev : ∀ᶠ y in 𝓝 x, q y ∈ shiftDomain (covectorCenter T) T.family.radius :=
    hqc.continuousAt.eventually ((isOpen_shiftDomain _ _).mem_nhds hq)
  have hYev : ∀ᶠ y in 𝓝 x, Y =ᶠ[𝓝 (q y)] averagedCovector (current T Q) :=
    hqc.continuousAt.eventually heY.eventuallyEq_nhds
  filter_upwards [hqev, hYev] with y hy hYy
  have hphys : ‖y‖ < T.family.radius := by
    simpa only [q, LinearIsometryEquiv.norm_map] using hy.1
  have hbase : (y,ζ) ∈ phaseDomain T := by
    change dist (y,ζ) (0,covectorCenter T) < T.family.radius
    rw [Prod.dist_eq, dist_zero_right, max_lt_iff]
    exact ⟨hphys, lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg (τ • η))) hy.2⟩
  have hshift : (y,ζ + τ • η) ∈ phaseDomain T := by
    change dist (y,ζ + τ • η) (0,covectorCenter T) < T.family.radius
    rw [Prod.dist_eq, dist_zero_right, max_lt_iff]
    refine ⟨hphys, lt_of_le_of_lt ?_ hy.2⟩
    simpa only [dist_eq_norm, add_sub_right_comm] using
      norm_add_le (ζ - covectorCenter T) (τ • η)
  rw [rawPrimaryPhaseDifference, extendedRetainedPhase_eq T Q hshift, extendedRetainedPhase_eq T Q hbase]
  exact literal_rawPhase_eq_originalSampledPhysicalPhase T Q hτ hy hYy

/-- Every physical jet of the normalized ORIGINAL retained phase agrees with
that of the SAME28 smooth phase. Derivatives are justified by genuine germ
agreement, without any quantitative frequency jet assumption. -/
theorem iteratedFDeriv_normalizedRetainedRawPhase_eq
    {Y : Point (Spacetime (m + 1 - 1)) (m + 1 - 1) → Eta}
    {x : E} {ζ η : Eta} {τ : ℝ} (hτ : τ ≠ 0)
    (hq : ((e).symm x, ζ, τ • η) ∈ shiftDomain (covectorCenter T) T.family.radius)
    (heY : Y =ᶠ[𝓝 ((e).symm x, ζ, τ • η)] averagedCovector (current T Q)) (k : ℕ) :
    iteratedFDeriv ℝ k
      (fun y ↦ rawPrimaryPhaseDifference (extendedRetainedPhase T Q) ζ τ y η / ‖η‖) x =
      iteratedFDeriv ℝ k (fun y ↦ originalSampledPhysicalPhase T Y ζ τ η y / ‖η‖) x := by
  have hg := retainedRawPhase_eventuallyEq_originalSampledPhysicalPhase T Q hτ hq heY
  have hd : (fun y ↦ rawPrimaryPhaseDifference (extendedRetainedPhase T Q) ζ τ y η / ‖η‖) =ᶠ[𝓝 x]
      (fun y ↦ originalSampledPhysicalPhase T Y ζ τ η y / ‖η‖) :=
    hg.mono fun _ hy ↦ congrArg (fun z : ℝ ↦ z / ‖η‖) hy
  exact (hd.iteratedFDeriv ℝ k).eq_of_nhds

/-- The SAME28 derivative-trade field differentiates the literal ORIGINAL native
full phase. The input identity is the already constructed28 Y/L identity, not
an assumed identity for the native phase (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem fderiv_retainedRawPhase_physicalTrade
    {Y : Point (Spacetime (m + 1 - 1)) (m + 1 - 1) → Eta} (hY : ContDiff ℝ ∞ Y)
    (L : Point (Spacetime (m + 1 - 1)) (m + 1 - 1) → Eta →L[ℝ] Spacetime (m + 1 - 1))
    {x : E} {ζ η : Eta} {τ : ℝ} (hτ : τ ≠ 0)
    (hq : ((e).symm x, ζ, τ • η) ∈ shiftDomain (covectorCenter T) T.family.radius)
    (heY : Y =ᶠ[𝓝 ((e).symm x, ζ, τ • η)] averagedCovector (current T Q))
    (h : Eta)
    (hid : fderiv ℝ (fun y ↦ inner ℝ (Y (y, ζ, τ • η)) η) ((e).symm x)
      (L ((e).symm x, ζ, τ • η) h) = inner ℝ h η) :
    fderiv ℝ (fun y ↦ rawPrimaryPhaseDifference (extendedRetainedPhase T Q) ζ τ y η) x
      (physicalTrade e L (x, ζ, τ • η) h) = inner ℝ h η := by
  rw [(retainedRawPhase_eventuallyEq_originalSampledPhysicalPhase T Q hτ hq heY).fderiv_eq]
  exact fderiv_phase_physicalTrade e hY L (x,ζ,τ • η) h η hid

end JanetCartan.PhysicalForwardMean
