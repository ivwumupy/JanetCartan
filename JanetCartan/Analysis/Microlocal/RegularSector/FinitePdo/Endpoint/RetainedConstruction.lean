module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.RetainedConstruction.PhysicalOperators

/-!
# Retained endpoint coverage on the actual finite physical evolutions

The SAME selected charts supply the physical retarded factors. Choose a single
radial threshold above every local threshold and a common output plateau in
original physical coordinates. These choices precede the varying coefficients,
Sobolev orders and accuracy. The complete physical partition still contains
its angular and low-frequency complements.
Consumer: the finite solver and `PW₁` term in
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo.RetainedConstruction
open ActualCarriers Characteristic Characteristic.ResidualCoordinates
open Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.ConicAmplitude
open FiniteMasks FiniteMasks.ActualFamily FiniteEvolution
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Turn the retained frequency inclusion into the exact `hcover` consumed
by both `EndpointPdoBounds.exists_supported_endpoint_pdo_budgets` and
`EndpointPdoBounds.exists_endpoint_integer_gain_constants`. Positions come
from the SAME selected family's physical ball; the radial band is unchanged
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem DiagonalFrequencyCoverage.selectedEndpoint_mapsTo
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {ra rb : ℝ} {β : E → ℂ}
    (hcoverage : DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2
      ((f.chart p).bufferRadius/2) ra rb β) :
    let e := coordinateSplit (f.chart p).index
    let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
    ∀ ζ ∈ tsupport β, ∃ R : ℝ, 1 ≤ R ∧ ∃ η : Euclidean d,
      spatialPart ζ = R • η ∧ ‖spatialPart ζ‖ ≤ R ∧
      MapsTo (Characteristic.EndpointPdoBounds.diagonalPoint η)
        (closedBall ((physicalCoordinates (f.chart p).index).symm x) (2*f.physicalRadius))
        (bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) ra rb) := by
  intro e z ζ hζ
  obtain ⟨R, hR, η, hη, he, hnorm⟩ := hcoverage ζ hζ
  refine ⟨R, hR, η, he, hnorm, ?_⟩
  intro y hy
  obtain ⟨ht, hx⟩ := selectedEndpoint_diagonal_position_buffer f p y hy
  exact (Characteristic.EndpointPdoBounds.diagonalPoint_mem_bufferedJetSet_iff
    (f.chart p).radialSection z ((f.chart p).bufferRadius/2) ra rb η y).mpr ⟨ht, hx, hη⟩

/-- Construct one common radial threshold and physical output plateau, and
instantiate the physical retarded theorem on every SAME selected chart.
Every analytic input comes from the original coefficient producer. The
result retains all local identities and all signed integer estimates in
`SelectedChartEvolutionAtWithDiagonal`; no operator estimate is assumed. The source
plateau contains the original common input support. The angular cover is
unchanged. The already selected `f` is an input; no second family is
chosen. For every `L' ≥ L ≥ f.radialThreshold`, normalized frequency coverage
and the literal amplitudes have the SAME existential radial band. Consumer:
the upper-endpoint PDO and signed integer gains for that selected `W₁`.
Source: `thm:sector`, `energy-complete-residual`. -/
theorem exists_finite_physical_evolution_data_with_diagonal
    (hΩ : IsOpen Ω) (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hradii : ∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (hM : 0 ≤ M) :
    ∃ L : ℝ, 1 ≤ L ∧ f.radialThreshold ≤ L ∧ f.radialThreshold ≤ 2 * L ∧
    ∃ (angular : f.centers → Euclidean d → ℝ)
      (χout χsource : f.centers → E → ℂ),
    ∃ hs : ∀ p, ContDiff ℝ ∞ (χsource p),
      (∀ p, ContDiff ℝ ∞ (angular p) ∧
        (∀ η, angular p η ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport (angular p) ∧
        tsupport (angular p) ⊆ angularCone (f.chart p).radialSection
          (coordinateSplit (f.chart p).index p.val.val).2
          (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius / 2) ∧
        (∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η)) ∧
      (∀ p, ContDiff ℝ ∞ (χout p) ∧ HasCompactSupport (χout p) ∧
        HasCompactSupport (χsource p) ∧
        tsupport (χsource p) ⊆ (physicalCoordinates (f.chart p).index) ⁻¹' Ω ∧
        (physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask ⊆
          interior {y | χsource p y = 1} ∧
        (∀ y ∈ tsupport (χout p), (f.chart p).timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1))) ∧
    ∃ (output : E → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ ∞ output ∧ (∀ y, output y ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport output ∧ tsupport output ⊆ ball x f.physicalRadius ∧
      closedBall x r ⊆ interior {y | output y = 1} ∧
      (∀ p, tsupport output ⊆ (physicalCoordinates (f.chart p).index).symm ⁻¹'
        interior {y | χout p y = 1}) ∧
      (∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
        (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) ∧
      (∀ p y, (output y : ℂ) *
        χout p ((physicalCoordinates (f.chart p).index).symm y) = (output y : ℂ)) ∧
      (∀ ζ : E, (∑ p, dilatedConicMask (f.angularMask p) (2*L) ζ) +
        dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) (2*L) ζ +
        FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1) ∧
      ∀ p : f.centers, SelectedChartEvolutionAtWithDiagonal (f.chart p)
        (fun L' ζ ↦ (dilatedConicMask (f.angularMask p) (2*L')
          (physicalCoordinates (f.chart p).index ζ) : ℂ))
        L (angular p) (χout p) (χsource p) (hs p) := by
  classical
  have hinput : x ∈ tsupport f.inputMask := by
    apply subset_tsupport f.inputMask
    have he := interior_subset
      (f.inputMask_plateau (mem_closedBall_self
        (mul_nonneg (by norm_num) f.physicalRadius_pos.le)))
    change f.inputMask x = 1 at he
    change f.inputMask x ≠ 0
    rw [he]
    exact one_ne_zero
  have hp (p : f.centers) : SelectedChartPhysicalEvolutionWithDiagonal (f.chart p) (f.angularMask p)
      ((physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask)
      ((physicalCoordinates (f.chart p).index) ⁻¹' Ω) :=
    exists_selected_chart_physical_operators_with_diagonal (f.chart p) (hradii p).1 (hradii p).2 hM
      (f.angularMask p) (f.angularMask_smooth p) (f.angularMask_support p)
      (f.inputMask_compact.image (physicalCoordinates (f.chart p).index).symm.continuous)
      ⟨(physicalCoordinates (f.chart p).index).symm x, x, hinput, rfl⟩
      (hΩ.preimage (physicalCoordinates (f.chart p).index).continuous)
      (selected_input_carrier_subset_domain f p)
  unfold SelectedChartPhysicalEvolutionWithDiagonal SelectedChartEvolutionForWithDiagonal at hp
  dsimp only at hp
  choose angular localL hL ha har hac has hap χout χsource ho hs hoc hsc hop hsp
    hos hss hκ hconstruct using hp
  let L := f.radialThreshold + ∑ p, localL p
  have hsum : 0 ≤ ∑ p, localL p := Finset.sum_nonneg fun p _ ↦ (zero_le_one.trans (hL p))
  have hLf : f.radialThreshold ≤ L := le_add_of_nonneg_right hsum
  have hLone : 1 ≤ L := f.radialThreshold_ge_one.trans hLf
  have hlocal (p : f.centers) : localL p ≤ L := by
    exact (Finset.single_le_sum (fun q _ ↦ zero_le_one.trans (hL q))
      (Finset.mem_univ p)).trans (le_add_of_nonneg_left
        (zero_le_one.trans f.radialThreshold_ge_one))
  let V : Set E := ball x f.physicalRadius ∩ ⋂ p : f.centers,
    (physicalCoordinates (f.chart p).index).symm ⁻¹' interior {y | χout p y = 1}
  have hV : IsOpen V := isOpen_ball.inter
    (isOpen_iInter_of_finite fun p ↦ isOpen_interior.preimage
      (physicalCoordinates (f.chart p).index).symm.continuous)
  have hx : x ∈ V := ⟨mem_ball_self f.physicalRadius_pos, mem_iInter.mpr fun p ↦ by
    simpa only [mem_preimage, physicalCoordinates_symm_center] using hop p⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV x hx
  obtain ⟨output, hout, hrange, hcompact, hsupport, hplateau⟩ :=
    CompatibleResponse.exists_compact_family_cutoff (isCompact_closedBall x (r/2))
      isOpen_ball (closedBall_subset_ball (by linarith : r/2 < r))
  have hsupportV : tsupport output ⊆ V := hsupport.trans hrV
  refine ⟨L, hLone, hLf, by linarith, angular, χout, χsource, hs,
    fun p ↦ ⟨ha p, har p, hac p, has p, hap p⟩,
    fun p ↦ ⟨ho p, hoc p, hsc p, hss p, hsp p, hκ p⟩,
    output, r/2, by positivity, hout, hrange, hcompact,
    fun y hy ↦ (hsupportV hy).1, hplateau,
    fun p y hy ↦ mem_iInter.mp (hsupportV hy).2 p, ?_, ?_, ?_, ?_⟩
  · intro p y
    by_cases hy : f.inputMask y = 0
    · simp only [hy, Complex.ofReal_zero, mul_zero]
    · have he := interior_subset (hsp p ⟨y, subset_tsupport f.inputMask hy, rfl⟩)
      change χsource p ((physicalCoordinates (f.chart p).index).symm y) = 1 at he
      rw [he, one_mul]
  · intro p y
    by_cases hy : output y = 0
    · simp only [hy, Complex.ofReal_zero, zero_mul]
    · have he := interior_subset (mem_iInter.mp (hsupportV (subset_tsupport output hy)).2 p)
      change χout p ((physicalCoordinates (f.chart p).index).symm y) = 1 at he
      rw [he, mul_one]
  · exact dilatedConicMask_complete_partition f.angularMask (2*L)
  · intro p L' hLL
    exact hconstruct p L' ((hlocal p).trans hLL)

end JanetCartan.RegularSector.FinitePdo.RetainedConstruction
