module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoefficientOrder
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Relations

/-!
# Fixed buffers on the already selected sector family

These deductions use the original `ActualMaskFamily` and the two radius
comparisons retained by `FiniteAssembly.exists_finite_direct_operator_bounds`.
The conic buffer below contains the original closed multiplier supports at
every allowed enlarged threshold. No chart, flow, or physical mask is chosen.

Consumer: the selected-family application of
`ProtectedMasks.exists_uniform_conic_nested_localization_data`, for
`app:ch_regular:lem:finite-chain` and `app:ch_regular:thm:no-return`.
The same-flow ODE, inverse-segment and joint jet certificates are retained by
`FiniteAssembly.ProtectionCertificates` and applied in `InitializedApplication`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedSectorProtection

open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteEvolution RegularSector.Characteristic
open ProtectedMasks

variable {d : ℕ} {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)}
variable {RQ M : ℝ} {A₀ : Fin (d + 1) → MetricTensor (d + 1)}
variable {K : Set (Euclidean (d + 1))}

local notation "E" => Euclidean (d + 1)

/-- Testing the retained physical-ball inclusion on the original selected
coordinate axis gives a scalar bound on the common physical radius. This
compares common elapsed times with every local source radius without choosing
new masks (`app:ch_regular:lem:finite-chain`, whole physical segments). -/
theorem selected_physical_radius_lt_chart_neighborhood
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) :
    4 * f.physicalRadius < (f.chart p).neighborhoodRadius := by
  let v : E := (4 * f.physicalRadius) • EuclideanSpace.single (f.chart p).index 1
  have hr : 0 ≤ 4 * f.physicalRadius := mul_nonneg (by norm_num) f.physicalRadius_pos.le
  have hv : ‖v‖ = 4 * f.physicalRadius := by
    simp [v, norm_smul, EuclideanSpace.single, PiLp.norm_single, Real.norm_of_nonneg hr]
  have hy : x + v ∈ closedBall x (4 * f.physicalRadius) := by
    simp [mem_closedBall, dist_eq_norm, hv]
  have hc := f.physicalBall_in_chart p hy
  change dist (coordinateSplit (f.chart p).index (x + v))
    (coordinateSplit (f.chart p).index x) < (f.chart p).neighborhoodRadius at hc
  have he : coordinateSplit (f.chart p).index v = (4 * f.physicalRadius, 0) := by
    simp [v]
  simpa [map_add, dist_eq_norm, ← map_sub, he, Prod.norm_def, Real.norm_of_nonneg hr,
    max_eq_left hr] using hc

/-- A common physical elapsed bound fits every selected mask and source
radius. Its comparison with the ODE time only needs the original constructor's
retained inequality `2 * sourceRadius ≤ evolutionTime / 4`
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem selected_common_elapsed_lt_source_radii
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) :
    0 < 6 * f.physicalRadius ∧
      6 * f.physicalRadius < (f.chart p).maskRadius ∧
      6 * f.physicalRadius < (f.chart p).sourceRadius := by
  have hphysical := selected_physical_radius_lt_chart_neighborhood f p
  have hneighborhood : (f.chart p).neighborhoodRadius ≤ (f.chart p).maskRadius / 8 :=
    min_le_left _ _
  have hr := f.physicalRadius_pos
  have hsource := (f.chart p).maskRadius_lt_sourceRadius
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Every pair of original physical support points has elapsed time less
than the SAME common bound in each chart and either orientation. This is a
bound on the entire supported pair product, not an interval substituted for
part of the retarded operator (`app:ch_regular:lem:finite-chain`). -/
theorem selected_physical_support_elapsed_bound
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) {y z : E}
    (hy : y ∈ tsupport f.inputMask ∪ tsupport f.outputMask)
    (hz : z ∈ tsupport f.inputMask ∪ tsupport f.outputMask) :
    |(coordinateSplit (f.chart p).index y).1 - (coordinateSplit (f.chart p).index z).1| <
      6 * f.physicalRadius := by
  have hsupport : tsupport f.inputMask ∪ tsupport f.outputMask ⊆
      ball x (3 * f.physicalRadius) := by
    apply union_subset f.inputMask_support
    exact f.outputMask_support.trans (ball_subset_ball (by
      have := f.physicalRadius_pos
      linarith : 2 * f.physicalRadius ≤ 3 * f.physicalRadius))
  have hdist : dist y z < 6 * f.physicalRadius := by
    have htriangle := dist_triangle y x z
    rw [dist_comm x z] at htriangle
    have hy' : dist y x < 3 * f.physicalRadius := hsupport hy
    have hz' : dist z x < 3 * f.physicalRadius := hsupport hz
    linarith
  simpa only [coordinateSplit_fst, Real.dist_eq] using
    (PiLp.dist_apply_le y z (f.chart p).index).trans_lt hdist

/-- The final endpoint mask retained by the finite operator constructor is
supported in the original selected output mask. Hence all the selected-support
lemmas apply to that very endpoint (`energy-complete-residual`). -/
theorem selected_endpoint_support_subset_outputMask
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (output : E → ℝ) (hsupport : tsupport output ⊆ ball x f.physicalRadius) :
    tsupport output ⊆ tsupport f.outputMask := by
  intro y hy
  have hone : f.outputMask y = 1 :=
    (interior_subset (s := {y | f.outputMask y = 1}))
      (f.outputMask_plateau (ball_subset_closedBall (hsupport hy)))
  exact subset_tsupport _ (by change f.outputMask y ≠ 0; rw [hone]; exact one_ne_zero)

/-- The original fixed sector low order controls the C³ norm both on its
coefficient ball and on the selected common physical ball. These are the
local restrictions used in the protected-mask construction; no new low
coefficient hypothesis is needed (`app:ch_regular:eq:fixed-high-derivative`). -/
theorem selected_coefficient_cubic_restriction
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hQM : cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M) :
    cNorm (closedBall x RQ) 3 Q ≤ M ∧
      cNorm (closedBall x (4 * f.physicalRadius)) 3 Q ≤ M := by
  have horder : 3 ≤ sectorLowOrder d := by
    have := (sectorLowOrder_bounds d).2.2
    omega
  have hlocal := (cNorm_mono_order horder).trans hQM
  refine ⟨hlocal, ?_⟩
  exact (cNorm_mono_set_of_contDiffAt f.physicalBall_coefficientDomain
    (isCompact_closedBall _ _)
    (fun y hy ↦ (hQ.contDiffAt (hΩ.mem_nhds (hKΩ hy))).of_le (by simp))).trans hlocal

/-- Take the protection radius `γ` to be the SAME selected source-mask
radius, and `β` to be half the selected target radius. The original elapsed
bound `3 * maskRadius / 4` fits without shrinking it. The source radius is
the inverse chart's `σ` (`app:ch_regular_base:lem:retarded-kernel`,
`app:ch_regular:lem:finite-chain`). -/
theorem selected_mask_radius_protection_bounds
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hradii : ∀ p : f.centers,
      (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
        (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4) (p : f.centers) :
    0 < (f.chart p).maskRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).targetRadius / 2 ∧
      (f.chart p).maskRadius ≤ (f.chart p).sourceRadius ∧
      0 < 3 * (f.chart p).maskRadius / 4 ∧
      3 * (f.chart p).maskRadius / 4 ≤ (f.chart p).maskRadius := by
  have hpos := (f.chart p).maskRadius_pos
  have htarget := (f.chart p).targetRadius_pos
  obtain ⟨hbuffer, hmask⟩ := hradii p
  refine ⟨hpos, ?_, (f.chart p).maskRadius_lt_sourceRadius.le, ?_, ?_⟩ <;> linarith

/-- The full original right support, including closed angular support at
the retained enlarged threshold, lies in the protection buffer with
`γ = maskRadius`. The bound on the absolute elapsed time treats both signs.
Consumer: the supported-carrier hypotheses of the conic interior and boundary
gaps (`app:ch_regular:lem:finite-chain`). -/
theorem selected_right_support_in_protection_buffer
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {L : ℝ} (hL : f.radialThreshold ≤ L) {y z ζ : E}
    (hy : y ∈ tsupport f.inputMask ∪ tsupport f.outputMask)
    (hz : z ∈ tsupport f.inputMask ∪ tsupport f.outputMask)
    (hζ : ζ ∈ tsupport (dilatedConicMask (f.angularMask p) L)) :
    let c := f.chart p
    let e := coordinateSplit c.index
    ((e y).1, ((e z).1, ((e y).2, (e ζ).2))) ∈
      ConicPhase.domain c.radialSection
        (ball ((e x).1, ((e x).1, ((e x).2, (e p.val.val).2))) (c.maskRadius / 2)) ∧
      |(e y).1 - (e z).1| < c.maskRadius / 4 := by
  let c := f.chart p
  let e := coordinateSplit c.index
  have hy' : dist (e y) (e x) < c.neighborhoodRadius :=
    f.physical_supports_in_chart p hy
  have hz' : dist (e z) (e x) < c.neighborhoodRadius :=
    f.physical_supports_in_chart p hz
  have hζ' := c.angularNeighborhood_of_mem_rightSupport
    (f.angularMask_support p) (f.radialThreshold_ge_one.trans hL) hζ
  have hn : c.neighborhoodRadius ≤ c.maskRadius / 8 := min_le_left _ _
  have hmask := c.maskRadius_pos
  have hhalf : c.neighborhoodRadius < c.maskRadius / 2 := by linarith
  rw [Prod.dist_eq, max_lt_iff] at hy' hz'
  refine ⟨⟨hζ'.1, ?_⟩, ?_⟩
  · simp only [ConicPhase.normalize, mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hy'.1.trans hhalf, hz'.1.trans hhalf, hy'.2.trans hhalf, hζ'.2.trans hhalf⟩
  · have hdist := dist_triangle (e y).1 (e x).1 (e z).1
    rw [dist_comm (e x).1 (e z).1] at hdist
    simp only [Real.dist_eq] at hdist hy' hz'
    linarith [hy'.1, hz'.1]

/-- The original selected input mask is one on every fixed response source
supported in the selected physical core. This discharges the source-recut
plateau from the existing mask choice (`app:ch_regular:lem:finite-chain`). -/
theorem selected_source_recut_plateau
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (χ₂ : E → ℝ) (hsupport : tsupport χ₂ ⊆ ball x f.physicalRadius) :
    EqOn f.inputMask 1 (tsupport χ₂) := by
  intro y hy
  have hball : y ∈ closedBall x (2 * f.physicalRadius) :=
    ball_subset_closedBall ((ball_subset_ball (by
      have := f.physicalRadius_pos
      linarith : f.physicalRadius ≤ 2 * f.physicalRadius)) (hsupport hy))
  change f.inputMask y = 1
  exact (interior_subset (s := {y | f.inputMask y = 1})) (f.inputMask_plateau hball)

/-- Recutting any actual signed or diagonal relation keeps the literal
selected source plateau, including its full closed support
(`app:ch_regular:lem:finite-chain`, protected finite-chain paragraph). -/
theorem selected_sourceRecut_outer_eq_one
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (χ₂ : E → ℝ) (hsupport : tsupport χ₂ ⊆ ball x f.physicalRadius)
    {R : (E × E) → (E × E) → Prop} {p q : E × E}
    (hrecut : sourceRecutRelation χ₂ R p q) : f.inputMask p.1 = 1 :=
  sourceRecutRelation_outer_eq_one (selected_source_recut_plateau f χ₂ hsupport) hrecut

end JanetCartan.ArbitraryAccuracy.SelectedSectorProtection
