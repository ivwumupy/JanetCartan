module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalConstruction
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.PhysicalMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Support

/-!
# Literal common masks on a retained selected chart

The common physical masks from `exists_finite_physical_evolution_data` are
inside the local retarded plateaux. These identities identify the localized
retained operator with the common-mask kernel. The source multiplication
stays inside the Fourier input. The original finite family's output mask is
also one near the new common output carrier; it need not equal that mask.
Consumer: the selected-chart equation in `energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.KernelIdentification
open Characteristic.EvolutionIntegral.UncutTestAction
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FourierIntegral FourierIntegral.LowBounds
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q

/-- Restricting the original input to the local source plateau gives the SAME
compact smooth Fourier input (`energy-complete-residual`). The premise is the
literal source multiplication identity exported by `PhysicalConstruction`. -/
theorem commonSourceMaskTest_eq
    (χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hp : ∀ x, χsource x * (ψ x : ℂ) = (ψ x : ℂ))
    (u : graphTestSpace (d + 1) q) :
    complexSourceMaskTest χsource hs (sourceCutTest ψ hψ u) =
      complexSourceMaskTest (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hψ) u := by
  apply Subtype.ext
  funext x
  change χsource x • ((ψ x : ℂ) • u.val x) = (ψ x : ℂ) • u.val x
  rw [← mul_smul, hp]

/-- Exact retarded kernel after applying the common physical masks. Both
original retarded endpoints and the Fourier multiplier remain unchanged
(`fixed-time-representation`, `energy-complete-residual`). -/
theorem retardedPhysicalIntegral_common_masks
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource) (a : ℝ)
    (ψout ψsource : E → ℝ) (hsource : ContDiff ℝ ∞ ψsource)
    (hout : ∀ x, (ψout x : ℂ) * χout x = (ψout x : ℂ))
    (hinput : ∀ x, χsource x * (ψsource x : ℂ) = (ψsource x : ℂ))
    (u : graphTestSpace (d + 1) q) (x : E) :
    (ψout x : ℂ) • retardedPhysicalIntegral Ψ b χout χsource β hs a
        (sourceCutTest ψsource hsource u) x =
      retardedPhysicalIntegral Ψ b (fun y ↦ (ψout y : ℂ))
        (fun y ↦ (ψsource y : ℂ)) β (Complex.ofRealCLM.contDiff.comp hsource) a u x := by
  unfold retardedPhysicalIntegral
  rw [commonSourceMaskTest_eq χsource hs ψsource hsource hinput, ← mul_smul, hout]

/-- The SAME signed retarded operator, localized by the common masks, has the
literal common-mask test action on its actual L² class. The analytic premise
is the output of `SelectedChartEvolutionAt`, including its `PW₁` instance;
no frequency regularization or successful residual equation is assumed.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem retained_retarded_common_masks_test
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (B : E → MetricTensor (d + 1)) (Δ a : ℝ)
    (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (o : ℕ) (A₀ : ℝ) (A : ℕ → ℝ) (Op : H →L[ℂ] H)
    (hOp : RetainedSignedRetardedBounds KQ Q B Δ a Ψ W χout χsource β hs o A₀ A Op)
    (ψout ψsource : E → ℝ) (ho : Continuous ψout) (hsource : ContDiff ℝ ∞ ψsource)
    (hob : ∀ x, ‖ψout x‖ ≤ 1) (hsb : ∀ x, ‖ψsource x‖ ≤ 1)
    (hout : ∀ x, (ψout x : ℂ) * χout x = (ψout x : ℂ))
    (hinput : ∀ x, χsource x * (ψsource x : ℂ) = (ψsource x : ℂ))
    (u : graphTestSpace (d + 1) q) :
    ((sourceCutMultiplier ψout ho hob).comp
      (Op.comp (sourceCutMultiplier ψsource hsource.continuous hsb))) (graphTestToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (retardedPhysicalIntegral Ψ W
          (fun y ↦ (ψout y : ℂ)) (fun y ↦ (ψsource y : ℂ)) β
          (Complex.ofRealCLM.contDiff.comp hsource) a u x) := by
  change sourceCutMultiplier ψout ho hob
    (Op (sourceCutMultiplier ψsource hsource.continuous hsb (graphTestToLp u))) =ᵐ[volume] _
  rw [sourceCutMultiplier_graphTestToLp ψsource hsource hsb u]
  filter_upwards [sourceCutMultiplier_coeFn ψout ho hob
    (Op (graphTestToLp (sourceCutTest ψsource hsource u))),
    (hOp.2.2.2.2.2 (sourceCutTest ψsource hsource u)).1] with x hx hu
  rw [hx, hu]
  exact congrArg (WithLp.toLp 2)
    (retardedPhysicalIntegral_common_masks Ψ W χout χsource β hs a
      ψout ψsource hsource hout hinput u x)

variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- Pull back the common source-support plateau without identifying it with
the local source mask. This is the exact premise exported by
`exists_finite_physical_evolution_data` (`energy-complete-residual`). -/
theorem selected_common_input_mask_plateau
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (χsource : E → ℂ)
    (hp : (physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask ⊆
      interior {y | χsource y = 1}) {y : E} (hy : y ∈ tsupport (chartInputMask f p)) :
    χsource =ᶠ[𝓝 y] fun _ ↦ (1 : ℂ) := by
  have hphys : physicalCoordinates (f.chart p).index y ∈ tsupport f.inputMask :=
    tsupport_comp_subset Complex.ofReal_zero f.inputMask
      (tsupport_comp_subset_preimage (fun z ↦ (f.inputMask z : ℂ))
        (physicalCoordinates (f.chart p).index).continuous hy)
  have hmem := hp ⟨physicalCoordinates (f.chart p).index y, hphys,
    (physicalCoordinates (f.chart p).index).symm_apply_apply y⟩
  filter_upwards [isOpen_interior.mem_nhds hmem] with z hz
  exact interior_subset (s := {y | χsource y = 1}) hz

/-- The original family output is one near the entire smaller output carrier
chosen by `PhysicalConstruction`; equality of the two masks is unnecessary.
Consumer: localization of the three constructed PDO symbols in the complete
residual (`energy-complete-residual`). -/
theorem chartOutputMask_eventuallyEq_one_on_common_output
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hout : tsupport output ⊆ ball x f.physicalRadius)
    {y : E} (hy : y ∈ tsupport (fun z ↦ (output (physicalCoordinates (f.chart p).index z) : ℂ))) :
    chartOutputMask f p =ᶠ[𝓝 y] fun _ ↦ (1 : ℂ) := by
  let e := physicalCoordinates (f.chart p).index
  have hphys : e y ∈ tsupport output :=
    tsupport_comp_subset Complex.ofReal_zero output
      (tsupport_comp_subset_preimage (fun z ↦ (output z : ℂ)) e.continuous hy)
  have hmem := f.outputMask_plateau (ball_subset_closedBall (hout hphys))
  have hg : f.outputMask =ᶠ[𝓝 (e y)] fun _ ↦ (1 : ℝ) := by
    filter_upwards [isOpen_interior.mem_nhds hmem] with z hz
    exact interior_subset (s := {y | f.outputMask y = 1}) hz
  filter_upwards [hg.comp_tendsto e.continuous.continuousAt] with z hz
  change (f.outputMask (e z) : ℂ) = 1
  change f.outputMask (e z) = 1 at hz
  rw [hz, Complex.ofReal_one]

/-- Multiplication of the common output with the original PDO output is
literal absorption, including at the edge of the support
(`energy-complete-residual`). -/
theorem commonOutput_mul_chartOutputMask
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hout : tsupport output ⊆ ball x f.physicalRadius) (y : E) :
    (output (physicalCoordinates (f.chart p).index y) : ℂ) * chartOutputMask f p y =
      (output (physicalCoordinates (f.chart p).index y) : ℂ) := by
  by_cases hy : (output (physicalCoordinates (f.chart p).index y) : ℂ) = 0
  · rw [hy, zero_mul]
  · rw [(chartOutputMask_eventuallyEq_one_on_common_output f p output hout
      (subset_tsupport _ hy)).eq_of_nhds, mul_one]

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
