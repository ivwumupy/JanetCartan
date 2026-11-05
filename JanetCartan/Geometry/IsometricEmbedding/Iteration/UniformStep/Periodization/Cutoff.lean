module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.Periodization.Norms
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.Extension

/-!
# The fixed physical cutoff and exact core jets

`main:thm:step` uses cut fields whose cutoff equals one near the core. The
cutoff, its support gap and its neighborhood are fixed inputs. All local jet
identities below are deductions, not additional inputs to the construction.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.UniformStep.Periodization

variable {n N : ℕ}

/-- The same physical cut field used for both the metric ledger and the
physical norm profile (`main:thm:step`, `main:eq:joint-physical-profile`). -/
def cutField (χ : Euclidean n → ℝ) (f : Euclidean n → Euclidean N) :
    Euclidean n → Euclidean N := fun x ↦ χ x • f x

/-- The concrete periodic correction from the physical cut field
(`main:thm:step`). -/
def cutToTorus (χ : Euclidean n → ℝ) (f : Euclidean n → Euclidean N) :
    Torus n → Euclidean N := vectorPeriodization (cutField χ f)

/-- Multiplication by the fixed cutoff gives the required support gap
(`main:thm:step`). -/
theorem tsupport_cutField_subset (χ : Euclidean n → ℝ) (f : Euclidean n → Euclidean N) :
    tsupport (cutField χ f) ⊆ tsupport χ := tsupport_smul_subset_left χ f

/-- Smoothness of the actual cut field (`main:eq:joint-physical-profile`). -/
theorem contDiff_cutField {χ : Euclidean n → ℝ} {f : Euclidean n → Euclidean N}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cutField χ f) :=
  hχ.smul hf

/-- Smooth periodicity is proved from the physical smoothness and the fixed
cutoff support, as required by `StageConstants.Identities` (`main:thm:step`). -/
theorem isSmoothPeriodic_cutToTorus {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    (hχ : ContDiff ℝ ∞ χ) {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) :
    IsSmoothPeriodic (cutToTorus χ f) :=
  isSmoothPeriodic_vectorPeriodization hr ((tsupport_cutField_subset χ f).trans hs)
    (contDiff_cutField hχ hf)

/-- The lift agrees with the uncut field on a neighborhood of each core point
(`main:eq:metric-ledger`), including points on the closed core boundary. -/
theorem cutToTorus_eventuallyEq (D : LocalDomain) {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    {U : Set (Euclidean n)} (hU : IsOpen U) (hcore : D.core n ⊆ U)
    (hone : EqOn χ (fun _ ↦ 1) U) (f : Euclidean n → Euclidean N)
    {x : Euclidean n} (hx : x ∈ D.core n) :
    periodicLift (cutToTorus χ f) =ᶠ[𝓝 x] f := by
  apply (vectorPeriodization_eventuallyEq hr ((tsupport_cutField_subset χ f).trans hs)
    (DefectSmoothing.core_subset_fundamentalCell D hx)).trans
  filter_upwards [hU.mem_nhds (hcore hx)] with y hy
  simp [cutField, hone hy]

/-- Every physical ambient jet is unchanged on the core (`main:eq:metric-ledger`). -/
theorem iteratedFDeriv_cutToTorus_eqOn (D : LocalDomain) {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    {U : Set (Euclidean n)} (hU : IsOpen U) (hcore : D.core n ⊆ U)
    (hone : EqOn χ (fun _ ↦ 1) U) (f : Euclidean n → Euclidean N) (j : ℕ) :
    EqOn (iteratedFDeriv ℝ j (periodicLift (cutToTorus χ f)))
      (iteratedFDeriv ℝ j f) (D.core n) := fun _ hx ↦
  ((cutToTorus_eventuallyEq D hr hs hU hcore hone f hx).iteratedFDeriv ℝ j).self_of_nhds

/-- First derivatives transfer without any jet-agreement hypothesis;
this is the strain input to `main:eq:metric-ledger`. -/
theorem fderiv_cutToTorus_eqOn (D : LocalDomain) {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    {U : Set (Euclidean n)} (hU : IsOpen U) (hcore : D.core n ⊆ U)
    (hone : EqOn χ (fun _ ↦ 1) U) (f : Euclidean n → Euclidean N) :
    EqOn (fderiv ℝ (periodicLift (cutToTorus χ f))) (fderiv ℝ f) (D.core n) :=
  fun _ hx ↦ (cutToTorus_eventuallyEq D hr hs hU hcore hone f hx).fderiv_eq

/-- Exact linearized strain transfer for both the mean and pair fields
in `main:eq:metric-ledger`. -/
theorem linearizedMetric_cutToTorus_eqOn (D : LocalDomain) {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    {U : Set (Euclidean n)} (hU : IsOpen U) (hcore : D.core n ⊆ U)
    (hone : EqOn χ (fun _ ↦ 1) U) (F f : Euclidean n → Euclidean N) :
    EqOn (linearizedMetric F (periodicLift (cutToTorus χ f)))
      (linearizedMetric F f) (D.core n) := by
  intro x hx
  unfold linearizedMetric partialDeriv
  rw [fderiv_cutToTorus_eqOn D hr hs hU hcore hone f hx]

/-- Exact quadratic metric transfer for the primary field
in `main:eq:metric-ledger`. -/
theorem inducedMetric_cutToTorus_eqOn (D : LocalDomain) {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    {U : Set (Euclidean n)} (hU : IsOpen U) (hcore : D.core n ⊆ U)
    (hone : EqOn χ (fun _ ↦ 1) U) (f : Euclidean n → Euclidean N) :
    EqOn (inducedMetric (periodicLift (cutToTorus χ f))) (inducedMetric f) (D.core n) := by
  intro x hx
  unfold inducedMetric partialDeriv
  rw [fderiv_cutToTorus_eqOn D hr hs hU hcore hone f hx]

/-- The fixed cutoff and representative are additive (`main:thm:step`). -/
theorem cutToTorus_add (χ : Euclidean n → ℝ) (f g : Euclidean n → Euclidean N) :
    cutToTorus χ (f + g) = cutToTorus χ f + cutToTorus χ g := by
  funext z
  exact smul_add _ _ _

/-- The same physical cutoff commutes with constant real amplitudes
(`main:thm:step`). -/
theorem cutToTorus_smul (χ : Euclidean n → ℝ) (a : ℝ) (f : Euclidean n → Euclidean N) :
    cutToTorus χ (a • f) = a • cutToTorus χ f := by
  funext z
  change χ _ • (a • f _) = a • (χ _ • f _)
  exact smul_comm _ _ _

/-- Exact L² norm of the actual cut field used by `StageConstants.ComponentEstimates`
(`main:eq:step-L2`). -/
theorem periodicL2Norm_cutToTorus {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    (f : Euclidean n → Euclidean N) :
    periodicL2Norm (cutToTorus χ f) = Real.sqrt (∫ x, ‖cutField χ f x‖ ^ 2) :=
  periodicL2Norm_vectorPeriodization hr ((tsupport_cutField_subset χ f).trans hs)

/-- Integer Sobolev bound from the identical cut physical field, with no
additional scale loss (`main:eq:joint-physical-profile`). -/
theorem periodicSobolevNorm_cutToTorus_le {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    (hχ : ContDiff ℝ ∞ χ) {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    periodicSobolevNorm m (cutToTorus χ f) ≤ Real.sqrt (m.factorial : ℝ) *
      LocalSobolev.cartesianJetNorm univ m (fun j ↦ iteratedFDeriv ℝ j (cutField χ f)) :=
  periodicSobolevNorm_vectorPeriodization_le hr ((tsupport_cutField_subset χ f).trans hs)
    (contDiff_cutField hχ hf) m

end JanetCartan.UniformStep.Periodization
