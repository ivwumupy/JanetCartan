module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.Periodization
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Supported
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The fixed physical cutoff for the uniform step

In `main:thm:step` every physical correction uses this one cutoff, chosen from
the working domain before accuracy, target dilation and finite history. The
periodization adapter supplies the exact core jets of the resulting fields.
This constructs the cutoff, not the wave, mean or pair fields.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.UniformStep

/-- The accepted physical cutoff in `main:thm:step`, with a plateau strictly
larger than the closed core and support strictly inside the working chart. -/
def physicalCutoff {n : ℕ} (D : LocalDomain) : ContDiffBump (0 : Euclidean n) where
  rIn := (2 * D.coreRadius + D.chartRadius) / 3
  rOut := (D.coreRadius + 2 * D.chartRadius) / 3
  rIn_pos := by linarith [D.coreRadius_pos, D.coreRadius_lt_chartRadius]
  rIn_lt_rOut := by linarith [D.coreRadius_lt_chartRadius]

/-- The fixed cutoff meets every support and plateau premise of
`Periodization.identities_fields` (`main:eq:metric-ledger`). -/
theorem physicalCutoff_properties {n : ℕ} (D : LocalDomain) :
    ContDiff ℝ ∞ (physicalCutoff (n := n) D) ∧
    tsupport (physicalCutoff (n := n) D) ⊆ D.chart n ∧
    tsupport (physicalCutoff (n := n) D) ⊆
      {x | ∀ i, |x i| ≤ D.chartRadius} ∧
    D.core n ⊆ ball (0 : Euclidean n) (physicalCutoff (n := n) D).rIn ∧
    EqOn (physicalCutoff (n := n) D) (fun _ ↦ 1)
      (ball (0 : Euclidean n) (physicalCutoff (n := n) D).rIn) := by
  have hout : (physicalCutoff (n := n) D).rOut < D.chartRadius := by
    dsimp [physicalCutoff]
    linarith [D.coreRadius_lt_chartRadius]
  have hsupport : tsupport (physicalCutoff (n := n) D) ⊆ D.chart n := by
    rw [(physicalCutoff (n := n) D).tsupport_eq]
    exact closedBall_subset_ball hout
  refine ⟨(physicalCutoff D).contDiff, hsupport, ?_, ?_, ?_⟩
  · intro x hx i
    have hnorm : ‖x‖ < D.chartRadius := by simpa [LocalDomain.chart] using hsupport hx
    exact (PiLp.norm_apply_le x i).trans hnorm.le
  · apply closedBall_subset_ball
    dsimp [physicalCutoff]
    linarith [D.coreRadius_lt_chartRadius]
  · intro x hx
    exact (physicalCutoff D).one_of_mem_closedBall (ball_subset_closedBall hx)

/-- The retained corrected atoms are smooth on their original chart
(`app:ch_response:cor:current-atoms`). The SAME fixed physical cutoff makes
each such field globally smooth, by the existing chart-extension theorem.
This supplies the regularity needed by
`physicalCutoff_periodization_of_contDiffOn` without assuming a global raw
atom or choosing another cutoff (`main:thm:step`). -/
theorem contDiff_physicalCutoff_smul_of_contDiffOn {n : ℕ} (D : LocalDomain)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Euclidean n → E} (hf : ContDiffOn ℝ ∞ f (D.chart n)) :
    ContDiff ℝ ∞ (fun x ↦ physicalCutoff D x • f x) := by
  obtain ⟨hχ, hs, _, _, _⟩ := physicalCutoff_properties (n := n) D
  exact PrimarySourceAdmission.contDiff_cutoff_of_support_subset hχ isOpen_ball hf hs

/-- `main:thm:step`: a physical field smooth on the working chart gives the
same globally smooth periodic cutoff, with all core jets unchanged. This
matches the actual local regularity of the retained corrected atoms and is
consumed by `identities_sampled_history_fields_of_contDiffOn`. -/
theorem physicalCutoff_periodization_of_contDiffOn {n N : ℕ} (D : LocalDomain)
    {f : Euclidean n → Euclidean N} (hf : ContDiffOn ℝ ∞ f (D.chart n)) :
    IsSmoothPeriodic (Periodization.cutToTorus (physicalCutoff D) f) ∧
    ∀ j : ℕ, EqOn
      (iteratedFDeriv ℝ j (periodicLift (Periodization.cutToTorus (physicalCutoff D) f)))
      (iteratedFDeriv ℝ j f) (D.core n) := by
  obtain ⟨_, _, hs, hcore, hone⟩ := physicalCutoff_properties (n := n) D
  refine ⟨Periodization.isSmoothPeriodic_vectorPeriodization D.chartRadius_lt_half
    ((Periodization.tsupport_cutField_subset _ f).trans hs)
    (contDiff_physicalCutoff_smul_of_contDiffOn D hf), ?_⟩
  exact fun j ↦ Periodization.iteratedFDeriv_cutToTorus_eqOn D D.chartRadius_lt_half hs
    isOpen_ball hcore hone f j

/-- `main:thm:step`: the concrete cutoff and existing periodization give a
smooth torus field with every physical jet unchanged on the closed core.
The physical field itself must still be constructed by its analytic producer. -/
theorem physicalCutoff_periodization {n N : ℕ} (D : LocalDomain)
    {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ ∞ f) :
    IsSmoothPeriodic (Periodization.cutToTorus (physicalCutoff D) f) ∧
    ∀ j : ℕ, EqOn
      (iteratedFDeriv ℝ j (periodicLift (Periodization.cutToTorus (physicalCutoff D) f)))
      (iteratedFDeriv ℝ j f) (D.core n) := by
  obtain ⟨hχ, _, hs, hcore, hone⟩ := physicalCutoff_properties (n := n) D
  exact ⟨Periodization.isSmoothPeriodic_cutToTorus D.chartRadius_lt_half hs hχ hf,
    fun j ↦ Periodization.iteratedFDeriv_cutToTorus_eqOn D D.chartRadius_lt_half hs
      isOpen_ball hcore hone f j⟩

end JanetCartan.UniformStep
