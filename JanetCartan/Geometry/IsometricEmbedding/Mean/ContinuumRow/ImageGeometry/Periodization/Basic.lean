module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization
public import JanetCartan.Geometry.IsometricEmbedding.Basic

/-!
# Real periodization for the continuum image coefficients

The centered-representative construction in `app:ch_background:defn:bg-row`
uses the existing complex amplitude periodization. Local equality transfers
full physical Fréchet derivatives, including at the faces of the closed cell.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace JanetCartan.ContinuumRow.ImageGeometry.Periodization

variable {n : ℕ}

/-- Literal real centered-representative formula for the coefficient extension
in `app:ch_background:defn:bg-row`. -/
def realPeriodization (f : Euclidean n → ℝ) : Torus n → ℝ :=
  f ∘ AmplitudeBound.centeredTorusRepresentative

/-- Local equality on the entire cell for the real coefficient extension
in `app:ch_background:defn:bg-row`. -/
theorem realPeriodization_eventuallyEq {r : ℝ} (hr : r < 1 / 2)
    {f : Euclidean n → ℝ} (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r})
    {x : Euclidean n} (hx : x ∈ fundamentalCell n) :
    periodicLift (realPeriodization f) =ᶠ[𝓝 x] f := by
  have hs' : AmplitudeBound.SupportedInCenteredBox r (fun y ↦ (f y : ℂ)) := by
    intro y hy
    apply hs (subset_tsupport f ?_)
    intro h
    exact hy (by simp [h])
  exact (AmplitudeBound.periodicLift_amplitudePeriodization_eventuallyEq hr hs' hx).mono
    fun _ hy ↦ Complex.ofReal_injective hy

/-- Smoothness of real periodization, deduced from complex amplitude periodization
for `app:ch_background:defn:bg-row`. -/
theorem isSmoothPeriodic_realPeriodization {r : ℝ} (hr : r < 1 / 2)
    {f : Euclidean n → ℝ} (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r})
    (hf : ContDiff ℝ ∞ f) : IsSmoothPeriodic (realPeriodization f) := by
  have hs' : AmplitudeBound.SupportedInCenteredBox r (fun y ↦ (f y : ℂ)) := by
    intro y hy
    apply hs (subset_tsupport f ?_)
    intro h
    exact hy (by simp [h])
  have h := AmplitudeBound.isSmoothPeriodic_amplitudePeriodization hr hs'
    (Complex.ofRealCLM.contDiff.comp hf)
  exact ⟨Complex.continuous_re.comp h.1, Complex.reCLM.contDiff.comp h.2⟩

/-- Every full physical derivative bound survives real periodization with its
original constant (`app:ch_background:eq:bg-frame-tame`). -/
theorem norm_iteratedFDeriv_realPeriodization_le {r : ℝ} (hr : r < 1 / 2)
    {f : Euclidean n → ℝ} (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r})
    (m : ℕ) {A : ℝ} (hA : ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ A) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ m (periodicLift (realPeriodization f)) x‖ ≤ A := by
  apply norm_iteratedFDeriv_periodicLift_le
  intro y hy
  rw [((realPeriodization_eventuallyEq hr hs hy).iteratedFDeriv ℝ m).self_of_nhds]
  exact hA y

end JanetCartan.ContinuumRow.ImageGeometry.Periodization
