module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredSupport
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.Periodization

/-!
# Periodize the same common physical measurement

The final application uses the common original current stress measurement, not
a row-dependent choice. Its physical cutoff already supplies the support gap;
no further cutoff is inserted (`app:ch_mean_pairs:defn:mean-canonical`).
Consumer: the actual measured raw-row identity and the canonical mean source.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalMeasurement
open AmplitudeBound

variable {n : ℕ}

/-- The actual common physical measurement at centered representatives, without
another multiplier (`app:ch_mean_pairs:defn:mean-canonical`). -/
def nativeMeasurement (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n) :
    Torus n → MetricTensor n →L[ℝ] Euclidean n :=
  C ∘ centeredTorusRepresentative

/-- Smoothness comes from the SAME compact physical measurement. The actual
original-data application supplies both certificates, without a new selection. -/
theorem nativeMeasurement_smooth
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n)
    (hC : ContDiff ℝ ∞ C) {b : ℝ} (hcell : b < 1/2)
    (hs : tsupport C ⊆ {x | ∀ i, |x i| ≤ b}) :
    IsSmoothPeriodic (nativeMeasurement C) := by
  have hslice (H : MetricTensor n) :
      IsSmoothPeriodic (fun z ↦ C (centeredTorusRepresentative z) H) := by
    have hsH : tsupport (fun x ↦ C x H) ⊆ {x | ∀ i, |x i| ≤ b} := by
      apply Subset.trans _ hs
      apply closure_minimal _ isClosed_closure
      intro x hx
      apply subset_tsupport C
      intro h
      exact hx (by simp [h])
    exact UniformStep.Periodization.isSmoothPeriodic_vectorPeriodization hcell hsH
      (hC.clm_apply contDiff_const)
  have hd : ContDiff ℝ ∞ (periodicLift (nativeMeasurement C)) := by
    apply contDiff_clm_apply_iff.mpr
    intro H
    exact (hslice H).2
  have hq : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      QuotientAddGroup.isOpenQuotientMap_mk)).comp
        (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  exact ⟨hq.isQuotientMap.continuous_iff.mpr hd.continuous, hd⟩

/-- The periodic measurement is literally the physical measurement at every
centered representative, including chart boundaries. -/
theorem nativeMeasurement_apply
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n) (z : Torus n) :
    nativeMeasurement C z = C (centeredTorusRepresentative z) := rfl

end JanetCartan.PhysicalMean.OriginalCanonicalMeasurement
end
