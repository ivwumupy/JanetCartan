module

public import JanetCartan.Iteration.PhysicalPairs.OriginalCorrectedLag

/-! # Transport of the original source discrepancy estimate

The graph observation and the published source data have separately checked
identities for their field and frequency. This consequence retains the same
uniform constant while passing the closed-core estimate to the named source
discrepancy (`main:eq:primary-strain`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Metric
open scoped ContDiff

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain

/-- The exact field and frequency identities preserve one constant over the
whole source-label family. The actual identities are supplied by the original
construction before this deduction is used for primary strain. -/
theorem point_of_cnorm_of_source_identities {n : ℕ} {ι : Type*}
    (c : Euclidean n) (r : ℝ) (observedFrequency frequency : ι → ℝ)
    (observed field : ι → Euclidean n → Euclidean n)
    (hfield : ∀ t, ContDiff ℝ ∞ (field t)) (q : ℝ)
    (hidentity : ∀ t, observed t = field t)
    (hfrequency : ∀ t, observedFrequency t = frequency t)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
      cNorm (closedBall c r) 0 (observed t) ≤ C * (observedFrequency t)^(-q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ∀ x ∈ closedBall c r,
      ‖field t x‖ ≤ C * (frequency t)^(-q) := by
  apply PhysicalPairs.OriginalCorrectedLag.point_of_cnorm c r frequency field hfield q
  obtain ⟨C,hC,h⟩ := h
  exact ⟨C,hC,fun t ↦ by simpa only [hidentity t,hfrequency t] using h t⟩

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
end

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.point_of_cnorm_of_source_identities
