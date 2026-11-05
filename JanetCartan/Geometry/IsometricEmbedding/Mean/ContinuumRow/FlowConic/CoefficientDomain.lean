module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelCoefficients

/-!
# Fit the entire coefficient domain inside the actual flow neighborhood

The incidence radius and physical radius must both be controlled. These
lemmas supply the caps consumed by `exists_actual_refined_supported_geometry_in_open`.
The product neighborhood is exactly the one constructed by
`CanonicalCarrier.exists_actual_canonical_primitive_controls`.
-/

@[expose] public noncomputable section
open Set Metric
namespace JanetCartan.ContinuumRow.FlowConic
open CanonicalConic CanonicalCarrier FullPhaseCharts.ActualComparison
open ContinuumNormalReduction.TransportSymbol

variable {n : ℕ}

/-- Both radii control the entire normal/detector evaluation domain in the
actual flow product, not just the finite norm chart (`app:ch_background:eq:bg-mixed-input`). -/
theorem coefficientDomain_subset_flowProduct (z₀ : Euclidean 3)
    {r a ε : ℝ} (hr : r ≤ ε) (ha : a ≤ ε) :
    coefficientDomain (n := n) z₀ r a ⊆
      ball (0 : Euclidean n) ε ×ˢ ball (z₀ 0, spectatorCenter z₀) ε := by
  intro p hp
  refine ⟨ball_subset_ball ha hp.1, ?_⟩
  rw [← ball_prod_same]
  exact ⟨ball_subset_ball hr hp.2.1, ball_subset_ball ha hp.2.2⟩

/-- An open neighborhood of the incidence center supplies a common positive
cap for both coefficient radii. Consumer: the capped actual conic geometry
for `app:ch_background:eq:bg-Psi` and `bg-mixed-input`. -/
theorem exists_coefficientDomain_cap (z₀ : Euclidean 3)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ E) :
    ∃ ε > (0 : ℝ), ∀ {r a : ℝ}, r ≤ ε → a ≤ ε →
      coefficientDomain (n := n) z₀ r a ⊆ E := by
  obtain ⟨ε, hε, hεE⟩ := Metric.mem_nhds_iff.mp (hE.mem_nhds hcenter)
  refine ⟨ε, hε, fun hr ha ↦ ?_⟩
  exact (coefficientDomain_subset_flowProduct z₀ hr ha).trans
    (by simpa only [ball_prod_same] using hεE)

end JanetCartan.ContinuumRow.FlowConic
