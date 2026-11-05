module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.Construction.InitializedAnalyticData.RawCaps

/-!
# Identifying the raw cap on the original selected cell

The prescribed common initializer is called with the minimum of the user's
extra cap and `retainedIncidenceCurrentRawCap`. Its selected-cell membership
identifies the latter with the exact cap required by the history inverse.
Consumer: `exists_common_initializer_with_capped_history_inverse`, specifically
its `hcap` argument to `exists_capped_source_history_inverse_from_original_leading`.
This is a deduction on the supplied cell, not a second initializer selection
(`app:ch_background:prop:bg-adjoint`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse.InitializedCappedHistory
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow
open ContinuumRow.CanonicalConic

/-- Selected-cell membership turns the original incidence raw cap into the
literal supplied-geometry cap. Both the arbitrary user cap and the inverse cap
are retained; no normal/adjoint estimate is postulated. -/
theorem selected_raw_cap_le
    {n : ℕ} {D : CoverData n} {c C : ℝ}
    (hn : 0 < n) (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches b l) U hU)
    (I : (b : Fin D.chartCount) → Fin (D.patchCount b) → Type*)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ b l, closedBall (0 : Euclidean n) (T b l).data.localReference.stateRadius ⊆ K)
    (Kinitial : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) →
      I b l → Set (Euclidean (n - 1) × Euclidean 3))
    (Jfull : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) →
      I b l → Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
    (hJfull : ∀ b l j, IsCompact (Jfull b l j))
    (E : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) →
      I b l → Set (Euclidean n × CarrierParameter))
    (hE : ∀ b l j, IsOpen (E b l j))
    (hgraph : ∀ b l j, MapsTo (LeadingPrimitive.carrierGraph (T b l))
      (E b l j) (Jfull b l j))
    (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) (j : I p.1.1 l)
    (hmem : ContinuumAdjoint.Canonical.AmplitudeProfiles.chartCenter (D.roots p.1.1 l p.1.2) ∈ E p.1.1 l j)
    {a userCap : ℝ}
    (ha : a ≤ min userCap
      (InitializedAnalyticData.retainedIncidenceCurrentRawCap hn hD T I hK hKU hball
        Kinitial Jfull hJfull E hE hgraph p l j).val) :
    a ≤ userCap ∧
      a ≤ (exists_current_rawAdjoint_cap_on_supplied_geometry (N := embeddingDimension n)
        hn (hD.2.2.2.2.1 p.1.1 l).1 (T p.1.1 l) hK hKU (hball p.1.1 l)
        (Kinitial p.1.1 l j) (hJfull p.1.1 l j) (E p.1.1 l j) (hE p.1.1 l j)
        (hgraph p.1.1 l j)
        ((hD.2.2.2.2.1 p.1.1 l).2.2.1 p.1.2 p.2.2).1 hmem).choose := by
  refine ⟨ha.trans (min_le_left _ _), ?_⟩
  have hraw := ha.trans (min_le_right _ _)
  simpa only [InitializedAnalyticData.retainedIncidenceCurrentRawCap, dite_eq_left hmem] using hraw

end JanetCartan.ContinuumInverse.InitializedCappedHistory
