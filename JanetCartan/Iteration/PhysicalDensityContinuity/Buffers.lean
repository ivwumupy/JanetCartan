module

public import JanetCartan.Iteration.PhysicalBackground.MeanProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.Masks
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms

/-!
# Original physical product for the entire external-weight collar

The external weight is one on the detector support, so its support extends
outside that detector support. The original physical plateau and product
geometry place the six-radius physical ball in the ORIGINAL physical product,
for every label of its open carrier cell. No weight or carrier is reselected.
Consumer: the actual mean term in `app:ch_background:prop:bg-current`.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.PhysicalDensityContinuity

open ContinuumRow CanonicalConic ContinuumNormalReduction.TransportSymbol

/-- The original `6 * μ < rᵢ` margin controls the physical factor of the entire
selected product cell, including the external-weight collar outside the
original detector support. -/
theorem original_density_mean_product
    {n : ℕ} {ι : Type*} (D : ι → CoefficientNormCharts n)
    (zRoot : ι → Euclidean 3) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {μ : ℝ} (hμr : ∀ i, 6 * μ < r i)
    {Rphysical : ι → ℝ} {V : ι → Set CarrierParameter}
    (hDregion : ∀ i, (D i).field.region ⊆ ball (0 : Euclidean n) (Rphysical i) ×ˢ V i)
    (hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (hr i) 1) ×ˢ
      carrierSupport (zRoot i) (r := r i) ⊆ (D i).field.carrier) :
    ∀ i, closedBall (0 : Euclidean n) (6 * μ) ×ˢ V i ⊆
      ball (0 : Euclidean n) (Rphysical i) ×ˢ V i := by
  intro i p hp
  have hx : p.1 ∈ closedBall (0 : Euclidean n) (((1 : Fin 3).val + 1 : ℝ) * r i) :=
    (closedBall_subset_closedBall (by norm_num; linarith [hμr i, hr i])) hp.1
  have he : FixedCutoffs.physical (hr i) 1 p.1 = 1 :=
    (interior_subset (s := {x : Euclidean n | FixedCutoffs.physical (hr i) 1 x = 1}))
      (FixedCutoffs.physical_plateau (hr i) 1 hx)
  have hxs : p.1 ∈ tsupport (FixedCutoffs.physical (n := n) (hr i) 1) := by
    apply subset_tsupport
    change FixedCutoffs.physical (hr i) 1 p.1 ≠ 0
    rw [he]
    norm_num
  have hz : ((zRoot i) 0, FullPhaseCharts.ActualComparison.spectatorCenter (zRoot i)) ∈
      carrierSupport (zRoot i) (r := r i) :=
    ⟨mem_closedBall_self (half_pos (hr i)).le, mem_closedBall_self (half_pos (hr i)).le⟩
  have hpair : (p.1, ((zRoot i) 0, FullPhaseCharts.ActualComparison.spectatorCenter (zRoot i))) ∈
      (D i).field.carrier := hsupportD i ⟨hxs, hz⟩
  have hregion := hDregion i ((D i).field.ball_subset hpair)
  exact ⟨hregion.1, hp.2⟩

end JanetCartan.PhysicalDensityContinuity
