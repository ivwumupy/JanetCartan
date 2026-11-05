module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.HistoryGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ScaleGap

/-!
# Actual history inputs for coefficient profiles

The consumers are the geometric, phase and transport profiles in
`main:prop:current-scale`. The Bernstein estimate, smoothness and compact jet
containment are proved for the literal admissible prefix. No future increment
or coefficient estimate is an input.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.ProjectedStressFrame

namespace JanetCartan.CurrentCoefficientProfiles

/-- `main:eq:history-current`: the proved periodic Bernstein estimate supplies
the profile of every admissible finite history on any subset of a fixed compact
set. Constants precede the scale, stage, prefix and requested derivative order.
This is the map input to the actual coefficient transfers below. -/
theorem exists_admissible_history_profile {n N : ℕ}
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    {K : Set (Euclidean n)} (hK : IsCompact K) (rStar kMin : ℕ)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ A : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧ ∀ R₀, 2 ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean N) (ell : Fin j → ℕ),
      IsAdmissibleHistory R₀ kMin u ell → ∀ W ⊆ K,
        HasDerivativeProfile W (finiteHistoryMap G u) rStar
          (currentCoefficientScale R₀ j) A := by
  obtain ⟨A, hA, hprofile⟩ := FiniteHistoryBounds.exists_prefix_derivative_profile hK
    (fun _ _ ↦ hG.contDiffAt) rStar horder
  refine ⟨A, hA, ?_⟩
  intro R₀ hR₀ j u ell hu W hWK
  exact hprofile R₀ hR₀ j u (fun i ↦ (ell i : ℝ))
    (fun i ↦ (hu i).2.1) (fun i ↦ (hu i).2.2.1)
    (fun i ↦ (hu i).2.2.2) (fun i ↦ Nat.cast_le.mpr (hu i).1) W hWK

/-- `main:prop:current-scale`: actual history jets lie in one compact subset
of BOTH geometric unit loci. The set and initial-scale threshold precede every
prefix and every high order. This discharges compact-range assumptions in the
finite-jet coefficient bounds, keeping the selected reference unchanged. -/
theorem exists_admissible_history_jet_range {n : ℕ} (G : FlatReference n)
    {R : ℝ} (hR : R < G.domain.chartRadius) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ L : Set (StressJet n (embeddingDimension n)), IsCompact L ∧
      (∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) ∧
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
          (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
        Set.MapsTo (stressJet (finiteHistoryMap G.map u)) (Metric.closedBall 0 R) L := by
  obtain ⟨d, hd, L, hL, hunit, hnear⟩ :=
    CurrentGeometricNeighborhood.exists_reference_jet_neighborhood G hR
  obtain ⟨S, hS, hclose⟩ := HistoryGeometry.exists_initialScale_for_c8_neighborhood
    G.map R horder (half_pos hd)
  refine ⟨L, hL, hunit, S, hS, ?_⟩
  intro R₀ hR₀ j u ell hu x hx
  apply hnear x hx
  have hb := CurrentGeometricNeighborhood.norm_stressJet_sub_le
    (isCompact_closedBall (0 : Euclidean n) R) isOpen_univ (Set.subset_univ _)
    (hu.contDiff_finiteHistoryMap G.contDiff).contDiffOn G.contDiff.contDiffOn hx
  have hc := hclose R₀ hR₀ j u ell hu
  exact hb.trans (by linarith)

end JanetCartan.CurrentCoefficientProfiles
