module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.DensityCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.HistoryGeometry.TransportBudget
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.HistoryGeometry

/-!
# The fixed map budget for the actual density carrier along histories

The uniform L² carrier construction uses the fixed order `2(n+1)+14`, rather
than C15 alone. Apply the existing arbitrary-fixed-order history producer at
that exact order. The same smooth reference and compact coefficient domain
are retained; the frequency threshold precedes every history.
-/

@[expose] public noncomputable section
open scoped ContDiff

namespace JanetCartan.ContinuumRow.CanonicalCarrier

/-- The literal finite history supplies the entire low map budget of
`exists_actual_density_carrier`, including the PDO source reserve. The
reference is unchanged and no high norm of the current map is assumed
(`main:eq:displacement-budget`, `app:ch_background:prop:bg-frame`, Step 1).
Separate frame and geometric gaps still require the same initialized
reference neighborhood. -/
theorem exists_initialScale_for_density_carrier_budget {n N : ℕ}
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    (K : Set (Euclidean n)) (hK : IsCompact K) {kMin : ℕ}
    (horder : displacementLoss n +
      bandExponent * ((canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean N) (ell : Fin j → ℕ),
      IsAdmissibleHistory R₀ kMin u ell →
        cNorm K (canonicalCarrierLowOrder n) (finiteHistoryMap G u) ≤
          cNorm K (canonicalCarrierLowOrder n) G + 1 :=
  HistoryGeometry.exists_initialScale_for_fixed_immersion_bound
    (canonicalCarrierLowOrder n) G hG K hK horder

/-- One threshold supplies both varying-map norm inputs of
`exists_finite_actual_density_row`, for the SAME actual finite history: its
complete carrier low order and its image C8 neighborhood on every chosen
measurement chart. The threshold even precedes the image chart radius. Frame
compatibility and the separate geometric gaps remain with initialization
(`main:eq:displacement-budget`, `app:ch_background:defn:bg-row`). -/
theorem exists_initialScale_for_row_map_inputs {n N : ℕ}
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    (K : Set (Euclidean n)) (hK : IsCompact K) {kMin : ℕ}
    (horder : displacementLoss n +
      bandExponent * ((canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2 < kMin)
    {δimage : ℝ} (hδimage : 0 < δimage) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean N) (ell : Fin j → ℕ),
      IsAdmissibleHistory R₀ kMin u ell →
        ContDiff ℝ ∞ (finiteHistoryMap G u) ∧
        cNorm K (canonicalCarrierLowOrder n) (finiteHistoryMap G u) ≤
          cNorm K (canonicalCarrierLowOrder n) G + 1 ∧
        ∀ b : ℝ, cNorm (Metric.closedBall 0 (6 * b)) 8 (finiteHistoryMap G u - G) < δimage := by
  have h8 : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin := by
    have hlow : (8 : ℝ) ≤ canonicalCarrierLowOrder n := by
      exact_mod_cast (show 8 ≤ canonicalCarrierLowOrder n by
        unfold canonicalCarrierLowOrder
        omega)
    have hband : (0 : ℝ) ≤ bandExponent := by norm_num [bandExponent]
    exact lt_of_le_of_lt (by gcongr) horder
  obtain ⟨Tcarrier, hTcarrier, hcarrier⟩ :=
    exists_initialScale_for_density_carrier_budget G hG K hK horder
  obtain ⟨Timage, hTimage, himage⟩ :=
    FiniteHistoryBounds.exists_initialScale_for_prefix_neighborhood
      (F := Euclidean N) 8 h8 hδimage
  refine ⟨max Tcarrier Timage, hTcarrier.trans (le_max_left _ _), ?_⟩
  intro R₀ hR₀ j u ell hu
  refine ⟨hu.contDiff_finiteHistoryMap hG,
    hcarrier R₀ ((le_max_left _ _).trans hR₀) j u ell hu, ?_⟩
  intro b
  have hh := himage R₀ ((le_max_right _ _).trans hR₀)
    (Metric.closedBall 0 (6 * b)) G j u (fun i ↦ (ell i : ℝ))
    (isCompact_closedBall _ _) (fun i ↦ (hu i).2.1) (fun i ↦ (hu i).2.2.1)
    (fun i ↦ (hu i).2.2.2) (fun i ↦ Nat.cast_le.mpr (hu i).1)
  exact hh.trans (half_lt_self hδimage)

end JanetCartan.ContinuumRow.CanonicalCarrier
