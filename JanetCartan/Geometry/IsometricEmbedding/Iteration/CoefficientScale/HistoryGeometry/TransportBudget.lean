module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.HistoryGeometry

/-!
# Fixed low immersion budgets for actual transport and carrier amplitudes

For `main:prop:current-scale` and `app:ch_waves:eq:joint-tame`, an admissible
finite history supplies the C12 immersion budget required by
`NullTransport.exists_finite_projected_tame_positive_amplitudes`. The threshold
precedes the initial scale, stage and history. The reference stays fixed.
The uniform-step and coefficient-scale constructions consume this bound along
with the separate geometric gaps from `HistoryGeometry`.

The same fixed-order deduction supplies the C15 immersion budget of
`ContinuumRow.CanonicalCarrier.exists_canonical_primitive_controls`, used in
`app:ch_background:eq:bg-mixed-input`. Initial scalar bounds and actual carrier
geometry remain separate obligations of the continuum-row construction.
-/

@[expose] public noncomputable section

open scoped ContDiff
namespace JanetCartan.HistoryGeometry

/-- For any fixed required low order, `main:eq:displacement-budget` bounds
every actual admissible prefix by the reference seminorm plus one. The order
and reference precede the initial-frequency threshold, which precedes all
histories. Its concrete consumers are the C12 transport and C15 canonical
carrier constructions below. No future increment or correction step is assumed. -/
theorem exists_initialScale_for_fixed_immersion_bound {n N : ℕ} (r : ℕ)
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    (K : Set (Euclidean n)) (hK : IsCompact K) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (r + (n : ℝ) / 2) + 2 < kMin) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean N) (ell : Fin j → ℕ),
      IsAdmissibleHistory R₀ kMin u ell →
        cNorm K r (finiteHistoryMap G u) ≤ cNorm K r G + 1 := by
  obtain ⟨T, hT, hnear⟩ :=
    FiniteHistoryBounds.exists_initialScale_for_prefix_neighborhood
      (F := Euclidean N) r horder (by norm_num : (0 : ℝ) < 1)
  refine ⟨T, hT, ?_⟩
  intro R₀ hR₀ j u ell hu
  have hclose := hnear R₀ hR₀ K G j u (fun i ↦ (ell i : ℝ)) hK
    (fun i ↦ (hu i).2.1) (fun i ↦ (hu i).2.2.1)
    (fun i ↦ (hu i).2.2.2) (fun i ↦ Nat.cast_le.mpr (hu i).1)
  change cNorm K r (finiteHistoryMap G u - G) < 1 / 2 at hclose
  have hF : ContDiff ℝ r (finiteHistoryMap G u) :=
    (hu.contDiff_finiteHistoryMap hG).of_le (by simp)
  have hGr : ContDiff ℝ r G := hG.of_le (by simp)
  calc
    cNorm K r (finiteHistoryMap G u) =
        cNorm K r ((finiteHistoryMap G u - G) + G) := by rw [sub_add_cancel]
    _ ≤ cNorm K r (finiteHistoryMap G u - G) + cNorm K r G :=
      cNorm_add_le hK (hF.sub hGr) hGr
    _ ≤ cNorm K r G + 1 := by linarith

/-- The C12 immersion budget in `app:ch_waves:eq:joint-tame` follows from the
actual Fourier/L2 prefix budgets and `main:eq:displacement-budget`. The bound
is the fixed reference C12 seminorm plus one. No current-map high norm,
transport estimate, future increment or correction step is assumed. -/
theorem exists_initialScale_for_transport_low_bound {n N : ℕ}
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    (K : Set (Euclidean n)) (hK : IsCompact K) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (12 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean N) (ell : Fin j → ℕ),
      IsAdmissibleHistory R₀ kMin u ell →
        cNorm K 12 (finiteHistoryMap G u) ≤ cNorm K 12 G + 1 :=
  exists_initialScale_for_fixed_immersion_bound 12 G hG K hK horder

/-- The C15 immersion premise of
`ContinuumRow.CanonicalCarrier.exists_canonical_primitive_controls` is a
consequence of actual admissible finite histories (`main:prop:current-scale`,
`app:ch_background:eq:bg-mixed-input`). The continuum-row parent must still
construct the initial scalar, its C15 budget, the separate geometric gaps and
all conic/transport inputs for the same reference and history. -/
theorem exists_initialScale_for_carrier_low_bound {n N : ℕ}
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    (K : Set (Euclidean n)) (hK : IsCompact K) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (15 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean N) (ell : Fin j → ℕ),
      IsAdmissibleHistory R₀ kMin u ell →
        cNorm K 15 (finiteHistoryMap G u) ≤ cNorm K 15 G + 1 :=
  exists_initialScale_for_fixed_immersion_bound 15 G hG K hK horder

end JanetCartan.HistoryGeometry
