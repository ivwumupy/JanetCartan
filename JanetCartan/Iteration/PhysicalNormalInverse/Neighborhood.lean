module

public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.DensityCarrier

/-!
# Physical histories in the retained normal-comparison neighborhood

For `app:ch_background:prop:bg-frame` and `main:eq:displacement-budget` in
`paper-v2.tex`, the actual physical Schwartz prefix enters the finite collection
of neighborhoods used by the full-amplitude carrier comparison.  The reserve
and the displacement loss are the literal revised ones.  The global increments
are never periodized.

Consumer: `PhysicalNormalInverse.exists_initialScale_for_realized_retained_history_coercivity`.
-/

@[expose] public noncomputable section

namespace JanetCartan.PhysicalNormalInverse

open ContinuumRow CanonicalCarrier

/-- The finite full-amplitude normal-comparison reserve is supplied by the
physical history estimate, with one threshold before every prefix and compact
measurement set.  This closes the immersion-smallness input of
`exists_finite_realized_retained_density_normal_comparison`, not an assumed
history coercivity conclusion. -/
theorem exists_initialScale_for_retained_normal_comparison_neighborhood
    {n N : ℕ} {ι : Type*} [Fintype ι]
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) {B : ℝ} (hB : 1 ≤ B)
    {rStar kMin : ℕ} (hStar : canonicalCarrierLowOrder n ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (G : Euclidean n → Euclidean N) (K : ι → Set (Euclidean n)),
      (∀ i, IsCompact (K i)) →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) (ell : Fin j → ℕ),
      RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell → ∀ i,
        cNorm (K i) (max 8 (max 1 (2 * (n + 1)) + 6))
          (RevisedGlobal.finiteMap G u - G) < δ i := by
  obtain ⟨ε, hε, hεδ⟩ := Pi.exists_forall_pos_add_lt hδ
  obtain ⟨S, hS, hnear⟩ := PhysicalHistory.exists_initialScale_for_prefix_neighborhood
    (N := N) hB horder hε
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ G K hK j u ell hu i
  have hclose := hnear R₀ hR₀ (K i) G (hK i) j u ell hu
  have hreserve : max 8 (max 1 (2 * (n + 1)) + 6) ≤ rStar := by
    unfold canonicalCarrierLowOrder at hStar
    omega
  exact ((cNorm_mono_order hreserve).trans_lt hclose).trans
    ((half_lt_self hε).trans (by simpa only [zero_add] using hεδ i))

end JanetCartan.PhysicalNormalInverse
