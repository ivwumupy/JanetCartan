module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RadialNormDomains
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.CommonTarget

/-!
# Matching the supplied radial input range to the original carrier cone

The common normalized inverse extends frequency only. Its whole range stays
inside the original carrier input cone whenever the local buffer does.
-/

open Set
open scoped ContDiff
@[expose] public noncomputable section
namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ContinuumNormalReduction TransportSymbol ConicChart
open ContinuumRow CanonicalConic NormalizedSelection

/-- The original carrier input cone contains the full radial extension of
any retained input buffer inside it. Only frequency changes, so every
physical position and scalar label stays fixed. This supplies the literal
inverse range used to match the common normalized cone with the retained
carrier (app:ch_background:eq:bg-Psi and bg-full-complex-amplitude). -/
theorem radialInputDomain_subset_symbolInputDomain
    {n : ℕ} {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    {O : Set (InputVariables n)} (hO : O ⊆ symbolInputDomain zRoot ηb r a) :
    radialInputDomain O ⊆ symbolInputDomain zRoot ηb r a := by
  rintro p ⟨t, ht, hp⟩
  have hscaled := hO hp
  refine ⟨hscaled.1, ?_⟩
  have hback := radialScale_mem_supportedCone hscaled.2 (inv_pos.mpr ht)
  simpa only [radialScale, scaleInput, inv_smul_smul₀ ht.ne'] using hback

/-- The SAME canonical inverse has its full range in the radial input buffer
when its normalized range lies in the retained local buffer. The normalized
range and radial law are outputs of
`NormalizedSelection.exists_finite_incidence_comparison_inputs`; no new
inverse or cone is selected. Consumer: `huRadial` in
`retained_source_normal_eq_normalized_on_common_cone`
(`app:ch_background:eq:bg-Psi`, `bg-full-complex-amplitude`). -/
theorem inverseCoordinates_mapsTo_radialInputDomain_of_normalized_range
    {n : ℕ} {b : ℝ} (hb : 0 < b)
    {u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {Ω : Set (Variables n × Euclidean 2)} {W : Set (InputVariables n)}
    (hne : ∀ q ∈ Ω, q.1.2.2 ≠ 0)
    (hrange : MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius b q)) Ω W)
    (hscale : ∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
      u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) :
    MapsTo (inverseCoordinates u) Ω (radialInputDomain W) := by
  intro q hq
  have ht : 0 < b / ‖q.1.2.2‖ := div_pos hb (norm_pos_iff.mpr (hne q hq))
  refine ⟨b / ‖q.1.2.2‖, ht, ?_⟩
  have hh := hrange hq
  have heq : inverseCoordinates u (normalizeOutputRadius b q) =
      scaleInput (b / ‖q.1.2.2‖) (inverseCoordinates u q) := by
    change inverseCoordinates u (scaleFrequency (b / ‖q.1.2.2‖) q.1, q.2) = _
    dsimp only [inverseCoordinates]
    rw [hscale _ ht q hq]
    rfl
  exact heq ▸ hh

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
