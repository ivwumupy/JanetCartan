module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.CommonTarget
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.Canonical

/-!
# The frozen quarter-radius section and the unit section

These identities account for the positive factor four while keeping the
exact image of the original target and the same homogeneous inverse. They
do not identify independently selected neighborhoods or mask families.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ContinuumRow.CanonicalConic ContinuumNormalReduction.TransportSymbol

/-- Convert the frozen radius `1/4` to the unit frequency section by the
literal factor four. Only frequency is dilated; the physical positions and
spectator are unchanged. In particular the image of the old target is retained
exactly, rather than replaced by a ball with the old radius. Consumer: the
single joint frozen/variation selection (`app:ch_background:eq:bg-Psi`,
`app:ch_background:prop:bg-normalized`). -/
theorem quarter_section_conicTarget_eq_unit_image {n : ℕ}
    (Ω : Set (Variables n × Euclidean 2)) :
    normalizedConicTarget (1 / 4) Ω =
      normalizedConicTarget 1 ((fun q ↦ (scaleFrequency 4 q.1, q.2)) '' Ω) := by
  let f : Variables n × Euclidean 2 → Variables n × Euclidean 2 :=
    fun q ↦ (scaleFrequency 4 q.1, q.2)
  have hf : Function.Injective f := by
    intro q p h
    have he := congrArg (fun w : Variables n × Euclidean 2 ↦
      (scaleFrequency (1 / 4) w.1, w.2)) h
    simpa [f, scaleFrequency, smul_smul] using he
  have hn (q : Variables n × Euclidean 2) :
      normalizeOutputRadius 1 q = f (normalizeOutputRadius (1 / 4) q) := by
    simp only [normalizeOutputRadius, f, scaleFrequency, smul_smul]
    rw [show (1 : ℝ) / ‖q.1.2.2‖ = 4 * ((1 / 4) / ‖q.1.2.2‖) by ring]
  ext q
  change (q.1.2.2 ≠ 0 ∧ normalizeOutputRadius (1 / 4) q ∈ Ω) ↔
    (q.1.2.2 ≠ 0 ∧ normalizeOutputRadius 1 q ∈ f '' Ω)
  rw [hn]
  exact and_congr_right fun _ ↦ (hf.mem_set_image).symm

/-- On the same homogeneous inverse the quarter-radius and unit-radius
formulas coincide, with both factors of four accounted for. Its hypothesis
is the proved global radial law of `symbolInverse_scale_all` or
`radialExtensionInverse_smul`; it asserts no equality between independently
chosen inverses. Consumer: the frozen/variation section conversion
(`app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-symbol`). -/
theorem radialExtensionInverse_quarter_eq_unit {n : ℕ}
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (hu : ∀ t : ℝ, 0 < t → ∀ q,
      u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) :
    radialExtensionInverse (1 / 4) u = radialExtensionInverse 1 u := by
  funext q
  have hn : normalizeOutputRadius 1 q =
      (scaleFrequency 4 (normalizeOutputRadius (1 / 4) q).1,
        (normalizeOutputRadius (1 / 4) q).2) := by
    simp only [normalizeOutputRadius, scaleFrequency, smul_smul]
    rw [show (1 : ℝ) / ‖q.1.2.2‖ = 4 * ((1 / 4) / ‖q.1.2.2‖) by ring]
  simp only [radialExtensionInverse, hn, hu 4 (by norm_num), smul_smul]
  congr 1
  congr 1
  ring

/-- Both physical endpoints and their original carrier labels are unchanged
by normalizing the output radius of the SAME homogeneous inverse. The root
may differ from the retained cell center. Consumer: original-domain primitive
regularity on the full cone (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem densityEndpoint_inverse_normalizeOutputRadius {n : ℕ}
    {u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {Ω : Set (Variables n × Euclidean 2)}
    (hu : ∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
      u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2))
    {b : ℝ} (hb : 0 < b) {q : Variables n × Euclidean 2}
    (hq : q ∈ Ω) (hne : q.1.2.2 ≠ 0) (side : Bool) :
    WideDensity.densityEndpoint side (inverseCoordinates u (normalizeOutputRadius b q)) =
      WideDensity.densityEndpoint side (inverseCoordinates u q) := by
  have ht : 0 < b / ‖q.1.2.2‖ := div_pos hb (norm_pos_iff.mpr hne)
  have he := congrArg Prod.fst (hu _ ht q hq)
  exact congrArg (fun s : ℝ ↦ (if side then q.1.2.1 else q.1.1, s, q.2)) he

/-- The normalized inverse range controls BOTH original endpoint ranges on
EVERY point of the full conic target. Only the frequency is normalized; no
outer domain or detector support is reduced. The range input is constructed
by `exists_common_geometry_in_cell`. Consumer: retained full-amplitude
regularity (`app:ch_background:eq:bg-Psi`, `bg-full-complex-amplitude`). -/
theorem densityEndpoint_inverse_mapsTo_of_normalized_range {n : ℕ}
    {u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {Ω : Set (Variables n × Euclidean 2)} {Ki : Set (InputVariables n)}
    {E : Set (Euclidean n × (ℝ × Euclidean 2))}
    {b : ℝ} (hb : 0 < b) (hne : ∀ q ∈ Ω, q.1.2.2 ≠ 0)
    (hu : ∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
      u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2))
    (hrange : MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius b q)) Ω Ki)
    (hend : ∀ side, MapsTo (WideDensity.densityEndpoint side) Ki E) :
    ∀ side, MapsTo (WideDensity.densityEndpoint side) (inverseCoordinates u '' Ω) E := by
  rintro side _ ⟨q, hq, rfl⟩
  rw [← densityEndpoint_inverse_normalizeOutputRadius hu hb hq (hne q hq) side]
  exact hend side (hrange hq)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
