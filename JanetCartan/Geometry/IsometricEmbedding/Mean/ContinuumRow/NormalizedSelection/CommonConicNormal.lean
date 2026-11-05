module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.SeedConicGeometry

/-!
# Literal reflected normals on the common conic target

The supported carrier is already constructed on its original inverse chart.
Expressing its amplitude on the common normalized cone retains the literal
zero-extended density, spectator integral and both reflected terms. The proof
uses the original mask support and exact inverse/Jacobian identities.
-/

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization

/-- Restricting the inverse target preserves the literal zero-extended
density when the SAME original masks map into the common target. The inverse
and Jacobian agree there by source matching and inverse uniqueness; equality
elsewhere follows from the original masks, not an amplitude hypothesis.
Consumer: transport of the supported carrier's normal to the normalized
common conic chart (`bg-full-complex-amplitude`, `bg-jacobian`). -/
theorem extendedDensity_common_conic_target
    {n N : ℕ} (a : Coefficients n N) (J J' : InputVariables n → ℝ)
    (u v : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω Ω' : Set (Variables n × Euclidean 2)} {W Z : Set (InputVariables n)}
    (hsub : Ω' ⊆ Ω)
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hmask : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ Z)
    (hbuffer : F '' Z ⊆ Ω')
    (hinverse : EqOn u v Ω')
    (hJac : ∀ p ∈ Ω', J (inverseCoordinates u p) = J' (inverseCoordinates u p)) :
    extendedDensity a J u Ω = extendedDensity a J' v Ω' := by
  have hsupp := (support_extendedDensity_subset a J u F hmap hright hmask).trans hbuffer
  funext p
  by_cases hp : p ∈ Ω'
  · simp only [extendedDensity, indicator_of_mem hp, indicator_of_mem (hsub hp)]
    have heq : inverseCoordinates u p = inverseCoordinates v p := by
      simp only [inverseCoordinates, hinverse hp]
    rw [← heq]
    simp only [inputDensity, inputWeight, hJac p hp]
  · have hz : extendedDensity a J u Ω p = 0 := by
      by_contra hne
      exact hp (hsupp hne)
    rw [hz]
    exact (indicator_of_notMem hp _).symm

/-- The full reflected matrix amplitude is unchanged when the original
carrier normal is expressed on the common conic target. This retains the
literal spectator measure, both positions, `2πξ`, and both reflected terms.
Consumer: the SAME carrier's PDO identity in `NormalizedNormalLimit`
(`bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem fullReflectedMatrixAmplitude_common_conic_target
    {n N : ℕ} (a : Coefficients n N) (J J' : InputVariables n → ℝ)
    (u v : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω Ω' : Set (Variables n × Euclidean 2)} {W Z : Set (InputVariables n)}
    (hsub : Ω' ⊆ Ω)
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hmask : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ Z)
    (hbuffer : F '' Z ⊆ Ω')
    (hinverse : EqOn u v Ω')
    (hJac : ∀ p ∈ Ω', J (inverseCoordinates u p) = J' (inverseCoordinates u p))
    (S : Set (Euclidean 2)) :
    fullReflectedMatrixAmplitude a J u Ω S = fullReflectedMatrixAmplitude a J' v Ω' S := by
  have heq := extendedDensity_common_conic_target a J J' u v F hsub hmap hright
    hmask hbuffer hinverse hJac
  unfold fullReflectedMatrixAmplitude reflectedSymbolAmplitude amplitude
  rw [heq]

end JanetCartan.ContinuumRow.NormalizedSelection
