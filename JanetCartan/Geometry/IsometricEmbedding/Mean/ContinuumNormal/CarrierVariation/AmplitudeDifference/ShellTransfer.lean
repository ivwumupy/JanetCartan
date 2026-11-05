module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.ShellTransfer.Global
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.ShellTransfer.Masks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.ShellTransfer.Physical

/-!
# Full complex and reflected amplitude differences from supported shell norms

This is the downstream transfer for `app:ch_osc:prop:osc-normal`, Step 4',
consumed by `jc-carrier-variation-amplitude-difference`. It proves both full
`HasAmplitudeDerivativeBound` conclusions from uniform normalized-shell
substituted-density differences. The literal amplitudes retain both positions,
all original masks, their spectator integral, `k = 2πξ`, and reflection.

The parent must instantiate `hb` using `jc-carrier-amplitude-primitive-density`
and supply the actual conic inverse/Jacobian identities and primitive support
buffer. This implication does not claim the unconditional primitive-to-normal
continuity theorem. The compact `Q` lies inside the common inverse chart;
only supported points of the normalized shell must lie in `Q`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CarrierNormalRealization
open AmplitudeBound
variable {n N : ℕ}

/-- Uniform supported-shell density differences imply the full complex and
reflected amplitude derivative bounds through the prescribed PDO reserve.
The constant precedes all varying fields and the distance `d`. The high-mask
gap, inverse-frequency comparison and punctured primitive buffer prove global
smoothness and vanishing at the cone vertex; no amplitude-difference estimate
is a hypothesis. Reflection contributes exactly four times the complex bound.
The shell premise `hb` is produced by `jc-carrier-amplitude-primitive-density`
and its instantiation remains the parent's obligation. Sources:
`app:ch_osc:prop:osc-normal`, Step 4',
`app:ch_background:eq:bg-full-complex-amplitude`, and `bg-real-symbol`. -/
theorem exists_fullAmplitude_sub_bounds_of_supported_shell
    (s : ℕ) (_hreserve : 2 * (n + 1) ≤ s)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {Q : Set (Variables n × Euclidean 2)} (hQ : IsCompact Q)
    {Cupper ℓ B : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ)
    (hlow : Cupper * ℓ ≤ 1) (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (a : Fin 2 → Coefficients n N) (J : Fin 2 → InputVariables n → ℝ)
      (u : Fin 2 → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (F : Fin 2 → InputVariables n → Variables n × Euclidean 2)
      (Ω : Set (Variables n × Euclidean 2)) (W Z : Fin 2 → Set (InputVariables n))
      (d : ℝ), 0 ≤ d → IsOpen Ω → Q ⊆ Ω →
      (∀ i, PrimitiveRegularity (a i) (J i) (W i)) →
      (∀ i, ContDiffOn ℝ ∞ (u i) Ω) →
      (∀ i, MapsTo (inverseCoordinates (u i)) Ω (W i)) →
      (∀ i p, p ∈ Ω → F i (inverseCoordinates (u i) p) = p) →
      (∀ i p, p ∈ W i → (a i).measurement p.1.1 ≠ 0 →
        (a i).measurement p.1.2 ≠ 0 →
        (a i).angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z i) →
      (∀ i, closure (F i '' Z i) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) →
      (∀ i r, r ≤ 1 → (a i).high r = 0) →
      (∀ i p, p ∈ Ω → ‖(u i p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ i t, 0 < t → ∀ p ∈ Ω,
        u i (scaleFrequency t p.1, p.2) = ((u i p).1, t • (u i p).2)) →
      (∀ i t, 0 < t → ∀ p ∈ Ω,
        J i (scaleInput t (inverseCoordinates (u i) p)) = t * J i (inverseCoordinates (u i) p)) →
      (∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ v ∈ S,
        (p, v) ∈ closure (F 0 '' Z 0) ∪ closure (F 1 '' Z 1) → (p, v) ∈ Q) →
      (∀ t : ℝ, 1 ≤ t → cNorm Q s
        (fun p ↦ inputDensity (rescaledCoefficients (a 0) t) (J 0) (inverseCoordinates (u 0) p) -
          inputDensity (rescaledCoefficients (a 1) t) (J 1) (inverseCoordinates (u 1) p)) ≤ B * d) →
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullComplexMatrixAmplitude (a 0) (J 0) (u 0) Ω S ξ z i j -
          fullComplexMatrixAmplitude (a 1) (J 1) (u 1) Ω S ξ z i j) s (C * d) ∧
        HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude (a 0) (J 0) (u 0) Ω S ξ z i j -
          fullReflectedMatrixAmplitude (a 1) (J 1) (u 1) Ω S ξ z i j) s ((4 * C) * d) := by
  obtain ⟨C₀, hC₀, hphysical⟩ := exists_fullAmplitude_sub_bounds_of_global_jets (n := n) (N := N) s
  let C := C₀ * B * volume.real S + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a J u F Ω W Z d hd hΩ hQΩ hreg hu hmap hright hsupp hbuffer hzero
    hupper hscale huScale hJScale hshell hb i j
  obtain ⟨hsm, hj⟩ := amplitude_sub_global_jets_of_supported_shell a J u F W Z
    hΩ hreg hu hmap hright hsupp hbuffer hzero hCupper hℓ hlow hupper
    hscale huScale hJScale hS hQ hQΩ hshell s hB hd hb
  obtain ⟨hc, hr⟩ := hphysical a J u Ω S hsm (B * d * volume.real S) (by positivity) hj i j
  have hbudget : C₀ * (B * d * volume.real S) ≤ C * d := by
    dsimp [C]
    nlinarith
  refine ⟨fun ξ is his z ↦ (hc ξ is his z).trans hbudget, ?_⟩
  intro ξ is his z
  exact (hr ξ is his z).trans (by nlinarith)

end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
