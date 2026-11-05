module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ZeroExtension
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ShellBounds.Integration

/-!
# Zero extension and integration of carrier density differences

For `app:ch_osc:prop:osc-normal`, Step 4', subtraction commutes with the
literal compact spectator integral. The original primitive masks and actual
forward identities imply that every jet vanishes at and beyond the chart
boundary. Smoothness and integrability follow from primitive regularity.

The quantitative substituted-density premise must be supplied by the
primitive-product and conic-shell estimates. This intermediate implication
is not a primitive-to-amplitude difference theorem. Its consumer is the
full complex and reflected amplitude assembly in `AmplitudeDifference`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
open ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

-- Unfold the Frobenius matrix topology when synthesizing integrability.
set_option backward.isDefEq.respectTransparency false in
/-- The difference of the two literal amplitudes is the spectator integral
of the density difference. Smoothness on the fixed compact spectator set
supplies integrability. Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem amplitude_sub_eq_spectatorIntegral_sub
    (a : Fin 2 → Coefficients n N) (J : Fin 2 → InputVariables n → ℝ)
    (u : Fin 2 → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) {S : Set (Euclidean 2)} (hS : IsCompact S)
    (hreg : ∀ t, ContDiff ℝ ∞ (extendedDensity (a t) (J t) (u t) Ω)) :
    amplitude (a 0) (J 0) (u 0) Ω S - amplitude (a 1) (J 1) (u 1) Ω S =
      fun p ↦ ∫ v in S, (extendedDensity (a 0) (J 0) (u 0) Ω -
        extendedDensity (a 1) (J 1) (u 1) Ω) (p, v) := by
  funext p
  have hi (t : Fin 2) : IntegrableOn (fun v ↦ extendedDensity (a t) (J t) (u t) Ω (p, v)) S :=
    ((hreg t).continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hS
  exact (integral_sub (hi 0) (hi 1)).symm

section Buffered
variable (a : Fin 2 → Coefficients n N) (J : Fin 2 → InputVariables n → ℝ)
  (u : Fin 2 → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
  (F : Fin 2 → InputVariables n → Variables n × Euclidean 2)
  {Ω : Set (Variables n × Euclidean 2)} (W L : Fin 2 → Set (InputVariables n))
  (hΩ : IsOpen Ω)
  (hmap : ∀ t, MapsTo (inverseCoordinates (u t)) Ω (W t))
  (hright : ∀ t p, p ∈ Ω → F t (inverseCoordinates (u t) p) = p)
  (hs : ∀ t p, p ∈ W t → (a t).measurement p.1.1 ≠ 0 →
    (a t).measurement p.1.2 ≠ 0 →
    (a t).angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → (a t).high ‖p.2.2‖ ≠ 0 →
    p ∈ L t)
  (hclosed : ∀ t, IsClosed (F t '' L t)) (hbuffer : ∀ t, F t '' L t ⊆ Ω)

include hΩ hmap hright hs hclosed hbuffer

/-- A substituted-density jet estimate extends across the common chart
boundary without a boundary term. The support buffer is derived from the
original masks, with independent actual forward maps for both families.
Consumer: spectator integration below. Source:
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem norm_iteratedFDeriv_extendedDensity_sub_le_of_substituted
    (s : ℕ) {X : Set (Variables n × Euclidean 2)} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p ∈ X ∩ Ω, ∀ j ≤ s,
      ‖iteratedFDeriv ℝ j (fun q ↦ inputDensity (a 0) (J 0) (inverseCoordinates (u 0) q) -
        inputDensity (a 1) (J 1) (inverseCoordinates (u 1) q)) p‖ ≤ B)
    {p : Variables n × Euclidean 2} (hp : p ∈ X) {j : ℕ} (hj : j ≤ s) :
    ‖iteratedFDeriv ℝ j (extendedDensity (a 0) (J 0) (u 0) Ω -
      extendedDensity (a 1) (J 1) (u 1) Ω) p‖ ≤ B := by
  by_cases hpΩ : p ∈ Ω
  · rw [iteratedFDeriv_extendedDensity_sub_of_mem _ _ _ _ _ _ hΩ hpΩ]
    exact hb p ⟨hp, hpΩ⟩ j hj
  · rw [iteratedFDeriv_extendedDensity_sub_of_notMem a J u F W L hmap hright hs hclosed
      hbuffer hpΩ j, norm_zero]
    exact hB

/-- The literal spectator integral costs only the fixed spectator volume.
All smoothness, boundary and integral-interchange obligations follow from
primitive regularity and masks; the finite density estimate is supplied by
the primitive composition/product and conic-shell producers. Both positions,
normal factors and Jacobian divisions remain inside `inputDensity`.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem norm_iteratedFDeriv_amplitude_sub_le_of_substituted
    (hreg : ∀ t, PrimitiveRegularity (a t) (J t) (W t))
    (hu : ∀ t, ContDiffOn ℝ ∞ (u t) Ω)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    (s : ℕ) {X : Set (Variables n)} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p ∈ (X ×ˢ S) ∩ Ω, ∀ j ≤ s,
      ‖iteratedFDeriv ℝ j (fun q ↦ inputDensity (a 0) (J 0) (inverseCoordinates (u 0) q) -
        inputDensity (a 1) (J 1) (inverseCoordinates (u 1) q)) p‖ ≤ B)
    {x : Variables n} (hx : x ∈ X) {j : ℕ} (hj : j ≤ s) :
    ‖iteratedFDeriv ℝ j (amplitude (a 0) (J 0) (u 0) Ω S -
      amplitude (a 1) (J 1) (u 1) Ω S) x‖ ≤ B * volume.real S := by
  have hr (t : Fin 2) : ContDiff ℝ ∞ (extendedDensity (a t) (J t) (u t) Ω) :=
    extendedDensity_contDiff (a t) (J t) (u t) (F t) hΩ (hreg t) (hu t)
      (hmap t) (hright t) (hs t) (hclosed t) (hbuffer t)
  rw [amplitude_sub_eq_spectatorIntegral_sub a J u Ω hS hr]
  apply norm_iteratedFDeriv_spectatorIntegral_le ((hr 0).sub (hr 1)) hS j x
  intro v hv
  exact norm_iteratedFDeriv_extendedDensity_sub_le_of_substituted a J u F W L hΩ hmap
    hright hs hclosed hbuffer s hB hb ⟨hx, hv⟩ hj
end Buffered
end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
