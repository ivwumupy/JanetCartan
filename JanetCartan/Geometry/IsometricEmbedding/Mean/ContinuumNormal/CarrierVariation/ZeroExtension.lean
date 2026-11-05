module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Smooth

/-!
# Compatibility of carrier-density differences with zero extension

For `app:ch_osc:prop:osc-normal`, Step 4', both densities are compared on one
fixed open inverse domain. Primitive support buffers put their difference
strictly inside that domain. Thus no boundary term is introduced by taking
jets of the difference. Consumer: the global amplitude-difference estimate
in `CarrierVariation`.
-/

@[expose] public noncomputable section
open Set Function Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation
open ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Subtraction commutes with the literal zero extension on a common chart;
the inverse points and Jacobians may differ.
Source: `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem extendedDensity_sub_eq_indicator
    (a b : Coefficients n N) (J J₀ : InputVariables n → ℝ)
    (u u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) :
    extendedDensity a J u Ω - extendedDensity b J₀ u₀ Ω =
      Ω.indicator (fun p ↦ inputDensity a J (inverseCoordinates u p) -
        inputDensity b J₀ (inverseCoordinates u₀ p)) := by
  classical
  funext p
  by_cases hp : p ∈ Ω <;> simp [extendedDensity, hp]

/-- At every interior point, all mixed jets of the zero-extended difference
are those of the literal substituted difference. No global amplitude
regularity is assumed. Source: `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem iteratedFDeriv_extendedDensity_sub_of_mem
    (a b : Coefficients n N) (J J₀ : InputVariables n → ℝ)
    (u u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    {Ω : Set (Variables n × Euclidean 2)} (hΩ : IsOpen Ω)
    {p : Variables n × Euclidean 2} (hp : p ∈ Ω) (j : ℕ) :
    iteratedFDeriv ℝ j (extendedDensity a J u Ω - extendedDensity b J₀ u₀ Ω) p =
      iteratedFDeriv ℝ j (fun q ↦ inputDensity a J (inverseCoordinates u q) -
        inputDensity b J₀ (inverseCoordinates u₀ q)) p := by
  have he : (extendedDensity a J u Ω - extendedDensity b J₀ u₀ Ω) =ᶠ[𝓝 p]
      (fun q ↦ inputDensity a J (inverseCoordinates u q) -
        inputDensity b J₀ (inverseCoordinates u₀ q)) := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    simp [extendedDensity, hq]
  exact (he.iteratedFDeriv ℝ j).eq_of_nhds

/-- A primitive mask buffer for each family gives a common support buffer for
their actual density difference. The forward maps may differ, but both images
lie inside the same inverse domain. Source: `app:ch_background:prop:bg-frame`
and `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem tsupport_extendedDensity_sub_subset
    (a : Fin 2 → Coefficients n N) (J : Fin 2 → InputVariables n → ℝ)
    (u : Fin 2 → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : Fin 2 → InputVariables n → Variables n × Euclidean 2)
    {Ω : Set (Variables n × Euclidean 2)} (W L : Fin 2 → Set (InputVariables n))
    (hmap : ∀ t, MapsTo (inverseCoordinates (u t)) Ω (W t))
    (hright : ∀ t p, p ∈ Ω → F t (inverseCoordinates (u t) p) = p)
    (hs : ∀ t p, p ∈ W t → (a t).measurement p.1.1 ≠ 0 →
      (a t).measurement p.1.2 ≠ 0 →
      (a t).angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → (a t).high ‖p.2.2‖ ≠ 0 →
      p ∈ L t)
    (hclosed : ∀ t, IsClosed (F t '' L t))
    (hbuffer : ∀ t, F t '' L t ⊆ Ω) :
    tsupport (extendedDensity (a 0) (J 0) (u 0) Ω -
      extendedDensity (a 1) (J 1) (u 1) Ω) ⊆ Ω := by
  have hsingle (t : Fin 2) : tsupport (extendedDensity (a t) (J t) (u t) Ω) ⊆ Ω :=
    (closure_minimal (support_extendedDensity_subset (a t) (J t) (u t) (F t)
      (hmap t) (hright t) (hs t)) (hclosed t)).trans (hbuffer t)
  intro p hp
  by_contra hout
  have hzero (t : Fin 2) : extendedDensity (a t) (J t) (u t) Ω =ᶠ[𝓝 p] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hout (hsingle t h))
  exact (notMem_tsupport_iff_eventuallyEq.mpr (by
    simpa using (hzero 0).sub (hzero 1))) hp

/-- Every jet of the difference vanishes off the common inverse chart,
including its boundary. The support conclusion is derived from the original
masks and actual forward identities, not assumed for the transformed density.
Source: `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem iteratedFDeriv_extendedDensity_sub_of_notMem
    (a : Fin 2 → Coefficients n N) (J : Fin 2 → InputVariables n → ℝ)
    (u : Fin 2 → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : Fin 2 → InputVariables n → Variables n × Euclidean 2)
    {Ω : Set (Variables n × Euclidean 2)} (W L : Fin 2 → Set (InputVariables n))
    (hmap : ∀ t, MapsTo (inverseCoordinates (u t)) Ω (W t))
    (hright : ∀ t p, p ∈ Ω → F t (inverseCoordinates (u t) p) = p)
    (hs : ∀ t p, p ∈ W t → (a t).measurement p.1.1 ≠ 0 →
      (a t).measurement p.1.2 ≠ 0 →
      (a t).angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → (a t).high ‖p.2.2‖ ≠ 0 →
      p ∈ L t)
    (hclosed : ∀ t, IsClosed (F t '' L t))
    (hbuffer : ∀ t, F t '' L t ⊆ Ω)
    {p : Variables n × Euclidean 2} (hp : p ∉ Ω) (j : ℕ) :
    iteratedFDeriv ℝ j (extendedDensity (a 0) (J 0) (u 0) Ω -
      extendedDensity (a 1) (J 1) (u 1) Ω) p = 0 := by
  have hsupp := tsupport_extendedDensity_sub_subset a J u F W L hmap hright hs hclosed hbuffer
  have he := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hp (hsupp h))
  simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds

end JanetCartan.ContinuumNormal.CarrierVariation
