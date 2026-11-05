module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityFreezing

/-!
# Localize density regularity without changing the measured normal

The canonical frozen inverse domain is unbounded in the physical positions.
The original initial density need only be smooth on its original bounded
domain. Intersecting the inverse domain with a physical region containing
the existing measurement support leaves the full amplitude exactly unchanged.
The inverse, both masks, density coefficients and spectator measure are retained.

Consumer: the original-domain primitive regularity and uniform zero-scale
amplitude bound used by `exists_sourceDensityLimit_frozen_error_constant`.
Sources: `app:ch_background:eq:bg-full-complex-amplitude`, `bg-Nsigma`, and
`app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.ActualConstruction
open ContinuumRow
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization

variable {n N : ℕ}

/-- Both existing measurement factors make physical localization of the
inverse domain an exact identity of the original zero-extended integrand.
No smoothness outside the original density region is needed, and the actual
inverse is retained (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem extendedDensity_inter_measurement_region
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (E : Set (Euclidean n))
    (hm : ∀ x, a.measurement x ≠ 0 → x ∈ E) :
    extendedDensity a J u (Ω ∩ {p | p.1.1 ∈ E ∧ p.1.2.1 ∈ E}) =
      extendedDensity a J u Ω := by
  classical
  funext p
  by_cases hl : a.measurement p.1.1 = 0
  · simp [extendedDensity, Set.indicator_apply, inputDensity, inputWeight, inverseCoordinates, hl]
  by_cases hr : a.measurement p.1.2.1 = 0
  · simp [extendedDensity, Set.indicator_apply, inputDensity, inputWeight, inverseCoordinates, hr]
  have hpos : p ∈ {p : Variables n × Euclidean 2 | p.1.1 ∈ E ∧ p.1.2.1 ∈ E} :=
    ⟨hm _ hl, hm _ hr⟩
  by_cases hΩ : p ∈ Ω
  · simp only [extendedDensity, indicator_of_mem hΩ,
      indicator_of_mem (show p ∈ Ω ∩ {p | p.1.1 ∈ E ∧ p.1.2.1 ∈ E} from ⟨hΩ, hpos⟩)]
  · simp only [extendedDensity, indicator_of_notMem hΩ,
      indicator_of_notMem (show p ∉ Ω ∩ {p | p.1.1 ∈ E ∧ p.1.2.1 ∈ E} from
        fun h ↦ hΩ h.1)]

/-- The original Lebesgue spectator integral is unchanged by restricting
physical positions to a region containing the same measurement support
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem amplitude_inter_measurement_region
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (E : Set (Euclidean n)) (hm : ∀ x, a.measurement x ≠ 0 → x ∈ E) :
    amplitude a J u (Ω ∩ {p | p.1.1 ∈ E ∧ p.1.2.1 ∈ E}) S =
      amplitude a J u Ω S := by
  funext p
  simp only [amplitude, extendedDensity_inter_measurement_region a J u Ω E hm]

/-- Physical localization retains the literal full reflected amplitude,
including both physical positions, its factor four and `2πξ` frequency.
It therefore transfers every derivative bound without changing its constant
(`app:ch_background:eq:bg-real-symbol`, `bg-full-complex-amplitude`). -/
theorem fullReflectedMatrixAmplitude_inter_measurement_region
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (E : Set (Euclidean n)) (hm : ∀ x, a.measurement x ≠ 0 → x ∈ E) :
    fullReflectedMatrixAmplitude a J u (Ω ∩ {p | p.1.1 ∈ E ∧ p.1.2.1 ∈ E}) S =
      fullReflectedMatrixAmplitude a J u Ω S := by
  funext ξ z
  ext i j
  simp only [fullReflectedMatrixAmplitude, reflectedSymbolAmplitude,
    amplitude_inter_measurement_region a J u Ω S E hm]

/-- For the actual fixed measurement mask, its existing `3r` support
discharges the domain-localization premise. The row's radius and mask are
unchanged; only the region on which its primitive density is checked is
restricted. Consumer: `exists_source_zero_density_reflected_bounds`, for the
canonical frozen domain which extends over all physical positions
(`app:ch_background:defn:bg-row`, `bg-full-complex-amplitude`, `bg-Nsigma`). -/
theorem fullReflectedMatrixAmplitude_inter_fixed_measurement_ball
    {r R : ℝ} (hr : 0 < r) (hR : 3 * r ≤ R)
    (a : Coefficients n N) (hm : a.measurement = FixedCutoffs.physical hr 1)
    (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2)) :
    fullReflectedMatrixAmplitude a J u
      (Ω ∩ {p | p.1.1 ∈ Metric.ball 0 R ∧ p.1.2.1 ∈ Metric.ball 0 R}) S =
      fullReflectedMatrixAmplitude a J u Ω S := by
  apply fullReflectedMatrixAmplitude_inter_measurement_region
  intro x hx
  rw [hm] at hx
  have hs := FixedCutoffs.physical_tsupport hr 1 (subset_tsupport _ hx)
  have hs' : x ∈ Metric.ball (0 : Euclidean n) (3 * r) := by
    convert hs using 1
    norm_num
  exact Metric.ball_subset_ball hR hs'

end JanetCartan.ContinuumNormal.ActualConstruction
