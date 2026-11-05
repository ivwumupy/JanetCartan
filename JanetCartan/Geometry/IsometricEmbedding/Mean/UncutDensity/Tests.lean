module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.Integral

/-!
# Density identity on the shared smooth compact test domain

This consumes the literal bounded realization supplied by `CarrierExtension`.
The remaining geometric inputs are continuity of each initial kernel section
and the angular plateau, supplied by the continuum-row and positive-background
owners. These statements alone do not settle passage to regular raw inputs.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.UncutDensity

open ContinuumRow

variable {n N : ℕ}

/-- Continuity of the literal initial kernel suffices for absolute convergence
on the existing smooth compact domain (`app:ch_background:eq:bg-density-twice`). -/
theorem integrable_test_carrierKernel (d : CarrierData n N) (x : Torus n)
    (hk : Continuous (carrierKernel d x)) (u : carrierInitialTestSpace n) :
    Integrable (fun p ↦ u.val p • carrierKernel d x p) (carrierMeasure n) :=
  (u.property.1.continuous.smul hk).integrable_of_hasCompactSupport
    u.property.2.smul_right

/-- The already constructed real carrier channel has its literal representative
`2 Re U f`; used for `app:ch_background:eq:bg-density-twice`. -/
theorem carrierChannel_coeFn (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (f : CarrierL2 n) :
    carrierChannel U f =ᵐ[volume] fun x ↦ (2 : ℝ) • euclideanRealPart (U f x) := by
  filter_upwards [Lp.coeFn_smul (2 : ℝ) (l2RealPart volume (U f)),
    euclideanRealPart.coeFn_compLpL (p := 2) (U f)] with x hx hy
  change ((2 : ℝ) • l2RealPart volume (U f)) x = _
  rw [hx]
  simp only [Pi.smul_apply, l2RealPart, hy]

/-- `4 Re` uncut density changes the measured mean by twice the actual
bounded channel on smooth compact tests (`app:ch_background:eq:bg-density-twice`).
The realization premise is exactly the conclusion furnished by `CarrierExtension`.
No density/channel identity is an input. -/
theorem measuredIncrement_four_test (d : CarrierData n N)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (hk : ∀ x, Continuous (carrierKernel d x))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
    (u : carrierInitialTestSpace n) :
    measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d 4 u.val) =ᵐ[volume]
      fun x ↦ (2 : ℝ) • carrierChannel U (carrierInitialTestToLp u) x := by
  filter_upwards [hU u, carrierChannel_coeFn U (carrierInitialTestToLp u)] with x hx hy
  rw [hy, hx]
  exact measuredIncrement_four d χ hχ u.val x
    (integrable_test_carrierKernel d x (hk x) u)

/-- `-2 Re` uncut density changes the measured mean by minus the actual
bounded channel on smooth compact tests (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem measuredIncrement_neg_two_test (d : CarrierData n N)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (hk : ∀ x, Continuous (carrierKernel d x))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
    (u : carrierInitialTestSpace n) :
    measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d (-2) u.val) =ᵐ[volume]
      fun x ↦ -(carrierChannel U (carrierInitialTestToLp u) x) := by
  filter_upwards [hU u, carrierChannel_coeFn U (carrierInitialTestToLp u)] with x hx hy
  rw [hy, hx]
  exact measuredIncrement_neg_two d χ hχ u.val x
    (integrable_test_carrierKernel d x (hk x) u)

end JanetCartan.UncutDensity
