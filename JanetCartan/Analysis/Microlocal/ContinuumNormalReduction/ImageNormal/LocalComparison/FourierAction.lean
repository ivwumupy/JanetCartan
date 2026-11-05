module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.BesselSymbol
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Poisson.Fourier.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image.Bessel.Symbol

/-!
# Periodization of the Bessel action on Schwartz tests

The Fourier identification needed by `app:ch_background:prop:bg-frame`,
Step 1. These results use the convergent periodization of a Schwartz *output*.
They do not assert that the singular Bessel kernel is Schwartz or that the
periodic kernel equals the Euclidean kernel. The bounded periodic operator's
only premise is its lattice Fourier action. Instantiating this complex scalar
interface from the actual real vector operator remains an assembly obligation.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap
open JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem complexPeriodicL2_ext {u v : PeriodicL2 d ℂ}
    (h : ∀ k, UnitAddTorus.mFourierCoeff u k = UnitAddTorus.mFourierCoeff v k) : u = v := by
  revert u v
  unfold PeriodicL2
  rw [torus_volume_eq_pi_haarAddCircle]
  intro u v h
  apply (UnitAddTorus.mFourierBasis (d := Fin d)).repr.injective
  apply lp.ext
  funext k
  simpa only [UnitAddTorus.mFourierBasis_repr] using h k

private theorem mFourierCoeff_toLp_volume (f : C(Torus d, ℂ)) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (f.toLp 2 volume ℂ) k = UnitAddTorus.mFourierCoeff f k := by
  unfold UnitAddTorus.mFourierCoeff
  change (∫ t, UnitAddTorus.mFourier (-k) t • (f.toLp 2 volume ℂ) t
      ∂Measure.pi (fun _ : Fin d ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))) =
    ∫ t, UnitAddTorus.mFourier (-k) t • f t
      ∂Measure.pi (fun _ : Fin d ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))
  rw [← torus_volume_eq_pi_haarAddCircle]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume f] with x hx
  rw [hx]

/-- The Euclidean multiplier samples to the actual unit-torus Bessel symbol,
including the physical factor `2π` (`app:not:fourier`, `app:ch_background:defn:bg-row`). -/
theorem imageBesselSymbol_integer (k : Fin d → ℤ) :
    imageBesselSymbol (WithLp.toLp 2 (fun i ↦ (k i : ℝ)) : E) =
      ContinuumRow.periodicBesselSymbol k := by
  rw [ContinuumRow.periodicBesselSymbol_eq_rpow]
  simp only [imageBesselSymbol, euclideanSobolevWeight, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi), frequencyNorm]
  congr 1
  norm_num

/-- Periodizing the Euclidean Bessel output gives the required lattice
coefficients (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem mFourierCoeff_periodization_imageBesselMultiplier (u : 𝓢(E, ℂ))
    (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization
      (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u)) k =
        (ContinuumRow.periodicBesselSymbol k : ℂ) *
          UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization u) k := by
  rw [mFourierCoeff_schwartzTorusPeriodization, mFourierCoeff_schwartzTorusPeriodization]
  change (𝓕 (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u) :
    𝓢(E, ℂ)) _ = _
  rw [fourier_imageBesselMultiplier, imageBesselSymbol_integer]
  rfl

/-- Exact intertwining on Schwartz tests, deduced solely from the periodic
operator's coefficient action (`app:ch_background:prop:bg-frame`, Step 1).
The two sides live in torus L²; Euclidean Fourier transforms retain Lebesgue
measure in the preceding coefficient theorem. -/
theorem periodicBessel_eq_periodized_euclidean_on_schwartz
    (J : PeriodicL2 d ℂ →L[ℂ] PeriodicL2 d ℂ)
    (hJ : ∀ (v : PeriodicL2 d ℂ) (k : Fin d → ℤ),
      UnitAddTorus.mFourierCoeff (J v) k =
        (ContinuumRow.periodicBesselSymbol k : ℂ) * UnitAddTorus.mFourierCoeff v k)
    (u : 𝓢(E, ℂ)) :
    J ((schwartzTorusPeriodization u).toLp 2 volume ℂ) =
      (schwartzTorusPeriodization
        (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u)).toLp
          2 volume ℂ := by
  apply complexPeriodicL2_ext
  intro k
  simp only [hJ, mFourierCoeff_toLp_volume,
    mFourierCoeff_periodization_imageBesselMultiplier]

end JanetCartan.ContinuumNormalReduction.ImageNormal
