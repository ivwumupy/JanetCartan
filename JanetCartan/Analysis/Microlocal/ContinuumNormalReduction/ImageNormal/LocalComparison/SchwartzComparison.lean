module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.FourierAction
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeSeparation
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2

/-!
# Local comparison on compact Schwartz tests

The exact test-level identity for `app:ch_background:prop:bg-frame`, Step 1.
The error is the convergent sum of the nonzero translates of the Euclidean
Bessel *output*. Its smoothness for each Schwartz input is not an L² smoothing
estimate. Identifying this error with `localizedImageBesselRemainder` requires
the separate heat-kernel and lattice-kernel estimates.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The nonzero-translate error on a Schwartz input for
`app:ch_background:prop:bg-frame`, Step 1. -/
def imageBesselSchwartzTail (u : 𝓢(E, ℂ)) (x : E) : ℂ :=
  ∑' k : Fin d → ℤ, if k = 0 then 0 else
    schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u
      (x + integerTranslation k)

/-- The Bessel output's lattice series converges absolutely, including its
nonzero-translate part (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem summable_norm_imageBesselSchwartzTail (u : 𝓢(E, ℂ)) (x : E) :
    Summable (fun k : Fin d → ℤ ↦ ‖if k = 0 then 0 else
      schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u
        (x + integerTranslation k)‖) := by
  classical
  apply (summable_norm_schwartz_lattice
    (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u) x).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro k
  split_ifs
  · simp
  · rfl

/-- Exact separation of the zero translate in the convergent output series
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem periodization_imageBessel_eq_add_tail (u : 𝓢(E, ℂ)) (x : E) :
    schwartzLatticePeriodization
      (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u) x =
        schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u x +
          imageBesselSchwartzTail u x := by
  classical
  have h := (summable_norm_schwartz_lattice
    (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u) x).of_norm
  have hz : (WithLp.toLp 2 (fun i : Fin d ↦ ((0 : Fin d → ℤ) i : ℝ)) : E) = 0 := by
    ext i
    simp
  simpa only [schwartzLatticePeriodization, imageBesselSchwartzTail, integerTranslation,
    hz, add_zero] using h.tsum_eq_add_tsum_ite (0 : Fin d → ℤ)

/-- Smoothness of the error for each Schwartz input
(`app:ch_background:prop:bg-frame`, Step 1); this does not claim an operator
smoothing bound in terms of the input L² norm. -/
theorem contDiff_imageBesselSchwartzTail (u : 𝓢(E, ℂ)) :
    ContDiff ℝ ∞ (imageBesselSchwartzTail u) := by
  have he : imageBesselSchwartzTail u =
      schwartzLatticePeriodization
        (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u) -
      ⇑(schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u) := by
    funext x
    simp only [Pi.sub_apply, periodization_imageBessel_eq_add_tail, add_sub_cancel_left]
  rw [he]
  exact (contDiff_schwartzLatticePeriodization _).sub (SchwartzMap.smooth _ ⊤)

/-- The measured chart restriction of a compact Schwartz test is its
periodization as an L² class (`app:ch_background:defn:bg-row`). -/
theorem toTorus_schwartz_eq_periodization {r : ℝ} (hr : r < 1 / 2)
    (u : 𝓢(E, ℂ)) (hu : SupportedInCenteredBox r u) :
    PeriodicLocalL2.toTorus (𝕜 := ℂ) (u.toLp 2) =
      (schwartzTorusPeriodization u).toLp 2 volume ℂ := by
  apply Lp.ext
  have hcoe := PeriodicLocalL2.measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
    (u.coeFn_toLp 2).restrict
  filter_upwards [PeriodicLocalL2.toTorus_coe (𝕜 := ℂ) (u.toLp 2), hcoe,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (schwartzTorusPeriodization u)]
    with z hz hu' hp
  rw [hz, hp, schwartzTorusPeriodization_eq_amplitudePeriodization hr u hu]
  exact hu'

/-- Exact local comparison on compact Schwartz tests with the distinct
measures and the zero-extension input map retained
(`app:ch_background:prop:bg-frame`, Step 1). The only operator premise is
its lattice coefficient action. Kernel realization and uniform smoothing
bounds are still required to extend this to the requested bounded operators. -/
theorem periodicBessel_chart_schwartz_eq_add_tail
    (J : PeriodicL2 d ℂ →L[ℂ] PeriodicL2 d ℂ)
    (hJ : ∀ (v : PeriodicL2 d ℂ) (k : Fin d → ℤ),
      UnitAddTorus.mFourierCoeff (J v) k =
        (ContinuumRow.periodicBesselSymbol k : ℂ) * UnitAddTorus.mFourierCoeff v k)
    {r : ℝ} (hr : r < 1 / 2) (u : 𝓢(E, ℂ)) (hu : SupportedInCenteredBox r u) :
    J (PeriodicLocalL2.toTorus (𝕜 := ℂ) (u.toLp 2)) =ᵐ[volume] fun z ↦
      schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u
        (centeredTorusRepresentative z) + imageBesselSchwartzTail u
          (centeredTorusRepresentative z) := by
  rw [toTorus_schwartz_eq_periodization hr u hu,
    periodicBessel_eq_periodized_euclidean_on_schwartz J hJ]
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
    (schwartzTorusPeriodization
      (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u))] with z hz
  rw [hz, ← torusQuotient_centeredTorusRepresentative z,
    schwartzTorusPeriodization_torusQuotient, periodization_imageBessel_eq_add_tail,
    torusQuotient_centeredTorusRepresentative]

end JanetCartan.ContinuumNormalReduction.ImageNormal
