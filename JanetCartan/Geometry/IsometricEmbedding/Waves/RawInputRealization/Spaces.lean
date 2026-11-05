module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Lebesgue annular inputs for raw synthesis

The initial variable in `app:ch_waves:thm:individual` has dimension `n - 1`.
These spaces use restricted Lebesgue measure, with both complex quadratures and
its inherited real Hilbert structure. They are not the torus `RawBandDataSpace`.
Consumers are the raw-primary and current-canonical constructions.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RawInputRealization

/-- A closed outer annulus for `app:ch_waves:thm:individual`. -/
def annulus (n : ℕ) (R : ℝ) : Set (Euclidean (n - 1)) :=
  Metric.closedBall 0 R \ Metric.ball 0 (R / 2)

/-- The annular input set is Lebesgue measurable (`app:ch_waves:thm:individual`). -/
theorem measurableSet_annulus (n : ℕ) (R : ℝ) : MeasurableSet (annulus n R) :=
  measurableSet_closedBall.diff measurableSet_ball

/-- Literal Lebesgue measure on an initial annulus (`app:ch_waves:thm:individual`). -/
def annularMeasure (n : ℕ) (R : ℝ) : Measure (Euclidean (n - 1)) :=
  volume.restrict (annulus n R)

instance annularMeasure_finite (n : ℕ) (R : ℝ) : IsFiniteMeasure (annularMeasure n R) := by
  constructor
  simpa [annularMeasure, annulus] using (measure_mono (Set.sdiff_subset : annulus n R ⊆
    Metric.closedBall 0 R)).trans_lt (measure_closedBall_lt_top (μ := volume))

/-- One complex annular `L²` input (`app:ch_waves:thm:individual`). -/
abbrev AnnularL2 (n : ℕ) (R : ℝ) := Lp ℂ 2 (annularMeasure n R)

/-- The real Hilbert space underlying the finite complex Hilbert sum `X_K`
(`app:ch_waves:thm:individual`). The ceiling is supplied by bounds on `radius`. -/
abbrev Input (n : ℕ) {ι : Type*} [Fintype ι] (radius : ι → ℝ) :=
  PiLp 2 (fun i ↦ AnnularL2 n (radius i))

/-- The actual Hilbert norm, with no factor depending on the number of annuli
(`app:ch_waves:eq:B-bounds`). -/
theorem norm_input_sq {n : ℕ} {ι : Type*} [Fintype ι] {radius : ι → ℝ}
    (v : Input n radius) : ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ v

/-- Literal half-derivative annular density, extended by zero. The mask `β` may
include fixed detector and high-pass masks (`app:ch_waves:eq:B-bounds`). -/
def channelDensity {n : ℕ} {R : ℝ} (β : Euclidean (n - 1) → ℂ)
    (v : AnnularL2 n R) : Euclidean (n - 1) → ℂ :=
  (annulus n R).indicator (fun η ↦ (Real.sqrt ‖η‖ : ℂ) * β η * v η)

/-- The literal finite sum `∑ ℓ |η|^(1/2) β_ℓ(η) v_ℓ(η)` before spatial
initial cutoff (`app:ch_waves:thm:individual`). -/
def density {n : ℕ} {ι : Type*} [Fintype ι] {radius : ι → ℝ}
    (β : ι → Euclidean (n - 1) → ℂ) (v : Input n radius) :
    Euclidean (n - 1) → ℂ := fun η ↦ ∑ i, channelDensity (β i) (v i) η

/-- Each channel vanishes off its actual annulus (`app:ch_waves:thm:individual`). -/
theorem channelDensity_eq_zero {n : ℕ} {R : ℝ} (β : Euclidean (n - 1) → ℂ)
    (v : AnnularL2 n R) {η : Euclidean (n - 1)} (hη : η ∉ annulus n R) :
    channelDensity β v η = 0 := Set.indicator_of_notMem hη _

/-- Fourier input support below the ceiling, before any spatial cutoff
(`app:ch_waves:thm:individual`). This concerns the literal density representative. -/
theorem density_eq_zero_above_ceiling {n : ℕ} {ι : Type*} [Fintype ι]
    {radius : ι → ℝ} (β : ι → Euclidean (n - 1) → ℂ) (v : Input n radius)
    {K : ℝ} (hK : ∀ i, radius i ≤ K) {η : Euclidean (n - 1)} (hη : K < ‖η‖) :
    density β v η = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply channelDensity_eq_zero
  intro h
  have : ‖η‖ ≤ radius i := by simpa using h.1
  exact (hη.trans_le (this.trans (hK i))).false

/-- Radian inverse-Fourier pairing: Mathlib's character is `exp(2π i t)` and
its Fourier integral uses `-L η x`. Thus this pairing gives `exp(i ⟨η,x⟩)`.
The density is synthesis-normalized: no prefactor multiplies its inverse integral;
the corresponding forward transform carries `(2π)^(-(n-1))`.
(`app:ch_waves:eq:individual-representation`). -/
def radianPairing (n : ℕ) : Euclidean (n - 1) →L[ℝ] Euclidean (n - 1) →L[ℝ] ℝ :=
  (-(2 * Real.pi)⁻¹) • innerSL ℝ

/-- Inverse Euclidean Fourier integral of the literal density, with radian
normalization (`app:ch_waves:eq:B-bounds`). The separate zero atom is not included. -/
def field {n : ℕ} {ι : Type*} [Fintype ι] {radius : ι → ℝ}
    (β : ι → Euclidean (n - 1) → ℂ) (v : Input n radius) :
    Euclidean (n - 1) → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume
    (radianPairing n).toLinearMap₁₂ (density β v)

end JanetCartan.RawInputRealization
