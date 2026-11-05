module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WideDilation

/-!
# The original wide datum on a buffered slice chart

The chart input in `app:ch_waves:eq:individual-raw-slice` is obtained by the
actual wide-band unitary, zero extension, and restriction to the original
buffered chart. Its norm is at most the original datum's norm. The integral
identity below requires only support of the amplitude in that chart; the
chart need not contain the whole annulus.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition RawInputHilbert

variable {n : ℕ}

/-- Actual source map for applying `SingleChannel` to one reassembled band
(`app:ch_waves:eq:individual-raw-slice`). -/
def wideBandChartInput (n j : ℕ) (D : Set (Euclidean (n - 1))) :
    WideBandL2 n j →L[ℂ] Lp ℂ 2 (volume.restrict D) :=
  (restriction D).comp ((zeroExtension (measurableSet_wideBand n 0)).toContinuousLinearMap.comp
    (wideBandDilation n j).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Source chart localization is a contraction on the literal original band;
there is no scale-count or quadrature loss (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_wideBandChartInput_le (j : ℕ) (D : Set (Euclidean (n - 1))) :
    ‖wideBandChartInput n j D‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖restriction D (zeroExtension (measurableSet_wideBand n 0)
    (wideBandDilation n j f))‖ ≤ _
  calc
    _ ≤ 1 * ‖zeroExtension (measurableSet_wideBand n 0) (wideBandDilation n j f)‖ :=
      ((restriction D).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_restriction_le D) (norm_nonneg _))
    _ = 1 * ‖f‖ := by rw [LinearIsometry.norm_map, norm_wideBandDilation]

/-- The chart datum is the zero extension of the SAME reassembled pullback
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem wideBandChartInput_apply_ae (j : ℕ) (D : Set (Euclidean (n - 1)))
    (f : WideBandL2 n j) :
    wideBandChartInput n j D f =ᵐ[volume.restrict D]
      (wideBand n 0).indicator (fun θ ↦ wideBandDilation n j f θ) :=
  (restriction_coeFn D _).trans
    (ae_restrict_of_ae (zeroExtension_coeFn (measurableSet_wideBand n 0) _))

/-- Literal integral transfer from the buffered chart to the complete wide
band. Sharp Hilbert refinements do not occur in the amplitude
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem integral_wideBandChartInput {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (j : ℕ) {D : Set (Euclidean (n - 1))}
    (a : Euclidean (n - 1) → E) (ha : ∀ θ ∉ D, a θ = 0) (f : WideBandL2 n j) :
    (∫ θ in D, wideBandChartInput n j D f θ • a θ) =
      ∫ θ in wideBand n 0, wideBandDilation n j f θ • a θ := by
  calc
    _ = ∫ θ in D, (wideBand n 0).indicator
        (fun θ ↦ wideBandDilation n j f θ • a θ) θ := by
      apply integral_congr_ae
      filter_upwards [wideBandChartInput_apply_ae j D f] with θ hθ
      rw [hθ, Set.indicator_smul_left]
    _ = ∫ θ, (wideBand n 0).indicator (fun θ ↦ wideBandDilation n j f θ • a θ) θ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro θ hθ
      by_cases hw : θ ∈ wideBand n 0 <;> simp [hw, ha θ hθ]
    _ = _ := integral_indicator (measurableSet_wideBand n 0)

end JanetCartan.RawPrimary.SliceBounds
