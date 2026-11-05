module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds.Carrier

/-!
# Full physical initial-variable Fourier energy

The frequency weight for `app:ch_background:prop:bg-adjoint` includes all
carrier and initial coordinates. `initialFourier` uses Mathlib's unit-period
normalization, so the physical derivative weight includes `2π` in every
coordinate. These are definitions of Fourier energy on physical `(z,y)`
classes. The weak-derivative characterization, complete Hilbert realization,
and pullback along the partial `η → y` transform are separate obligations.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.CarrierSobolev
open ContinuumRow RawCutoffBounds

variable {n : ℕ}

/-- Full physical Bessel weight for `app:ch_background:prop:bg-adjoint`.
Unlike an η-only moment this includes all three dual carrier coordinates.
Its `2π` factor converts the unit-period full Fourier transform to derivatives. -/
def initialWeight (s : ℕ) (ξ : CarrierVariable n) : ℝ :=
  (1 + (2 * Real.pi) ^ 2 * ‖initialCoordinates n ξ‖ ^ 2) ^ ((s : ℝ) / 2)

/-- Literal coordinate formula for the physical derivative weight
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialWeight_eq_coordinates (s : ℕ) (ξ : CarrierVariable n) :
    initialWeight s ξ =
      (1 + (2 * Real.pi) ^ 2 * (|ξ.1.1| ^ 2 + ‖ξ.1.2‖ ^ 2 + ‖ξ.2‖ ^ 2)) ^
        ((s : ℝ) / 2) := by
  rw [initialWeight, initialCoordinates_norm_sq]

/-- The physical derivative weight is positive
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialWeight_pos (s : ℕ) (ξ : CarrierVariable n) : 0 < initialWeight s ξ := by
  unfold initialWeight
  positivity

/-- Order zero has no weight (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem initialWeight_zero (ξ : CarrierVariable n) : initialWeight 0 ξ = 1 := by
  simp [initialWeight]

/-- The full weight increases with the Sobolev order
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialWeight_mono {s t : ℕ} (hst : s ≤ t) (ξ : CarrierVariable n) :
    initialWeight s ξ ≤ initialWeight t ξ := by
  apply Real.rpow_le_rpow_of_exponent_le
  · have : 0 ≤ (2 * Real.pi) ^ 2 * ‖initialCoordinates n ξ‖ ^ 2 := by positivity
    linarith
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hst) (by norm_num)

/-- The full initial weight is measurable on the literal product measure
(`app:ch_background:prop:bg-adjoint`). -/
theorem measurable_initialWeight (s : ℕ) : Measurable (initialWeight (n := n) s) := by
  unfold initialWeight
  exact (measurable_const.add (measurable_const.mul
    (((initialCoordinates n).measurable.norm).pow_const 2))).pow_const _

/-- Finite full Fourier energy on physical `(z,y)` L² classes
(`app:ch_background:prop:bg-adjoint`). The actual initial input in `(z,η)`
must first be realized by the partial unitary inverse transform. -/
def MemPhysicalSobolev (s : ℕ) (f : CarrierL2 n) : Prop :=
  CarrierWeightedMem (initialWeight s) (initialFourier n f)

/-- Numerical full Fourier Sobolev energy on physical `(z,y)` classes.
Use only together with `MemPhysicalSobolev`: an infinite extended norm has
`toReal = 0` (`app:ch_background:prop:bg-adjoint`). -/
def physicalSobolevNorm (s : ℕ) (f : CarrierL2 n) : ℝ :=
  (eLpNorm (fun ξ ↦ initialWeight s ξ • initialFourier n f ξ) 2 (carrierMeasure n)).toReal

/-- Measurability of the weighted Fourier representative
(`app:ch_background:prop:bg-adjoint`). -/
theorem aestronglyMeasurable_weightedInitialFourier (s : ℕ) (f : CarrierL2 n) :
    AEStronglyMeasurable (fun ξ ↦ initialWeight s ξ • initialFourier n f ξ)
      (carrierMeasure n) :=
  (measurable_initialWeight s).aestronglyMeasurable.smul (Lp.memLp _).aestronglyMeasurable

/-- Finite energy at order zero is exactly automatic for L² data
(`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem memPhysicalSobolev_zero (f : CarrierL2 n) : MemPhysicalSobolev 0 f := by
  simpa [MemPhysicalSobolev, CarrierWeightedMem] using (Lp.memLp (initialFourier n f))

/-- The physical Sobolev norm has the published carrier L² normalization at
level zero (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem physicalSobolevNorm_zero (f : CarrierL2 n) :
    physicalSobolevNorm 0 f = ‖f‖ := by
  simp only [physicalSobolevNorm, initialWeight_zero, one_smul]
  rw [← Lp.norm_def, initialFourier_norm]

/-- Lower orders inherit convergence of the full energy
(`app:ch_background:prop:bg-adjoint`). -/
theorem MemPhysicalSobolev.mono {s t : ℕ} {f : CarrierL2 n}
    (hf : MemPhysicalSobolev t f) (hst : s ≤ t) : MemPhysicalSobolev s f := by
  apply MemLp.mono hf (aestronglyMeasurable_weightedInitialFourier s f)
  filter_upwards [] with ξ
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (initialWeight_pos _ _)]
  exact mul_le_mul_of_nonneg_right (initialWeight_mono hst ξ) (norm_nonneg _)

/-- Quantitative comparison of full Sobolev orders, under the necessary
finite-energy premise (`app:ch_background:prop:bg-adjoint`). -/
theorem physicalSobolevNorm_mono {s t : ℕ} {f : CarrierL2 n}
    (hf : MemPhysicalSobolev t f) (hst : s ≤ t) :
    physicalSobolevNorm s f ≤ physicalSobolevNorm t f := by
  apply ENNReal.toReal_mono hf.eLpNorm_ne_top
  apply eLpNorm_mono (aestronglyMeasurable_weightedInitialFourier s f)
  intro ξ
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (initialWeight_pos _ _)]
  exact mul_le_mul_of_nonneg_right (initialWeight_mono hst ξ) (norm_nonneg _)

/-- The full finite energy controls the base L² norm
(`app:ch_background:prop:bg-adjoint`). -/
theorem norm_le_physicalSobolevNorm {s : ℕ} {f : CarrierL2 n}
    (hf : MemPhysicalSobolev s f) : ‖f‖ ≤ physicalSobolevNorm s f := by
  simpa using physicalSobolevNorm_mono hf (Nat.zero_le s)

/-- Compatibility with the existing weighted carrier norm API, applied to
the *full Fourier transform* (`app:ch_background:prop:bg-adjoint`). -/
theorem physicalSobolevNorm_eq_carrierWeightedNorm (s : ℕ) (f : CarrierL2 n)
    (hf : MemPhysicalSobolev s f) :
    physicalSobolevNorm s f =
      carrierWeightedNorm (initialWeight s) (initialFourier n f) hf := by
  exact (Lp.norm_toLp _ hf).symm

end JanetCartan.CarrierSobolev
