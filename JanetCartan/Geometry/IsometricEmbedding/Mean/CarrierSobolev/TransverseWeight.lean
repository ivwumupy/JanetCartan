module
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.RawSpace
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.TransverseWeight.Bounded
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Full raw Sobolev energy controls the transverse Bessel weight

The raw cutoff estimate following `app:ch_background:defn:bg-mixed` needs
transverse Bessel energy on the literal carrier product measure `dz dη`.
Starting from the full physical Sobolev energy of the constructed partial
unitary inverse (`app:ch_background:prop:bg-adjoint`), we prove that energy
bound, including weighted membership, without additional analytic hypotheses.

Bounded transverse weights obey the exact rescaled Plancherel identity proved
in `TransverseWeight.Bounded`. The rescaled Bessel weight is pointwise bounded
by the full initial weight. Truncation and the lower semicontinuity of the
extended L² norm then give the unbounded estimate. All statements include
transverse dimension zero.
-/

open MeasureTheory Filter
open scoped ENNReal Topology
@[expose] public noncomputable section
namespace JanetCartan.CarrierSobolev
open ContinuumRow RawCutoffBounds
variable {n : ℕ}

/-- The literal transverse Bessel weight used by the raw cutoff estimate
following `app:ch_background:defn:bg-mixed`. -/
def transverseBesselWeight (s : ℕ) (x : CarrierVariable n) : ℝ :=
  Real.sqrt (1 + ‖x.2‖ ^ 2) ^ s

/-- Measurability of the raw cutoff weight, needed for the L² limit passage
in `app:ch_background:defn:bg-mixed`. -/
theorem measurable_transverseBesselWeight (s : ℕ) :
    Measurable (transverseBesselWeight (n := n) s) :=
  (measurable_const.add (measurable_snd.norm.pow_const 2)).sqrt.pow_const s

/-- Nonnegativity of the transverse energy weight in the raw cutoff estimate
following `app:ch_background:defn:bg-mixed`. -/
theorem transverseBesselWeight_nonneg (s : ℕ) (x : CarrierVariable n) :
    0 ≤ transverseBesselWeight s x := by
  unfold transverseBesselWeight
  positivity

/-- The radian transverse weight is controlled by the full physical derivative
weight. This comparison connects `app:ch_background:prop:bg-adjoint` to the
raw cutoff estimate following `app:ch_background:defn:bg-mixed`. -/
theorem transverseBesselWeight_rescaled_le_initialWeight (s : ℕ) (x : CarrierVariable n) :
    transverseBesselWeight s (x.1, (2 * Real.pi) • x.2) ≤ initialWeight s x := by
  rw [transverseBesselWeight, initialWeight_eq_coordinates,
    Real.rpow_div_two_eq_sqrt _ (by positivity), Real.rpow_natCast]
  apply pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_pow]
  nlinarith only [mul_nonneg (sq_nonneg (2 * Real.pi))
    (add_nonneg (sq_nonneg |x.1.1|) (sq_nonneg ‖x.1.2‖))]

private def truncatedWeight (s N : ℕ) (η : Euclidean (n - 1)) : ℝ :=
  min (Real.sqrt (1 + ‖η‖ ^ 2) ^ s) (N : ℝ)

private theorem measurable_truncatedWeight (s N : ℕ) :
    Measurable (truncatedWeight (n := n) s N) :=
  ((measurable_const.add (measurable_id.norm.pow_const 2)).sqrt.pow_const s).min
    measurable_const

private theorem truncatedWeight_nonneg (s N : ℕ) (η : Euclidean (n - 1)) :
    0 ≤ truncatedWeight s N η := by
  unfold truncatedWeight
  positivity

private theorem truncatedWeight_bound (s N : ℕ) (η : Euclidean (n - 1)) :
    |truncatedWeight s N η| ≤ (N : ℝ) := by
  rw [abs_of_nonneg (truncatedWeight_nonneg s N η)]
  exact min_le_right _ _

private theorem truncatedWeight_eLpNorm_le (s N : ℕ) (f : CarrierL2 n) :
    eLpNorm (fun x => truncatedWeight s N x.2 • f x) 2 (carrierMeasure n) ≤
      eLpNorm (fun x => initialWeight s x • initialFourier n (partialUnitaryInverse n f) x)
        2 (carrierMeasure n) := by
  rw [TransverseWeight.bounded_eLpNorm_rescale (truncatedWeight s N)
    (measurable_truncatedWeight s N) (truncatedWeight_bound s N) f]
  apply eLpNorm_mono
    (((measurable_truncatedWeight s N).comp
      (measurable_snd.const_smul (2 * Real.pi))).aestronglyMeasurable.smul
      (Lp.memLp _).aestronglyMeasurable)
  intro x
  change ‖truncatedWeight s N ((2 * Real.pi) • x.2) •
    initialFourier n (partialUnitaryInverse n f) x‖ ≤
    ‖initialWeight s x • initialFourier n (partialUnitaryInverse n f) x‖
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (truncatedWeight_nonneg _ _ _), abs_of_pos (initialWeight_pos _ _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (min_le_left _ _).trans (transverseBesselWeight_rescaled_le_initialWeight s x)

/-- Extended transverse energy is bounded by the full Fourier energy after
actual partial synthesis. Bounded truncations and the L² limit bound prove
this without assuming weighted membership (`app:ch_background:prop:bg-adjoint`). -/
theorem transverseBesselWeight_eLpNorm_le (s : ℕ) (f : CarrierL2 n) :
    eLpNorm (fun x => transverseBesselWeight s x • f x) 2 (carrierMeasure n) ≤
      eLpNorm (fun x => initialWeight s x • initialFourier n (partialUnitaryInverse n f) x)
        2 (carrierMeasure n) := by
  apply Lp.eLpNorm_le_of_ae_tendsto
    (f := fun N x => truncatedWeight s N x.2 • f x)
    (u := atTop) (.of_forall fun N => truncatedWeight_eLpNorm_le s N f)
    (fun N => ((measurable_truncatedWeight s N).comp measurable_snd).aestronglyMeasurable.smul
      (Lp.memLp f).aestronglyMeasurable)
    ((measurable_transverseBesselWeight s).aestronglyMeasurable.smul
      (Lp.memLp f).aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (transverseBesselWeight s x)] with N hN
  change transverseBesselWeight s x • f x =
    min (transverseBesselWeight s x) (N : ℝ) • f x
  rw [min_eq_left hN]

/-- Full raw Sobolev membership supplies the transverse weighted membership
required by `RawCutoffBounds.carrierSquaredCutoff_tail` in the raw cutoff
estimate following `app:ch_background:defn:bg-mixed`. -/
theorem MemRawSobolev.carrierWeightedMem_transverseBesselWeight {s : ℕ} {f : CarrierL2 n}
    (hf : MemRawSobolev s f) : CarrierWeightedMem (transverseBesselWeight s) f := by
  exact (transverseBesselWeight_eLpNorm_le s f).trans_lt hf.eLpNorm_lt_top

/-- The full raw Sobolev norm controls transverse Bessel energy with constant
one. This is the carrier comparison needed to deduce the raw cutoff estimate
following `app:ch_background:defn:bg-mixed` from the full `X^s` norm of
`app:ch_background:prop:bg-adjoint`. -/
theorem carrierWeightedNorm_transverseBesselWeight_le {s : ℕ} {f : CarrierL2 n}
    (hf : MemRawSobolev s f) :
    carrierWeightedNorm (transverseBesselWeight s) f
      hf.carrierWeightedMem_transverseBesselWeight ≤ rawSobolevNorm s f := by
  exact (Lp.norm_toLp _ hf.carrierWeightedMem_transverseBesselWeight).trans_le
    (ENNReal.toReal_mono hf.eLpNorm_ne_top (transverseBesselWeight_eLpNorm_le s f))

end JanetCartan.CarrierSobolev
