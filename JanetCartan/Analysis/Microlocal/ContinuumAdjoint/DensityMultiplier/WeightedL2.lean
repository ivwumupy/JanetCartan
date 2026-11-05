module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds.Carrier

/-!
# The unbounded half-order multiplier on carrier L²

The frequency-side estimate needed in `app:ch_background:eq:bg-density-adjoint`.
The measure is the shared literal Lebesgue measure `dz dη`. No upper frequency
cutoff is imposed. These results also apply to each differentiated angular mask
in the eventual carrier-variable Leibniz expansion.

This is a weighted L² estimate, not the full mixed Sobolev estimate: the latter
additionally needs weak carrier derivatives and partial inverse Plancherel.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier

open ContinuumRow RawCutoffBounds

variable {n : ℕ}

/-- Transverse Bessel weight for the raw tail and density estimates
(`app:ch_background:defn:bg-mixed`, `app:ch_background:eq:bg-density-adjoint`). -/
def etaBesselWeight (s : ℕ) (x : CarrierVariable n) : ℝ :=
  Real.sqrt (1 + ‖x.2‖ ^ 2) ^ s

/-- Nonnegativity of the transverse weight in the density estimate. -/
theorem etaBesselWeight_nonneg (s : ℕ) (x : CarrierVariable n) :
    0 ≤ etaBesselWeight s x := by unfold etaBesselWeight; positivity

/-- The transverse weight is measurable on the actual initial variables
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem continuous_etaBesselWeight (s : ℕ) :
    Continuous (etaBesselWeight (n := n) s) := by
  unfold etaBesselWeight
  fun_prop

/-- Spending one integer transverse derivative bounds the exact half-order
symbol on the whole frequency space (`app:ch_background:eq:bg-density-adjoint`). -/
theorem etaBesselWeight_mul_sqrt_le (s : ℕ) (x : CarrierVariable n) :
    etaBesselWeight s x * Real.sqrt ‖x.2‖ ≤ etaBesselWeight (s + 1) x := by
  have h : ‖x.2‖ ≤ 1 + ‖x.2‖ ^ 2 := by nlinarith [sq_nonneg (‖x.2‖ - 1)]
  simpa only [etaBesselWeight, pow_succ] using
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (etaBesselWeight_nonneg s x)

/-- The exact half-order symbol with its fixed mask, prior to inverse Fourier
transform (`app:ch_background:eq:bg-density-adjoint`). -/
def halfOrderCoefficient (a : CarrierVariable n → ℂ) (x : CarrierVariable n) : ℂ :=
  (Real.sqrt ‖x.2‖ : ℂ) * a x

/-- Measurability of the exact, unbounded symbol
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem aestronglyMeasurable_halfOrderCoefficient {a : CarrierVariable n → ℂ}
    (ha : AEStronglyMeasurable a (carrierMeasure n)) :
    AEStronglyMeasurable (halfOrderCoefficient a) (carrierMeasure n) :=
  ((Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp (continuous_snd.norm))).aestronglyMeasurable).mul ha

/-- Pointwise weighted estimate for the exact symbol. The mask bound, rather
than an operator estimate, is the input (`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_weighted_halfOrderCoefficient_mul_le (s : ℕ)
    {a : CarrierVariable n → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (x : CarrierVariable n) (ha : ‖a x‖ ≤ M) (v : ℂ) :
    ‖etaBesselWeight s x • (halfOrderCoefficient a x * v)‖ ≤
      M * ‖etaBesselWeight (s + 1) x • v‖ := by
  simp only [halfOrderCoefficient, norm_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (etaBesselWeight_nonneg _ _)]
  calc
    _ ≤ etaBesselWeight s x * (Real.sqrt ‖x.2‖ * M * ‖v‖) := by
      gcongr
      exact etaBesselWeight_nonneg s x
    _ = M * (etaBesselWeight s x * Real.sqrt ‖x.2‖) * ‖v‖ := by ring
    _ ≤ M * etaBesselWeight (s + 1) x * ‖v‖ := by
      gcongr
      exact etaBesselWeight_mul_sqrt_le s x
    _ = _ := by ring

/-- Actual membership of the weighted output for arbitrary carrier L² data,
without frequency truncation (`app:ch_background:eq:bg-density-adjoint`). -/
theorem memLp_weighted_halfOrder_mul (s : ℕ)
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    MemLp (fun x ↦ etaBesselWeight s x • (halfOrderCoefficient a x * f x))
      2 (carrierMeasure n) := by
  apply (hf.norm.const_mul M).mono'
  · exact (continuous_etaBesselWeight s).aestronglyMeasurable.smul
      ((aestronglyMeasurable_halfOrderCoefficient ha).mul (Lp.aestronglyMeasurable f))
  · filter_upwards [hbound] with x hx
    exact norm_weighted_halfOrderCoefficient_mul_le s hM x hx (f x)

/-- Frequency-side weighted output as an actual L² class, with the original
half-order multiplier (`app:ch_background:eq:bg-density-adjoint`). -/
def weightedHalfOrderOutput (s : ℕ)
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    CarrierL2 n :=
  (memLp_weighted_halfOrder_mul s ha hM hbound f hf).toLp _

/-- The constructed class agrees almost everywhere with the literal symbol
times the input (`app:ch_background:eq:bg-density-adjoint`). -/
theorem weightedHalfOrderOutput_coeFn (s : ℕ)
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    weightedHalfOrderOutput s ha hM hbound f hf =ᵐ[carrierMeasure n]
      fun x ↦ etaBesselWeight s x • (halfOrderCoefficient a x * f x) :=
  MemLp.coeFn_toLp _

/-- The all-data weighted L² estimate for the unbounded half-order multiplier.
This is the frequency-side ingredient of `app:ch_background:eq:bg-density-adjoint`;
no Fourier, weak derivative, or physical cutoff estimate is assumed. -/
theorem norm_weightedHalfOrderOutput_le (s : ℕ)
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    ‖weightedHalfOrderOutput s ha hM hbound f hf‖ ≤
      M * carrierWeightedNorm (etaBesselWeight (s + 1)) f hf := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedHalfOrderOutput_coeFn s ha hM hbound f hf,
    hf.coeFn_toLp, hbound] with x hout hin hx
  rw [hout, hin]
  exact norm_weighted_halfOrderCoefficient_mul_le s hM x hx (f x)

/-- The single unweighted frequency output for the density construction. The
one-derivative weighted domain is sufficient at level zero, and the coefficient
is still the exact half-order coefficient (`app:ch_background:eq:bg-density-adjoint`). -/
def halfOrderOutput
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight 1) f) : CarrierL2 n :=
  weightedHalfOrderOutput 0 ha hM hbound f hf

/-- The unweighted frequency output agrees with the same symbol at every
Sobolev order (`app:ch_background:eq:bg-density-adjoint`). -/
theorem halfOrderOutput_coeFn
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight 1) f) :
    halfOrderOutput ha hM hbound f hf =ᵐ[carrierMeasure n]
      fun x ↦ halfOrderCoefficient a x * f x := by
  simpa only [halfOrderOutput, etaBesselWeight, pow_zero, one_smul] using
    weightedHalfOrderOutput_coeFn 0 ha hM hbound f hf

/-- Every higher-order weighted estimate concerns the same frequency output,
not an order-dependent choice of realization
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem carrierWeightedMem_halfOrderOutput (s : ℕ)
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight 1) f)
    (hs : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    CarrierWeightedMem (etaBesselWeight s) (halfOrderOutput ha hM hbound f hf) := by
  apply (memLp_weighted_halfOrder_mul s ha hM hbound f hs).ae_eq
  filter_upwards [halfOrderOutput_coeFn ha hM hbound f hf] with x hx
  rw [hx]

/-- All weighted estimates hold for the one common unweighted output. This
is the transverse part of the final Sobolev estimate before the physical cutoff
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem carrierWeightedNorm_halfOrderOutput_le (s : ℕ)
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight 1) f)
    (hs : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    carrierWeightedNorm (etaBesselWeight s) (halfOrderOutput ha hM hbound f hf)
      (carrierWeightedMem_halfOrderOutput s ha hM hbound f hf hs) ≤
        M * carrierWeightedNorm (etaBesselWeight (s + 1)) f hs := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(carrierWeightedMem_halfOrderOutput s ha hM hbound f hf hs).coeFn_toLp,
    hs.coeFn_toLp, halfOrderOutput_coeFn ha hM hbound f hf, hbound] with x hw hin hout hx
  rw [hw, hin, hout]
  exact norm_weighted_halfOrderCoefficient_mul_le s hM x hx (f x)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
