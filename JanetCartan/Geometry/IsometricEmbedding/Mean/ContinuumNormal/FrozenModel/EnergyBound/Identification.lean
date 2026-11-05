module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.EuclideanEnergy
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.EuclideanSupportGap

/-!
# Identification of the two frozen Fourier energies

The adapter for `app:ch_background:prop:bg-frame` identifies the L² multiplier
energy with the frozen model's literal Fourier integral. Both quadratures and
the physical covector `2πξ` are retained. The spectral producer supplies a
continuous symbol bounded in Frobenius norm; the operator bound and energy
integrability below are consequences, not additional analytic premises.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Matrix
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel

open EuclideanSupportGap

variable {n : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "L²" => Lp (α := E) V 2 volume

/-- The complex real-part pairing is exactly the sum of the frozen model's
two real quadratic forms (`app:ch_background:prop:bg-frame`). -/
theorem re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm
    (a : Matrix (Fin n) (Fin n) ℝ) (z : V) :
    (inner ℂ z (complexifyMatrix a z)).re = realifiedMatrixQuadraticForm a z := by
  rw [re_inner_complexifyMatrix]
  simp [realifiedMatrixQuadraticForm, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- The Frobenius bound from the actual frozen-symbol producer implies the
complex operator bound used by the Euclidean energy leaf
(`app:ch_background:prop:bg-frame`). -/
theorem norm_complexifyMatrix_le_two_mul_frobenius
    (a : Matrix (Fin n) (Fin n) ℝ) : ‖complexifyMatrix a‖ ≤ 2 * ‖a‖ := by
  apply norm_complexifyMatrix_le
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
    ← replicateCol_mulVec, frobenius_norm_replicateCol, WithLp.toLp_ofLp] using
    (frobenius_norm_mul a (replicateCol Unit v.ofLp))

/-- Real quadratic spectral bounds pass to the literal frozen form on both
Fourier quadratures (`app:ch_background:prop:bg-frame`). -/
theorem realifiedMatrixQuadraticForm_ge {a : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (ha : ∀ v : E, c * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (a *ᵥ v.ofLp)) (z : V) :
    c * ‖z‖ ^ 2 ≤ realifiedMatrixQuadraticForm a z := by
  rw [← re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm]
  apply complexifyMatrix_gap
  intro v
  simpa [PiLp.inner_apply, RCLike.inner_apply, Matrix.toLpLin_apply,
    dotProduct, mul_comm] using ha v

/-- Almost-everywhere equality of the energy densities follows from the
existing Fourier-integral/L² identification. The symbol is evaluated at the
same physical frequency on both sides (`app:ch_background:prop:bg-frame`). -/
theorem ae_energyDensity_complexifyMatrix_eq_realified
    (b : E → Matrix (Fin n) (Fin n) ℝ) (f : E → V)
    (hf : Integrable f) (hf₂ : MemLp f 2 volume) :
    (fun ξ ↦ (inner ℂ ((𝓕 (hf₂.toLp f) : L²) ξ)
      (complexifyMatrix (b ((2 * Real.pi) • ξ)) ((𝓕 (hf₂.toLp f) : L²) ξ))).re)
      =ᵐ[volume] (fun ξ ↦ realifiedMatrixQuadraticForm (b ((2 * Real.pi) • ξ)) (𝓕 f ξ)) := by
  have hu : Integrable (hf₂.toLp f : E → V) := hf.congr hf₂.coeFn_toLp.symm
  have hFourier : (𝓕 (hf₂.toLp f) : L²) =ᵐ[volume] 𝓕 f :=
    (Localization.fourierTransform_coeFn_ae_integral_hilbert (hf₂.toLp f) hu).trans
      (Filter.Eventually.of_forall (Real.fourier_congr_ae hf₂.coeFn_toLp))
  filter_upwards [hFourier] with ξ hξ
  rw [hξ, re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm]

/-- The leaf's actual L² energy equals the frozen model's literal integral
for every L¹ ∩ L² field (`app:ch_background:prop:bg-frame`). No energy identity
is assumed, and no regularity of the symbol is needed for this equality. -/
theorem energy_complexifyMatrix_toLp_eq_euclideanFrozenEnergy
    (b : E → Matrix (Fin n) (Fin n) ℝ) (f : E → V)
    (hf : Integrable f) (hf₂ : MemLp f 2 volume) :
    energy (fun k ↦ complexifyMatrix (b k)) (hf₂.toLp f) = euclideanFrozenEnergy b f :=
  integral_congr_ae (ae_energyDensity_complexifyMatrix_eq_realified b f hf hf₂)

/-- The same equality for an L² representative, used by the physical support
and inner-radius deductions (`app:ch_background:prop:bg-frame`). -/
theorem energy_complexifyMatrix_eq_euclideanFrozenEnergy
    (b : E → Matrix (Fin n) (Fin n) ℝ) (u : L²) (hu : Integrable (u : E → V)) :
    energy (fun k ↦ complexifyMatrix (b k)) u = euclideanFrozenEnergy b u := by
  apply integral_congr_ae
  filter_upwards [Localization.fourierTransform_coeFn_ae_integral_hilbert u hu] with ξ hξ
  rw [hξ, re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm]

/-- Continuity and the Frobenius bound of the frozen symbol prove
integrability of its literal energy density (`app:ch_background:prop:bg-frame`). -/
theorem integrable_euclideanFrozenEnergy_density
    (b : E → Matrix (Fin n) (Fin n) ℝ) (hb : Continuous b)
    {M : ℝ} (hM : ∀ k, ‖b k‖ ≤ M) (f : E → V)
    (hf : Integrable f) (hf₂ : MemLp f 2 volume) :
    Integrable (fun ξ ↦ realifiedMatrixQuadraticForm (b ((2 * Real.pi) • ξ)) (𝓕 f ξ)) := by
  have hbound (k : E) : ‖complexifyMatrix (b k)‖ ≤ 2 * M :=
    (norm_complexifyMatrix_le_two_mul_frobenius (b k)).trans (by gcongr; exact hM k)
  exact (integrable_energy (fun k ↦ complexifyMatrix (b k))
    (continuous_complexifyMatrix hb) hbound (hf₂.toLp f)).congr
      (ae_energyDensity_complexifyMatrix_eq_realified b f hf hf₂)

end JanetCartan.ContinuumNormal.FrozenModel
