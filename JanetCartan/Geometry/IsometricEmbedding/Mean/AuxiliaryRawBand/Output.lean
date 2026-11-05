module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.Source
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Assembly

/-!
# The complete cut auxiliary output

The image and exterior components in `app:ch_background:defn:bg-mixed` retain
their original operators after the raw input cuts. The order-zero bounds below
use only the norm of the original augmented row and a bounded `Q₀`. No Sobolev
regularity or inverse property of `Q₀` is assumed or asserted.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.AuxiliaryRawBand

open ContinuumRow

variable {n : ℕ}

/-- Image output using the same ordered covector and original measurement cutoff
(`app:ch_background:defn:bg-mixed`). -/
def imageOutput (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) : OutputL2 n :=
  cutoffMultiplier χmeas (reducedWeakOperator c (rawCovectorH1 χsrc K h))

/-- Compatibility with the literal published image channel, without a normal
reduction hypothesis (`app:ch_background:defn:bg-mixed`). -/
theorem imageOutput_eq_imageChannel
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) :
    imageOutput c χmeas χsrc K h =
      imageChannel c χmeas χsrc (RawCutoffBounds.auxiliarySquaredCutoff K h) := rfl

/-- The original exterior channel applied after the same raw Fourier cut
(`app:ch_background:defn:bg-mixed`). -/
def exteriorOutput (ψ : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) : OutputL2 n :=
  exteriorChannel ψ (RawCutoffBounds.auxiliarySquaredCutoff K h)

/-- The exterior output has the original cut-and-multiply representative
(`app:ch_background:prop:bg-mixed-physical`). -/
theorem exteriorOutput_coeFn (ψ : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) :
    exteriorOutput ψ K h =ᵐ[volume] rawSource (1 - ψ) K h :=
  rawSourceL2_coeFn (1 - ψ) K h

/-- The exterior representative is smooth whenever the original exterior
cutoff is smooth (`app:ch_background:eq:bg-Vaux-raw-band`). -/
theorem isSmoothPeriodic_exteriorOutput (ψ : C(Torus n, ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) :
    IsSmoothPeriodic (rawSource (1 - ψ) K h) :=
  isSmoothPeriodic_rawSource (1 - ψ)
    ⟨continuous_const.sub hψ.1, contDiff_const.sub hψ.2⟩ K h

/-- Both auxiliary components are retained (`app:ch_background:eq:bg-Vaux-raw-band`). -/
def auxiliaryOutput (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ)) (K : ℝ) (him hout : OutputL2 n) : OutputL2 n :=
  imageOutput c χmeas χsrc K him + exteriorOutput ψ K hout

/-- The exterior output vanishes on the actual plateau of the original `ψ`
(`app:ch_background:prop:bg-mixed-physical`). -/
theorem exteriorOutput_zero_on_core (ψ : C(Torus n, ℝ)) (core : Set (Torus n))
    (hψ : ∀ x ∈ core, ψ x = 1) (K : ℝ) (h : OutputL2 n) :
    ∀ᵐ x ∂volume, x ∈ core → exteriorOutput ψ K h x = 0 :=
  exteriorChannel_zero_on_core ψ core hψ _

/-- On the core the full auxiliary output is the weak reduced image expression
of the same covector (`app:ch_background:prop:bg-mixed-physical`). -/
theorem auxiliaryOutput_on_core
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ)) (core : Set (Torus n))
    (hm : ∀ x ∈ core, χmeas x = 1) (hψ : ∀ x ∈ core, ψ x = 1)
    (K : ℝ) (him hout : OutputL2 n) :
    ∀ᵐ x ∂volume, x ∈ core → auxiliaryOutput c χmeas χsrc ψ K him hout x =
      reducedWeakOperator c (rawCovectorH1 χsrc K him) x := by
  filter_upwards [Lp.coeFn_add (imageOutput c χmeas χsrc K him) (exteriorOutput ψ K hout),
    cutoffMultiplier_coeFn χmeas (reducedWeakOperator c (rawCovectorH1 χsrc K him)),
    exteriorOutput_zero_on_core ψ core hψ K hout] with x ha hi ho
  intro hx
  change (imageOutput c χmeas χsrc K him + exteriorOutput ψ K hout) x = _
  rw [ha, Pi.add_apply, ho hx, add_zero]
  change cutoffMultiplier χmeas (reducedWeakOperator c (rawCovectorH1 χsrc K him)) x = _
  rw [hi, hm x hx, one_smul]

/-- The image contribution is uniformly L² bounded after the raw cut
(`app:ch_background:eq:bg-Vaux-raw-band`, order zero). -/
theorem norm_imageOutput_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K) (h : OutputL2 n) :
    ‖imageOutput c χmeas χsrc K h‖ ≤
      (‖χmeas‖ * reducedCoefficientBound c * ‖χsrc‖) * ‖h‖ := by
  rw [imageOutput_eq_imageChannel]
  apply (imageChannel_norm_apply_le _ _ _ _).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity [reducedCoefficientBound_nonneg c])
  simpa only [pow_zero, one_mul, (periodicSobolevScale n (Euclidean n)).gradeNorm_zero]
    using RawCutoffBounds.auxiliarySquaredCutoff_band hK h 0

/-- The original exterior component satisfies the same raw order-zero bound
(`app:ch_background:eq:bg-Vaux-raw-band`). -/
theorem norm_exteriorOutput_le (ψ : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K)
    (h : OutputL2 n) : ‖exteriorOutput ψ K h‖ ≤ ‖1 - ψ‖ * ‖h‖ := by
  exact norm_rawSourceL2_le (1 - ψ) hK h

/-- The complete auxiliary output includes both contributions in its estimate
(`app:ch_background:eq:bg-Vaux-raw-band`, order zero). -/
theorem norm_auxiliaryOutput_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K) (him hout : OutputL2 n) :
    ‖auxiliaryOutput c χmeas χsrc ψ K him hout‖ ≤
      (‖χmeas‖ * reducedCoefficientBound c * ‖χsrc‖) * ‖him‖ + ‖1 - ψ‖ * ‖hout‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_imageOutput_le c χmeas χsrc hK him)
    (norm_exteriorOutput_le ψ hK hout))

/-- The actual two-channel cut normal `A₀ π_K² A₀*`
(`app:ch_background:defn:bg-mixed`). -/
def cutAuxiliaryNormal
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K) :
    OutputL2 n →L[ℝ] OutputL2 n :=
  imageChannel c χmeas χsrc ∘L RawCutoffBounds.auxiliarySquaredCutoffCLM hK ∘L
      (imageChannel c χmeas χsrc).adjoint +
    exteriorChannel ψ ∘L RawCutoffBounds.auxiliarySquaredCutoffCLM hK ∘L exteriorChannel ψ

/-- Exact specialization to the original auxiliary adjoint, without changing
the raw cutoff order (`app:ch_background:defn:bg-mixed`). -/
theorem cutAuxiliaryNormal_apply
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K) (w : OutputL2 n) :
    cutAuxiliaryNormal c χmeas χsrc ψ hK w = auxiliaryOutput c χmeas χsrc ψ K
      ((imageChannel c χmeas χsrc).adjoint w) (exteriorChannel ψ w) := rfl

section OriginalRow

variable {ι : Type*} [Fintype ι]

/-- The image datum is literally the image slot of the original augmented
adjoint (`app:ch_background:defn:bg-mixed`). -/
theorem augmentedAdjoint_image
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (w : OutputL2 n) :
    ((augmentedRow image T ψ).adjoint w).fst.fst = image.adjoint w := by
  rw [augmentedRow_adjoint_apply]
  change ((physicalRow image T).adjoint w).fst = _
  rw [physicalRow_adjoint_apply]
  rfl

/-- The exterior datum is literally the original exterior adjoint slot
(`app:ch_background:defn:bg-mixed`). -/
theorem augmentedAdjoint_exterior
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (w : OutputL2 n) :
    ((augmentedRow image T ψ).adjoint w).snd = exteriorChannel ψ w := by
  rw [augmentedRow_adjoint_apply]
  rfl

/-- Only the original row norm and the L² operator norm of `Q₀` control the
image datum (`app:ch_background:eq:bg-Vaux-band`, order zero). The actual
coercive inverse must later be supplied by `jc-continuum-l2-inverse`. -/
theorem norm_imageAdjoint_Q0_le
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n) :
    ‖image.adjoint (Q0 e)‖ ≤ ‖augmentedRow image T ψ‖ * ‖Q0‖ * ‖e‖ := by
  rw [← augmentedAdjoint_image image T ψ]
  calc
    _ ≤ ‖(augmentedRow image T ψ).adjoint (Q0 e)‖ :=
      (WithLp.norm_fst_le _ _).trans (WithLp.norm_fst_le _ _)
    _ ≤ ‖(augmentedRow image T ψ).adjoint‖ * ‖Q0 e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖augmentedRow image T ψ‖ * (‖Q0‖ * ‖e‖) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul_of_nonneg_left (Q0.le_opNorm e) (norm_nonneg _)
    _ = _ := by ring

/-- The same original row controls the exterior datum, with no regularity
assumption on `Q₀ e` (`app:ch_background:eq:bg-Vaux-band`, order zero). -/
theorem norm_exterior_Q0_le
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n) :
    ‖exteriorChannel ψ (Q0 e)‖ ≤ ‖augmentedRow image T ψ‖ * ‖Q0‖ * ‖e‖ := by
  rw [← augmentedAdjoint_exterior image T ψ]
  calc
    _ ≤ ‖(augmentedRow image T ψ).adjoint (Q0 e)‖ := WithLp.norm_snd_le _ _
    _ ≤ ‖(augmentedRow image T ψ).adjoint‖ * ‖Q0 e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖augmentedRow image T ψ‖ * (‖Q0‖ * ‖e‖) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul_of_nonneg_left (Q0.le_opNorm e) (norm_nonneg _)
    _ = _ := by ring

/-- The same original augmented row controls the realized covector in H¹,
using only raw L² input (`app:ch_background:eq:bg-Vaux-band`, order zero). -/
theorem norm_rawCovectorH1_imageAdjoint_Q0_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) {K : ℝ} (hK : 1 ≤ K) (e : OutputL2 n) :
    ‖rawCovectorH1 χsrc K ((imageChannel c χmeas χsrc).adjoint (Q0 e))‖ ≤
      ‖χsrc‖ * ‖augmentedRow (imageChannel c χmeas χsrc) T ψ‖ * ‖Q0‖ * ‖e‖ := by
  apply (norm_rawCovectorH1_le χsrc hK _).trans
  calc
    _ ≤ ‖χsrc‖ * (‖augmentedRow (imageChannel c χmeas χsrc) T ψ‖ * ‖Q0‖ * ‖e‖) :=
      mul_le_mul_of_nonneg_left (norm_imageAdjoint_Q0_le _ T ψ Q0 e) (norm_nonneg _)
    _ = _ := by ring

/-- Complete order-zero raw-band bound for the same auxiliary cut normal and
the original augmented row (`app:ch_background:eq:bg-Vaux-band`). -/
theorem norm_cutAuxiliaryNormal_Q0_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) {K : ℝ} (hK : 1 ≤ K) (e : OutputL2 n) :
    ‖cutAuxiliaryNormal c χmeas χsrc ψ hK (Q0 e)‖ ≤
      (‖χmeas‖ * reducedCoefficientBound c * ‖χsrc‖ + ‖1 - ψ‖) *
        ‖augmentedRow (imageChannel c χmeas χsrc) T ψ‖ * ‖Q0‖ * ‖e‖ := by
  rw [cutAuxiliaryNormal_apply]
  apply (norm_auxiliaryOutput_le c χmeas χsrc ψ hK _ _).trans
  calc
    _ ≤ (‖χmeas‖ * reducedCoefficientBound c * ‖χsrc‖) *
          (‖augmentedRow (imageChannel c χmeas χsrc) T ψ‖ * ‖Q0‖ * ‖e‖) +
        ‖1 - ψ‖ * (‖augmentedRow (imageChannel c χmeas χsrc) T ψ‖ * ‖Q0‖ * ‖e‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (norm_imageAdjoint_Q0_le _ T ψ Q0 e)
          (mul_nonneg (mul_nonneg (norm_nonneg _) (reducedCoefficientBound_nonneg c))
            (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left (norm_exterior_Q0_le _ T ψ Q0 e) (norm_nonneg _))
    _ = _ := by ring

end OriginalRow
end JanetCartan.AuxiliaryRawBand
