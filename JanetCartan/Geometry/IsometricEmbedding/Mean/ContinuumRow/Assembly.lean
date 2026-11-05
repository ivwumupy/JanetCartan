module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Cutoff
public import JanetCartan.Analysis.Operator.RealQuadratures
public import JanetCartan.Analysis.Operator.NormalAugmentation

/-!
# Assembly on the continuum Hilbert spaces

The algebraic assembly in `app:ch_background:defn:bg-row` and
`app:ch_background:eq:bg-realification`. These lemmas take a bounded image
operator and bounded complex carrier operators as explicit arguments. They do
not construct those operators from the geometric kernel. That analytic obligation
remains with the continuum-row task, rather than being hidden in a record field.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Both real quadratures of a bounded carrier operator on the specified spaces
(`app:ch_background:eq:bg-realification`); its kernel realization is a separate obligation. -/
def carrierChannel (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    CarrierL2 n →L[ℝ] OutputL2 n := realQuadratureChannel T

/-- Literal real adjoint, retaining both initial quadratures
(`app:ch_background:eq:bg-realification`). -/
theorem carrierChannel_adjoint_apply (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (w : OutputL2 n) :
    (carrierChannel T).adjoint w = (2 : ℝ) • T.adjoint (l2ComplexInclusion volume w) :=
  realQuadratureChannel_adjoint_apply T w

/-- The real normal has the manuscript's factor four
(`app:ch_background:eq:bg-realification`). -/
theorem carrierChannel_normal (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    carrierChannel T ∘L (carrierChannel T).adjoint =
      (4 : ℝ) • realOutputCompression (T ∘L T.adjoint) :=
  realQuadratureChannel_normal_eq_four_realPart T

/-- Realification preserves boundedness with factor two
(`app:ch_background:eq:bg-realification`). -/
theorem carrierChannel_norm_le (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    ‖carrierChannel T‖ ≤ 2 * ‖T‖ := realQuadratureChannel_norm_le T

/-- Finite carrier row on the Hilbert sum (`app:ch_background:defn:bg-row`). -/
def carrierRow (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    CarrierFamilyL2 n ι →L[ℝ] OutputL2 n :=
  ∑ a, carrierChannel (T a) ∘L PiLp.proj 2 (fun _ : ι ↦ CarrierL2 n) a

/-- Action of the carrier row (`app:ch_background:defn:bg-row`). -/
@[simp] theorem carrierRow_apply (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (f : CarrierFamilyL2 n ι) : carrierRow T f = ∑ a, carrierChannel (T a) (f a) := by
  simp [carrierRow]

/-- The literal adjoint in each carrier slot (`app:ch_background:eq:bg-realification`). -/
theorem carrierRow_adjoint_apply (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (w : OutputL2 n) :
    (carrierRow T).adjoint w =
      WithLp.toLp 2 (fun a ↦ (carrierChannel (T a)).adjoint w) := by
  apply ext_inner_right ℝ
  intro f
  simp [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, inner_sum]

/-- The physical row on its full Hilbert input, conditional on construction of
its image and carrier operators (`app:ch_background:defn:bg-row`). -/
def physicalRow (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    PhysicalInput n ι →L[ℝ] OutputL2 n :=
  image ∘L WithLp.fstL 2 ℝ (OutputL2 n) (CarrierFamilyL2 n ι) +
    carrierRow T ∘L WithLp.sndL 2 ℝ (OutputL2 n) (CarrierFamilyL2 n ι)

/-- Physical-row action (`app:ch_background:defn:bg-row`). -/
@[simp] theorem physicalRow_apply (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (f : PhysicalInput n ι) :
    physicalRow image T f = image f.fst + carrierRow T f.snd := rfl

/-- Literal adjoint of the image/carrier Hilbert row (`app:ch_background:defn:bg-row`). -/
theorem physicalRow_adjoint_apply (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (w : OutputL2 n) :
    (physicalRow image T).adjoint w =
      WithLp.toLp 2 (image.adjoint w, (carrierRow T).adjoint w) := by
  apply ext_inner_right ℝ
  intro f
  simp [ContinuousLinearMap.adjoint_inner_left, inner_add_right, WithLp.prod_inner_apply]

/-- Augment the physical row by the actual exterior multiplier
(`app:ch_background:defn:bg-row`). -/
def augmentedRow (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) :
    AugmentedInput n ι →L[ℝ] OutputL2 n :=
  NormalAugmentation.augmentedRow (physicalRow image T) (cutoffMultiplier ψ)

/-- Literal augmented-row action (`app:ch_background:defn:bg-row`). -/
@[simp] theorem augmentedRow_apply (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (f : AugmentedInput n ι) :
    augmentedRow image T ψ f = physicalRow image T f.fst + exteriorChannel ψ f.snd := by
  rw [exteriorChannel_eq_sub]
  rfl

/-- Literal augmented-row adjoint with a self-adjoint exterior multiplier
(`app:ch_background:defn:bg-row`). -/
theorem augmentedRow_adjoint_apply (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) (w : OutputL2 n) :
    (augmentedRow image T ψ).adjoint w =
      WithLp.toLp 2 ((physicalRow image T).adjoint w, exteriorChannel ψ w) := by
  apply ext_inner_right ℝ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left, augmentedRow_apply, inner_add_right,
    WithLp.prod_inner_apply, ContinuousLinearMap.adjoint_inner_left,
    ← exteriorChannel_adjoint ψ, ContinuousLinearMap.adjoint_inner_left]
  rw [exteriorChannel_adjoint]
  rfl

/-- The assembled normal operator (`app:ch_background:defn:bg-row`), conditional
on realization of the image and carrier channels. -/
def augmentedNormal (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) :
    OutputL2 n →L[ℝ] OutputL2 n :=
  augmentedRow image T ψ ∘L (augmentedRow image T ψ).adjoint

end JanetCartan.ContinuumRow
