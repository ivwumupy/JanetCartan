module
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Disintegration.Bounds
import JanetCartan.Analysis.Operator.HilbertSchmidt.Kernel
/-!
# Actual finite-band carrier adjoints

Derive the adjoints in `app:ch_background:eq:bg-T` from the given forward AE
formulas. The fiber identification in `app:ch_waves:eq:sampling-prefix-normal`
then follows by Fubini. No adjoint formula is an input to these results.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace
namespace JanetCartan.ContinuumRow
variable {n : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]

private theorem adjoint_ae_of_dominated_kernel (K : Torus n → X → EuclideanSpace ℂ (Fin n))
    (hK : StronglyMeasurable (Function.uncurry K))
    (g : X → ℝ) (hg : MemLp g 2 μ)
    (hbound : ∀ x u, ‖K x u‖ ≤ g u)
    (T : Lp ℂ 2 μ →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ f, (T f : Torus n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume]
      fun x ↦ ∫ u, f u • K x u ∂μ) (w : ComplexOutputL2 n) :
    (T.adjoint w : X → ℂ) =ᵐ[μ] fun u ↦ ∫ x, inner ℂ (K x u) (w x) := by
  have hw : Integrable (fun x ↦ ‖w x‖) volume :=
    ((Lp.memLp w).integrable (by norm_num)).norm
  let A : X → ℂ := fun u ↦ ∫ x, inner ℂ (K x u) (w x)
  have hm : StronglyMeasurable A :=
    (hK.inner ((Lp.stronglyMeasurable w).comp_measurable measurable_fst)).integral_prod_left
  have hA : MemLp A 2 μ := by
    apply (hg.mul_const (∫ x, ‖w x‖)).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro u
    calc
      ‖A u‖ ≤ ∫ x, g u * ‖w x‖ := norm_integral_le_of_norm_le (hw.const_mul _) <|
        Filter.Eventually.of_forall (fun x ↦ (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hbound x u) (norm_nonneg _)))
      _ = g u * ∫ x, ‖w x‖ := integral_const_mul _ _
  let a := hA.toLp A
  have ha : (a : X → ℂ) =ᵐ[μ] A := hA.coeFn_toLp
  have heq : T.adjoint w = a := by
    apply ext_inner_left ℂ
    intro f
    have hfg : Integrable (fun u ↦ ‖f u‖ * g u) μ := (Lp.memLp f).norm.integrable_mul hg
    have hsection (x : Torus n) : Integrable (fun u ↦ f u • K x u) μ := by
      apply hfg.mono'
      · exact ((Lp.stronglyMeasurable f).smul (hK.comp_measurable
          (measurable_const.prodMk measurable_id))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun u ↦ by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hbound x u) (norm_nonneg _))
    have hpair : Integrable (fun p : Torus n × X ↦
        star (f p.2) * inner ℂ (K p.1 p.2) (w p.1)) (volume.prod μ) := by
      apply (hw.mul_prod hfg).mono'
      · exact (((Lp.stronglyMeasurable f).comp_measurable measurable_snd).star.mul
          (hK.inner ((Lp.stronglyMeasurable w).comp_measurable measurable_fst))).aestronglyMeasurable
      · apply Filter.Eventually.of_forall
        intro p
        calc
          ‖star (f p.2) * inner ℂ (K p.1 p.2) (w p.1)‖
              ≤ ‖f p.2‖ * (g p.2 * ‖w p.1‖) := by
                rw [norm_mul, norm_star]
                exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
                  (mul_le_mul_of_nonneg_right (hbound _ _) (norm_nonneg _))) (norm_nonneg _)
          _ = ‖w p.1‖ * (‖f p.2‖ * g p.2) := by ring
    rw [T.adjoint_inner_right]
    calc
      inner ℂ (T f) w = ∫ x, inner ℂ (∫ u, f u • K x u ∂μ) (w x) := by
        rw [L2.inner_def]
        exact integral_congr_ae ((hT f).mono (fun x hx ↦ congrArg (fun v ↦ inner ℂ v (w x)) hx))
      _ = ∫ x, ∫ u, star (f u) * inner ℂ (K x u) (w x) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x ↦ by
          dsimp only
          have hi := congrArg (starRingEnd ℂ) (integral_inner (𝕜 := ℂ) (hsection x) (w x))
          simp only [← integral_conj, inner_conj_symm, inner_smul_left] at hi
          simpa only [starRingEnd_apply] using hi.symm)
      _ = ∫ u, (∫ x, star (f u) * inner ℂ (K x u) (w x)) ∂μ :=
        integral_integral_swap hpair
      _ = ∫ u, inner ℂ (f u) (A u) ∂μ := by
        simp only [A, RCLike.inner_apply, integral_const_mul, starRingEnd_apply, mul_comm]
      _ = inner ℂ f a := by
        rw [L2.inner_def]
        exact integral_congr_ae (ha.symm.mono (fun u hu ↦ congrArg (fun v ↦ inner ℂ (f u) v) hu))
  rw [heq]
  exact ha
/-- The actual Hilbert adjoint of the finite-band continuum channel is its literal
kernel adjoint (`app:ch_background:eq:bg-T`). Only the forward formula is assumed. -/
theorem carrier_adjoint_ae_eq_integral {N : ℕ} (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (h : FiniteCarrierKernelBounds d m)
    (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ f, (T f : Torus n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume]
      regularizedCarrierIntegral d m f) (w : ComplexOutputL2 n) :
    (T.adjoint w : CarrierVariable n → ℂ) =ᵐ[carrierMeasure n]
      fun u ↦ ∫ x, inner ℂ (maskedCarrierKernel d m x u) (w x) := by
  apply adjoint_ae_of_dominated_kernel (maskedCarrierKernel d m)
    h.stronglyMeasurable h.inputEnvelope h.memLp_inputEnvelope
    h.norm_kernel_le_inputEnvelope T ?_ w
  intro f
  filter_upwards [hT f] with x hx
  exact hx.trans (regularizedCarrierIntegral_eq_masked d m f x)

/-- Each actual slice adjoint is its literal transverse kernel adjoint
(`app:ch_waves:eq:sampling-prefix-normal`). Only its forward formula is assumed. -/
theorem carrierSlice_adjoint_ae_eq_integral {N : ℕ} (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (h : FiniteCarrierKernelBounds d m)
    (z : CarrierParameter) (S : CarrierSliceL2 n →L[ℂ] ComplexOutputL2 n)
    (hS : ∀ f, (S f : Torus n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume]
      regularizedCarrierSliceIntegral d m z f) (w : ComplexOutputL2 n) :
    (S.adjoint w : Euclidean (n - 1) → ℂ) =ᵐ[volume]
      fun η ↦ ∫ x, inner ℂ (maskedCarrierKernel d m x (z, η)) (w x) := by
  apply adjoint_ae_of_dominated_kernel (fun x η ↦ maskedCarrierKernel d m x (z, η))
    (h.stronglyMeasurable.comp_measurable
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
    h.sliceEnvelope h.memLp_sliceEnvelope
    (fun x η ↦ h.norm_kernel_le_sliceEnvelope x z η) S hS w

/-- Almost every fiber of the actual full adjoint equals the actual slice adjoint
in transverse L² (`app:ch_waves:eq:sampling-prefix-normal`). This statement uses
quotient representatives only through almost-everywhere equality. -/
theorem carrier_adjoint_fiber_ae_eq {N : ℕ} (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (h : FiniteCarrierKernelBounds d m)
    (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (S : CarrierParameter → CarrierSliceL2 n →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ f, (T f : Torus n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume]
      regularizedCarrierIntegral d m f)
    (hS : ∀ z f, (S z f : Torus n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume]
      regularizedCarrierSliceIntegral d m z f) (w : ComplexOutputL2 n) :
    ∀ᵐ z ∂volume.prod volume,
      (fun η ↦ (T.adjoint w) (z, η)) =ᵐ[volume] ((S z).adjoint w) := by
  have hf : ∀ᵐ z ∂volume.prod volume, ∀ᵐ η ∂volume,
      (T.adjoint w) (z, η) = ∫ x, inner ℂ (maskedCarrierKernel d m x (z, η)) (w x) :=
    Measure.ae_ae_of_ae_prod (carrier_adjoint_ae_eq_integral d m h T hT w)
  filter_upwards [hf] with z hz
  exact Filter.EventuallyEq.trans hz (carrierSlice_adjoint_ae_eq_integral d m h z (S z) (hS z) w).symm

end JanetCartan.ContinuumRow
