module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.FullCompatibility
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds.Carrier

/-!
# Bounded transverse weights and partial Fourier synthesis

For `app:ch_background:prop:bg-adjoint` and the raw cutoff estimate in
`app:ch_background:defn:bg-mixed`, bounded transverse weights commute with
parameter Fourier transformation. This leaf proves their exact norm identity
under the actual partial unitary inverse, with its `2π` rescaling. The
unbounded Bessel weight estimate consumes this identity for its truncations.
-/

open MeasureTheory
open scoped ENNReal
@[expose] public noncomputable section
set_option maxHeartbeats 800000
namespace JanetCartan.CarrierSobolev.TransverseWeight
open ContinuumRow RawCutoffBounds
variable {n : ℕ}

private def coefficient (m : Euclidean (n - 1) → ℝ) (hm : Measurable m)
    {C : ℝ} (hC : ∀ η, |m η| ≤ C) : Lp ℂ ∞ (volume : Measure (Euclidean (n - 1))) :=
  (memLp_top_of_bound (Complex.measurable_ofReal.comp hm).aestronglyMeasurable C
    (.of_forall fun η => by simpa using hC η)).toLp _

private def multiplier (m : Euclidean (n - 1) → ℝ) (hm : Measurable m)
    {C : ℝ} (hC : ∀ η, |m η| ≤ C) : TransverseL2 n →L[ℂ] TransverseL2 n :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL volume ∞ 2 2 (coefficient m hm hC)

private theorem multiplier_coeFn (m : Euclidean (n - 1) → ℝ) (hm : Measurable m)
    {C : ℝ} (hC : ∀ η, |m η| ≤ C) (f : TransverseL2 n) :
    multiplier m hm hC f =ᵐ[volume] fun η => m η • f η := by
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder (r := 2)
    (coefficient m hm hC) f, (MemLp.coeFn_toLp _ :
      coefficient m hm hC =ᵐ[volume] fun η => (m η : ℂ))] with η hη hc
  change multiplier m hm hC f η = coefficient m hm hC η • f η at hη
  change coefficient m hm hC η = (m η : ℂ) at hc
  rw [hc] at hη
  simpa only [Complex.real_smul, smul_eq_mul] using hη

private theorem mem_carrier (m : Euclidean (n - 1) → ℝ) (hm : Measurable m)
    {C : ℝ} (hC : ∀ η, |m η| ≤ C) (f : CarrierL2 n) :
    CarrierWeightedMem (fun x => m x.2) f :=
  (memLp_top_of_bound (hm.comp measurable_snd).aestronglyMeasurable C
    (.of_forall fun x => by simpa using hC x.2)).smul (Lp.memLp f)

private theorem fubini_mul (m : Euclidean (n - 1) → ℝ) (hm : Measurable m)
    {C : ℝ} (hC : ∀ η, |m η| ≤ C) (f : CarrierL2 n) :
    carrierFubiniEquiv n ((mem_carrier m hm hC f).toLp _) =
      (multiplier m hm hC).compLp (carrierFubiniEquiv n f) := by
  apply Lp.ext
  filter_upwards [carrierFubiniEquiv_toLp_coeFn (mem_carrier m hm hC f),
    (multiplier m hm hC).coeFn_compLp (carrierFubiniEquiv n f),
    carrierFubiniEquiv_coeFn n f] with z hz hL hf
  rw [hL]
  apply Lp.ext
  filter_upwards [hz, hf, multiplier_coeFn m hm hC (carrierFubiniEquiv n f z)]
    with η hη hfη hLη
  rw [hη, hLη, hfη]

private theorem dilation_symm_multiplier
    (m : Euclidean (n - 1) → ℝ) (hm : Measurable m)
    {C : ℝ} (hC : ∀ η, |m η| ≤ C) (f : TransverseL2 n) :
    (transverseDilation n ℂ).symm (multiplier m hm hC f) =
      multiplier (fun η => m ((2 * Real.pi) • η)) (hm.comp (measurable_id.const_smul (2 * Real.pi)))
        (fun η => hC ((2 * Real.pi) • η)) ((transverseDilation n ℂ).symm f) := by
  apply Lp.ext
  have he := (Measure.quasiMeasurePreserving_smul (volume : Measure (Euclidean (n - 1)))
    (by positivity : (2 * Real.pi : ℝ) ≠ 0)).ae (multiplier_coeFn m hm hC f)
  filter_upwards [transverseDilation_symm_coeFn (multiplier m hm hC f), he,
    multiplier_coeFn (fun η => m ((2 * Real.pi) • η))
      (hm.comp (measurable_id.const_smul (2 * Real.pi))) (fun η => hC ((2 * Real.pi) • η))
      ((transverseDilation n ℂ).symm f), transverseDilation_symm_coeFn f]
    with η h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  exact smul_comm _ _ _

private theorem iterated_dilation_symm_multiplier
    (m : Euclidean (n - 1) → ℝ) (hm : Measurable m)
    {C : ℝ} (hC : ∀ η, |m η| ≤ C) (g : IteratedCarrierL2 n) :
    (iteratedTransverseDilation n).symm ((multiplier m hm hC).compLp g) =
      (multiplier (fun η => m ((2 * Real.pi) • η))
        (hm.comp (measurable_id.const_smul (2 * Real.pi))) (fun η => hC ((2 * Real.pi) • η))).compLp
          ((iteratedTransverseDilation n).symm g) := by
  apply Lp.ext
  filter_upwards [iteratedTransverseEquiv_symm_coeFn (transverseDilation n ℂ)
    ((multiplier m hm hC).compLp g), (multiplier m hm hC).coeFn_compLp g,
    (multiplier (fun η => m ((2 * Real.pi) • η))
      (hm.comp (measurable_id.const_smul (2 * Real.pi))) (fun η => hC ((2 * Real.pi) • η))).coeFn_compLp
        ((iteratedTransverseDilation n).symm g),
    iteratedTransverseEquiv_symm_coeFn (transverseDilation n ℂ) g]
    with z h₁ h₂ h₃ h₄
  change (iteratedTransverseDilation n).symm ((multiplier m hm hC).compLp g) z = _ at h₁
  change (iteratedTransverseDilation n).symm g z = _ at h₄
  rw [h₁, h₂, h₃, h₄, dilation_symm_multiplier]


private theorem bounded_norm_rescale
    (m : Euclidean (n - 1) → ℝ) (hm : Measurable m)
    {C : ℝ} (hC : ∀ η, |m η| ≤ C) (f : CarrierL2 n) :
    ‖(mem_carrier m hm hC f).toLp _‖ =
      ‖(mem_carrier (fun η => m ((2 * Real.pi) • η))
        (hm.comp (measurable_id.const_smul (2 * Real.pi)))
        (fun η => hC ((2 * Real.pi) • η))
        (initialFourier n (partialUnitaryInverse n f))).toLp _‖ := by
  let L := multiplier m hm hC
  let g := carrierFubiniEquiv n (initialFourier n (partialUnitaryInverse n f))
  calc
    _ = ‖L.compLp (carrierFubiniEquiv n f)‖ := by
      rw [← carrierFubiniEquiv_norm, fubini_mul]
    _ = ‖L.compLp (iteratedTransverseDilation n g)‖ :=
      (initialFourier_partialUnitaryInverse_rescaled_compLp_norm L f).symm
    _ = ‖(iteratedTransverseDilation n).symm
        (L.compLp (iteratedTransverseDilation n g))‖ :=
      ((iteratedTransverseDilation n).symm.norm_map _).symm
    _ = _ := by
      rw [iterated_dilation_symm_multiplier,
        LinearIsometryEquiv.symm_apply_apply, ← fubini_mul, carrierFubiniEquiv_norm]


/-- Bounded transverse-weight Plancherel, including the radian frequency
rescaling. Consumed by the truncated Bessel bound for the raw cutoff estimate
following `app:ch_background:defn:bg-mixed`. -/
theorem bounded_eLpNorm_rescale
    (m : Euclidean (n - 1) → ℝ) (hm : Measurable m)
    {C : ℝ} (hC : ∀ η, |m η| ≤ C) (f : CarrierL2 n) :
    eLpNorm (fun x => m x.2 • f x) 2 (carrierMeasure n) =
      eLpNorm (fun x => m ((2 * Real.pi) • x.2) •
        initialFourier n (partialUnitaryInverse n f) x) 2 (carrierMeasure n) := by
  apply (ENNReal.toReal_eq_toReal_iff' (mem_carrier m hm hC f).eLpNorm_ne_top
    (mem_carrier (fun η => m ((2 * Real.pi) • η))
      (hm.comp (measurable_id.const_smul (2 * Real.pi)))
      (fun η => hC ((2 * Real.pi) • η))
      (initialFourier n (partialUnitaryInverse n f))).eLpNorm_ne_top).mp
  exact (Lp.norm_toLp _ (mem_carrier m hm hC f)).symm.trans
    ((bounded_norm_rescale m hm hC f).trans
      (Lp.norm_toLp _ (mem_carrier (fun η => m ((2 * Real.pi) • η))
        (hm.comp (measurable_id.const_smul (2 * Real.pi)))
        (fun η => hC ((2 * Real.pi) • η))
        (initialFourier n (partialUnitaryInverse n f)))))

end JanetCartan.CarrierSobolev.TransverseWeight
