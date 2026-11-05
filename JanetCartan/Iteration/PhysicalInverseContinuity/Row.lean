module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Carrier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.InputScale
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Restriction
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.DensityFamily
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RealAdjoint

/-!
# Fixed-datum adjoint comparison for the same real augmented row

The physical adjoint is a direct sum, not a composition with the image
adjoint. The original two real quadratures give a single factor of two, the
common measurement multiplier acts on the same complexified datum, and the
identical uncut exterior slot cancels. The raw Sobolev slot budget is derived
from the actual full augmented bound. Consumer: `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 90000
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow CarrierSobolev CommonMeasurement ContinuumAdjoint.Canonical

variable {n : ℕ} {ι : Type*} [Fintype ι]

private theorem augmented_restricted_adjoint_slot
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (χ ψ : C(Torus n, ℝ))
    (w : OutputL2 n) (i : ι) :
    ((augmentedRow image (fun j ↦ restrictCarrier χ (V j)) ψ).adjoint w).fst.snd i =
      (2 : ℝ) • (V i).adjoint (complexMultiplier χ (l2ComplexInclusion volume w)) := by
  simp only [augmentedRow_adjoint_apply, WithLp.toLp_fst, physicalRow_adjoint_apply,
    WithLp.toLp_snd, carrierRow_adjoint_apply, PiLp.toLp_apply, carrierChannel_adjoint_apply,
    restrictCarrier_adjoint, ContinuousLinearMap.comp_apply]

private theorem raw_component_le_full {u : AugmentedInput n ι} {s : ℕ}
    (hu : u ∈ (augmentedInputSobolevScale n ι).level s) (i : ι) :
    rawSobolevNorm s (u.fst.snd i) ≤ (augmentedInputSobolevScale n ι).gradeNorm s u := by
  obtain ⟨z, rfl⟩ := hu
  change rawSobolevNorm s (RawSobolevSpace.toRawL2 s (z.fst.snd i)) ≤
    (augmentedInputSobolevScale n ι).gradeNorm s (augmentedInputToL2 s z)
  exact (carrier_norm_le_augmentedInput s z i).trans_eq (augmentedInputSobolevScale_gradeNorm s z).symm

/-- The actual full augmented adjoint level bounds the original complex
carrier slot at the common measured datum. Both real quadratures are retained
in recovering the exact factor one-half. -/
theorem raw_complex_slot_of_augmented_adjoint
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (χ ψ : C(Torus n, ℝ))
    (w : OutputL2 n) (s : ℕ)
    (hu : (augmentedRow image (fun j ↦ restrictCarrier χ (V j)) ψ).adjoint w ∈
      (augmentedInputSobolevScale n ι).level s) (i : ι) :
    let v := (V i).adjoint (complexMultiplier χ (l2ComplexInclusion volume w))
    MemRawSobolev s v ∧ rawSobolevNorm s v ≤
      (augmentedInputSobolevScale n ι).gradeNorm s
        ((augmentedRow image (fun j ↦ restrictCarrier χ (V j)) ψ).adjoint w) / 2 := by
  let u := (augmentedRow image (fun j ↦ restrictCarrier χ (V j)) ψ).adjoint w
  let v := (V i).adjoint (complexMultiplier χ (l2ComplexInclusion volume w))
  have hmem : MemRawSobolev s (u.fst.snd i) := ((mem_augmentedInputLevel_iff s u).mp hu).2.1 i
  have hnorm : rawSobolevNorm s (u.fst.snd i) ≤ (augmentedInputSobolevScale n ι).gradeNorm s u :=
    raw_component_le_full hu i
  have he : u.fst.snd i = (2 : ℝ) • v := augmented_restricted_adjoint_slot image V χ ψ w i
  rw [he] at hmem hnorm
  obtain ⟨hhalf, hhalfNorm⟩ := rawSobolev_real_smul hmem (1 / 2 : ℝ)
  have hh : (1 / 2 : ℝ) • (2 : ℝ) • v = v := by rw [smul_smul]; norm_num
  rw [hh] at hhalf hhalfNorm
  change MemRawSobolev s v ∧ rawSobolevNorm s v ≤ (augmentedInputSobolevScale n ι).gradeNorm s u / 2
  refine ⟨hhalf, ?_⟩
  rw [hhalfNorm, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  linarith only [hnorm]

private theorem norm_two_real_smul (f : CarrierL2 n) : ‖(2 : ℝ) • f‖ = 2 * ‖f‖ := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

private theorem norm_product_le_add {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]
    (v : WithLp 2 (E × G)) : ‖v‖ ≤ ‖v.fst‖ + ‖v.snd‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, by nlinarith [mul_nonneg (norm_nonneg v.fst) (norm_nonneg v.snd)]⟩

private theorem norm_augmented_le_components (v : AugmentedInput n ι) :
    ‖v‖ ≤ (‖v.fst.fst‖ + ∑ i, ‖v.fst.snd i‖) + ‖v.snd‖ := by
  have hsum : ‖v.fst.snd‖ ≤ ∑ i, ‖v.fst.snd i‖ := by
    rw [PiLp.norm_eq_of_L2]
    exact Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _),
      Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)⟩
  exact (norm_product_le_add v).trans (add_le_add
    ((norm_product_le_add v.fst).trans (add_le_add le_rfl hsum)) le_rfl)

/-- Strong comparison of the actual augmented real adjoints at a single datum.
The fixed exterior term cancels identically. Each complex carrier difference
is on the original common measured datum, with no cutoff added to either row. -/
theorem norm_augmented_restricted_adjoint_sub_le
    (image image₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (V V₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (χ ψ : C(Torus n, ℝ))
    (w : OutputL2 n) :
    let wc := complexMultiplier χ (l2ComplexInclusion volume w)
    ‖(augmentedRow image (fun i ↦ restrictCarrier χ (V i)) ψ).adjoint w -
      (augmentedRow image₀ (fun i ↦ restrictCarrier χ (V₀ i)) ψ).adjoint w‖ ≤
      ‖image.adjoint w - image₀.adjoint w‖ +
        2 * ∑ i, ‖(V i).adjoint wc - (V₀ i).adjoint wc‖ := by
  let wc : ComplexOutputL2 n := complexMultiplier χ (l2ComplexInclusion volume w)
  let a : AugmentedInput n ι := (augmentedRow image (fun i ↦ restrictCarrier χ (V i)) ψ).adjoint w
  let b : AugmentedInput n ι := (augmentedRow image₀ (fun i ↦ restrictCarrier χ (V₀ i)) ψ).adjoint w
  let v : AugmentedInput n ι := a - b
  have hext : v.snd = 0 := by
    simp only [v, WithLp.sub_snd, a, b, augmentedRow_adjoint_apply, WithLp.toLp_snd,
      sub_self]
  have himage : v.fst.fst = image.adjoint w - image₀.adjoint w := by
    simp only [v, WithLp.sub_fst, a, b, augmentedRow_adjoint_apply, WithLp.toLp_fst,
      physicalRow_adjoint_apply]
  have hslot (i : ι) : v.fst.snd i = (2 : ℝ) • ((V i).adjoint wc - (V₀ i).adjoint wc) := by
    simp only [v, WithLp.sub_fst, WithLp.sub_snd, PiLp.sub_apply, a, b,
      augmented_restricted_adjoint_slot, smul_sub, wc]
  have hsum : (∑ i, ‖v.fst.snd i‖) = 2 * ∑ i, ‖(V i).adjoint wc - (V₀ i).adjoint wc‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (congrArg norm (hslot i)).trans (norm_two_real_smul _)
  have h := norm_augmented_le_components v
  rw [hext, norm_zero, add_zero, himage, hsum] at h
  exact h

end JanetCartan.PhysicalInverseContinuity
