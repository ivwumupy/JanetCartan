module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ObservedSourceInputs

/-!
# The literal signed source entering the normalized inverse

The original tensor cutoff and auxiliary stress cutoff remain inside the
inverse's inner bump. Identify that actual datum, including its restriction,
zero extension and complex inclusion, with the signed source whose tensor
cutoff is the product of the original cutoff and the SAME inner bump.
Only the inner bump must be supported in the measured domain.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory Filter
open scoped ContDiff NNReal ENNReal Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open LocalSobolev SmallSupport
open RegularSector.Characteristic.RetardedLocalization
open RawPrimary.AmplitudeGrades.Polynomial
variable {d N : ℕ} {ι : Type*}
local notation "E" => Euclidean (d+1)
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The inner multiplication preserves the literal signed tensor, half stress
contraction and auxiliary cutoff. This is the source in
`normalized_correctedSource_angular_finite_expansion`, before any residual
power (`app:ch_regular:thm:exact-correction`, `app:ch_pairs:eq:pairs-lag-one-error`). -/
theorem innerCut_signed_product_source_eq
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (χ₂ χ ψ : E → ℝ)
    (θ : ι → E → ℝ) (A : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ)
    (minus : Bool) (i k : ι) :
    (fun y ↦ χ₂ y • WithLp.toLp 2 (AmbientResponse.cutoffSource ψ
      (AmbientResponse.stressSource Q (fun x ↦ χ x •
        (if minus then ProductSum.minusSource θ A i k x
          else ProductSum.plusSource θ A i k x))) y)) =
    (fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource ψ
      (AmbientResponse.stressSource Q (fun x ↦ (χ₂ x * χ x) •
        (if minus then ProductSum.minusSource θ A i k x
          else ProductSum.plusSource θ A i k x))) y)) := by
  ext y j
  change χ₂ y * (ψ y * ((1 / 2 : ℝ) * inner ℝ (Q y j)
    (χ y • (if minus then ProductSum.minusSource θ A i k y
      else ProductSum.plusSource θ A i k y)))) =
    ψ y * ((1 / 2 : ℝ) * inner ℝ (Q y j)
      ((χ₂ y * χ y) • (if minus then ProductSum.minusSource θ A i k y
        else ProductSum.plusSource θ A i k y)))
  rw [inner_smul_right, inner_smul_right]
  ring

/-- The inner-cut signed source is the local L² realization of the combined
cutoff. No plateau that removes the inner bump is used
(`app:ch_regular:thm:exact-correction`, `app:ch_pairs:eq:pairs-lag-one-error`). -/
theorem innerCut_signed_product_source_local_eq
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (χ ψ : E → ℝ)
    (θ : ι → E → ℝ) (A : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ)
    (minus : Bool) (i k : ι) {center : E} (χ₂ : ContDiffBump center)
    {W : Set E}
    (hg : MemLp (fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource ψ
      (AmbientResponse.stressSource Q (fun x ↦ χ x •
        (if minus then ProductSum.minusSource θ A i k x
          else ProductSum.plusSource θ A i k x))) y)) 2 volume)
    (hcut : MemLp (fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource ψ
      (AmbientResponse.stressSource Q (fun x ↦ (χ₂ x * χ x) •
        (if minus then ProductSum.minusSource θ A i k x
          else ProductSum.plusSource θ A i k x))) y)) 2 volume) :
    bumpL2 (p := 2) le_rfl χ₂
      ((hg.mono_measure (Measure.restrict_le_self (s := W))).toLp _) =
      (hcut.mono_measure (Measure.restrict_le_self (s := W))).toLp _ := by
  apply Lp.ext
  filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ₂
      ((hg.mono_measure (Measure.restrict_le_self (s := W))).toLp _),
    (hg.mono_measure (Measure.restrict_le_self (s := W))).coeFn_toLp,
    (hcut.mono_measure (Measure.restrict_le_self (s := W))).coeFn_toLp]
    with y hb hg' hc
  rw [hb, hg', hc]
  exact congrFun (innerCut_signed_product_source_eq Q χ₂ χ ψ θ A minus i k) y

/-- Only the inner bump must lie in the measurement domain to identify the
zero-extended signed datum. The original source cutoff can extend beyond that
domain; this is the literal source used by `ObservedChains` and the normalized
inverse expansion (`app:ch_regular:lem:finite-chain`). -/
theorem innerCut_signed_product_source_zeroExtend_eq
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (χ ψ : E → ℝ)
    (θ : ι → E → ℝ) (A : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ)
    (minus : Bool) (i k : ι) {center : E} (χ₂ : ContDiffBump center)
    {W : Set E} (hW : MeasurableSet W) (hχ₂W : tsupport (χ₂ : E → ℝ) ⊆ W)
    (hg : MemLp (fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource ψ
      (AmbientResponse.stressSource Q (fun x ↦ χ x •
        (if minus then ProductSum.minusSource θ A i k x
          else ProductSum.plusSource θ A i k x))) y)) 2 volume)
    (hcut : MemLp (fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource ψ
      (AmbientResponse.stressSource Q (fun x ↦ (χ₂ x * χ x) •
        (if minus then ProductSum.minusSource θ A i k x
          else ProductSum.plusSource θ A i k x))) y)) 2 volume) :
    zeroExtend hW (bumpL2 (p := 2) le_rfl χ₂
      ((hg.mono_measure (Measure.restrict_le_self (s := W))).toLp _)) = hcut.toLp _ := by
  rw [innerCut_signed_product_source_local_eq Q χ ψ θ A minus i k χ₂ hg hcut]
  apply Lp.ext
  filter_upwards [zeroExtend_coeFn hW
      ((hcut.mono_measure (Measure.restrict_le_self (s := W))).toLp _),
    (ae_restrict_iff' hW).mp
      (hcut.mono_measure (Measure.restrict_le_self (s := W))).coeFn_toLp,
    hcut.coeFn_toLp] with y hz hc hg'
  rw [hz, hg']
  by_cases hy : y ∈ W
  · rw [indicator_of_mem hy, hc hy]
  · rw [indicator_of_notMem hy]
    have hχ₂ : χ₂ y = 0 := image_eq_zero_of_notMem_tsupport (fun hs ↦ hy (hχ₂W hs))
    ext j
    simp [hχ₂, AmbientResponse.cutoffSource, AmbientResponse.stressSource, tensorPairing]

/-- The literal complex datum of `ObservedChains` is the same combined-cutoff
signed source, with complex inclusion performed once before the whole word.
The source is independent of the proof depth and no real projection is
inserted between residual factors (`app:ch_regular:lem:finite-chain`). -/
theorem innerCut_signed_product_chain_source_eq
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (χ ψ : E → ℝ)
    (θ : ι → E → ℝ) (A : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ)
    (minus : Bool) (i k : ι) {center : E} (χ₂ : ContDiffBump center)
    {W : Set E} (hW : MeasurableSet W) (hχ₂W : tsupport (χ₂ : E → ℝ) ⊆ W)
    (hg : MemLp (fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource ψ
      (AmbientResponse.stressSource Q (fun x ↦ χ x •
        (if minus then ProductSum.minusSource θ A i k x
          else ProductSum.plusSource θ A i k x))) y)) 2 volume)
    (hcut : MemLp (fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource ψ
      (AmbientResponse.stressSource Q (fun x ↦ (χ₂ x * χ x) •
        (if minus then ProductSum.minusSource θ A i k x
          else ProductSum.plusSource θ A i k x))) y)) 2 volume) :
    restrictL2 univ (l2ComplexInclusion volume (zeroExtend hW
      (bumpL2 (p := 2) le_rfl χ₂
        ((hg.mono_measure (Measure.restrict_le_self (s := W))).toLp _)))) =
      l2ComplexInclusion (volume.restrict univ)
        ((hcut.mono_measure (Measure.restrict_le_self (s := univ))).toLp _) := by
  rw [innerCut_signed_product_source_zeroExtend_eq Q χ ψ θ A minus i k χ₂ hW hχ₂W hg hcut]
  apply Lp.ext
  filter_upwards [restrictL2_coeFn univ (l2ComplexInclusion volume (hcut.toLp _)),
    ae_restrict_of_ae (euclideanComplexInclusion.coeFn_compLpL (hcut.toLp _)),
    ae_restrict_of_ae hcut.coeFn_toLp,
    euclideanComplexInclusion.coeFn_compLpL
      ((hcut.mono_measure (Measure.restrict_le_self (s := univ))).toLp _),
    (hcut.mono_measure (Measure.restrict_le_self (s := univ))).coeFn_toLp]
    with y hr hi hg' hc hl
  exact hr.trans (hi.trans ((congrArg euclideanComplexInclusion hg').trans
    ((congrArg euclideanComplexInclusion hl).symm.trans hc.symm)))

/-- Compact smoothness of the retained inner bump supplies its own fixed
Leibniz profile. Multiplication of the original source cutoff keeps the exact
slow power `L^r`; no accuracy, sample, target or history enters these constants.
Consumers are the recut angular source and its first proof mask
(`app:ch_pairs:eq:pairs-lag-envelope`, `app:ch_regular:eq:source-tail`). -/
theorem exists_innerCut_source_cutoff_jet_constants {center : E}
    (χ₂ : ContDiffBump center) (X : ℕ → ℝ) (hX : ∀ r, 0 ≤ X r) :
    ∃ Xcut : ℕ → ℝ, (∀ r, 0 ≤ Xcut r) ∧
      ∀ (U : Set E), IsOpen U → ∀ (χ : E → ℝ), ContDiffOn ℝ ∞ χ U →
      ∀ L : ℝ, 1 ≤ L →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ y‖ ≤ X r * L^r) →
      ∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r (fun z ↦ χ₂ z * χ z) y‖ ≤ Xcut r * L^r := by
  choose Xb hXb hbound using fun r : ℕ ↦
    χ₂.hasCompactSupport.exists_bound_iteratedFDeriv χ₂.contDiff r
  let mulMap := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
  refine ⟨productProfile mulMap Xb X, productProfile_nonneg _ hXb hX, ?_⟩
  intro U hU χ hχ L hL hχb y hy r
  exact jet_bilinear_le mulMap hU χ₂.contDiff.contDiffOn hχ hy (b := 0) hL hXb hX
    (fun j ↦ (hbound j j le_rfl y).trans
      (le_mul_of_one_le_right (hXb j) (one_le_pow₀ hL))) (hχb y hy) r

end JanetCartan.SignedProductEstimates
