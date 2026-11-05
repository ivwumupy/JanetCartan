module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalPrefixData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.Accumulation
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FourierMeasure
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalNumerics

/-!
# Fourier measures of the literal raw-prefix canonical changes

The same smooth raw map and fixed zero atom determine the full cross row.
Its raw prefixes determine both the physical derivative changes and their
initial Fourier measures. Primitive raw `H^0` estimates give the component
bounds and hence finite variation and initial derivative profiles. No
separate kernel-band, canonical-input or final current-mean estimate is
assumed (`main:eq:variation`, `main:lem:mean-recurrence`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory Metric Finset
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.CurrentMean
open CanonicalChange CanonicalTailRealization CanonicalDataBounds
open RawInputPartition RawInputRealization RawPrimary ContinuumRow SmoothPeriodicFamily

variable {n J : ℕ} {m ι : Type*} [Fintype m]
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (G : ι → WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ι → ℝ)
    (hG : ∀ i v, periodicL2Norm (fun x ↦ (G i v).val x ()) ≤ CG i * ‖v‖)

/-- The constructed prefix map yields exactly the original wide initial
field and Fourier density (`main:eq:old-canonical`). This follows from the
raw projection and cross-response calculus; no kernel realization premise
or independently chosen full row is used. -/
theorem canonicalWidePrefix_fourierData_eq
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (K : ℝ) (CGcut : ι → ℝ)
    (hGcut : ∀ i v, periodicL2Norm (fun x ↦
      (canonicalWidePrefixRawMap (G i) (cutoffCount K) v).val x ()) ≤ CGcut i * ‖v‖)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (r : OutputL2 n) (i : ι) :
    let A := smoothRawCrossOperator base C hC
      (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount K)) CGcut hGcut i
    let v := widePrefix n J (cutoffCount K)
      ((smoothRawCrossOperator base C hC G CG hG i).adjoint (Q₀ r))
    initialDatum (fun j : RefinedIndex J ↦ weightedRadialBand d j.1.val) A Q₀ r = weightedWideField d v ∧
      fourierDensity (fun j : RefinedIndex J ↦ weightedRadialBand d j.1.val) A Q₀ r =ᵐ[volume]
        weightedWideDensity d v := by
  dsimp only
  rw [smoothRawCrossOperator_widePrefix_eq_groupedPrefixRow base C hC G CG hG K CGcut hGcut i]
  constructor
  · exact initialDatum_groupedPrefixRow_eq_wideField hd hM hb _ Q₀ K r
  · rw [fourierDensity, adjointInput_groupedPrefixRow, adjoint_refinedRow]
    change density _ (refinedPrefix n J (cutoffCount K) (wideRefinement n J _)) =ᵐ[volume] _
    rw [← wideRefinement_prefix]
    exact (weightedWideDensity_eq_refined hd hM hb _).symm

/-- The actual finite canonical data have support, variation and initial
`C^s` bounds from primitive raw `H^0` profiles (`main:lem:mean-recurrence`).
The original unit zero atom is retained, and the only residual input is the
norm sum proved by the SAME run. Constants do not depend on the number of
updates, samples or full bands; all projections act on the same raw row. -/
theorem canonicalWidePrefixMeasures_bounds (hn : 1 ≤ n)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (K : ℕ → ℝ)
    (CGcut : ℕ → ι → ℝ)
    (hGcut : ∀ l i v, periodicL2Norm (fun x ↦
      (canonicalWidePrefixRawMap (G i) (cutoffCount (K l)) v).val x ()) ≤ CGcut l i * ‖v‖)
    {coefBound baseBound rawBound inverseBound Kmax ε : ℝ}
    (hcoefBound : 0 ≤ coefBound) (hbaseBound : 0 ≤ baseBound) (hrawBound : 0 ≤ rawBound)
    (hcoef : cNorm (fundamentalCell n) 0 (periodicLift C) ≤ coefBound)
    (hQ : ‖Q₀‖ ≤ inverseBound) (i : ι) (hbase : componentCSeminorm 0 i base ≤ baseBound)
    (I : ℕ) (hmax0 : 0 ≤ Kmax) (hK : ∀ l < I, 1 ≤ K l)
    (hKJ : ∀ l < I, cutoffCount (K l) ≤ J) (hmax : ∀ l < I, K l ≤ Kmax)
    (hraw : ∀ l < I, ∀ v, periodicSobolevNorm 0 (fun x ↦
      (canonicalWidePrefixRawMap (G i) (cutoffCount (K l)) v).val x ()) ≤
        rawBound * K l ^ (1/2 : ℝ) * ‖v‖)
    (r : ℕ → OutputL2 n) (hbudget : ∑ l ∈ range I, ‖r l‖ ≤ 2 * ε) :
    let A : ℕ → RefinedInput n J →L[ℝ] OutputL2 n := fun l ↦ smoothRawCrossOperator base C hC
      (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount (K l))) (CGcut l) (hGcut l) i
    let v := fun l ↦ widePrefix n J (cutoffCount (K l))
      ((smoothRawCrossOperator base C hC G CG hG i).adjoint (Q₀ (r l)))
    let μ : VectorMeasure (Euclidean (n - 1)) ℂ := ∑ l ∈ range I, wideFourierMeasure d (v l)
    let CA := 2 * coefBound * baseBound * rawBound
    let Cdata := 2 * refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2) * CA * inverseBound
    IsFiniteMeasure μ.variation ∧
      μ.variation (closedBall (0 : Euclidean (n - 1)) (4 * Kmax))ᶜ = 0 ∧
      μ.variation.real univ ≤ Cdata * ε * Kmax ^ meanDerivativeLoss n ∧
      (VectorMeasure.dirac (0 : Euclidean (n - 1)) (1 : ℂ) + μ).variation
        (closedBall (0 : Euclidean (n - 1)) (4 * Kmax))ᶜ = 0 ∧
      (VectorMeasure.dirac (0 : Euclidean (n - 1)) (1 : ℂ) + μ).variation.real univ ≤
        1 + Cdata * ε * Kmax ^ meanDerivativeLoss n ∧
      ∀ (s : ℕ) (S : Set (Euclidean (n - 1))), IsCompact S →
        cNorm S s (∑ l ∈ range I, initialDatum
          (fun j : RefinedIndex J ↦ weightedRadialBand d j.1.val) (A l) Q₀ (r l)) ≤
          (2 * ((s + 1 : ℕ) : ℝ) * refinedFourierConstant n M *
            4 ^ ((s : ℝ) + (n : ℝ) / 2) * CA * inverseBound) *
              ε * Kmax ^ ((s : ℝ) + meanDerivativeLoss n) := by
  let Awide : WideInput n J →L[ℝ] OutputL2 n := smoothRawCrossOperator base C hC G CG hG i
  let Aref : RefinedInput n J →L[ℝ] OutputL2 n := refinedRow Awide
  let A : ℕ → RefinedInput n J →L[ℝ] OutputL2 n := fun l ↦ smoothRawCrossOperator base C hC
    (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount (K l))) (CGcut l) (hGcut l) i
  let β := fun j : RefinedIndex J ↦ weightedRadialBand d j.1.val
  let ρ : ℕ → Euclidean (n - 1) → ℂ := fun l ↦ fourierDensity β (A l) Q₀ (r l)
  let μ : VectorMeasure (Euclidean (n - 1)) ℂ := ∑ l ∈ range I, wideFourierMeasure d
    (widePrefix n J (cutoffCount (K l)) (Awide.adjoint (Q₀ (r l))))
  let CA := 2 * coefBound * baseBound * rawBound
  have hCA : 0 ≤ CA := by dsimp only [CA]; positivity
  have hCQ : 0 ≤ inverseBound := (norm_nonneg _).trans hQ
  have hAeq (l : ℕ) : A l = groupedPrefixRow Aref (K l) :=
    smoothRawCrossOperator_widePrefix_eq_groupedPrefixRow base C hC G CG hG (K l) (CGcut l) (hGcut l) i
  have hint (l : ℕ) : Integrable (ρ l) volume :=
    integrable_fourierDensity (n := n) (radius := refinedRadius (J := J))
      (fun j : RefinedIndex J ↦ measurable_weightedRadialBand hd j.1.val)
      (fun j : RefinedIndex J ↦ norm_weightedRadialBand_le hb j.1.val) (A l) Q₀ (r l)
  have hmeasure : μ = volume.withDensityᵥ (fun η ↦ ∑ l ∈ range I, ρ l η) := by
    have hid (l : ℕ) : wideFourierMeasure d
        (widePrefix n J (cutoffCount (K l)) (Awide.adjoint (Q₀ (r l)))) = volume.withDensityᵥ (ρ l) :=
      WithDensityᵥEq.congr_ae
        (canonicalWidePrefix_fourierData_eq base C hC G CG hG hd hM hb (K l) (CGcut l) (hGcut l) Q₀ (r l) i).2.symm
    dsimp only [μ]
    simp_rw [hid]
    have hsum (k : ℕ) : (∑ l ∈ range k, volume.withDensityᵥ (ρ l)) =
        volume.withDensityᵥ (fun η ↦ ∑ l ∈ range k, ρ l η) := by
      induction k with
      | zero => simp only [sum_range_zero]; exact (withDensityᵥ_zero (μ := volume) (E := ℂ)).symm
      | succ k ih =>
        simp only [sum_range_succ, ih]
        exact (withDensityᵥ_add (integrable_finsetSum (range k) (fun l _ ↦ hint l)) (hint k)).symm
    exact hsum I
  have hvariation : μ.variation = volume.withDensity (fun η ↦ ‖∑ l ∈ range I, ρ l η‖ₑ) := by
    rw [hmeasure]
    exact Measure.variation_withDensityᵥ (integrable_finsetSum (range I) (fun l _ ↦ hint l))
  have hfinite : IsFiniteMeasure μ.variation := by
    rw [hvariation]
    exact ⟨by simpa [HasFiniteIntegral] using (integrable_finsetSum (range I) (fun l _ ↦ hint l)).2⟩
  have hsupp : μ.variation (closedBall (0 : Euclidean (n - 1)) (4 * Kmax))ᶜ = 0 := by
    rw [hvariation, withDensity_apply _ isClosed_closedBall.measurableSet.compl]
    apply lintegral_eq_zero_of_ae_eq_zero
    have hzero := sum_fourierDensity_groupedPrefixRow_eq_zero_above_four_mul
      (range I) β Aref Q₀ K r (fun l hl ↦ hK l (mem_range.mp hl))
      (fun l hl ↦ hmax l (mem_range.mp hl))
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem isClosed_closedBall.measurableSet.compl] with η hη hηout
    have hh : 4 * Kmax < ‖η‖ := by simpa using hηout
    dsimp only [ρ]
    simp_rw [hAeq]
    rw [hη hh, enorm_zero]
    rfl
  have hA (l : ℕ) (hl : l < I) : ‖groupedPrefixRow Aref (K l)‖ ≤ CA * Real.sqrt (K l) := by
    rw [← hAeq l]
    have hh := norm_smoothRawCrossOperator_le_of_sobolev_zero base C hC
      (fun i ↦ canonicalWidePrefixRawMap (G i) (cutoffCount (K l))) (CGcut l) (hGcut l)
      hcoefBound hbaseBound hrawBound (zero_le_one.trans (hK l hl)) hcoef i hbase (hraw l hl)
    simpa only [Real.sqrt_eq_rpow] using hh
  have hvar : μ.variation.real univ ≤
      (2 * refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2) * CA * inverseBound) *
        ε * Kmax ^ meanDerivativeLoss n := by
    rw [measureReal_def, hvariation, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← integral_norm_eq_lintegral_enorm (integrable_finsetSum (range I) (fun l _ ↦ hint l)).aestronglyMeasurable]
    dsimp only [ρ]
    simp_rw [hAeq]
    apply (integral_norm_sum_fourierDensity_groupedPrefixRow_le (range I) β Aref Q₀ K r
      (fun j ↦ measurable_weightedRadialBand hd j.1.val) (fun j ↦ norm_weightedRadialBand_le hb j.1.val)).trans
    exact (sum_integral_norm_fourierDensity_groupedPrefixRow_le (range I) β Aref Q₀ K r hn
      (fun j ↦ measurable_weightedRadialBand hd j.1.val) hM
      (fun j ↦ norm_weightedRadialBand_le hb j.1.val) hCA hmax0
      (fun l hl ↦ hK l (mem_range.mp hl)) (fun l hl ↦ hKJ l (mem_range.mp hl))
      (fun l hl ↦ hmax l (mem_range.mp hl)) (fun l hl ↦ hA l (mem_range.mp hl)) hQ hbudget).trans_eq
        (by dsimp [meanDerivativeLoss]; ring)
  have hzeroSupp : (VectorMeasure.dirac (0 : Euclidean (n - 1)) (1 : ℂ) + μ).variation
      (closedBall (0 : Euclidean (n - 1)) (4 * Kmax))ᶜ = 0 := by
    apply le_antisymm _ zero_le
    apply (VectorMeasure.variation_add_le _).trans_eq
    rw [Measure.add_apply, hsupp, add_zero, VectorMeasure.variation_dirac]
    simp [show (0 : Euclidean (n - 1)) ∈ closedBall 0 (4 * Kmax) by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hmax0]
  refine ⟨hfinite, hsupp, hvar, hzeroSupp, ?_, ?_⟩
  · let : IsFiniteMeasure μ.variation := hfinite
    let ν : VectorMeasure (Euclidean (n - 1)) ℂ := VectorMeasure.dirac 0 1
    have ht : (ν + μ).variation.real univ ≤ ν.variation.real univ + μ.variation.real univ := by
      rw [← measureReal_add_apply]
      exact ENNReal.toReal_mono (by finiteness) (VectorMeasure.variation_add_le _)
    have hz : ν.variation.real univ = 1 := by simp [ν, measureReal_def, VectorMeasure.variation_dirac]
    rw [hz] at ht
    exact ht.trans (add_le_add le_rfl hvar)
  · intro s S hS
    let Bs := ((s + 1 : ℕ) : ℝ) * refinedFourierConstant n M *
      4 ^ ((s : ℝ) + (n : ℝ) / 2) * CA * inverseBound
    have hBs : 0 ≤ Bs := by dsimp [Bs]; positivity [refinedFourierConstant_nonneg n hM]
    have hf (l : ℕ) : ContDiff ℝ ∞ (initialDatum β (A l) Q₀ (r l)) :=
      contDiff_initialDatum (n := n) (radius := refinedRadius (J := J))
        (fun j ↦ measurable_weightedRadialBand hd j.1.val) (fun j ↦ norm_weightedRadialBand_le hb j.1.val)
        (A l) Q₀ (r l) (show 0 ≤ (2 : ℝ) ^ J by positivity) refinedRadius_le_ceiling
    change cNorm S s (∑ l ∈ range I, initialDatum β (A l) Q₀ (r l)) ≤ _
    have htriangle : cNorm S s (∑ l ∈ range I, initialDatum β (A l) Q₀ (r l)) ≤
        ∑ l ∈ range I, cNorm S s (initialDatum β (A l) Q₀ (r l)) := by
      simpa only [← Finset.sum_apply] using
        cNorm_sum_le (range I) hS (fun l _ ↦ (hf l).of_le (show (s : ℕ∞ω) ≤ ∞ by simp))
    apply htriangle.trans
    calc
      _ ≤ ∑ l ∈ range I, Bs * Kmax ^ ((s : ℝ) + meanDerivativeLoss n) * ‖r l‖ := by
        apply sum_le_sum
        intro l hl
        have hlI := mem_range.mp hl
        have hbnd := (canonicalWidePrefix_initialData_bounds base C hC G CG hG hn hd hM hb Q₀
          hcoefBound hbaseBound hrawBound hcoef hQ (hK l hlI) (hKJ l hlI) (CGcut l) (hGcut l)
          i hbase (hraw l hlI) (r l)).2 s S
        apply hbnd.trans
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (zero_le_one.trans (hK l hlI)) (hmax l hlI) (by positivity)) hBs) (norm_nonneg _)
      _ = Bs * Kmax ^ ((s : ℝ) + meanDerivativeLoss n) * ∑ l ∈ range I, ‖r l‖ := by rw [Finset.mul_sum]
      _ ≤ Bs * Kmax ^ ((s : ℝ) + meanDerivativeLoss n) * (2 * ε) :=
        mul_le_mul_of_nonneg_left hbudget (mul_nonneg hBs (Real.rpow_nonneg hmax0 _))
      _ = _ := by dsimp [Bs]; ring

end JanetCartan.CurrentMean
