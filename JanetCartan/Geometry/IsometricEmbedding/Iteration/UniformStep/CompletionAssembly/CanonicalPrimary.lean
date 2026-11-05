module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.CompletionAssembly.PrimaryStrain

/-!
# The original sampled primary after all canonical updates

The final family in `exists_normalized_measured_direct_sampled_stage_at_original_mesh`
is the base corrected wave plus a finite sum of corrected canonical waves.
On the source support this is exactly one correction of their raw sum.
Both quadratures of that full source belong to the original solver domain.
No inverse is reselected and no response is moved through an integral.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.UniformStep

open PrimarySourceAdmission ResponseSourceExtension FixedDomainInverse LocalSobolev
open CorrectedAtoms ProjectedStressFrame CharacteristicTransport.CompleteResidual
open GeometricProfile ResponseTransfer.RetainedFactors RawPrimary ProtectedFlow
open PrimarySourceAdmission.InitialScalarCalculus

private theorem complexLinearizedMetric_sum {n N : ℕ} {ι : Type*}
    (F : Euclidean n → Euclidean N) (s : Finset ι)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) {x : Euclidean n}
    (hZ : ∀ i ∈ s, DifferentiableAt ℝ (Z i) x) :
    WKB.complexLinearizedMetric F (∑ i ∈ s, Z i) x =
      ∑ i ∈ s, WKB.complexLinearizedMetric F (Z i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    ext a b
    simp [WKB.complexLinearizedMetric, partialDeriv]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      complexLinearizedMetric_add F (hZ i (Finset.mem_insert_self _ _))
        (DifferentiableAt.sum fun j hj ↦ hZ j (Finset.mem_insert_of_mem hj))]
    rw [ih (fun j hj ↦ hZ j (Finset.mem_insert_of_mem hj))]

/-- The full cutoff source of the final canonical raw sum is the sum of its
actual complete sources (`app:ch_lag:eq:lag-recurrence`).  Only smoothness on
the original source chart is needed: outside that chart the source cutoff
vanishes.  The sum retains every lower-order strain term. -/
theorem complexAtomicSource_add_sum_of_contDiffOn {n N : ℕ} {ι : Type*}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    {X : Set (Euclidean n)} (hX : IsOpen X) (hχX : tsupport χ ⊆ X)
    (s : Finset ι) (Z₀ : Euclidean n → EuclideanSpace ℂ (Fin N))
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ₀ : ContDiffOn ℝ ∞ Z₀ X) (hZ : ∀ i ∈ s, ContDiffOn ℝ ∞ (Z i) X) :
    complexAtomicSource F χ (Z₀ + ∑ i ∈ s, Z i) =
      complexAtomicSource F χ Z₀ + ∑ i ∈ s, complexAtomicSource F χ (Z i) := by
  classical
  funext x
  by_cases hχ : χ x = 0
  · simp [complexAtomicSource, hχ]
  · have hx : x ∈ X := hχX (subset_tsupport χ hχ)
    have hd₀ := (hZ₀.contDiffAt (hX.mem_nhds hx)).differentiableAt (by simp)
    have hd (i : ι) (hi : i ∈ s) :=
      ((hZ i hi).contDiffAt (hX.mem_nhds hx)).differentiableAt (by simp)
    simp only [complexAtomicSource, Pi.add_apply, Finset.sum_apply]
    rw [complexLinearizedMetric_add F hd₀ (DifferentiableAt.sum hd),
      complexLinearizedMetric_sum F s Z hd, smul_add, Finset.smul_sum]

/-- One fixed response corrects the final canonical raw sum exactly as it
corrects its base and individual updates (`app:ch_lag:eq:lag-recurrence`).
This is a finite-source identity on the actual fields; it neither interchanges
the response with an integral nor assumes quantitative response decay. -/
theorem complexCorrectedAtom_add_sum_of_contDiffOn {n N : ℕ} {ι : Type*}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    {X : Set (Euclidean n)} (hX : IsOpen X) (hχX : tsupport χ ⊆ X)
    (s : Finset ι) (Z₀ : Euclidean n → EuclideanSpace ℂ (Fin N))
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ₀ : ContDiffOn ℝ ∞ Z₀ X) (hZ : ∀ i ∈ s, ContDiffOn ℝ ∞ (Z i) X) :
    complexCorrectedAtom F χ B (Z₀ + ∑ i ∈ s, Z i) =
      complexCorrectedAtom F χ B Z₀ + ∑ i ∈ s, complexCorrectedAtom F χ B (Z i) := by
  rw [complexCorrectedAtom, complexAtomicSource_add_sum_of_contDiffOn F χ hX hχX s Z₀ Z
    hZ₀ hZ, map_add, map_sum]
  simp only [complexCorrectedAtom, Finset.sum_sub_distrib]
  abel

/-- The original source admissions of the base atom and every canonical
wave also admit both quadratures of their literal raw sum.  This supplies
the normalized residual's domain for the final primary without introducing
a separate successful-source-admission premise
(`app:ch_lag:eq:lag-recurrence`, `main:eq:primary-strain`). -/
theorem complexAtomicSource_add_sum_quadratures_mem {n N : ℕ} {ι : Type*}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    {S X : Set (Euclidean n)} (hX : IsOpen X) (hχX : tsupport χ ⊆ X)
    (s : Finset ι) (Z₀ : Euclidean n → EuclideanSpace ℂ (Fin N))
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ₀ : ContDiffOn ℝ ∞ Z₀ X) (hZ : ∀ i ∈ s, ContDiffOn ℝ ∞ (Z i) X)
    (hR₀ : tensorFieldRealPart (complexAtomicSource F χ Z₀) ∈ compactSmoothSources S)
    (hI₀ : tensorFieldImagPart (complexAtomicSource F χ Z₀) ∈ compactSmoothSources S)
    (hR : ∀ i ∈ s,
      tensorFieldRealPart (complexAtomicSource F χ (Z i)) ∈ compactSmoothSources S)
    (hI : ∀ i ∈ s,
      tensorFieldImagPart (complexAtomicSource F χ (Z i)) ∈ compactSmoothSources S) :
    tensorFieldRealPart (complexAtomicSource F χ (Z₀ + ∑ i ∈ s, Z i)) ∈
        compactSmoothSources S ∧
      tensorFieldImagPart (complexAtomicSource F χ (Z₀ + ∑ i ∈ s, Z i)) ∈
        compactSmoothSources S := by
  rw [complexAtomicSource_add_sum_of_contDiffOn F χ hX hχX s Z₀ Z hZ₀ hZ]
  simp only [map_add, map_sum]
  exact ⟨(compactSmoothSources S).add_mem hR₀ ((compactSmoothSources S).sum_mem hR),
    (compactSmoothSources S).add_mem hI₀ ((compactSmoothSources S).sum_mem hI)⟩

end JanetCartan.UniformStep
