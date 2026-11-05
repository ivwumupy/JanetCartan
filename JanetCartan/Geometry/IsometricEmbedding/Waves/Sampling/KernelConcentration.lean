module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.Concentration
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RefinedKernels

/-!
# Bernstein for the unchanged grouped kernel rows

This connects the actual kernel construction to the probability law in
`app:ch_waves:thm:sampling`. Continuity, compactness and the trace budget are
proved from `BandKernelData`, on `RawInputPartition.RefinedInput`. The two
remaining analytic estimates are the sharp single-band bound and the order-one
norm of the largest continuum normal. The latter controls all prefixes by
positivity; no separate normal estimate is assumed for each prefix.

These inputs must be discharged for the original wave family before the full
source sampling theorem is complete. In particular, this is not a construction
of the geometric phase/amplitude or a proof of the colored-normal comparison.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace JanetCartan.Sampling
open SeparatedSampling Realization RawInputRealization RawInputPartition
open SamplingKernelBounds SamplingKernelBounds.Expectation

variable {n J p : ℕ}

/-- The largest grouped normal dominates every unchanged prefix
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem refinedKernelPrefix_normal_le_full
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]
    (D : BandKernelData (Fin J × P) n) (L : ℕ) (z : P) :
    atomNormal (refinedKernelPrefix D L z) ≤ atomNormal (refinedKernelPrefix D J z) := by
  classical
  have hfull : Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val < J) = Finset.univ := by
    ext i
    simp
  rw [refinedKernelPrefix_normal, refinedKernelPrefix_normal, hfull]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ ↦ atomNormal_nonneg _)

/-- The trace hypothesis of Bernstein follows from the common smooth-band
kernel on both shells and the literal compact sampling weights
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem refinedKernelPrefix_mean_diagonal_le
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (hn : 1 ≤ n) (L : ℕ) {ψ : Point → ℝ} {w : ℝ → ℝ} {B P W h : ℝ}
    (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h) (hh₁ : h ≤ 1)
    (m : ℕ) (e : Fin m → SamplingKernelBounds.Output n) (he : Orthonormal ℂ e) :
    ∑ k, Complex.re ⟪e k,
      patchMeanNormal p B ψ w h (fun c z ↦ refinedKernelPrefix D L (c, z)) (e k)⟫_ℂ ≤
        ((D.squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
          (countConstant p B * (P * W ^ 3))) * ((2 : ℝ) ^ J) ^ n := by
  classical
  obtain ⟨δ, b, _⟩ := exists_hilbertBasis ℂ (RefinedInput n J)
  let T := fun c z ↦ refinedKernelPrefix D L (c, z)
  have hc c : Continuous (T c) := (continuous_refinedKernelPrefix D L).comp
    (continuous_const.prodMk continuous_id)
  have hHS c z := (refinedKernelPrefix_hilbertSchmidt D b L (c, z)).1
  have hs c : Continuous (fun z ↦ hilbertSchmidtSq b (T c z)) :=
    (continuous_hilbertSchmidtSq_refinedKernelPrefix D b L).comp
      (continuous_const.prodMk continuous_id)
  let F := blockFamily (h := h) b hw hψ hψc hwc T hc hHS hs
  have hF : F.expectation = patchMeanNormal p B ψ w h T :=
    blockFamily_expectation_eq ..
  let U := Submodule.span ℂ (↑(Finset.univ.image e) : Set (SamplingKernelBounds.Output n))
  let a := OrthonormalBasis.span he Finset.univ
  have htrace := F.trace_finiteCompression_le_scale (outputHilbertBasis n) U n
    ((2 : ℝ) ^ J) (D.squaredKernelConstant * (1 + (2 : ℝ) ^ n))
    (countConstant p B * (P * W ^ 3))
    (mul_nonneg (mul_nonneg D.squaredKernelConstant_nonneg (by positivity)) (by positivity))
    (fun q z ↦ hilbertSchmidtSq_refinedKernelPrefix_le D b hn L (color p q, z))
    (blockFamily_mass_le b hw hψ hψc hwc T hc hHS hs hh hh₁)
  rw [hF, LinearMap.trace_eq_sum_inner _ a, Complex.re_sum] at htrace
  change (∑ k, Complex.re (inner ℂ (a k)
    (finiteCompression U (patchMeanNormal p B ψ w h T) (a k)))) ≤ _ at htrace
  have ht : (∑ k, Complex.re ⟪(a k : SamplingKernelBounds.Output n),
      patchMeanNormal p B ψ w h T (a k)⟫_ℂ) ≤ _ :=
    (Finset.sum_congr rfl (fun k _ ↦ congrArg Complex.re
      (finiteCompression_inner U _ (a k) (a k)))).symm.trans_le htrace
  simpa [a, T] using ht

private theorem norm_sum_patchMeanNormal_le
    {A E H : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ψ : A → Point → ℝ} {w : ℝ → ℝ} {B W h : ℝ} {P : A → ℝ}
    (hw : WindowBounds p w W) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hψc : ∀ a, Continuous (ψ a)) (hwc : Continuous w)
    (T S : A → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ a c, Continuous (T a c)) (hS : ∀ a c, Continuous (S a c))
    (hle : ∀ a c z, atomNormal (T a c z) ≤ atomNormal (S a c z)) :
    ‖∑ a, patchMeanNormal p B (ψ a) w h (T a)‖ ≤
      ‖∑ a, patchMeanNormal p B (ψ a) w h (S a)‖ := by
  have hwpos a q z : 0 ≤ ψ a z * blockWeight w h q z :=
    mul_nonneg ((hψ a).nonneg z) (Finset.prod_nonneg fun i _ ↦ hw.nonneg _)
  apply CStarAlgebra.norm_le_norm_of_le_of_nonneg
  · apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro q _
    exact integral_mono (integrable_blockIntegrand (hψ a) (hψc a) hwc h _ (hT a) q)
      (integrable_blockIntegrand (hψ a) (hψc a) hwc h _ (hS a) q)
      (fun z ↦ smul_le_smul_of_nonneg_left (hle a (color p q) z) (hwpos a q z))
  · exact Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun q _ ↦
      integral_nonneg (fun z ↦ smul_nonneg (hwpos a q z) (atomNormal_nonneg _))

/-- A single order-one estimate for the largest continuum normal controls all
prefixes of the same finite chart family (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_refinedKernelPrefix_mean_le_full
    {A : Type*} [Fintype A]
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (L : ℕ) {ψ : A → Point → ℝ} {w : ℝ → ℝ} {B W h : ℝ} {P : A → ℝ}
    (hw : WindowBounds p w W) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hψc : ∀ a, Continuous (ψ a)) (hwc : Continuous w) :
    ‖∑ a, patchMeanNormal p B (ψ a) w h (fun c z ↦ refinedKernelPrefix (D a) L (c, z))‖ ≤
      ‖∑ a, patchMeanNormal p B (ψ a) w h (fun c z ↦ refinedKernelPrefix (D a) J (c, z))‖ := by
  have hc a K c : Continuous (fun z ↦ refinedKernelPrefix (D a) K (c, z)) :=
    (continuous_refinedKernelPrefix (D a) K).comp (continuous_const.prodMk continuous_id)
  exact norm_sum_patchMeanNormal_le hw hψ hψc hwc _ _ (fun a ↦ hc a L) (fun a ↦ hc a J)
    (fun a _ _ ↦ refinedKernelPrefix_normal_le_full (D a) L _)

/-- Bernstein for the literal grouped annular kernels of a finite chart family,
with every trace, measurability, compactness, independence and variance premise
discharged (`app:ch_waves:eq:sampling-all-prefixes`). The original sharp band
estimate and largest expectation norm are the remaining analytic inputs.
The same constants work for every `L` and for zero actual variance. -/
theorem operatorBernstein_refinedKernelPrefix
    {A : Type*} [Fintype A]
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (hn : 1 ≤ n) (L : ℕ) {ψ : A → Point → ℝ} {w : ℝ → ℝ}
    {B W h C_op R C t : ℝ} {P : A → ℝ}
    (hw : WindowBounds p w W) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hψc : ∀ a, Continuous (ψ a)) (hwc : Continuous w) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hC_op : 0 ≤ C_op)
    (hband : ∀ a (i : RefinedIndex J) c z,
      ‖(D a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C_op * refinedRadius i)
    (hblock : ∀ a, (nodesPerBlock p : ℝ) * (h ^ 3 * (P a * W ^ 3)) *
      ((3 * C_op) * (2 : ℝ) ^ J) ≤ R)
    (hR : 0 < R) (hC : 0 < C)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) w h
      (fun c z ↦ refinedKernelPrefix (D a) J (c, z))‖ ≤ C)
    (ht : 0 < t) (hthreshold : R * C + R * t / 3 ≤ t ^ 2) :
    familyShiftLaw A p B h
      {ω | t < ‖familyDeviation p B ψ w h
        (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ω‖} ≤
      OperatorCompression.bernsteinTail R (R * C)
        (R * ((∑ a, ((D a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
          (countConstant p B * (P a * W ^ 3))) * ((2 : ℝ) ^ J) ^ n)) t := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  apply operatorBernstein_familyDeviation hw hψ hψc hwc hh _
    (fun a c ↦ (continuous_refinedKernelPrefix (D a) L).comp
      (continuous_const.prodMk continuous_id))
    (fun a c z ↦ isCompactOperator_refinedKernelPrefix (D a) L (c, z))
    (fun a c z ↦ norm_refinedKernelPrefix_sq_le (D a) L (c, z) hC_op
      (fun i ↦ hband a i c z)) hblock hR hC
    ((norm_refinedKernelPrefix_mean_le_full D L hw hψ hψc hwc).trans hmean) ?_ ht hthreshold
  intro m e he
  change (∑ k, diagonalCLM (e k) (∑ a, patchMeanNormal p B (ψ a) w h
    (fun c z ↦ refinedKernelPrefix (D a) L (c, z)))) ≤ _
  simp only [map_sum]
  rw [Finset.sum_comm, Finset.sum_mul]
  exact Finset.sum_le_sum fun a _ ↦
    refinedKernelPrefix_mean_diagonal_le (D a) hn L hw (hψ a) (hψc a) hwc hh hh₁ m e he

end JanetCartan.Sampling
