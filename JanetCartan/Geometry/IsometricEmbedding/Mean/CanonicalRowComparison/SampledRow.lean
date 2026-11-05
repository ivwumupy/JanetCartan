module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RefinedKernels
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization.Family
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.Comparison

/-!
# The literal finite sampling row

For `app:ch_mean_pairs:defn:mean-canonical`, enumerate the SAME finite charts,
nodes, colors and weights as `Sampling.Realization.familyDeviation`. The normal
of the real row is exactly four times the real compression of that sample
normal. Both input quadratures and the original annular measures are retained.

The sample event and colored comparison are the existing sampling producer's
inputs. Identifying its kernel with the final corrected cross response is a
separate obligation; the algebra here does not assume that identification.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace JanetCartan.CanonicalRowComparison

open SeparatedSampling Sampling Sampling.Realization SamplingKernelBounds

variable {J : Type*} [Fintype J] {n p : ℕ}

/-- Literal sample labels of `app:ch_waves:eq:sampling-prefix-normal`, with
the chart label retained even when two charts contain the same physical node. -/
abbrev SampleIndex (p : ℕ) (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : J → Lattice → Point) :=
  (a : J) × samples p B (ψ a) w h (U a)

/-- The original nonnegative sample weight in
`app:ch_mean_pairs:defn:mean-canonical`; no normalization or inverse weight. -/
def sampleWeight (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : J → Lattice → Point) (i : SampleIndex p B ψ w h U) : ℝ :=
  weight (ψ i.1) w h (U i.1) i.2

omit [Fintype J] in
/-- Nonnegativity follows from the actual patch and window, including the
degenerate zero-weight case (`app:ch_waves:thm:sampling`). -/
theorem sampleWeight_nonneg {B h W : ℝ} {P : J → ℝ}
    {ψ : J → Point → ℝ} {w : ℝ → ℝ} (U : J → Lattice → Point)
    (hw : WindowBounds p w W) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hh : 0 ≤ h) (i : SampleIndex p B ψ w h U) :
    0 ≤ sampleWeight B ψ w h U i :=
  weight_nonneg hw (hψ i.1) hh i.2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- The literal component `2 Re T_{c(i),Z_i}` of
`app:ch_waves:eq:sampling-prefix-normal`, before taking any adjoint or inverse. -/
def sampledComponent (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : J → Lattice → Point)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] Output n)
    (i : SampleIndex p B ψ w h U) :
    E →L[ℝ] Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) :=
  realQuadratureChannel (T i.1 (color p i.2.val.1) (node h (U i.1) i.2))

/-- Exact identification with the producer's literal sampled normal, retaining
both quadratures and factor four (`app:ch_waves:eq:real-normal`,
`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem sampled_weightedRow_normal (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ)
    (h : ℝ) (U : J → Lattice → Point)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] Output n)
    (hμ : ∀ i : SampleIndex p B ψ w h U, 0 ≤ sampleWeight B ψ w h U i) :
    let A := CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (sampledComponent B ψ w h U T)
    A.comp A.adjoint = (4 : ℝ) • realOutputCompression
      (∑ a, patchSampleNormal p B (ψ a) w h (T a) (U a)) := by
  dsimp only
  rw [CanonicalRow.weightedRow_comp_adjoint _ hμ]
  simp only [sampledComponent, realQuadratureChannel_normal_eq_four_realPart,
    sampleWeight, Fintype.sum_sigma]
  ext1 q
  simp only [patchSampleNormal, realOutputCompression, atomNormal,
    ContinuousLinearMap.comp_apply, sum_apply, smul_apply,
    ContinuousLinearMap.coe_restrictScalars',
    map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

/-- Applying the common event and colored comparison to the SAME literal
finite real row gives its transport comparison. These two inequalities are
exactly the sampling producer's outputs, not a normal comparison assumed for
the canonical row (`app:ch_waves:eq:sampling-all-prefixes`,
`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sampled_weightedRow_normal_sub_transport_le
    (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (ξ : J → ShiftSpace p B h)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] Output n)
    (T₀ : J → Point → E →L[ℂ] Output n)
    (hμ : ∀ i : SampleIndex p B ψ w h (fun a ↦ extendedShift (ξ a)),
      0 ≤ sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)) i)
    {samplingError transportError : ℝ}
    (hevent : ‖familyDeviation p B ψ w h T ξ‖ ≤ samplingError)
    (htransport : ‖(∑ a, patchMeanNormal p B (ψ a) w h (T a)) -
      (∑ a, ∫ z : Point, ψ a z • atomNormal (T₀ a z))‖ ≤ transportError) :
    let A := CanonicalRow.weightedRow
      (sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)))
      (sampledComponent B ψ w h (fun a ↦ extendedShift (ξ a)) T)
    ‖A.comp A.adjoint - (4 : ℝ) • realOutputCompression
      (∑ a, ∫ z : Point, ψ a z • atomNormal (T₀ a z))‖ ≤
        4 * (samplingError + transportError) := by
  dsimp only
  rw [sampled_weightedRow_normal B ψ w h _ T hμ, ← smul_sub,
    ← realOutputCompression_sub, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply mul_le_mul_of_nonneg_left ((realOutputCompression_norm_le _).trans ?_)
    (by norm_num)
  have hsampling : ‖(∑ a, patchSampleNormal p B (ψ a) w h (T a)
      (extendedShift (ξ a))) - (∑ a, patchMeanNormal p B (ψ a) w h (T a))‖ ≤
        samplingError := by
    simpa only [familyDeviation, Finset.sum_sub_distrib] using hevent
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (∑ a, patchMeanNormal p B (ψ a) w h (T a)) _).trans
      (add_le_add hsampling htransport)

end JanetCartan.CanonicalRowComparison
