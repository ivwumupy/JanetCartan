module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Synthesis
public import JanetCartan.Analysis.Operator.NormalPerturbation.Weighted

/-!
# Unchanged finite annular rows

The rows and prefixes of `app:ch_waves:eq:sampling-prefix-normal` use the same
full annular Hilbert input. The parent sampling construction supplies each band
operator; no wave estimate or row estimate is assumed here.
-/

@[expose] public noncomputable section

open ContinuousLinearMap
attribute [local instance] Classical.propDecidable
namespace JanetCartan.SamplingKernelBounds
open RawInputRealization NormalPerturbation

variable {ι : Type*} [Fintype ι] {n : ℕ} {radius : ι → ℝ}

/-- The unchanged annular row (`app:ch_waves:eq:sampling-prefix-normal`). -/
def annularRow (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) :
    Input n radius →L[ℂ] Output n := weightedRow (fun _ ↦ 1) T

/-- A coordinate prefix, still on the full input of the unchanged row
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def prefixRow (s : Finset ι) (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) :
    Input n radius →L[ℂ] Output n := by
  classical
  exact weightedRow (fun i ↦ if i ∈ s then 1 else 0) T

/-- Literal sum of unchanged bands (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem annularRow_apply (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n)
    (x : Input n radius) : annularRow T x = ∑ i, T i (x i) := by
  simp [annularRow, weightedRow_apply]

/-- Literal prefix sum (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem prefixRow_apply (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) (x : Input n radius) :
    prefixRow s T x = ∑ i ∈ s, T i (x i) := by
  classical
  simp [prefixRow, weightedRow_apply, apply_ite, ite_smul]

/-- The largest prefix is the original row (`app:ch_waves:eq:sampling-prefix-normal`). -/
@[simp] theorem prefixRow_univ (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) :
    prefixRow Finset.univ T = annularRow T := by
  classical
  simp [prefixRow, annularRow]

/-- Adjoint coordinates retain each entire annular input
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem prefixRow_adjoint_apply (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) (y : Output n) (i : ι) :
    (prefixRow s T).adjoint y i = if i ∈ s then (T i).adjoint y else 0 := by
  classical
  by_cases hi : i ∈ s <;> simp [prefixRow, hi]

/-- Adjoint coordinates of the unchanged row (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem annularRow_adjoint_apply
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) (y : Output n) (i : ι) :
    (annularRow T).adjoint y i = (T i).adjoint y := by
  simp [annularRow]

/-- Compatibility with any supplied coordinate projection having the literal
formula, without constructing a second projection API
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem annularRow_comp_coordinateProjection (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n)
    (P : Input n radius →L[ℂ] Input n radius)
    (hP : ∀ x i, P x i = if i ∈ s then x i else 0) :
    annularRow T ∘L P = prefixRow s T := by
  classical
  ext1 x
  simp [annularRow_apply, prefixRow_apply, hP, apply_ite]

/-- Exact prefix normal, with no cross-band terms
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem prefixRow_normal (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) :
    prefixRow s T ∘L (prefixRow s T).adjoint = ∑ i ∈ s, T i ∘L (T i).adjoint := by
  classical
  have h := normal_weightedRow (fun i ↦ if i ∈ s then 1 else 0)
    (fun i ↦ by split_ifs <;> norm_num) T
  simpa [prefixRow, normal, ite_smul] using h

/-- No factor in the number of bands occurs in the squared row bound
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_prefixRow_sq_le (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) :
    ‖prefixRow s T‖ ^ 2 ≤ ∑ i ∈ s, ‖T i‖ ^ 2 := by
  classical
  have h := norm_normal_weightedRow_le (fun i ↦ if i ∈ s then 1 else 0)
    (fun i ↦ by split_ifs <;> norm_num) T
  simpa [norm_normal, prefixRow, ite_mul] using h

/-- Squared adjoint energy splits exactly across the selected coordinates
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_prefixRow_adjoint_sq (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) (y : Output n) :
    ‖(prefixRow s T).adjoint y‖ ^ 2 = ∑ i ∈ s, ‖(T i).adjoint y‖ ^ 2 := by
  classical
  rw [norm_input_sq]
  simp [prefixRow_adjoint_apply, apply_ite]

/-- Operator-norm continuity follows from continuity of the individual bands
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_prefixRow {P : Type*} [TopologicalSpace P] (s : Finset ι)
    (T : ∀ i, P → AnnularL2 n (radius i) →L[ℂ] Output n)
    (hT : ∀ i, Continuous (T i)) : Continuous (fun p ↦ prefixRow s (fun i ↦ T i p)) := by
  have he (p : P) : prefixRow s (fun i ↦ T i p) =
      ∑ i ∈ s, T i p ∘L PiLp.proj 2 (fun i ↦ AnnularL2 n (radius i)) i := by
    ext1 x
    simp [prefixRow_apply, PiLp.proj, PiLp.projₗ]
  simp_rw [he]
  exact continuous_finsetSum _ (fun i _ ↦ (hT i).clm_comp continuous_const)

end JanetCartan.SamplingKernelBounds
