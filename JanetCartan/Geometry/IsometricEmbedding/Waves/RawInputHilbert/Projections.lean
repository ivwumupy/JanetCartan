module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Synthesis

/-!
# Coordinate prefixes of the annular input

All prefixes in `app:ch_waves:eq:sampling-prefix-normal` act on one and the
same finite annular Hilbert sum. These coordinate projections discard complete
complex channels and retain both quadratures of every retained channel.
-/

@[expose] public noncomputable section

open MeasureTheory
namespace JanetCartan.RawInputHilbert
open RawInputRealization

variable {n : ℕ} {ι : Type*} [Fintype ι] {radius : ι → ℝ}

/-- Projection retaining a specified collection of channels, on the fixed
input Hilbert space (`app:ch_waves:eq:sampling-prefix-normal`). -/
def coordinateProjection (s : Finset ι) : Input n radius →L[ℂ] Input n radius := by
  classical
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun i ↦ AnnularL2 n (radius i))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i ↦ if i ∈ s then PiLp.proj 2 _ i else 0))

/-- Literal retained-coordinate formula (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem coordinateProjection_apply [DecidableEq ι] (s : Finset ι) (v : Input n radius) (i : ι) :
    coordinateProjection s v i = if i ∈ s then v i else 0 := by
  classical
  by_cases hi : i ∈ s <;> simp [coordinateProjection, hi, PiLp.proj_apply]

/-- Every coordinate prefix is a contraction, uniformly in the number of
channels (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_coordinateProjection_le (s : Finset ι) :
    ‖coordinateProjection (n := n) (radius := radius) s‖ ≤ 1 := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_input_sq, norm_input_sq]
  apply Finset.sum_le_sum
  intro i _
  rw [coordinateProjection_apply]
  split_ifs <;> simp

/-- Idempotence on the original input space
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem coordinateProjection_idempotent (s : Finset ι) :
    (coordinateProjection (n := n) (radius := radius) s).comp (coordinateProjection s) =
      coordinateProjection s := by
  classical
  ext1 v
  apply PiLp.ext
  intro i
  by_cases hi : i ∈ s <;> simp [coordinateProjection_apply, hi]

/-- Self-adjointness is proved in the complex Hilbert space first
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_coordinateProjection (s : Finset ι) :
    (coordinateProjection (n := n) (radius := radius) s).adjoint = coordinateProjection s := by
  classical
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v w
  simp only [PiLp.inner_apply, coordinateProjection_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- A prefix is selected by its labels, rather than changing the input type
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def prefixProjection (label : ι → ℕ) (cutoff : ℕ) : Input n radius →L[ℂ] Input n radius :=
  coordinateProjection (Finset.univ.filter (fun i ↦ label i ≤ cutoff))

/-- Prefix contractions have no scale-count factor
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_prefixProjection_le (label : ι → ℕ) (cutoff : ℕ) :
    ‖prefixProjection (n := n) (radius := radius) label cutoff‖ ≤ 1 :=
  norm_coordinateProjection_le _

/-- Prefixes are self-adjoint on the same input Hilbert space
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_prefixProjection (label : ι → ℕ) (cutoff : ℕ) :
    (prefixProjection (n := n) (radius := radius) label cutoff).adjoint =
      prefixProjection label cutoff := adjoint_coordinateProjection _

/-- The output prefix normal is precisely the sum of the retained channel
normals (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem synthesis_coordinateProjection_adjoint
    {M : ι → ℝ} {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (radius i)))
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (radius i), ‖β i η‖ ≤ M i)
    (s : Finset ι) :
    (synthesis hβ hM hb).comp ((coordinateProjection s).comp (synthesis hβ hM hb).adjoint) =
      ∑ i ∈ s, (channel (hβ i) (hM i) (hb i)).comp (channel (hβ i) (hM i) (hb i)).adjoint := by
  classical
  ext1 f
  simp only [ContinuousLinearMap.comp_apply, synthesis_apply,
    coordinateProjection_apply, adjoint_synthesis_apply, sum_apply]
  simp only [apply_ite, map_zero]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]

end JanetCartan.RawInputHilbert
