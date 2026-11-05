module

public import JanetCartan.Iteration.PhysicalForwardMean.OriginalScalar
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.DerivativeBounds

/-!
# Regularity of the unchanged full native scalar mask

The scalar band shape and the actual finite sample/shell indexing produce
continuity, compact source support and the original high-frequency implication.
These are the qualitative input conditions of the forward/adjoint integral
construction; no frequency derivative bound or cutoff-size norm bound is used.
The original sample weights can be zero and are never inverted.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalForwardMean
open PhysicalSamplingShells Sampling Sampling.Realization SamplingKernelBounds
open SeparatedSampling CanonicalRowComparison RawInputPartition

/-- The unchanged full half-weighted band mask is continuous. -/
theorem continuous_forwardScalarBandMask {n : ℕ} {d : Euclidean (n - 1) → ℝ}
    (hd : Continuous d) (j : ℕ) : Continuous (forwardScalarBandMask n d j) := by
  exact (((continuous_const.mul (Real.continuous_sqrt.comp continuous_norm)).mul hd).mul
    (contDiff_radialBand n j (r := 0)).continuous)

/-- Only the ORIGINAL smooth radial band supplies compact source support. -/
theorem hasCompactSupport_forwardScalarBandMask (n : ℕ) (d : Euclidean (n - 1) → ℝ) (j : ℕ) :
    HasCompactSupport (forwardScalarBandMask n d j) :=
  (hasCompactSupport_radialBand n j).mul_left

variable {n J p : ℕ} {A : Type*} [Fintype A]
  (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ) (U : A → Lattice → Point)
  [TopologicalSpace (SampleIndex p B ψ w h U)] [DiscreteTopology (SampleIndex p B ψ w h U)]
local notation "I" => SampleIndex p B ψ w h U × RefinedIndex J
local notation "E" => Euclidean (n - 1)

omit [Fintype A] in
/-- The literal full native mask is jointly continuous even for zero original
sample weights. Discrete labels are not differentiated. -/
theorem continuous_nativeForwardScalarMask
    (b : A → Fin J → E → ℝ) (L : ℕ) (hb : ∀ a j, Continuous (b a j)) :
    Continuous (nativeForwardScalarMask (p := p) B ψ w h U b L) := by
  apply continuous_prod_of_discrete_left.mpr
  intro i
  by_cases hi : i.2.1.val < L
  · simpa only [nativeForwardScalarMask, hi, ite_true] using
      continuous_const.fun_mul (hb i.1.1 i.2.1)
  · simpa only [nativeForwardScalarMask, hi, ite_false] using
      (continuous_const (X := E) (y := (0 : ℝ)))

/-- The original finite family of compact radial bands produces compact source
support for the SAME mask. Its size is used only qualitatively, never in the
forward derivative estimate (`app:ch_mean_pairs:eq:block-normal`). -/
theorem hasCompactSupport_nativeForwardScalarMask
    (b : A → Fin J → E → ℝ) (L : ℕ) (hb : ∀ a j, HasCompactSupport (b a j)) :
    HasCompactSupport (nativeForwardScalarMask (p := p) B ψ w h U b L) := by
  classical
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_univ : IsCompact (univ : Set I)).prod
      (isCompact_iUnion fun a ↦ isCompact_iUnion fun j ↦ hb a j))
  intro u hu
  refine ⟨mem_univ _, mem_iUnion.mpr ⟨u.1.1.1, mem_iUnion.mpr ⟨u.1.2.1, ?_⟩⟩⟩
  apply subset_tsupport
  intro hz
  exact hu (by simp only [nativeForwardScalarMask, hz, mul_zero, ite_self])

omit [Fintype A] [TopologicalSpace (SampleIndex p B ψ w h U)] [DiscreteTopology (SampleIndex p B ψ w h U)] in
/-- The original high-pass implication survives the native sample weights and
prefix indicator, without requiring either factor to be positive. -/
theorem one_lt_norm_of_nativeForwardScalarMask_ne_zero
    (b : A → Fin J → E → ℝ) (L : ℕ)
    (hb : ∀ a j η, ‖η‖ ≤ 1 → b a j η = 0)
    {u : I × E} (hu : nativeForwardScalarMask (p := p) B ψ w h U b L u ≠ 0) : 1 < ‖u.2‖ := by
  by_contra hle
  exact hu (by simp only [nativeForwardScalarMask, hb _ _ _ (not_lt.mp hle), mul_zero, ite_self])

end JanetCartan.PhysicalForwardMean
