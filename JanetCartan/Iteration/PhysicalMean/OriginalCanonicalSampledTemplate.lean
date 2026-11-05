module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.SampledRow
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalPrefixData
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaselineTemplate

/-!
# Pack the original supported outer nodes without changing the baseline

These are only index-preserving assembly operations for the actual source14
objects. Every sample is the original filtered outer sample, including nodes
where the inner incidence factor vanishes. The positive baseline is unscaled;
the derivative alone carries its original full-angular factor. Consumers are
the actual raw-row identity and fixed-source Picard data
(`app:ch_mean_pairs:defn:mean-canonical`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalSampled
open SeparatedSampling CanonicalRowComparison RawInputPartition CurrentMean

variable {ι : Type*} {n N J p : ℕ}

/-- Original sample membership itself supplies outer support. No division by a
sample weight or nonvanishing inner-factor assumption occurs. -/
theorem sample_in_outer_support (B : ℝ) (ψ : ι → Point → ℝ)
    (w : ℝ → ℝ) (h : ℝ) (U : ι → Lattice → Point)
    (i : SampleIndex p B ψ w h U) :
    node h (U i.1) i.2 ∈ tsupport (ψ i.1) := by
  have hi : weight (ψ i.1) w h (U i.1) i.2 ≠ 0 :=
    (Finset.mem_filter.mp i.2.property).2
  exact subset_tsupport _ (weight_ne_zero_factors hi).1

/-- Collect the SAME supported positive amplitudes over the original outer
sample index. In particular, no incidence factor multiplies the baseline. -/
def sampledPositiveBaseline (B : ℝ) (ψ : ι → Point → ℝ)
    (w : ℝ → ℝ) (h : ℝ) (U : ι → Lattice → Point)
    (base : ∀ i : ι, (Fin 3 → Fin (p+1)) → ∀ z : Point,
      z ∈ tsupport (ψ i) → SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ)) :
    SmoothPeriodicFamily n (SampleIndex p B ψ w h U) (Matrix (Fin N) (Fin n) ℂ) :=
  ⟨fun x i ↦ (base i.1 (color p i.2.val.1) (node h (U i.1) i.2)
      (sample_in_outer_support B ψ w h U i)).val x (),
    fun i ↦ (base i.1 (color p i.2.val.1) (node h (U i.1) i.2)
      (sample_in_outer_support B ψ w h U i)).property ()⟩

/-- The packed baseline has exactly the original positive value at each outer
sample, independently of the inner incidence factor. -/
theorem sampledPositiveBaseline_apply (B : ℝ) (ψ : ι → Point → ℝ)
    (w : ℝ → ℝ) (h : ℝ) (U : ι → Lattice → Point)
    (base : ∀ i : ι, (Fin 3 → Fin (p+1)) → ∀ z : Point,
      z ∈ tsupport (ψ i) → SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (x : Torus n) (i : SampleIndex p B ψ w h U) :
    (sampledPositiveBaseline B ψ w h U base).val x i =
      (base i.1 (color p i.2.val.1) (node h (U i.1) i.2)
        (sample_in_outer_support B ψ w h U i)).val x () := rfl

/-- Use the identical row, color and node to collect the full-angular G. -/
def sampledDerivative (B : ℝ) (ψ : ι → Point → ℝ)
    (w : ℝ → ℝ) (h : ℝ) (U : ι → Lattice → Point)
    (G : ι → (Fin 3 → Fin (p+1)) → Point →
      WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (i : SampleIndex p B ψ w h U) :
    WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) :=
  G i.1 (color p i.2.val.1) (node h (U i.1) i.2)

/-- Apply only the original wide prefix and exact real refinement isometry.
The physical G has no inverse-Fourier scalar or new input normalization. -/
def sampledPrefixDerivative (B : ℝ) (ψ : ι → Point → ℝ)
    (w : ℝ → ℝ) (h : ℝ) (U : ι → Lattice → Point)
    (G : ι → (Fin 3 → Fin (p+1)) → Point →
      WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (L : ℕ) (i : SampleIndex p B ψ w h U) :
    RefinedInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) :=
  CurrentMean.canonicalWidePrefixRawMap (sampledDerivative B ψ w h U G i) L

/-- The original prefix/isometry does not alter the zero-safe angular
construction. This is the full-versus-inner G join for the actual `hraw`; it
requires neither a physical derivative expansion nor division by the factor. -/
theorem canonicalWidePrefixRawMap_zero_safe (a : ℝ)
    (G : a ≠ 0 → WideInput n J →ₗ[ℝ]
      SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ)) (L : ℕ) :
    canonicalWidePrefixRawMap (if ha : a = 0 then 0 else a • G ha) L =
      if ha : a = 0 then 0 else a • canonicalWidePrefixRawMap (G ha) L := by
  by_cases ha : a = 0
  · simp only [dite_eq_left ha, canonicalWidePrefixRawMap, LinearMap.zero_comp]
  · simp only [dite_eq_right ha, canonicalWidePrefixRawMap, LinearMap.smul_comp]

end JanetCartan.PhysicalMean.OriginalCanonicalSampled
end
