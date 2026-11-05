module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.FrequencySupport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.DyadicSum.Overlap

/-!
# Uniform physical derivatives of the summed normal amplitude

The full two-position matrix amplitude in the proof following
`app:ch_waves:eq:sampling-operator-bounds`. Its derivative reserve is exactly
`2 * (n + 1)`, independent of the number of bands. All amplitude bounds come
from the primitive-input calculus; only the original averaged-gradient gap is
an additional hypothesis. The consuming result is the dyadic normal sum bound.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeanNormalBound
open NormalComparison AmplitudeBound RawInputPartition

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

local instance (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

private theorem coordinateDerivList_sum {d J : ℕ}
    (f : Fin J → Euclidean d → ℂ) (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (is : List (Fin d)) :
    euclideanCoordinateDerivList is (fun z ↦ ∑ j, f j z) =
      fun z ↦ ∑ j, euclideanCoordinateDerivList is (f j) z := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    funext z
    simp only [euclideanCoordinateDerivList, ih]
    rw [fderiv_fun_sum (fun j _ ↦
      (contDiff_euclideanCoordinateDerivList (hf j) is).differentiable (by simp) z)]
    simp only [sum_apply]

private theorem coordinateDerivList_zero {d : ℕ} (is : List (Fin d)) :
    euclideanCoordinateDerivList is (fun _ : Euclidean d ↦ (0 : ℂ)) = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    funext z
    simp [euclideanCoordinateDerivList, ih]

private theorem matrixCoordinateDerivList_sum {d J : ℕ}
    (f : Fin J → Euclidean d → Matrix (Fin r) (Fin r) ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (is : List (Fin d)) (z : Euclidean d) :
    matrixAmplitudeCoordinateDerivList is (fun z ↦ ∑ j, f j z) z =
      ∑ j, matrixAmplitudeCoordinateDerivList is (f j) z := by
  ext a b
  simp only [matrixAmplitudeCoordinateDerivList, Matrix.sum_apply]
  exact congrFun (coordinateDerivList_sum (fun j z ↦ f j z a b)
    (fun j ↦ (matrixEntryEvaluation a b).contDiff.comp (hf j)) is) z

private theorem matrixCoordinateDerivList_zero {d : ℕ} (is : List (Fin d))
    (z : Euclidean d) :
    matrixAmplitudeCoordinateDerivList is
      (fun _ : Euclidean d ↦ (0 : Matrix (Fin r) (Fin r) ℂ)) z = 0 := by
  ext a b
  exact congrFun (coordinateDerivList_zero is) z

/-- The sum of the literal rescaled full matrix amplitudes, retaining both
physical positions (`app:ch_waves:eq:sampling-operator-bounds`). -/
def dyadicNormalAmplitude {J : ℕ} (F : Fin J → UniformNormalData G C)
    (ε : Fin J → ℝ) (ξ : Euclidean n) (z : Euclidean (2 * n)) :
    Matrix (Fin r) (Fin r) ℂ :=
  ∑ j, unitFrequencyAmplitude (dyadicScale j.val) ((F j).pairedInverseAmplitude (ε j)) ξ z

/-- The finite summed full amplitude is jointly smooth, as required by
`app:ch_osc:lem:osc-amplitude`. No estimate uses the number of summands. -/
theorem contDiff_dyadicNormalAmplitude {J : ℕ} (F : Fin J → UniformNormalData G C)
    (ε : Fin J → ℝ) (hε : ∀ j, ε j ∈ Icc 0 G.ε₀) :
    ContDiff ℝ ∞ (Function.uncurry (dyadicNormalAmplitude F ε)) := by
  unfold dyadicNormalAmplitude Function.uncurry
  exact ContDiff.sum (fun j _ ↦ contDiff_unitFrequencyAmplitude (dyadicScale j.val)
    ((F j).pairedInverseAmplitude_contDiff (hε j)))

/-- The primitive-input bounds and the primitive frequency gap imply a
band-count-independent physical derivative bound for the summed full
amplitude. The SAME fixed reserve `2 * (n + 1)` is used before and after
summation (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_dyadicNormalAmplitude_bounds
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ R > 0, ∃ A > 0, ∀ (J : ℕ) (F : Fin J → UniformNormalData G C)
      (ε : Fin J → ℝ), (∀ j, ε j ∈ Icc 0 G.ε₀) →
      (∀ j, ∀ x ∈ G.X₀, ∀ y ∈ G.X₀, ∀ u ∈ G.D₀,
        γ ≤ ‖averagedGradient ((F j).phase (ε j)) x y u‖) →
      MatrixNormalAmplitudeBounds (dyadicNormalAmplitude F ε) R A := by
  classical
  obtain ⟨R, hR, A, hA, hb⟩ := G.exists_unitFrequencyAmplitude_bounds C
  obtain ⟨β, _, hβ⟩ := exists_unitFrequencyAmplitude_frequency_upper G C
  obtain ⟨N, hN, hcount⟩ := exists_dyadic_annular_overlap_bound
    (β := β) (div_pos hγ (by positivity : 0 < 2 * Real.pi))
  refine ⟨R, hR, N * A, mul_pos (by exact_mod_cast hN) hA, ?_⟩
  intro J F ε hε hgap
  let b := fun j : Fin J ↦
    unitFrequencyAmplitude (dyadicScale j.val) ((F j).pairedInverseAmplitude (ε j))
  have hbs (j : Fin J) := hb (F j) (ε j) (hε j) (dyadicScale j.val)
  have hdiff := contDiff_dyadicNormalAmplitude F ε hε
  refine ⟨hdiff.continuous.stronglyMeasurable,
    fun ξ ↦ hdiff.comp (contDiff_const.prodMk contDiff_id), ?_, ?_⟩
  · intro ξ a b' z hz i
    have he : ∃ j : Fin J, b j ξ z a b' ≠ 0 := by
      by_contra! h
      apply hz
      change (∑ j, b j ξ z) a b' = 0
      simp only [Matrix.sum_apply, h, Finset.sum_const_zero]
    obtain ⟨j, hj⟩ := he
    exact (hbs j).support ξ a b' z hj i
  · intro ξ is hi z
    let s := Finset.univ.filter (fun j : Fin J ↦
      (γ / (2 * Real.pi)) * dyadicScale j.val ≤ ‖ξ‖ ∧
        ‖ξ‖ ≤ β * dyadicScale j.val)
    have hout (j : Fin J) (hj : j ∉ s) : b j ξ = 0 := by
      funext w
      by_contra hn
      have hl := unitFrequencyAmplitude_frequency_lower (F j) (hε j)
        (dyadicScale_pos j.val) (hgap j) hn
      have hu := hβ (F j) (ε j) (hε j) _ (dyadicScale_pos j.val) ξ w hn
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, hu⟩)
    have hderiv (j : Fin J) (hj : j ∉ s) :
        matrixAmplitudeCoordinateDerivList is (b j ξ) z = 0 := by
      rw [hout j hj]
      exact matrixCoordinateDerivList_zero is z
    change ‖matrixAmplitudeCoordinateDerivList is (fun w ↦ ∑ j, b j ξ w) z‖ ≤ _
    rw [matrixCoordinateDerivList_sum _ (fun j ↦ (hbs j).smooth ξ)]
    rw [← Finset.sum_subset (Finset.subset_univ s) (fun j _ hj ↦ hderiv j hj)]
    calc
      ‖∑ j ∈ s, matrixAmplitudeCoordinateDerivList is (b j ξ) z‖ ≤
          ∑ j ∈ s, ‖matrixAmplitudeCoordinateDerivList is (b j ξ) z‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ s, A := Finset.sum_le_sum (fun j _ ↦ (hbs j).derivative ξ is hi z)
      _ = (s.card : ℝ) * A := by simp
      _ ≤ (N : ℝ) * A := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount J ‖ξ‖) hA.le

end JanetCartan.Sampling.MeanNormalBound
