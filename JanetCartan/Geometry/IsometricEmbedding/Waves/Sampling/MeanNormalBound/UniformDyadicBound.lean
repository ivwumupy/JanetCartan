module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.DyadicSum
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.AtomicBlocks
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Rounding

/-!
# The original full-band scale in the uniform normal bound

The literal kernel dilation uses `2^j = dyadicScale (j + 1)`. Positivity
transfers the checked dyadic sum bound to this shifted range without a
band-count loss. The consumer is the spectator estimate in `UniformBound`,
for `app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
open Set
open scoped BigOperators Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeanNormalBound
open NormalComparison AmplitudeBound RawInputPartition SeparatedSampling

/-- The finite full-normal sum at the literal dilation scales `2^j` has a
constant independent of the number of bands. A positive extra band at scale
`1/2` embeds it in the existing dyadic estimate
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_uniform_powTwoNormal_bound
    {n r : ℕ} (G : UniformNormalGeometry n r) (C : ℕ → ℝ)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ B > 0, ∀ (J : ℕ) (F : Fin J → UniformNormalData G C) (ε : Fin J → ℝ),
      (∀ j, ε j ∈ Icc 0 G.ε₀) →
      (∀ j, ∀ x ∈ G.X₀, ∀ y ∈ G.X₀, ∀ u ∈ G.D₀,
        γ ≤ ‖averagedGradient ((F j).phase (ε j)) x y u‖) →
      ‖∑ j, ((F j).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).comp
        ((F j).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).adjoint‖ ≤ B := by
  classical
  obtain ⟨B, hB, hb⟩ := exists_uniform_dyadicOscillatoryNormalOperator_bound G C hγ
  refine ⟨B, hB, ?_⟩
  intro J F ε hε hgap
  cases J with
  | zero => simpa using hB.le
  | succ J =>
    let F' : Fin (J + 1 + 1) → UniformNormalData G C := Fin.cases (F 0) F
    let ε' : Fin (J + 1 + 1) → ℝ := Fin.cases (ε 0) ε
    have he' : ∀ j, ε' j ∈ Icc 0 G.ε₀ := Fin.cases (hε 0) hε
    have hg' : ∀ j, ∀ x ∈ G.X₀, ∀ y ∈ G.X₀, ∀ u ∈ G.D₀,
        γ ≤ ‖averagedGradient ((F' j).phase (ε' j)) x y u‖ :=
      Fin.cases (hgap 0) hgap
    have hb' := hb (J + 1 + 1) F' ε' he' hg'
    rw [Fin.sum_univ_succ] at hb'
    simp only [F', ε', Fin.cases_succ, Fin.val_succ, dyadicScale_succ_eq_pow] at hb'
    apply le_trans (CStarAlgebra.norm_le_norm_of_le_of_nonneg ?_ ?_) hb'
    · exact le_add_of_nonneg_left (atomNormal_nonneg _)
    · exact Finset.sum_nonneg fun j _ ↦ atomNormal_nonneg _

end JanetCartan.Sampling.MeanNormalBound
