module

public import JanetCartan.Analysis.Microlocal.NormalComparison
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition

/-!
# Uniform summation of the actual masked normal homotopies

The finite-band summation for `app:ch_waves:eq:colored-normal-comparison`.
The per-band bound is proved by the input-only normal comparison theorem,
not assumed. The endpoint here is still the sum of the colored zero-parameter
normals: identifying it with the common transport normal is a separate exact
phase/amplitude and partition argument.

The original dyadic labels start at one half, retaining the high-pass transition
between one and two. Every prefix sits below the same fixed sample ceiling.
The constant has no band-count, sample-count, or inverse-weight factor.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace JanetCartan.Sampling.ColoredNormalComparison
open NormalComparison RawInputPartition

/-- Exact geometric sum for the retained source labels, including the first
half-scale band (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_range_dyadicScale (J : ℕ) :
    ∑ j ∈ Finset.range J, dyadicScale j = dyadicScale J - 1 / 2 := by
  induction J with
  | zero => norm_num [dyadicScale]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [dyadicScale, pow_succ]
    ring

/-- All original grouped prefixes have scale sum at most twice the fixed
ceiling, without a logarithmic loss
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_range_dyadicScale_le_ceiling {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {J : ℕ} (hJ : J ≤ cutoffCount Λ) :
    ∑ j ∈ Finset.range J, dyadicScale j ≤ 2 * Λ := by
  rw [sum_range_dyadicScale]
  have h := (dyadicScale_strictMono.monotone hJ).trans (cutoffCount_plateau hΛ).2
  linarith

variable {n r : ℕ} {Color : Type*} [Fintype Color]

/-- The actual quotient parameter `ε = τ_c κ_j` stays in the original buffer
for every band of every prefix under the fixed ceiling. Only the fixed positive
lower radial bound is needed (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem radial_band_parameter_mem {G : UniformNormalGeometry n r}
    {R Rmin lam Λ : ℝ} (hRmin : 0 < Rmin) (hR : Rmin ≤ R)
    (hlam : 0 < lam) (hΛ : 1 ≤ Λ) (hbuffer : Λ / (Rmin * lam) ≤ G.ε₀)
    {j : ℕ} (hj : j < cutoffCount Λ) :
    (R * lam)⁻¹ * dyadicScale j ∈ Icc 0 G.ε₀ := by
  have hRpos := hRmin.trans_le hR
  have hinv : (R * lam)⁻¹ ≤ (Rmin * lam)⁻¹ :=
    inv_anti₀ (mul_pos hRmin hlam) (mul_le_mul_of_nonneg_right hR hlam.le)
  refine ⟨mul_nonneg (inv_nonneg.mpr (mul_pos hRpos hlam).le)
    (dyadicScale_pos j).le, ?_⟩
  calc
    _ ≤ (Rmin * lam)⁻¹ * dyadicScale j :=
      mul_le_mul_of_nonneg_right hinv (dyadicScale_pos j).le
    _ ≤ (Rmin * lam)⁻¹ * Λ := mul_le_mul_of_nonneg_left
      ((lt_cutoffCount_iff hΛ j).mp hj) (by positivity)
    _ = Λ / (Rmin * lam) := by ring
    _ ≤ G.ε₀ := hbuffer

/-- Uniform finite-family comparison with the sum of the zero-parameter
colored normals, proved from the primitive `UniformNormalData` and the exact
L∞ realizations of the masks. This is the summation step of
`app:ch_waves:eq:colored-normal-comparison`, not an assumption of per-band
operator estimates. The constant precedes the family, radial labels, scales,
mesh, fixed ceiling, and every grouped prefix. The remaining endpoint
identification must use common primitive phases/amplitudes and the literal
color partition. -/
theorem exists_colored_prefix_homotopy_bound (G : UniformNormalGeometry n r)
    (C : ℕ → ℝ) {Rmin L : ℝ} (hRmin : 0 < Rmin) (hL : 0 ≤ L) :
    ∃ A > 0, ∀ (F : Color → ℕ → UniformNormalData G C)
      (R : Color → ℝ), (∀ c, Rmin ≤ R c) →
      ∀ (m : Color → Euclidean n → ℝ),
      (∀ c, ContDiffOn ℝ ∞ (m c) G.D) →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
      (∀ c u, u ∈ G.D → 0 ≤ m c u ∧ m c u ≤ 1) →
      (∀ c u, u ∈ G.D → ‖fderiv ℝ (m c) u‖ ≤ L / h) →
      ∀ g : Color → Lp ℂ ∞ (volume.restrict G.D),
      (∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦ (m c u : ℂ)) →
      ∀ lam Λ : ℝ, 0 < lam → 1 ≤ Λ → Λ / (Rmin * lam) ≤ G.ε₀ →
      ∀ J ≤ cutoffCount Λ,
        ‖(∑ c, ∑ j ∈ Finset.range J,
            (F c j).uniformOscillatoryNormalOperator (dyadicScale j) (g c)
              ((R c * lam)⁻¹ * dyadicScale j)) -
          (∑ c, ∑ j ∈ Finset.range J,
            (F c j).uniformOscillatoryNormalOperator (dyadicScale j) (g c) 0)‖ ≤
          A * lam⁻¹ * Λ / h := by
  obtain ⟨B, hB, hcomp⟩ := G.exists_uniformOscillatoryNormalOperator_comparison C
  let D := B * (1 + (n : ℝ) * L)
  have hD : 0 < D := by dsimp [D]; positivity
  let A := 2 * ((Fintype.card Color : ℝ) + 1) * D / Rmin
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro F R hR m hm h hh hh₁ hmask hderiv g hg lam Λ hlam hΛ hbuffer J hJ
  have hband (c : Color) (j : ℕ) (hj : j ∈ Finset.range J) :
      ‖(F c j).uniformOscillatoryNormalOperator (dyadicScale j) (g c)
          ((R c * lam)⁻¹ * dyadicScale j) -
        (F c j).uniformOscillatoryNormalOperator (dyadicScale j) (g c) 0‖ ≤
        D * (Rmin * lam)⁻¹ * dyadicScale j / h := by
    have hε := radial_band_parameter_mem hRmin (hR c) hlam hΛ hbuffer
      ((Finset.mem_range.mp hj).trans_le hJ)
    have hinv : (R c * lam)⁻¹ ≤ (Rmin * lam)⁻¹ :=
      inv_anti₀ (mul_pos hRmin hlam) (mul_le_mul_of_nonneg_right (hR c) hlam.le)
    calc
      _ ≤ D * ((R c * lam)⁻¹ * dyadicScale j) / h :=
        hcomp (F c j) (dyadicScale j) (dyadicScale_pos j) (m c) (hm c)
          h L hh hh₁ hL (hmask c) (hderiv c) (g c) (hg c) _ hε
      _ ≤ D * ((Rmin * lam)⁻¹ * dyadicScale j) / h := by
        gcongr
        exact (dyadicScale_pos j).le
      _ = _ := by ring
  have hsum (c : Color) :
      (∑ j ∈ Finset.range J,
        ‖(F c j).uniformOscillatoryNormalOperator (dyadicScale j) (g c)
            ((R c * lam)⁻¹ * dyadicScale j) -
          (F c j).uniformOscillatoryNormalOperator (dyadicScale j) (g c) 0‖) ≤
        2 * D * (Rmin * lam)⁻¹ * Λ / h := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, D * (Rmin * lam)⁻¹ * dyadicScale j / h :=
        Finset.sum_le_sum (hband c)
      _ = D * (Rmin * lam)⁻¹ * (∑ j ∈ Finset.range J, dyadicScale j) / h := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
      _ ≤ D * (Rmin * lam)⁻¹ * (2 * Λ) / h := by
        gcongr
        exact sum_range_dyadicScale_le_ceiling hΛ hJ
      _ = _ := by ring
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, ‖(∑ j ∈ Finset.range J,
        (F c j).uniformOscillatoryNormalOperator (dyadicScale j) (g c)
          ((R c * lam)⁻¹ * dyadicScale j)) -
        ∑ j ∈ Finset.range J,
          (F c j).uniformOscillatoryNormalOperator (dyadicScale j) (g c) 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : Color, 2 * D * (Rmin * lam)⁻¹ * Λ / h := by
      apply Finset.sum_le_sum
      intro c _
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (hsum c)
    _ = (Fintype.card Color : ℝ) * (2 * D * (Rmin * lam)⁻¹ * Λ / h) := by
      simp
    _ ≤ ((Fintype.card Color : ℝ) + 1) * (2 * D * (Rmin * lam)⁻¹ * Λ / h) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = A * lam⁻¹ * Λ / h := by
      dsimp [A]
      rw [mul_inv_rev]
      ring

end JanetCartan.Sampling.ColoredNormalComparison
