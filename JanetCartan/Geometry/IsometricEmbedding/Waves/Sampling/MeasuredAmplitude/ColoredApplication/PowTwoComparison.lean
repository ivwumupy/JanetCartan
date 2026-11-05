module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.Bands
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.PatchMultiplier

/-!
# Homotopy comparison at the retained normalization

The measured kernel uses frequency `2^j`, while the unchanged wide band is
indexed by `dyadicScale j = 2^j/2`. We keep the original `cutoffCount` and
account for the factor two explicitly. The other change from the generic
comparison is a bounded patch-weighted multiplier, whose bound need not be
one. The consumer is the actual retained application of
`app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
open NormalComparison AmplitudeBound RawInputPartition ColoredNormalComparison

private theorem normal_smul_symbol {n r : ℕ} {G : UniformNormalGeometry n r}
    {C : ℕ → ℝ} (F : UniformNormalData G C) (K ε : ℝ)
    (g : Lp ℂ ∞ (volume.restrict G.D)) (a : ℂ) :
    F.uniformOscillatoryNormalOperator K (a • g) ε =
      a • F.uniformOscillatoryNormalOperator K g ε := by
  simp only [UniformNormalData.uniformOscillatoryNormalOperator, multiplicationOperator,
    map_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

private theorem exists_bounded_multiplier_comparison {n r : ℕ}
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) {P L : ℝ}
    (hP : 0 ≤ P) (hL : 0 ≤ L) :
    ∃ D > 0, ∀ F : UniformNormalData G C, ∀ K > 0,
      ∀ (m : Euclidean n → ℝ), ContDiffOn ℝ ∞ m G.D →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
      (∀ u ∈ G.D, 0 ≤ m u ∧ m u ≤ P) →
      (∀ u ∈ G.D, ‖fderiv ℝ m u‖ ≤ L / h) →
      ∀ g : Lp ℂ ∞ (volume.restrict G.D),
        g =ᵐ[volume.restrict G.D] (fun u ↦ (m u : ℂ)) →
      ∀ ε ∈ Icc 0 G.ε₀,
        ‖F.uniformOscillatoryNormalOperator K g ε -
          F.uniformOscillatoryNormalOperator K g 0‖ ≤ D * ε / h := by
  obtain ⟨B, hB, hcomp⟩ := G.exists_uniformOscillatoryNormalOperator_comparison C
  let S := P + 1
  have hS : 0 < S := by dsimp [S]; linarith
  have hS₁ : 1 ≤ S := by dsimp [S]; linarith
  have hSi : S⁻¹ ≤ 1 := (inv_le_one₀ hS).mpr hS₁
  refine ⟨S * (B * (1 + (n : ℝ) * L)), by positivity, ?_⟩
  intro F K hK m hm h hh hh₁ hrange hderiv g hg ε hε
  let m' := fun u ↦ S⁻¹ * m u
  let g' : Lp ℂ ∞ (volume.restrict G.D) := (S⁻¹ : ℂ) • g
  have hg' : g' =ᵐ[volume.restrict G.D] fun u ↦ (m' u : ℂ) := by
    filter_upwards [Lp.coeFn_smul (S⁻¹ : ℂ) g, hg] with u hu hgu
    simpa only [g', m', Pi.smul_apply, hgu, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_inv] using hu
  have hd' (u) (hu : u ∈ G.D) : ‖fderiv ℝ m' u‖ ≤ L / h := by
    rw [show m' = fun u ↦ S⁻¹ * m u from rfl,
      fderiv_const_mul ((hm.differentiableOn (by simp)).differentiableAt
        (G.isOpen_D.mem_nhds hu)) S⁻¹,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hS.le)]
    exact (mul_le_mul_of_nonneg_right hSi (norm_nonneg _)).trans
      (by simpa only [one_mul] using hderiv u hu)
  have hb := hcomp F K hK m' (contDiffOn_const.mul hm) h L hh hh₁ hL
    (fun u hu ↦ ⟨mul_nonneg (inv_nonneg.mpr hS.le) (hrange u hu).1,
      (mul_le_mul_of_nonneg_left ((hrange u hu).2.trans (by dsimp [S]; linarith))
        (inv_nonneg.mpr hS.le)).trans_eq (inv_mul_cancel₀ hS.ne')⟩)
    hd' g' hg' ε hε
  have he (t : ℝ) : F.uniformOscillatoryNormalOperator K g t =
      (S : ℂ) • F.uniformOscillatoryNormalOperator K g' t := by
    change _ = (S : ℂ) • F.uniformOscillatoryNormalOperator K ((S⁻¹ : ℂ) • g) t
    rw [normal_smul_symbol, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hS.ne', Complex.ofReal_one, one_smul]
  rw [he ε, he 0, ← smul_sub (S : ℂ)
    (F.uniformOscillatoryNormalOperator K g' ε) (F.uniformOscillatoryNormalOperator K g' 0),
    norm_smul, Complex.norm_real, Real.norm_of_nonneg hS.le]
  exact (mul_le_mul_of_nonneg_left hb hS.le).trans_eq (by ring)

/-- Retained normalization and the original band label differ by exactly two;
the band itself is unchanged (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem powTwo_eq_twice_dyadicScale (j : ℕ) :
    (2 : ℝ) ^ j = 2 * dyadicScale j := by
  simp only [dyadicScale]
  ring

/-- Every grouped prefix has total retained normalization at most four times
the original fixed ceiling. There is no logarithmic loss and no reindexing of
the half-scale band (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_range_powTwo_le_ceiling {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {J : ℕ} (hJ : J ≤ cutoffCount Λ) :
    ∑ j ∈ Finset.range J, (2 : ℝ) ^ j ≤ 4 * Λ := by
  simp_rw [powTwo_eq_twice_dyadicScale]
  rw [← Finset.mul_sum]
  linarith [sum_range_dyadicScale_le_ceiling hΛ hJ]

/-- The actual retained homotopy parameter is `τ * 2^j`. Its buffer condition
has the explicit fixed factor two, and uses the unchanged band ceiling
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem radial_powTwo_parameter_mem {n r : ℕ} {G : UniformNormalGeometry n r}
    {R Rmin lam Λ : ℝ} (hRmin : 0 < Rmin) (hR : Rmin ≤ R)
    (hlam : 0 < lam) (hΛ : 1 ≤ Λ) (hbuffer : 2 * Λ / (Rmin * lam) ≤ G.ε₀)
    {j : ℕ} (hj : j < cutoffCount Λ) :
    (R * lam)⁻¹ * (2 : ℝ) ^ j ∈ Icc 0 G.ε₀ := by
  have hRpos : 0 < R := hRmin.trans_le hR
  have hinv : (R * lam)⁻¹ ≤ (Rmin * lam)⁻¹ :=
    inv_anti₀ (mul_pos hRmin hlam) (mul_le_mul_of_nonneg_right hR hlam.le)
  have hscale : (2 : ℝ) ^ j ≤ 2 * Λ := by
    rw [powTwo_eq_twice_dyadicScale]
    exact mul_le_mul_of_nonneg_left ((lt_cutoffCount_iff hΛ j).mp hj) (by norm_num)
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (Rmin * lam)⁻¹ * (2 * Λ) :=
      mul_le_mul hinv hscale (by positivity) (by positivity)
    _ = 2 * Λ / (Rmin * lam) := by ring
    _ ≤ G.ε₀ := hbuffer

/-- Apply the existing input-only normal comparison at the actual `2^j`
normalization with bounded patch-weighted multipliers. Constants precede the
normal data, radial labels, frequencies and every prefix of the original
ceiling. The zero endpoint is still written with its colored multipliers;
`sum_patch_mul_coloredBlockMask` supplies their exact uncolored sum
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_bounded_powTwo_prefix_homotopy_bound {n r : ℕ}
    {Color : Type*} [Fintype Color] (G : UniformNormalGeometry n r) (C : ℕ → ℝ)
    {Rmin P L : ℝ} (hRmin : 0 < Rmin) (hP : 0 ≤ P) (hL : 0 ≤ L) :
    ∃ A > 0, ∀ (F : Color → ℕ → UniformNormalData G C)
      (R : Color → ℝ), (∀ c, Rmin ≤ R c) →
      ∀ (m : Color → Euclidean n → ℝ), (∀ c, ContDiffOn ℝ ∞ (m c) G.D) →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
      (∀ c u, u ∈ G.D → 0 ≤ m c u ∧ m c u ≤ P) →
      (∀ c u, u ∈ G.D → ‖fderiv ℝ (m c) u‖ ≤ L / h) →
      ∀ g : Color → Lp ℂ ∞ (volume.restrict G.D),
      (∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦ (m c u : ℂ)) →
      ∀ lam Λ : ℝ, 0 < lam → 1 ≤ Λ → 2 * Λ / (Rmin * lam) ≤ G.ε₀ →
      ∀ J ≤ cutoffCount Λ,
        ‖(∑ c, ∑ j ∈ Finset.range J,
            (F c j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c)
              ((R c * lam)⁻¹ * (2 : ℝ) ^ j)) -
          (∑ c, ∑ j ∈ Finset.range J,
            (F c j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c) 0)‖ ≤
          A * lam⁻¹ * Λ / h := by
  obtain ⟨D, hD, hcomp⟩ := exists_bounded_multiplier_comparison G C hP hL
  let A := 4 * ((Fintype.card Color : ℝ) + 1) * D / Rmin
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro F R hR m hm h hh hh₁ hmask hderiv g hg lam Λ hlam hΛ hbuffer J hJ
  have hband (c : Color) (j : ℕ) (hj : j ∈ Finset.range J) :
      ‖(F c j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c)
          ((R c * lam)⁻¹ * (2 : ℝ) ^ j) -
        (F c j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c) 0‖ ≤
        D * (Rmin * lam)⁻¹ * (2 : ℝ) ^ j / h := by
    have hε := radial_powTwo_parameter_mem hRmin (hR c) hlam hΛ hbuffer
      ((Finset.mem_range.mp hj).trans_le hJ)
    have hinv : (R c * lam)⁻¹ ≤ (Rmin * lam)⁻¹ :=
      inv_anti₀ (mul_pos hRmin hlam) (mul_le_mul_of_nonneg_right (hR c) hlam.le)
    calc
      _ ≤ D * ((R c * lam)⁻¹ * (2 : ℝ) ^ j) / h :=
        hcomp (F c j) _ (by positivity) (m c) (hm c) h hh hh₁
          (hmask c) (hderiv c) (g c) (hg c) _ hε
      _ ≤ D * ((Rmin * lam)⁻¹ * (2 : ℝ) ^ j) / h := by gcongr
      _ = _ := by ring
  have hsum (c : Color) :
      (∑ j ∈ Finset.range J,
        ‖(F c j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c)
            ((R c * lam)⁻¹ * (2 : ℝ) ^ j) -
          (F c j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c) 0‖) ≤
        4 * D * (Rmin * lam)⁻¹ * Λ / h := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, D * (Rmin * lam)⁻¹ * (2 : ℝ) ^ j / h :=
        Finset.sum_le_sum (hband c)
      _ = D * (Rmin * lam)⁻¹ * (∑ j ∈ Finset.range J, (2 : ℝ) ^ j) / h := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
      _ ≤ D * (Rmin * lam)⁻¹ * (4 * Λ) / h := by
        gcongr
        exact sum_range_powTwo_le_ceiling hΛ hJ
      _ = _ := by ring
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, ‖(∑ j ∈ Finset.range J,
        (F c j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c)
          ((R c * lam)⁻¹ * (2 : ℝ) ^ j)) -
        ∑ j ∈ Finset.range J,
          (F c j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c) 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : Color, 4 * D * (Rmin * lam)⁻¹ * Λ / h := by
      apply Finset.sum_le_sum
      intro c _
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (hsum c)
    _ = (Fintype.card Color : ℝ) * (4 * D * (Rmin * lam)⁻¹ * Λ / h) := by simp
    _ ≤ ((Fintype.card Color : ℝ) + 1) * (4 * D * (Rmin * lam)⁻¹ * Λ / h) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = A * lam⁻¹ * Λ / h := by
      dsimp [A]
      rw [mul_inv_rev]
      ring

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
