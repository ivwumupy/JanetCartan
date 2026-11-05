module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PhysicalCompletion
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricProfiles

/-!
# Uniform normal-completion bounds for the actual finite history

The normal multiplier in `main:eq:mean-coarse-size` and
`main:eq:mean-fine-size` is the literal canonical completion of the supplied
history. Its coefficient estimates are instantiated from the existing
geometric-history producer. Leibniz keeps the derivative orders on the tensor
datum separate, so the bound preserves either the coarse or fine input scale.

Constants and the history threshold precede every tensor datum and every
finite history. This supplies the normal-multiplier part of the mean field
estimates, not the preparation, sampled residual or fine tensor bounds.
-/

@[expose] public noncomputable section

open Set Finset
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open scoped JanetCartan.NormalRankStability

namespace JanetCartan.CurrentMean

open AmbientResponse CurrentCoefficientProfiles

variable {n : ℕ}

/-- Actual-history normal-completion bound for the two field profiles in
`main:prop:mean`. The constants come from the geometric coefficient producer;
no normal inverse estimate is an input. The Leibniz sum retains the original
datum and its derivative orders, and introduces no accuracy or update-count
factor. -/
theorem exists_admissible_history_meanNormalCorrection_bounds
    (G : FlatReference n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < G.domain.chartRadius) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ T : MetricField n, ContDiffOn ℝ ∞ T (Metric.ball 0 R) → ∀ s : ℕ,
      cNorm (Metric.closedBall 0 r) s (meanNormalCorrection (finiteHistoryMap G.map u) T) ≤
        ∑ q ∈ range (s + 1), ∑ i ∈ range (q + 1),
          (q.choose i : ℝ) * C i * currentCoefficientScale R₀ j ^ i *
            cNorm (Metric.closedBall 0 r) (q - i) T := by
  obtain ⟨S, hS, C₀, _, κ, _, A, C, _, hC, hgeom⟩ :=
    exists_admissible_history_geometric_profiles G hr hrR hR hStar
      (show 2 + 0 ≤ rStar by omega) horder
  refine ⟨S, hS, C, hC, ?_⟩
  intro R₀ hR₀ j u ell hu T hT s
  let F := finiteHistoryMap G.map u
  let K := Metric.closedBall (0 : Euclidean n) r
  let U := Metric.ball (0 : Euclidean n) R
  let L := fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap
  have hF : ContDiff ℝ ∞ F := hu.contDiff_finiteHistoryMap G.contDiff
  obtain ⟨hi, hrank, _, _, _, _, hcoeff⟩ := hgeom R₀ hR₀ j u ell hu
  have hKU : K ⊆ U := Metric.closedBall_subset_ball hrR
  have hK : IsCompact K := isCompact_closedBall _ _
  have hL : ContDiffOn ℝ ∞ L U := by
    apply contDiffOn_clm_apply.mpr
    intro H
    exact contDiffOn_canonicalNormalCompletion Metric.isOpen_ball hF.contDiffOn
      contDiffOn_const hi hrank
  have hLbound (i : ℕ) : cNorm K i L ≤ C i * currentCoefficientScale R₀ j ^ i := by
    have hnonneg : 0 ≤
        (cNorm K i (inducedMetric F) + cNorm K i (fun x ↦ (inducedMetric F x)⁻¹)) +
          (∑ a, ∑ b, cNorm K i (fun x ↦ secondFundamentalForm F x a b)) +
          (∑ a, cNorm K i (fun x ↦ ProjectedStressFrame.projectedStress F x a)) := by
      exact add_nonneg (add_nonneg
        (add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _))
        (sum_nonneg fun a _ ↦ sum_nonneg fun b _ ↦ cNorm_nonneg _ _ _))
        (sum_nonneg fun a _ ↦ cNorm_nonneg _ _ _)
    have hb := hcoeff i
    simp only [Nat.sub_zero] at hb
    exact (le_add_of_nonneg_left hnonneg).trans hb
  have hLjet (i : ℕ) (x : Euclidean n) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ i L x‖ ≤ C i * currentCoefficientScale R₀ j ^ i :=
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hL.contDiffAt (Metric.isOpen_ball.mem_nhds (hKU hy))).of_le (by simp))
      hx le_rfl).trans (hLbound i)
  have hTjet (i : ℕ) (x : Euclidean n) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ i T x‖ ≤ cNorm K i T :=
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hT.contDiffAt (Metric.isOpen_ball.mem_nhds (hKU hy))).of_le (by simp))
      hx le_rfl
  have hscale : 0 ≤ currentCoefficientScale R₀ j :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans
      (one_le_currentCoefficientScale (by linarith [hS.trans hR₀]) j)
  let B := ContinuousLinearMap.id ℝ
    (MetricTensor n →L[ℝ] Euclidean (embeddingDimension n))
  have hprod : ContDiffOn ℝ ∞ (fun x ↦ L x (T x)) U := hL.clm_apply hT
  apply cNorm_le_sum_of_bounds
    (fun q _ ↦ sum_nonneg fun i _ ↦ mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (pow_nonneg hscale i))
      (cNorm_nonneg _ _ _))
  intro q _ x hx
  have hderiv := B.norm_iteratedFDerivWithin_le_of_bilinear hL hT
    Metric.isOpen_ball.uniqueDiffOn (hKU hx) (n := q) (by simp)
  simp only [U, iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball (hKU hx)] at hderiv
  have hcorr : ‖iteratedFDeriv ℝ q (meanNormalCorrection F T) x‖ =
      (1 / 2 : ℝ) * ‖iteratedFDeriv ℝ q (fun y ↦ L y (T y)) x‖ := by
    change ‖iteratedFDeriv ℝ q ((-(1 / 2 : ℝ)) • (fun y ↦ L y (T y))) x‖ = _
    rw [iteratedFDeriv_const_smul_apply
      ((hprod.contDiffAt (Metric.isOpen_ball.mem_nhds (hKU hx))).of_le (by simp)), norm_smul]
    norm_num
  rw [hcorr]
  calc
    _ ≤ ‖iteratedFDeriv ℝ q (fun y ↦ L y (T y)) x‖ := by
      nlinarith [norm_nonneg (iteratedFDeriv ℝ q (fun y ↦ L y (T y)) x)]
    _ ≤ ‖B‖ * ∑ i ∈ range (q + 1), (q.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i L x‖ * ‖iteratedFDeriv ℝ (q - i) T x‖ := hderiv
    _ ≤ 1 * ∑ i ∈ range (q + 1), (q.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i L x‖ * ‖iteratedFDeriv ℝ (q - i) T x‖ := by
      apply mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_id_le)
      positivity
    _ ≤ _ := by
      rw [one_mul]
      apply sum_le_sum
      intro i _
      calc
        _ ≤ (q.choose i : ℝ) * (C i * currentCoefficientScale R₀ j ^ i) *
            cNorm K (q - i) T := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hLjet i x hx) (Nat.cast_nonneg _))
            (hTjet (q - i) x hx) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC i) (pow_nonneg hscale i)))
        _ = _ := by ring

end JanetCartan.CurrentMean
