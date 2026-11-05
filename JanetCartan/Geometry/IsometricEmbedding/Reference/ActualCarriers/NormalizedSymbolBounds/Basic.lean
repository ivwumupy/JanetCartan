module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Finite jets of the normalized determinant symbol

The literal coefficient in Step 1 of `app:ch_seed:prop:seed-actual-menu` is
`determinant (Q x) ξ * ‖ξ‖ ^ (1 - n : ℤ)`. The results here concern this
formula, without assuming a symbol budget or a Hamilton flow. Compact covector
patches must avoid zero. Frame regularity and low frame bounds remain inputs
of the actual carrier construction.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.NormalizedSymbolBounds

/-- The actual determinant products and inverse radial powers are jointly
smooth off the zero covector, as required by `app:lem:common-hamilton-phase`.
No frame invertibility is needed. -/
theorem contDiffAt_determinant_norm_zpow {n : ℕ}
    {p : (Fin n → MetricTensor n) × Euclidean n} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : (Fin n → MetricTensor n) × Euclidean n ↦
      determinant q.1 q.2 * ‖q.2‖ ^ (1 - (n : ℤ))) p :=
  contDiff_determinant.contDiffAt.mul
    ((contDiffAt_determinantNormalization hp).comp p contDiffAt_snd)

/-- On a compact frame range and a compact annular patch, all coefficient
jets have a uniform finite bound (`app:ch_seed:prop:seed-actual-menu`, Step 1).
The bound is chosen before the frame and covector, including singular pencils. -/
theorem exists_bound_coefficient_jets {n : ℕ}
    {T : Set (Fin n → MetricTensor n)} (hT : IsCompact T)
    {A : Set (Euclidean n)} (hA : IsCompact A) (hA0 : ∀ ξ ∈ A, ξ ≠ 0) (r : ℕ) :
    ∃ C > (0 : ℝ), ∀ j ≤ r, ∀ Q ∈ T, ∀ ξ ∈ A,
      ‖iteratedFDeriv ℝ j
        (fun p : (Fin n → MetricTensor n) × Euclidean n ↦
          determinant p.1 p.2 * ‖p.2‖ ^ (1 - (n : ℤ))) (Q, ξ)‖ ≤ C := by
  let f := fun p : (Fin n → MetricTensor n) × Euclidean n ↦
    determinant p.1 p.2 * ‖p.2‖ ^ (1 - (n : ℤ))
  refine ⟨1 + cNorm (T ×ˢ A) r f, by positivity [cNorm_nonneg (T ×ˢ A) r f], ?_⟩
  intro j hj Q hQ ξ hξ
  exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (hT.prod hA)
    (fun p hp ↦ (contDiffAt_determinant_norm_zpow (hA0 p.2 hp.2)).of_le (by simp))
    (show (Q, ξ) ∈ T ×ˢ A from ⟨hQ, hξ⟩) hj).trans (by linarith)

private theorem fst_mem_ball {n : ℕ} {a : Euclidean n × Euclidean n} {ρ : ℝ}
    {z : Euclidean n × Euclidean n} (hz : z ∈ Metric.closedBall a ρ) :
    z.1 ∈ Metric.closedBall a.1 ρ := by
  exact (le_max_left _ _).trans (show max (dist z.1 a.1) (dist z.2 a.2) ≤ ρ from hz)

private theorem cNorm_frame_lift_le {n : ℕ} (a : Euclidean n × Euclidean n)
    (ρ : ℝ) (r : ℕ) {Q : Euclidean n → Fin n → MetricTensor n}
    (hQ : ContDiff ℝ ∞ Q) :
    cNorm (Metric.closedBall a ρ) r (fun z ↦ (Q z.1, z.2)) ≤
      (r + 1 : ℝ) * (cNorm (Metric.closedBall a.1 ρ) r Q +
        cNorm (Metric.closedBall a ρ) r (Prod.snd : Euclidean n × Euclidean n → Euclidean n)) := by
  let L := ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)
  have hb := cNorm_le_sum_of_bounds (s := Metric.closedBall a ρ) (r := r)
    (f := fun z ↦ (Q z.1, z.2))
    (C := fun _ ↦ cNorm (Metric.closedBall a.1 ρ) r Q +
      cNorm (Metric.closedBall a ρ) r (Prod.snd : Euclidean n × Euclidean n → Euclidean n))
    (fun _ _ ↦ add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..)) ?_
  · simpa [mul_add] using hb
  intro j hj z hz
  have hQfst : ContDiff ℝ ∞ (fun z : Euclidean n × Euclidean n ↦ Q z.1) :=
    hQ.comp contDiff_fst
  rw [iteratedFDeriv_prodMk hQfst.contDiffAt
    contDiff_snd.contDiffAt (by simp : (j : ℕ∞ω) ≤ ∞),
    ContinuousMultilinearMap.opNorm_prod]
  have hfst : ‖iteratedFDeriv ℝ j (fun z : Euclidean n × Euclidean n ↦ Q z.1) z‖ ≤
      cNorm (Metric.closedBall a.1 ρ) r Q := by
    change ‖iteratedFDeriv ℝ j (Q ∘ L) z‖ ≤ _
    rw [L.iteratedFDeriv_comp_right hQ z (by simp)]
    apply ((iteratedFDeriv ℝ j Q (L z)).norm_compContinuousLinearMap_le (fun _ ↦ L)).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j Q (L z)‖ * 1 :=
        mul_le_mul_of_nonneg_left (by
          simpa using (pow_le_pow_left₀ (norm_nonneg L)
            (ContinuousLinearMap.norm_fst_le ℝ (Euclidean n) (Euclidean n)) j)) (norm_nonneg _)
      _ ≤ _ := by
        rw [mul_one]
        exact norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
          (hQ.of_le (by simp)) (fst_mem_ball hz) hj
  have hsnd := norm_iteratedFDeriv_le_cNorm (isCompact_closedBall a ρ)
    (show ContDiff ℝ r (Prod.snd : Euclidean n × Euclidean n → Euclidean n) from contDiff_snd) hz hj
  exact max_le (hfst.trans (le_add_of_nonneg_right (cNorm_nonneg ..)))
    (hsnd.trans (le_add_of_nonneg_left (cNorm_nonneg ..)))

/-- On any fixed joint closed ball whose covectors avoid zero, a low bound on
frame values gives a one-high symbol estimate with **zero derivative loss**.
The constant is chosen before `Q` and its high norms. This is the symbol input
of `app:lem:common-hamilton-phase` in Step 1 of the actual-menu proof. -/
theorem exists_cNorm_symbol_le_frame {n : ℕ}
    (a : Euclidean n × Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (hzero : ∀ ξ ∈ Metric.closedBall a.2 ρ, ξ ≠ 0) (M : ℝ) (r : ℕ) :
    ∃ C > (0 : ℝ), ∀ Q : Euclidean n → Fin n → MetricTensor n,
      ContDiff ℝ ∞ Q → (∀ x ∈ Metric.closedBall a.1 ρ, ‖Q x‖ ≤ M) →
      cNorm (Metric.closedBall a ρ) r
        (normalizedSymbol Q) ≤
          C * (1 + cNorm (Metric.closedBall a.1 ρ) r Q) := by
  let T := Metric.closedBall (0 : Fin n → MetricTensor n) M ×ˢ Metric.closedBall a.2 ρ
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range
    a hρ (show IsCompact T from (isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
    (le_refl r) (fun p hp ↦
      (contDiffAt_determinant_norm_zpow (hzero p.2 hp.2)).of_le (by simp))
  let S := cNorm (Metric.closedBall a ρ) r
    (Prod.snd : Euclidean n × Euclidean n → Euclidean n)
  have hS : 0 ≤ S := cNorm_nonneg ..
  refine ⟨C * (1 + (r + 1 : ℝ) * (1 + S)), by positivity, ?_⟩
  intro Q hQ hM
  have hm : Set.MapsTo (fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2))
      (Metric.closedBall a ρ) T := by
    intro z hz
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hM z.1 (fst_mem_ball hz)
    · exact (le_max_right _ _).trans
        (show max (dist z.1 a.1) (dist z.2 a.2) ≤ ρ from hz)
  have hb := hbound _ ((hQ.comp contDiff_fst).prodMk contDiff_snd) hm
  have hl := cNorm_frame_lift_le a ρ r hQ
  have hq := cNorm_nonneg (Metric.closedBall a.1 ρ) r Q
  simp only [Function.comp_def] at hb
  apply hb.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hprod : 0 ≤ ((r + 1 : ℝ) * S) * cNorm (Metric.closedBall a.1 ρ) r Q :=
    mul_nonneg (mul_nonneg (by positivity) hS) hq
  change _ ≤ (1 + (r + 1 : ℝ) * (1 + S)) * _
  change _ ≤ (r + 1 : ℝ) * (cNorm (Metric.closedBall a.1 ρ) r Q + S) at hl
  nlinarith

/-- Local smooth frames suffice for the zero-loss symbol estimate; no global
extension is assumed (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem exists_cNorm_symbol_le_frame_contDiffOn {n : ℕ}
    (a : Euclidean n × Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (hzero : ∀ ξ ∈ Metric.closedBall a.2 ρ, ξ ≠ 0) (M : ℝ) (r : ℕ) :
    ∃ C > (0 : ℝ), ∀ (U : Set (Euclidean n)), IsOpen U →
      Metric.closedBall a.1 ρ ⊆ U → ∀ Q : Euclidean n → Fin n → MetricTensor n,
      ContDiffOn ℝ ∞ Q U → (∀ x ∈ Metric.closedBall a.1 ρ, ‖Q x‖ ≤ M) →
      cNorm (Metric.closedBall a ρ) r
        (normalizedSymbol Q) ≤
          C * (1 + cNorm (Metric.closedBall a.1 ρ) r Q) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_symbol_le_frame a hρ hzero M r
  refine ⟨C, hC, ?_⟩
  intro U hU hball Q hQ hM
  obtain ⟨q, hq, _, _, heq⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall a.1 hρ hU hball hQ
  have hm : ∀ x ∈ Metric.closedBall a.1 ρ, ‖q x‖ ≤ M := by
    intro x hx
    rw [(heq x hx).eq_of_nhds]
    exact hM x hx
  have hnorm := GeometricProfile.cNorm_eq_of_eventuallyEq heq r
  have hsymbol : cNorm (Metric.closedBall a ρ) r
      (normalizedSymbol q) =
      cNorm (Metric.closedBall a ρ) r
      (normalizedSymbol Q) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro z hz
    filter_upwards [(heq z.1 (fst_mem_ball hz)).comp_tendsto continuous_fst.continuousAt]
      with w hw
    change q w.1 = Q w.1 at hw
    simp only [normalizedSymbol, hw]
  simpa only [hnorm, hsymbol] using hb q hq hm

/-- The primitive frame loss two gives the exact `r+1` symbol budget used for
order `r` phases: only `r+3` immersion derivatives occur
(`app:ch_seed:eq:seed-frame-tame` and `app:lem:common-hamilton-phase`).
The frame estimate is the explicit input produced by the projected-stress
construction; a symbol or phase bound is not an assumption. -/
theorem exists_symbol_phase_input_of_frame_bound {n N : ℕ}
    (a : Euclidean n × Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (hzero : ∀ ξ ∈ Metric.closedBall a.2 ρ, ξ ≠ 0) (M : ℝ) (r : ℕ)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ C > (0 : ℝ), ∀ (U : Set (Euclidean n)), IsOpen U →
      Metric.closedBall a.1 ρ ⊆ U → ∀ (Q : Euclidean n → Fin n → MetricTensor n)
      (F : Euclidean n → Euclidean N) (K : Set (Euclidean n)),
      ContDiffOn ℝ ∞ Q U → (∀ x ∈ Metric.closedBall a.1 ρ, ‖Q x‖ ≤ M) →
      cNorm (Metric.closedBall a.1 ρ) (r + 1) Q ≤ D * (1 + cNorm K (r + 3) F) →
      cNorm (Metric.closedBall a ρ) (r + 1)
        (normalizedSymbol Q) ≤
          C * (1 + cNorm K (r + 3) F) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_symbol_le_frame_contDiffOn a hρ hzero M (r + 1)
  refine ⟨C * (1 + D), by positivity, ?_⟩
  intro U hU hball Q F K hQ hM hframe
  apply (hb U hU hball Q hQ hM).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC.le
  linarith [cNorm_nonneg K (r + 3) F]

end JanetCartan.ActualCarriers.NormalizedSymbolBounds
