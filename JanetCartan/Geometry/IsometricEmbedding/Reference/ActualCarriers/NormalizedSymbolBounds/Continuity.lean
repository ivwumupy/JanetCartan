module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbolBounds.Basic
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.Composition.Continuity

/-!
# Finite-order comparison with a frozen frame

The `C³` and `C⁶` symbol neighborhoods in `app:lem:common-hamilton-phase`
follow from frame closeness at exactly the same order. The determinant and
inverse norm power are fixed smooth functions on a compact annular range.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.NormalizedSymbolBounds

private theorem norm_fst_pair_zero_jet_le {n : ℕ}
    {f : Euclidean n → Fin n → MetricTensor n} {r j : ℕ} (hf : ContDiff ℝ r f)
    (hj : j ≤ r) (z : Euclidean n × Euclidean n) :
    ‖iteratedFDeriv ℝ j (fun w : Euclidean n × Euclidean n ↦
      (f w.1, (0 : Euclidean n))) z‖ ≤ ‖iteratedFDeriv ℝ j f z.1‖ := by
  let L := ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)
  have hfst : ContDiff ℝ r (fun w : Euclidean n × Euclidean n ↦ f w.1) :=
    hf.comp contDiff_fst
  rw [iteratedFDeriv_prodMk hfst.contDiffAt contDiff_const.contDiffAt (by exact_mod_cast hj),
    ContinuousMultilinearMap.opNorm_prod]
  change max ‖iteratedFDeriv ℝ j (fun w : Euclidean n × Euclidean n ↦ f w.1) z‖
    ‖iteratedFDeriv ℝ j (0 : Euclidean n × Euclidean n → Euclidean n) z‖ ≤ _
  simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero, max_eq_left (norm_nonneg _)]
  change ‖iteratedFDeriv ℝ j (f ∘ L) z‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf z (by exact_mod_cast hj)]
  apply ((iteratedFDeriv ℝ j f (L z)).norm_compContinuousLinearMap_le (fun _ ↦ L)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hp : ‖L‖ ^ j ≤ (1 : ℝ) := by
    simpa using pow_le_pow_left₀ (norm_nonneg L)
      (ContinuousLinearMap.norm_fst_le ℝ (Euclidean n) (Euclidean n)) j
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)

private theorem cNorm_fst_pair_zero_le {n : ℕ}
    (a : Euclidean n × Euclidean n) (ρ : ℝ) {r : ℕ}
    {f : Euclidean n → Fin n → MetricTensor n} (hf : ContDiff ℝ r f) :
    cNorm (Metric.closedBall a ρ) r (fun w ↦ (f w.1, (0 : Euclidean n))) ≤
      (r + 1 : ℝ) * cNorm (Metric.closedBall a.1 ρ) r f := by
  apply (cNorm_le_sum_of_bounds (C := fun _ ↦ cNorm (Metric.closedBall a.1 ρ) r f)
    (fun _ _ ↦ cNorm_nonneg ..) ?_).trans_eq
  · simp
  intro j hj z hz
  apply (norm_fst_pair_zero_jet_le hf hj z).trans
  apply norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _) hf _ hj
  exact (le_max_left _ _).trans
    (show max (dist z.1 a.1) (dist z.2 a.2) ≤ ρ from hz)

/-- Fixed-order comparison with a frozen frame on a buffered joint covector
patch (`app:ch_seed:prop:seed-actual-menu`, Step 1). The threshold is chosen
before the current frame. Only `C^m` frame closeness is assumed, and no
higher derivative enters the comparison. -/
theorem exists_symbol_comparison_radius {n : ℕ}
    (a : Euclidean n × Euclidean n) (ρ : ℝ)
    (hzero : ∀ ξ ∈ Metric.closedBall a.2 ρ, ξ ≠ 0)
    (Q₀ : Fin n → MetricTensor n) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q : Euclidean n → Fin n → MetricTensor n,
      ContDiff ℝ m Q → cNorm (Metric.closedBall a.1 ρ) m (Q - fun _ ↦ Q₀) < δ →
      cNorm (Metric.closedBall a ρ) m
        (normalizedSymbol Q - normalizedSymbol (fun _ ↦ Q₀)) < ε := by
  let K := Metric.closedBall a ρ
  let L := Metric.closedBall (0 : Fin n → MetricTensor n) (‖Q₀‖ + 1) ×ˢ
    Metric.closedBall a.2 ρ
  let f := fun p : (Fin n → MetricTensor n) × Euclidean n ↦
    determinant p.1 p.2 * ‖p.2‖ ^ (1 - (n : ℤ))
  let g₀ := fun z : Euclidean n × Euclidean n ↦ (Q₀, z.2)
  have hf : ∀ y ∈ L, ContDiffAt ℝ m f y := fun y hy ↦
    (contDiffAt_determinant_norm_zpow (hzero y.2 hy.2)).of_le (by simp)
  have hg₀ : ContDiff ℝ m g₀ := contDiff_const.prodMk contDiff_snd
  have hξ : ∀ z ∈ K, z.2 ∈ Metric.closedBall a.2 ρ := fun z hz ↦
    (le_max_right _ _).trans (show max (dist z.1 a.1) (dist z.2 a.2) ≤ ρ from hz)
  have hrange₀ : Set.MapsTo g₀ K L := by
    intro z hz
    exact ⟨by simp [g₀, Metric.mem_closedBall, dist_zero_right], hξ z hz⟩
  obtain ⟨d, hd, hb⟩ := HamiltonPhase.CompositionContinuity.exists_cNorm_comp_sub_lt
    (isCompact_closedBall a ρ)
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)) hf
    (fun _ _ ↦ hg₀.contDiffAt) hrange₀ hε
  refine ⟨min 1 (d / (m + 1 : ℝ)), lt_min zero_lt_one (div_pos hd (by positivity)), ?_⟩
  intro Q hQ hsmall
  let g := fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2)
  have hg : ContDiff ℝ m g := (hQ.comp contDiff_fst).prodMk contDiff_snd
  have hdiff : ContDiff ℝ m (Q - fun _ ↦ Q₀) := hQ.sub contDiff_const
  have hrange : Set.MapsTo g K L := by
    intro z hz
    refine ⟨?_, hξ z hz⟩
    have hx : z.1 ∈ Metric.closedBall a.1 ρ := (le_max_left _ _).trans
      (show max (dist z.1 a.1) (dist z.2 a.2) ≤ ρ from hz)
    have hdif := norm_le_cNorm (isCompact_closedBall _ _) hdiff hx
    have h1 := hsmall.trans_le (min_le_left _ _)
    simp only [Pi.sub_apply] at hdif
    have hbQ := norm_add_le (Q z.1 - Q₀) Q₀
    simp only [sub_add_cancel] at hbQ
    change dist (Q z.1) 0 ≤ ‖Q₀‖ + 1
    rw [dist_zero_right]
    linarith
  have hinner : cNorm K m (g - g₀) < d := by
    have heq : g - g₀ = fun z : Euclidean n × Euclidean n ↦
        (Q z.1 - Q₀, (0 : Euclidean n)) := by
      funext z
      simp [g, g₀]
    rw [heq]
    apply (cNorm_fst_pair_zero_le a ρ hdiff).trans_lt
    have hs := hsmall.trans_le (min_le_right _ _)
    exact (lt_div_iff₀' (by positivity : (0 : ℝ) < m + 1)).mp hs
  have houter : cNorm L m (f - f) < d := by simpa using hd
  simpa only [f, g, g₀, Function.comp_def, Pi.sub_def, normalizedSymbol,
    determinantNormalization] using
    hb f g hf (fun _ _ ↦ hg.contDiffAt) hrange houter hinner

/-- Local smoothness on the construction chart suffices for finite-order
comparison (`app:lem:common-hamilton-phase`). The extension is constructed
internally and agrees on neighborhoods of the closed physical ball. -/
theorem exists_symbol_comparison_radius_contDiffOn {n : ℕ}
    (a : Euclidean n × Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (hzero : ∀ ξ ∈ Metric.closedBall a.2 ρ, ξ ≠ 0)
    (Q₀ : Fin n → MetricTensor n) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (U : Set (Euclidean n)), IsOpen U →
      Metric.closedBall a.1 ρ ⊆ U → ∀ Q : Euclidean n → Fin n → MetricTensor n,
      ContDiffOn ℝ ∞ Q U → cNorm (Metric.closedBall a.1 ρ) m (Q - fun _ ↦ Q₀) < δ →
      cNorm (Metric.closedBall a ρ) m
        (normalizedSymbol Q - normalizedSymbol (fun _ ↦ Q₀)) < ε := by
  obtain ⟨δ, hδ, hb⟩ := exists_symbol_comparison_radius a ρ hzero Q₀ m hε
  refine ⟨δ, hδ, ?_⟩
  intro U hU hball Q hQ hsmall
  obtain ⟨q, hq, _, _, heq⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall a.1 hρ hU hball hQ
  have hdiff : cNorm (Metric.closedBall a.1 ρ) m (q - fun _ ↦ Q₀) =
      cNorm (Metric.closedBall a.1 ρ) m (Q - fun _ ↦ Q₀) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro x hx
    filter_upwards [heq x hx] with y hy
    simp only [Pi.sub_apply, hy]
  have hs := hb q (hq.of_le (by simp)) (by rwa [hdiff])
  convert hs using 1
  symm
  apply GeometricProfile.cNorm_eq_of_eventuallyEq
  intro z hz
  have hx : z.1 ∈ Metric.closedBall a.1 ρ := (le_max_left _ _).trans
    (show max (dist z.1 a.1) (dist z.2 a.2) ≤ ρ from hz)
  filter_upwards [(heq z.1 hx).comp_tendsto continuous_fst.continuousAt] with w hw
  change q w.1 = Q w.1 at hw
  simp only [Pi.sub_apply, normalizedSymbol, hw]

/-- One primitive `C⁶` frame neighborhood gives both the `C³` neighborhood
for common chart construction and the `C⁶` comparison used for `C⁵` phases
(`app:ch_seed:prop:seed-actual-menu`, Step 1). The frozen symbol is literally
the existing cube determinant times the inverse radial power. -/
theorem exists_cube_symbol_C3_C6_comparison_radius {n : ℕ}
    (a : Euclidean n × Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (hzero : ∀ ξ ∈ Metric.closedBall a.2 ρ, ξ ≠ 0)
    {ε₃ ε₆ : ℝ} (hε₃ : 0 < ε₃) (hε₆ : 0 < ε₆) :
    ∃ δ > (0 : ℝ), ∀ (U : Set (Euclidean n)), IsOpen U →
      Metric.closedBall a.1 ρ ⊆ U → ∀ Q : Euclidean n → Fin n → MetricTensor n,
      ContDiffOn ℝ ∞ Q U → cNorm (Metric.closedBall a.1 ρ) 6 (Q - fun _ ↦ cubeStress n) < δ →
      let e := normalizedSymbol Q - normalizedSymbol (fun _ ↦ cubeStress n)
      cNorm (Metric.closedBall a ρ) 3 e < ε₃ ∧
        cNorm (Metric.closedBall a ρ) 6 e < ε₆ := by
  obtain ⟨d₃, hd₃, hb₃⟩ := exists_symbol_comparison_radius_contDiffOn a hρ hzero
    (cubeStress n) 3 hε₃
  obtain ⟨d₆, hd₆, hb₆⟩ := exists_symbol_comparison_radius_contDiffOn a hρ hzero
    (cubeStress n) 6 hε₆
  refine ⟨min d₃ d₆, lt_min hd₃ hd₆, ?_⟩
  intro U hU hball Q hQ hs
  constructor
  · exact hb₃ U hU hball Q hQ
      ((cNorm_mono_order (s := Metric.closedBall a.1 ρ) (f := Q - fun _ ↦ cubeStress n)
        (by decide : 3 ≤ 6)).trans_lt (hs.trans_le (min_le_left _ _)))
  · exact hb₆ U hU hball Q hQ
      (hs.trans_le (min_le_right _ _))

end JanetCartan.ActualCarriers.NormalizedSymbolBounds
