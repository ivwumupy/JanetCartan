module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.PrincipalGap

/-!
# Full-modulation principal normal gap

The actual full coefficient constructor supplies the phase and null-column
gaps, and positive transport supplies the scalar gap. This local geometric
adapter derives the projected-frame basis and the normal-pairing operator
bound from primitive data, then applies the existing principal-normal theorem.
It is consumed by `exists_actual_positive_amplitude`
(`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.LeadingWave.FullModulation
open ActualCarriers ProjectedStressFrame AmbientResponse

/-- Primitive projected-frame closeness and a fixed map budget give the
principal-normal lower bound for every full characteristic covector and null
amplitude with the stated positive gaps (`app:ch_waves:thm:leading`). -/
theorem exists_normal_gap_threshold {n : ℕ} (hn : 5 ≤ n)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (M : ℝ) {cξ cb : ℝ} (hcξ : 0 < cξ) (hcb : 0 < cb) :
    ∃ δ cν : ℝ, 0 < δ ∧ 0 < cν ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (_hF : ContDiffOn ℝ ∞ F U) (_hi : IsImmersionOn F U)
        (_hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ M →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∀ x ∈ K, ∀ ξ b : Euclidean n,
          pencil (projectedStress F x) ξ *ᵥ (fun j ↦ b j) = 0 →
          cξ ≤ ‖ξ‖ → cb ≤ ‖b‖ →
          cν ≤ ‖principalNormal (canonicalNormalCompletion F x) ξ b‖ := by
  obtain ⟨ε, hε, γ, _hγ, hbasis⟩ := exists_projectedStress_basis_neighborhood hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let C : ℝ := 1 + 2 * n * |M|
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε / n, cξ * cb / (2 * C), div_pos hε hnpos,
    div_pos (mul_pos hcξ hcb) (mul_pos (by norm_num) hC), ?_⟩
  intro F hF hi hrank hFM hclose x hxK ξ b hnull hξ hb
  have hFx : ContDiffAt ℝ 2 F x := (hF.contDiffAt (hU.mem_nhds (hKU hxK))).of_le (by simp)
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hs : ∀ y ∈ K, ContDiffAt ℝ 6 (projectedStress F - fun _ ↦ cubeStress n) y :=
    fun y hy ↦ ((hframe.contDiffAt (hU.mem_nhds (hKU hy))).sub contDiffAt_const).of_le (by simp)
  have hop : ‖(normalMapLinear F x).adjoint.toContinuousLinearMap‖ ≤ C := by
    apply (normalMapLinear_adjoint_norm_le_cNorm_four hK
      (fun y hy ↦ hF.contDiffAt (hU.mem_nhds (hKU hy))) hxK).trans
    calc
      2 * n * cNorm K 4 F ≤ 2 * n * |M| :=
        mul_le_mul_of_nonneg_left (hFM.trans (le_abs_self M)) (by positivity)
      _ ≤ C := by dsimp [C]; linarith
  have hpoint : ‖projectedStress F x - cubeStress n‖ < ε / n := by
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hs hxK (Nat.zero_le 6)
    have he : ‖projectedStress F x - cubeStress n‖ ≤
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hb
    exact he.trans_lt (hclose.trans_le (le_refl _))
  have hsum : (∑ i, ‖projectedStress F x i - cubeStress n i‖) < ε := by
    calc
      _ < ∑ _ : Fin n, ε / n := by
        apply Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
        intro i _
        exact (norm_le_pi_norm (projectedStress F x - cubeStress n) i).trans_lt hpoint
      _ = ε := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hbas := (hbasis F x hFx (hi x (hKU hxK)) (hrank x (hKU hxK)) hsum).1
  exact (principalNormal_norm_lower_of_pencil_null hFx (hrank x (hKU hxK)) hbas hnull
    hcξ hcb hC hξ hb hop).2

end JanetCartan.LeadingWave.FullModulation
