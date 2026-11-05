module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Smoothness
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.InverseBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.JetGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.JetBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Tame
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Pencil

/-!
# The projected current stress frame

The geometric construction and basis property in `app:ch_seed:setup:seed-current`.
The frame is obtained from the actual ambient inverse formula, is smooth, and
is a basis of the symmetric stress kernel in a fixed low neighborhood of the
cube frame. The separate metric and normal gaps give the stipulated inverse
operator bounds. The second-jet coefficient agrees with this construction
and satisfies the linear tame bound with loss two. Its compact admissible
range is derived from the low hypotheses, and the estimate is local to the
open construction domain. The final theorem assembles smoothness, the
symmetric stress basis, the Gram gap, and the uniform bound at every order.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ProjectedStressFrame

/-- A fixed neighborhood of the cube frame gives an actual basis of the
symmetric stress kernel and a uniform Gram gap, in
`app:ch_seed:setup:seed-current`. The normal-space dimension is derived from
immersion and the Janet--Cartan ambient dimension. -/
theorem exists_projectedStress_basis_neighborhood {n : ℕ} (hn : 5 ≤ n) :
    ∃ ε > 0, ∃ γ > 0,
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (x : Euclidean n),
      ContDiffAt ℝ 2 F x → Function.Injective (fderiv ℝ F x) →
      Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean (embeddingDimension n))) →
      (∑ i, ‖projectedStress F x i - cubeStress n i‖) < ε →
      (∃ b : Module.Basis (Fin n) ℝ (symmetricNormalMap F x).ker,
        ∀ i, ((b i : SymmetricTensor n) : MetricTensor n) = projectedStress F x i) ∧
      ∀ c : Euclidean n,
        γ * (∑ i, (c i) ^ 2) ≤ ∑ i, ∑ j, c i * c j *
          tensorPairing (projectedStress F x i) (projectedStress F x j) := by
  obtain ⟨ε, hε, γ, hγ, hframe⟩ := StressFrame.exists_cubeStress_frame_neighborhood hn
  refine ⟨ε, hε, γ, hγ, ?_⟩
  intro F x hF himm hrank hclose
  have hclose' : (∑ i, ‖StressFrame.projectedCubeStress (symmetricNormalMap F x) i -
      cubeSymmetricStress n i‖) < ε := by
    simp only [← Submodule.norm_coe, Submodule.coe_sub, cubeSymmetricStress]
    simpa only [projectedStress_eq_projectedCubeStress hF hrank] using hclose
  obtain ⟨hind, hgap⟩ := hframe _ hclose'
  have hsurj := symmetricNormalMap_surjective hF hrank
  have hdim := finrank_symmetricTensor_eq_add_normalSpace himm
  refine ⟨⟨StressFrame.projectedCubeStressBasis _ hsurj hdim hind, ?_⟩, ?_⟩
  · intro i
    rw [StressFrame.projectedCubeStressBasis_apply]
    exact (projectedStress_eq_projectedCubeStress hF hrank i).symm
  · simpa only [projectedStress_eq_projectedCubeStress hF hrank] using hgap

/-- The `C⁶` neighborhood in `app:ch_seed:setup:seed-current` makes the actual
projected tensors a basis throughout any fixed compact working domain. The
constants are chosen before the immersion, domain and point. -/
theorem exists_projectedStress_basis_of_cNorm_closeness {n : ℕ} (hn : 5 ≤ n) :
    ∃ ε > 0, ∃ γ > 0,
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (s K : Set (Euclidean n)), IsOpen s → IsCompact K → K ⊆ s →
      ContDiffOn ℝ ∞ F s → IsImmersionOn F s → HasFullNormalRankOn F s →
      (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) < ε) →
      ∀ x ∈ K,
      (∃ b : Module.Basis (Fin n) ℝ (symmetricNormalMap F x).ker,
        ∀ i, ((b i : SymmetricTensor n) : MetricTensor n) = projectedStress F x i) ∧
      ∀ c : Euclidean n,
        γ * (∑ i, (c i) ^ 2) ≤ ∑ i, ∑ j, c i * c j *
          tensorPairing (projectedStress F x i) (projectedStress F x j) := by
  obtain ⟨δ, hδ, γ, hγ, hbasis⟩ := exists_projectedStress_basis_neighborhood hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨δ / n, div_pos hδ hnpos, γ, hγ, ?_⟩
  intro F s K hs hK hKs hF himm hrank hclose x hx
  apply hbasis F x (((hF x (hKs hx)).contDiffAt (hs.mem_nhds (hKs hx))).of_le (by simp))
    (himm x (hKs hx)) (hrank x (hKs hx))
  have hpoint (i : Fin n) : ‖projectedStress F x i - cubeStress n i‖ < δ / n := by
    have hQ := (contDiffOn_projectedStress hs hF himm hrank i).sub
      (contDiffOn_const (c := cubeStress n i))
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (r := 6) hK
      (fun y hy ↦ ((hQ y (hKs hy)).contDiffAt (hs.mem_nhds (hKs hy))).of_le (by simp))
      hx (Nat.zero_le 6)
    have hnorm : ‖projectedStress F x i - cubeStress n i‖ ≤
        cNorm K 6 (fun y ↦ projectedStress F y i - cubeStress n i) := by
      simpa only [norm_iteratedFDeriv_zero] using hb
    exact hnorm.trans_lt (hclose i)
  calc
    (∑ i, ‖projectedStress F x i - cubeStress n i‖) < ∑ _ : Fin n, δ / n :=
      Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
        (fun i _ ↦ hpoint i)
    _ = δ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- The operator `Pperp = I - dF g⁻¹ (dF)*` of
`app:ch_seed:setup:seed-current`, with the inverse taken on the fixed
Euclidean tangent space. -/
theorem normalProjection_eq_inverse_metric {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ F x)) :
    normalProjection F x = ContinuousLinearMap.id ℝ _ -
      (fderiv ℝ F x).comp ((Ring.inverse (metricOperator F x)).comp
        (fderiv ℝ F x).adjoint) := by
  have ht := jetTangent_stressJet hi
  ext w : 1
  rw [normalProjection_eq_sub_tangentProjection, ← ht]
  rfl

/-- The projected-current-frame conclusions of
`app:ch_seed:setup:seed-current` and `app:ch_seed:eq:seed-frame-tame`, assembled
from the original low hypotheses. On a fixed positive-radius closed ball the
stresses are smooth, form a basis of the symmetric stress kernel, have a
uniform Gram gap, and obey the stated maximum-over-indices tame bound.
The high norm may be measured on any larger compact construction domain.
All constants precede the immersion; in particular they require no high-norm
smallness. The metric and normal singular-value gaps are separate hypotheses. -/
theorem exists_projectedStress_frame_estimates {n : ℕ} (hn : 5 ≤ n)
    (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ ε > 0, ∃ γ > 0, ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (s Kconstruction : Set (Euclidean n)),
      IsOpen s → IsCompact Kconstruction → Metric.closedBall a ρ ⊆ Kconstruction →
      Kconstruction ⊆ s → ContDiffOn ℝ ∞ F s → IsImmersionOn F s →
      HasFullNormalRankOn F s → cNorm Kconstruction 4 F ≤ C₀ →
      (∀ x ∈ Kconstruction, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ Kconstruction, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      (∀ i, cNorm Kconstruction 6 (fun x ↦ projectedStress F x i - cubeStress n i) < ε) →
      (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) s ∧
        ∀ x ∈ s, projectedStress F x i ∈ stressSpace F x) ∧
      (∀ x ∈ Kconstruction,
        (∃ b : Module.Basis (Fin n) ℝ (symmetricNormalMap F x).ker,
          ∀ i, ((b i : SymmetricTensor n) : MetricTensor n) = projectedStress F x i) ∧
        ∀ c : Euclidean n,
          γ * (∑ i, (c i) ^ 2) ≤ ∑ i, ∑ j, c i * c j *
            tensorPairing (projectedStress F x i) (projectedStress F x j)) ∧
      ∀ r, (⨆ i : Fin n, cNorm (Metric.closedBall a ρ) r
        (fun x ↦ projectedStress F x i)) ≤ C r * (1 + cNorm Kconstruction (r + 2) F) := by
  obtain ⟨ε, hε, γ, hγ, hbasis⟩ := exists_projectedStress_basis_of_cNorm_closeness hn
  have htame := fun r ↦ exists_cNorm_projectedStress_le_tame
    (N := embeddingDimension n) a hρ C₀ hκmet hκ r
  choose C hC hbound using htame
  refine ⟨ε, hε, γ, hγ, C, hC, ?_⟩
  intro F s K hs hK hball hKs hF hi hrank hlow hmet hnormal hclose
  refine ⟨?_, hbasis F s K hs hK hKs hF hi hrank hclose, ?_⟩
  · intro i
    refine ⟨contDiffOn_projectedStress hs hF hi hrank i, ?_⟩
    intro x hx
    exact projectedStress_mem_stressSpace
      (((hF x hx).contDiffAt (hs.mem_nhds hx)).of_le (by simp)) (hrank x hx) i
  · intro r
    let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact ciSup_le (hbound r F s K hs hK hball hKs hF hi hlow hmet hnormal)

end JanetCartan.ProjectedStressFrame
