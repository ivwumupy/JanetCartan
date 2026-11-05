module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.StressFrame.Smoothness
public import JanetCartan.Geometry.IsometricEmbedding.Normal.StressFrame.Stability

/-!
# A neighborhood of the projected cube-stress frame

The algebraic stability and uniform Gram gap in
`app:ch_background:defn:bg-geometry` and `app:ch_seed:setup:seed-current`.
The neighborhood is measured by the sum of the Frobenius distances from the
frozen cube stresses. No independence of the projected family is assumed.

The operator neighborhood is obtained from continuity of the actual projector.
Projected independence and the uniform Gram gap are proved, not assumed.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff Topology

namespace JanetCartan.StressFrame

/-- Uniform independence and Gram gap near the frozen cube stresses, as used in
`app:ch_background:defn:bg-geometry`. Both constants are fixed before choosing
the perturbed family. -/
theorem exists_cubeStress_frame_neighborhood {n : ℕ} (hn : 5 ≤ n) :
    ∃ ε > 0, ∃ γ > 0, ∀ Q : Fin n → SymmetricTensor n,
      (∑ i, ‖Q i - cubeSymmetricStress n i‖) < ε →
      LinearIndependent ℝ Q ∧
        ∀ c : EuclideanSpace ℝ (Fin n),
          γ * (∑ i, (c i) ^ 2) ≤
            ∑ i, ∑ j, c i * c j * tensorPairing (Q i).val (Q j).val := by
  obtain ⟨ε, hε, a, ha, h⟩ :=
    exists_uniform_synthesis_lower_bound (cubeSymmetricStress_linearIndependent hn)
  refine ⟨ε, hε, a ^ 2, sq_pos_of_pos ha, ?_⟩
  intro Q hQ
  exact ⟨linearIndependent_of_synthesis_lower_bound ha (h Q hQ),
    gramGap_of_synthesis_lower_bound ha.le (h Q hQ)⟩

/-- Projecting the cube stresses gives a basis of every surjective normal
map's kernel of the correct dimension in the fixed frame neighborhood, with a
uniform Frobenius Gram gap (`app:ch_background:defn:bg-geometry`). -/
theorem exists_projectedCubeStress_basis_neighborhood {n : ℕ} (hn : 5 ≤ n)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ (SymmetricTensor n) = n + Module.finrank ℝ F) :
    ∃ ε > 0, ∃ γ > 0, ∀ B : SymmetricTensor n →ₗ[ℝ] F,
      Function.Surjective B →
      (∑ i, ‖projectedCubeStress B i - cubeSymmetricStress n i‖) < ε →
      (∃ b : Module.Basis (Fin n) ℝ B.ker,
        ∀ i, (b i : SymmetricTensor n) = projectedCubeStress B i) ∧
      ∀ c : EuclideanSpace ℝ (Fin n),
        γ * (∑ i, (c i) ^ 2) ≤ ∑ i, ∑ j, c i * c j *
          tensorPairing (projectedCubeStress B i).val (projectedCubeStress B j).val := by
  obtain ⟨ε, hε, γ, hγ, h⟩ := exists_cubeStress_frame_neighborhood hn
  refine ⟨ε, hε, γ, hγ, ?_⟩
  intro B hB hclose
  obtain ⟨hind, hgap⟩ := h (projectedCubeStress B) hclose
  exact ⟨⟨projectedCubeStressBasis B hB hdim hind,
    projectedCubeStressBasis_apply B hB hdim hind⟩, hgap⟩

/-- The basis and uniform Gram-gap conclusion of
`app:ch_background:defn:bg-geometry`, expressed solely in terms of the stress
subspace so it is invariant under identification of normal output spaces. -/
def HasCubeStressFrame {n : ℕ} (K : Submodule ℝ (SymmetricTensor n)) (γ : ℝ) : Prop :=
  (∃ b : Module.Basis (Fin n) ℝ K,
    ∀ i, (b i : SymmetricTensor n) = K.starProjection (cubeSymmetricStress n i)) ∧
  ∀ c : EuclideanSpace ℝ (Fin n), γ * (∑ i, (c i) ^ 2) ≤
    ∑ i, ∑ j, c i * c j * tensorPairing
      (K.starProjection (cubeSymmetricStress n i)).val
      (K.starProjection (cubeSymmetricStress n j)).val

/-- `app:ch_background:defn:bg-geometry`: a full-rank reference whose kernel
is the frozen cube-stress span has an operator-norm neighborhood with one
positive Gram gap and the specified projected basis at every operator. -/
theorem exists_operator_cubeStressFrame_neighborhood {n : ℕ} (hn : 5 ≤ n)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (B₀ : SymmetricTensor n →L[ℝ] F)
    (hsurj : Function.Surjective B₀)
    (hker : B₀.ker = Submodule.span ℝ (Set.range (cubeSymmetricStress n))) :
    ∃ δ > 0, ∃ γ > 0, ∀ B : SymmetricTensor n →L[ℝ] F,
      ‖B - B₀‖ < δ → Function.Surjective B ∧ HasCubeStressFrame B.ker γ := by
  have hdim : Module.finrank ℝ (SymmetricTensor n) = n + Module.finrank ℝ F := by
    have hr := B₀.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
      finrank_span_eq_card (cubeSymmetricStress_linearIndependent hn), Fintype.card_fin] at hr
    omega
  obtain ⟨ε, hε, γ, hγ, hframe⟩ := exists_projectedCubeStress_basis_neighborhood hn hdim
  have hfix (i : Fin n) : projectedCubeStress B₀.toLinearMap i =
      cubeSymmetricStress n i := by
    apply Submodule.starProjection_eq_self_iff.mpr
    rw [hker]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hc : ContinuousAt (fun B : SymmetricTensor n →L[ℝ] F ↦
      ∑ i, ‖projectedCubeStress B.toLinearMap i - cubeSymmetricStress n i‖) B₀ := by
    exact tendsto_finsetSum _ fun i _ ↦
      ((continuousAt_projectedCubeStress B₀ hsurj i).sub continuousAt_const).norm
  have he : ∀ᶠ B in 𝓝 B₀,
      (∑ i, ‖projectedCubeStress B.toLinearMap i - cubeSymmetricStress n i‖) < ε :=
    hc.eventually (gt_mem_nhds (by simpa only [hfix, sub_self, norm_zero,
      Finset.sum_const_zero] using hε))
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp
    (Filter.Eventually.and (NormalInverse.isOpen_surjective.mem_nhds hsurj) he)
  refine ⟨δ, hδ, γ, hγ, fun B hB ↦ ?_⟩
  have hb := hδball (show dist B B₀ < δ by rwa [_root_.dist_eq_norm B B₀])
  exact ⟨hb.1, hframe B.toLinearMap hb.1 hb.2⟩

/-- `app:ch_seed:prop:seed-gram` and `app:ch_background:defn:bg-geometry`:
all reference hypotheses of the operator neighborhood are discharged for the
concrete cube normal map. -/
theorem exists_cubeNormal_operator_neighborhood {n : ℕ} (hn : 5 ≤ n) :
    ∃ δ > 0, ∃ γ > 0, ∀ B : SymmetricTensor n →L[ℝ]
      EuclideanSpace ℝ (CoordinatePair n),
      ‖B - (cubeNormalLinearMapOnSymmetric n).toContinuousLinearMap‖ < δ →
      Function.Surjective B ∧ HasCubeStressFrame B.ker γ :=
  exists_operator_cubeStressFrame_neighborhood hn _
    (cubeNormalLinearMapOnSymmetric_surjective hn) (cubeNormalLinearMapOnSymmetric_ker hn)

end JanetCartan.StressFrame
