module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.Reconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Pencil
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Geometry

/-!
# Principal normal pairing and transported density

Conditional pointwise deductions for `app:ch_waves:eq:arbitrary-b-amplitudes`
and `app:ch_waves:thm:leading` in `paper.tex`. The actual projected stresses
and symmetric normal map are those of `ProjectedStressFrame`; the completion
is `AmbientResponse.canonicalNormalCompletion`.

The published basis property and actual pencil-null relation imply orthogonality
to the symmetric stress kernel. The projection identity then proves the normal
pairing equation, which transfers explicit phase and amplitude gaps to the
principal normal. Immersion is used upstream to construct the basis; these
pointwise deductions only need that basis, `C²` regularity and full normal rank.

The consumers `jc-leading-wave` and `jc-normalized-background` must supply the
basis, null relation, quantitative gaps and operator bound. No phase or transport
existence is asserted here. The density identity uses the literal supplied
Euclidean footpoint formula `a x * r (Y x)` and makes no change of measure.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Matrix
namespace JanetCartan.LeadingWave
open ProjectedStressFrame AmbientResponse

/-- Contraction of `ξ ⊙ b` against a symmetric stress is the corresponding
row of the actual pencil applied to `b`. This is the algebraic step in
`app:ch_waves:thm:leading` consumed by
`symmetricProduct_mem_stressKernel_orthogonal_of_pencil_null`. -/
theorem tensorPairing_symmetricProduct_eq_pencil_mulVec {n : ℕ}
    (Q : Fin n → MetricTensor n) (hQ : ∀ i, (Q i).IsSymm)
    (ξ b : Euclidean n) (i : Fin n) :
    tensorPairing (Q i) (symmetricProduct ξ b) =
      (ActualCarriers.pencil Q ξ *ᵥ (fun j ↦ b j)) i := by
  have hs : (∑ j, ∑ k, Q i j k * ξ j * b k) =
      ∑ j, ∑ k, Q i j k * b j * ξ k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [(hQ i).apply k j]
    ring
  simp only [tensorPairing, symmetricProduct, ActualCarriers.pencil,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  simp only [← mul_div_assoc, mul_add, ← mul_assoc,
    ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hs]
  have he : (∑ j, ∑ k, Q i j k * ξ k * b j) =
      ∑ j, ∑ k, Q i j k * b j * ξ k := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  ring

/-- The actual pencil-null relation puts `ξ ⊙ b` in the orthogonal complement
of the symmetric stress kernel (`app:ch_waves:thm:leading`). The frame hypothesis
is exactly the basis output of `exists_projectedStress_basis_neighborhood`;
no orthogonality or pairing equation is assumed. -/
theorem symmetricProduct_mem_stressKernel_orthogonal_of_pencil_null {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n} {ξ b : Euclidean n}
    (hframe : ∃ e : Module.Basis (Fin n) ℝ (symmetricNormalMap F x).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = projectedStress F x i)
    (hnull : ActualCarriers.pencil (projectedStress F x) ξ *ᵥ (fun j ↦ b j) = 0) :
    (⟨symmetricProduct ξ b, symmetricProduct_isSymm ξ b⟩ : SymmetricTensor n) ∈
      (symmetricNormalMap F x).kerᗮ := by
  obtain ⟨e, he⟩ := hframe
  have hQ (i : Fin n) : (projectedStress F x i).IsSymm := by
    rw [← he i]
    exact (e i).val.property
  apply (Submodule.mem_orthogonal _ _).mpr
  intro H hH
  have hre : ∑ i, e.repr ⟨H, hH⟩ i • (e i : SymmetricTensor n) = H := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg Subtype.val (e.sum_repr ⟨H, hH⟩)
  rw [← hre, sum_inner]
  apply Finset.sum_eq_zero
  intro i _
  rw [real_inner_smul_left (e i : SymmetricTensor n)
    (⟨symmetricProduct ξ b, symmetricProduct_isSymm ξ b⟩ : SymmetricTensor n)]
  change _ * tensorPairing (e i).val.val (symmetricProduct ξ b) = 0
  rw [he, tensorPairing_symmetricProduct_eq_pencil_mulVec _ hQ, hnull]
  simp

/-- The actual completion recovers a symmetric tensor orthogonal to the stress
kernel (`app:ch_waves:eq:arbitrary-b-amplitudes`). This uses the geometric
projection identity equivalent to the adjoint normal-completion identity,
and supplies the pairing step for `principalNormal_pairing_of_pencil_null`. -/
theorem canonicalNormalCompletion_pairing_of_stressKernel_orthogonal {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (H : SymmetricTensor n) (hH : H ∈ (symmetricNormalMap F x).kerᗮ) :
    normalPairing F (fun _ ↦ canonicalNormalCompletion F x H.val) x = H.val := by
  have hp : (symmetricNormalMap F x).ker.starProjection H = 0 :=
    Submodule.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _)
      (by simpa using hH)
  have hz : stressProjection F x H.val = 0 := by
    rw [stressProjection_eq_symmetric_starProjection hF hrank, hp]
    rfl
  rw [stressProjection_eq_sub_completion hrank] at hz
  exact (sub_eq_zero.mp hz).symm

/-- The equation `B_F* ν_b = ξ ⊙ b` in `app:ch_waves:thm:leading`, derived
from the actual pencil-null relation and projected stress basis. The normal
amplitude is the canonical completion from
`app:ch_waves:eq:arbitrary-b-amplitudes`, not a supplied solution. -/
theorem principalNormal_pairing_of_pencil_null {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n} {ξ b : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (hframe : ∃ e : Module.Basis (Fin n) ℝ (symmetricNormalMap F x).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = projectedStress F x i)
    (hnull : ActualCarriers.pencil (projectedStress F x) ξ *ᵥ (fun j ↦ b j) = 0) :
    normalPairing F (fun _ ↦ principalNormal (canonicalNormalCompletion F x) ξ b) x =
      symmetricProduct ξ b :=
  canonicalNormalCompletion_pairing_of_stressKernel_orthogonal hF hrank
    ⟨_, symmetricProduct_isSymm ξ b⟩
    (symmetricProduct_mem_stressKernel_orthogonal_of_pencil_null hframe hnull)

/-- Quantitative positive principal-normal bound in `app:ch_waves:thm:leading`.
The operator in the upper bound is the actual normal-pairing operator. Constants
valid uniformly on a working domain yield this same bound at every point;
construction of those constants remains with the geometric and transport owners. -/
theorem principalNormal_norm_lower_of_pencil_null {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n} {ξ b : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (hframe : ∃ e : Module.Basis (Fin n) ℝ (symmetricNormalMap F x).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = projectedStress F x i)
    (hnull : ActualCarriers.pencil (projectedStress F x) ξ *ᵥ (fun j ↦ b j) = 0)
    {cξ cb C : ℝ} (hcξ : 0 < cξ) (hcb : 0 < cb) (hC : 0 < C)
    (hξ : cξ ≤ ‖ξ‖) (hb : cb ≤ ‖b‖)
    (hQ : ‖(normalMapLinear F x).adjoint.toContinuousLinearMap‖ ≤ C) :
    0 < cξ * cb / (2 * C) ∧
      cξ * cb / (2 * C) ≤ ‖principalNormal (canonicalNormalCompletion F x) ξ b‖ := by
  refine normalAmplitude_norm_lower_of_pairing (normalMapLinear F x).adjoint
    (ξ := ξ) (b := b) ?_ hcξ hcb hC hξ hb ?_
  · rw [adjoint_normalMapLinear]
    exact principalNormal_pairing_of_pencil_null hF hrank hframe hnull
  · intro v
    exact ((normalMapLinear F x).adjoint.toContinuousLinearMap.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hQ (norm_nonneg v))

/-- The exact Hermitian rank-one tensor of the canonical principal amplitude
in `app:ch_waves:thm:leading`, using the shared real-to-complex convention. -/
theorem principalNormal_hermitianTensor {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x ξ b : Euclidean n) :
    hermitianTensor ((principalMatrix
      (principalNormal (canonicalNormalCompletion F x) ξ b) ξ).map Complex.ofReal) =
      fun i j ↦ ‖principalNormal (canonicalNormalCompletion F x) ξ b‖ ^ 2 * ξ i * ξ j :=
  principalMatrix_hermitianTensor _ _

/-- Literal transported-density identity in `app:ch_waves:thm:leading`.
For the supplied amplitude `(a x * r (Y x)) • k x`, the Hermitian tensor is
`a x ^ 2 * r (Y x) ^ 2` times the fixed `k` tensor. Thus, for fixed `F`, `ξ`,
`k`, `a` and `Y`, it depends linearly on the initial density `r²`. The flow
factor and footpoint map are inputs; their existence is not asserted. -/
theorem principalNormal_hermitianTensor_transport_density {n N m : ℕ}
    (F : Euclidean n → Euclidean N) (ξ k : Euclidean n → Euclidean n)
    (a : Euclidean n → ℝ) (r : Euclidean m → ℝ)
    (Y : Euclidean n → Euclidean m) (x : Euclidean n) :
    hermitianTensor ((principalMatrix (principalNormal (canonicalNormalCompletion F x)
      (ξ x) ((a x * r (Y x)) • k x)) (ξ x)).map Complex.ofReal) =
      (a x ^ 2 * r (Y x) ^ 2) •
        hermitianTensor ((principalMatrix
          (principalNormal (canonicalNormalCompletion F x) (ξ x) (k x))
          (ξ x)).map Complex.ofReal) := by
  rw [hermitianTensor_ofReal, hermitianTensor_ofReal,
    principalNormal_density_scaling, mul_pow]

end JanetCartan.LeadingWave
