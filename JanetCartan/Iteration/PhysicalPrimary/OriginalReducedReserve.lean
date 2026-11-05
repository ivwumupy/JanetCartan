module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.ProfileFamilyFourier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.PrimaryResponse
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.MatrixParameterProfiles

/-! # The actual Fourier-to-classical reserve and matrix entries
The full-source reserve is `reserve + n + 1`. The diagonal Fourier profile
pays for the original Sobolev embedding, including low derivative orders
where natural subtraction truncates. The source size is never cancelled. -/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalReducedReserve
open CanonicalAtomRealization Pseudodifferential

/-- The positive inverse's order-by-order profile is transported through its
*own* classical representatives, in the actual ordered parameter directions.
Unlike the unreserved estimate, there is no residual factor `K^(n+1)`;
exactly the source reserve pays for it even below the floor. -/
theorem reserved_joint_of_ordered_classes {n d N : ℕ}
    {V : Set (Euclidean 3 × Euclidean d)} (hV : IsOpen V)
    {f : Euclidean n × (Euclidean 3 × Euclidean d) → EuclideanSpace ℂ (Fin N)}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ V)) (S : ℕ → ℕ → ℝ) (hS : ∀ k p, 0 ≤ S k p)
    {τ size K : ℝ} (hτ : 0 < τ) (hsize : 0 ≤ size) (hK : 1 ≤ K) (reserve : ℕ)
    (hfourier : ∀ c ∈ V, ∀ k p : ℕ, ∀ w : Fin k → (Euclidean 3 × Euclidean d),
      (∀ l, ‖w l‖ ≤ 1) →
      ∃ u : PiLp 2 (fun _ : Fin N ↦ Lp ℂ 2 (volume : Measure (Euclidean n))),
        (∀ i, u i =ᵐ[volume] fun x ↦ (iteratedFDeriv ℝ k (fun b ↦ f (x,b)) c w) i) ∧
        MemMatrixFourierSobolev (p : ℝ) u ∧ matrixFourierSobolevNorm (p : ℝ) u ≤
          S k p * (τ^3*size) * K^(p+k-(reserve+n+1))) :
    ∀ m q, q ∈ univ ×ˢ V →
      ‖iteratedFDeriv ℝ m f q‖ ≤ reducedProfileClassicalBudget n d N S m * (τ^3*size) * K^(m-reserve) ∧
      ∀ i, ‖iteratedFDeriv ℝ m (fun b ↦ f b i) q‖ ≤
        reducedProfileClassicalBudget n d N S m * (τ^3*size) * K^(m-reserve) := by
  classical
  intro m q hq
  let D := ∑ k ∈ Finset.range (m+1), S k (m-k+n+1)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ ↦ hS k _)
  have hA : 0 ≤ τ^3*size := mul_nonneg (pow_nonneg hτ.le _) hsize
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hb := (exists_reducedParameterJet_fourier_constant n d N m).choose_spec.2
    V hV f hf (D*(τ^3*size)*K^(m-reserve)) (by positivity) ?_ q hq
  · have he : (exists_reducedParameterJet_fourier_constant n d N m).choose *
          (D*(τ^3*size)*K^(m-reserve)) =
          reducedProfileClassicalBudget n d N S m * (τ^3*size) * K^(m-reserve) := by
      dsimp only [D,reducedProfileClassicalBudget]
      ring
    simpa only [he] using hb
  · intro c hc k hk v hv
    obtain ⟨u,hu,hm,hb⟩ := hfourier c hc k (m-k+n+1) v hv
    refine ⟨u,hu,hm,?_⟩
    have hdiag : m-k+n+1+k-(reserve+n+1) = m-reserve := by omega
    rw [hdiag] at hb
    apply hb.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (s := Finset.range (m+1)) (f := fun j ↦ S j (m-j+n+1))
        (a := k) (fun j _ ↦ hS j _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))) hA)
      (pow_nonneg hK0 _)

/-- Entrywise smoothness and reserved jet estimates of the genuine full
matrix, without attempting to invert the contracted stress. -/
theorem strain_coordinate_entries {n d : ℕ} {V : Set (Euclidean 3 × Euclidean d)} (hV : IsOpen V)
    (f : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin n) (Fin n) ℂ)
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ V)) {B : ℕ → ℝ} {τ size K : ℝ} {r : ℕ}
    (hb : ∀ m q, q.2 ∈ V → ‖iteratedFDeriv ℝ m f q‖ ≤ B m*(τ^3*size)*K^(m-r)) :
    (∀ ij : Fin n × Fin n, ContDiffOn ℝ ∞ (fun q ↦ f q ij.1 ij.2) (univ ×ˢ V)) ∧
      ∀ ij : Fin n × Fin n, ∀ m q, q.2 ∈ V →
        ‖iteratedFDeriv ℝ m (fun p ↦ f p ij.1 ij.2) q‖ ≤ B m*(τ^3*size)*K^(m-r) := by
  let ev := fun ij : Fin n × Fin n ↦ AmplitudeBound.matrixEntryEvaluation ij.1 ij.2
  have he ij : ‖ev ij‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖v ij.1 ij.2‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using AmplitudeBound.norm_matrixEntry_le_frobenius v ij.1 ij.2
  refine ⟨fun ij ↦ (ev ij).contDiff.comp_contDiffOn hf,?_⟩
  intro ij m q hq
  have hat := hf.contDiffAt ((isOpen_univ.prod hV).mem_nhds (show q ∈ univ ×ˢ V from ⟨mem_univ _,hq⟩))
  apply ((ev ij).norm_iteratedFDeriv_comp_left hat (by simp : (m : ℕ∞ω) ≤ ∞)).trans
  exact (mul_le_of_le_one_left (norm_nonneg _) (he ij)).trans (hb m q hq)

end JanetCartan.PhysicalPrimary.OriginalReducedReserve
