module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Uniform mixed parameter directions for finite residual envelopes

The one-letter estimate quantifies over each ordered parameter word. Its next
application needs one source constant for all unit directions of a fixed length.
Finite basis expansion gives that constant, preserving the exact source scale
and the Fourier grade. The multilinear map in the consumer is the actual
Fréchet jet of the same jointly smooth residual representative.

Consumer: repeated application of `app:ch_response:eq:fixed-factor-transfer`
in the finite expansion of `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section

namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes

open ResponseTransfer

variable {d : ℕ} {I H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

local notation "Par" => Euclidean 3 × Euclidean d

private def parameterBasis : Module.Basis (Fin 3 ⊕ Fin d) ℝ Par :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.prod
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

private theorem parameterBasis_norm_le (j : Fin 3 ⊕ Fin d) :
    ‖parameterBasis j‖ ≤ 1 := by
  cases j <;> simp [parameterBasis, Prod.norm_def]

private theorem parameterBasis_repr_le (v : Par) (j : Fin 3 ⊕ Fin d) :
    ‖parameterBasis.repr v j‖ ≤ ‖v‖ := by
  cases j with
  | inl j =>
    change ‖v.1 j‖ ≤ ‖v‖
    exact (PiLp.norm_apply_le v.1 j).trans (norm_fst_le v)
  | inr j =>
    change ‖v.2 j‖ ≤ ‖v‖
    exact (PiLp.norm_apply_le v.2 j).trans (norm_snd_le v)

private theorem gradeNorm_smul_eq (G : GradedScale H) {s : ℕ} {x : H}
    (hx : x ∈ G.level s) (a : ℝ) :
    G.gradeNorm s (a • x) = ‖a‖ * G.gradeNorm s x := by
  rw [G.gradeNorm_eq ((G.level s).smul_mem a hx), G.gradeNorm_eq hx]
  change G.seminorm s (a • (⟨x, hx⟩ : G.level s)) = _
  exact map_smul_eq_mul _ _ _

/-- A fixed Sobolev grade has a uniform constant over all unit parameter
words, for an arbitrary prescribed scale weight. The weight may be the
naturally truncated reserve `A i * K i^(s+l-R)`. No factorization into a
negative power is used (`app:ch_response:cor:finite-jets`). -/
theorem exists_uniform_parameter_jet_grade_constant
    (G : GradedScale H) (l s : ℕ)
    (D : I → ContinuousMultilinearMap ℝ (fun _ : Fin l ↦ Par) H) (W : I → ℝ)
    (hD : ∀ v : Fin l → Par, (∀ j, ‖v j‖ ≤ 1) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i, D i v ∈ G.level s ∧ G.gradeNorm s (D i v) ≤ C*W i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i (v : Fin l → Par),
      (∀ j, ‖v j‖ ≤ 1) → D i v ∈ G.level s ∧ G.gradeNorm s (D i v) ≤ C*W i := by
  classical
  let b : Module.Basis (Fin 3 ⊕ Fin d) ℝ Par := parameterBasis
  choose C hC hbound using fun a : Fin l → (Fin 3 ⊕ Fin d) ↦
    hD (fun j ↦ b (a j)) (fun j ↦ parameterBasis_norm_le (a j))
  refine ⟨∑ a, C a, Finset.sum_nonneg (fun a _ ↦ hC a), ?_⟩
  intro i v hv
  let coeff : (Fin l → (Fin 3 ⊕ Fin d)) → ℝ := fun a ↦ ∏ j, b.repr (v j) (a j)
  have hcoeff a : ‖coeff a‖ ≤ 1 := by
    dsimp only [coeff]
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦
      (parameterBasis_repr_le (v j) (a j)).trans (hv j)
  have he : D i v = ∑ a : Fin l → (Fin 3 ⊕ Fin d),
      coeff a • D i (fun j ↦ b (a j)) := by
    have hv' : v = fun j ↦ ∑ k, b.repr (v j) k • b k := by
      funext j
      exact (b.sum_repr (v j)).symm
    conv_lhs => rw [hv', (D i).map_sum]
    simp only [(D i).map_smul_univ, coeff]
  have hmem a : coeff a • D i (fun j ↦ b (a j)) ∈ G.level s :=
    (G.level s).smul_mem _ ((hbound a i).1)
  obtain ⟨hsum, hsumBound⟩ := gradeNorm_sum_le G Finset.univ
    (fun a ↦ coeff a • D i (fun j ↦ b (a j))) s (fun a _ ↦ hmem a)
  rw [he]
  refine ⟨hsum, hsumBound.trans ?_⟩
  calc
    ∑ a, G.gradeNorm s (coeff a • D i (fun j ↦ b (a j)))
        ≤ ∑ a, C a * W i := by
      apply Finset.sum_le_sum
      intro a _
      rw [gradeNorm_smul_eq G (hbound a i).1]
      exact (mul_le_of_le_one_left (G.gradeNorm_nonneg _ _) (hcoeff a)).trans
        (hbound a i).2
    _ = (∑ a, C a) * W i := by rw [Finset.sum_mul]


/-- A single constant controls every unit mixed parameter direction. The
constant is the sum of finitely many coordinate-word constants; neither the
amplitude nor the frequency scale changes. The supplied multilinear map is
instantiated with the actual `iteratedFDeriv` of the jointly smooth residual
envelope (`app:ch_response:cor:finite-jets`). -/
theorem exists_uniform_parameter_jet_envelope_constant
    (G : GradedScale H) (l : ℕ)
    (D : I → ContinuousMultilinearMap ℝ (fun _ : Fin l ↦ Par) H)
    (A K : I → ℝ)
    (hD : ∀ v : Fin l → Par, (∀ j, ‖v j‖ ≤ 1) →
      HasEnvelopeProfile G (fun i ↦ D i v) A K) :
    ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i (v : Fin l → Par),
      (∀ j, ‖v j‖ ≤ 1) → D i v ∈ G.level s ∧
        G.gradeNorm s (D i v) ≤ C * A i * K i ^ s := by
  intro s
  have h := exists_uniform_parameter_jet_grade_constant G l s D (fun i ↦ A i*K i^s) (by
    intro v hv
    obtain ⟨C,hC,hbound⟩ := hD v hv s
    exact ⟨C,hC,fun i ↦ ⟨(hbound i).1,by simpa only [mul_assoc] using (hbound i).2⟩⟩)
  simpa only [mul_assoc] using h

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
