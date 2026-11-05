module

public import JanetCartan.Analysis.Fourier.Conventions.NormComparison.Cartesian
public import Mathlib.Analysis.Matrix.Normed

/-!
# The componentwise `C^r` convention for vectors and matrices

`app:not:fourier` takes the maximum over all fixed coordinates. The project
uses Euclidean and Frobenius norms before taking derivative operator norms.
Both comparisons below have fixed dimension-and-order constants. The actual
matrix result applies to the stress tensors in Section 4 and preserves their
original Frobenius topology and smooth neighborhood.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.FourierConventions
open LocalSobolev

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

private theorem norm_le_coordinate_sum {ι G : Type*} [Fintype ι] [NormedAddCommGroup G]
    (v : PiLp 2 (fun _ : ι ↦ G)) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  rw [PiLp.norm_eq_of_L2]
  exact Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _),
    Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)⟩

private theorem norm_jet_le_sum_components
    {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    (P : ι → F →L[ℝ] 𝕜) (hP : ∀ v, ‖v‖ ≤ ∑ i, ‖P i v‖)
    {f : EuclideanSpace ℝ (Fin n) → F} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) (r : ℕ) :
    ‖iteratedFDeriv ℝ r f x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ r (P i ∘ f) x‖ := by
  have he (i : ι) (v : Fin r → EuclideanSpace ℝ (Fin n)) :
      P i (iteratedFDeriv ℝ r f x v) = iteratedFDeriv ℝ r (P i ∘ f) x v := by
    exact (congrArg (fun T ↦ T v)
      ((P i).iteratedFDeriv_comp_left hf (i := r) (by simp))).symm
  apply ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  intro v
  calc
    _ ≤ ∑ i, ‖P i (iteratedFDeriv ℝ r f x v)‖ := hP _
    _ = ∑ i, ‖iteratedFDeriv ℝ r (P i ∘ f) x v‖ := by simp_rw [he]
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ r (P i ∘ f) x‖ * ∏ j, ‖v j‖ :=
      Finset.sum_le_sum fun i _ ↦ (iteratedFDeriv ℝ r (P i ∘ f) x).le_opNorm v
    _ = _ := (Finset.sum_mul ..).symm

private theorem cNorm_le_sum_components
    {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    (P : ι → F →L[ℝ] 𝕜) (hP : ∀ v, ‖v‖ ≤ ∑ i, ‖P i v‖)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsCompact D)
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ∀ x ∈ D, ContDiffAt ℝ ∞ f x) (r : ℕ) :
    cNorm D r f ≤ ∑ i, cNorm D r (P i ∘ f) := by
  have hb (i : ι) (j : ℕ) :
      BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j (P i ∘ f) x‖) '' D) :=
    bddAbove_norm_iteratedFDeriv_of_contDiffAt hD
      (fun x hx ↦ ((P i).contDiff.contDiffAt.comp x (hf x hx)).of_le (by simp)) le_rfl
  have h := cNorm_le_sum_of_bounds (s := D) (r := r)
    (C := fun j ↦ ∑ i, sSup ((fun x ↦ ‖iteratedFDeriv ℝ j (P i ∘ f) x‖) '' D))
    (fun j _ ↦ Finset.sum_nonneg fun i _ ↦ sSup_norm_iteratedFDeriv_nonneg D j (P i ∘ f))
    (fun j _ x hx ↦ (norm_jet_le_sum_components P hP (hf x hx) j).trans
      (Finset.sum_le_sum fun i _ ↦ le_csSup (hb i j) (Set.mem_image_of_mem _ hx)))
  exact h.trans_eq (Finset.sum_comm ..)

private theorem cartesianCNorm_component_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : F →L[ℝ] 𝕜) (hP : ∀ v, ‖P v‖ ≤ ‖v‖)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsCompact D)
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ∀ x ∈ D, ContDiffAt ℝ ∞ f x) (r : ℕ) :
    cartesianCNorm D r (P ∘ f) ≤ cNorm D r f := by
  apply cartesianCNorm_le_of_bound (cNorm_nonneg D r f)
  intro α hα x hx
  have he : cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j (P ∘ f))
      (fun i ↦ α (some i)) x = P (cartesianJetDerivative
        (fun j ↦ iteratedFDeriv ℝ j f) (fun i ↦ α (some i)) x) := by
    unfold cartesianJetDerivative
    dsimp only
    rw [P.iteratedFDeriv_comp_left (hf x hx) (by simp)]
    rfl
  rw [he]
  apply (hP _).trans ((norm_cartesianJetDerivative_le _ _ _).trans
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hD
      (fun y hy ↦ (hf y hy).of_le (by simp)) hx ?_))
  have := mem_sobolevMultiindices.mp hα
  omega

private theorem components_comparison
    {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    (P : ι → F →L[ℝ] 𝕜)
    (hP : ∀ i v, ‖P i v‖ ≤ ‖v‖) (hF : ∀ v, ‖v‖ ≤ ∑ i, ‖P i v‖)
    {D U : Set (EuclideanSpace ℝ (Fin n))} (hD : IsCompact D)
    (hU : IsOpen U) (hDU : D ⊆ U) (r : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : ContDiffOn ℝ ∞ f U) :
    let M := sSup (Set.range fun i ↦ cartesianCNorm D r (P i ∘ f))
    0 ≤ M ∧ M ≤ cNorm D r f ∧
      cNorm D r f ≤ (Fintype.card ι * cartesianCNormComparisonConstant n r) * M := by
  dsimp only
  have hm : 0 ≤ sSup (Set.range fun i ↦ cartesianCNorm D r (P i ∘ f)) :=
    Real.sSup_nonneg (by rintro _ ⟨i, rfl⟩; exact cartesianCNorm_nonneg D r _)
  have hlocal : ∀ x ∈ D, ContDiffAt ℝ ∞ f x := fun x hx ↦
    hf.contDiffAt (hU.mem_nhds (hDU hx))
  refine ⟨hm, Real.sSup_le ?_ (cNorm_nonneg D r f), ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact cartesianCNorm_component_le (P i) (hP i) hD hlocal r
  · apply (cNorm_le_sum_components P hF hD hlocal r).trans
    calc
      _ ≤ ∑ _i : ι, cartesianCNormComparisonConstant n r *
          sSup (Set.range fun i ↦ cartesianCNorm D r (P i ∘ f)) := by
        apply Finset.sum_le_sum
        intro i _
        exact (cNorm_le_cartesianCNorm hD hU hDU
          ((P i).contDiff.comp_contDiffOn hf)).trans
          (mul_le_mul_of_nonneg_left
            (le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i))
            (cartesianCNormComparisonConstant_pos n r).le)
      _ = _ := by simp [mul_assoc]

section Matrix
variable {I J : Type*} [Fintype I] [Fintype J]

private def entryProjection (ij : I × J) : Matrix I J 𝕜 →L[ℝ] 𝕜 :=
  ({ toFun := fun M ↦ M ij.1 ij.2
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl } : Matrix I J 𝕜 →ₗ[ℝ] 𝕜).mkContinuous 1
    (fun M ↦ by
      change ‖M ij.1 ij.2‖ ≤ 1 * ‖M‖
      rw [one_mul]
      exact (PiLp.norm_apply_le (WithLp.toLp 2 (M ij.1)) ij.2).trans
        (PiLp.norm_apply_le (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (M i))) ij.1))

/-- The manuscript's maximum over all matrix entries and Cartesian
multiindices, with the fixed physical domain explicit (`app:not:fourier`). -/
def matrixCartesianCNorm (D : Set (EuclideanSpace ℝ (Fin n))) (r : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → Matrix I J 𝕜) : ℝ :=
  sSup (Set.range fun ij : I × J ↦ cartesianCNorm D r (fun x ↦ f x ij.1 ij.2))

/-- The entrywise convention is equivalent to the original Frobenius
`cNorm`, with constants depending only on the dimensions and order.
This applies directly to the Section 4 real metric and stress tensors
(`app:not:fourier`). -/
theorem matrixCartesianCNorm_comparison
    {D U : Set (EuclideanSpace ℝ (Fin n))} (hD : IsCompact D)
    (hU : IsOpen U) (hDU : D ⊆ U) (r : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → Matrix I J 𝕜} (hf : ContDiffOn ℝ ∞ f U) :
    0 ≤ matrixCartesianCNorm D r f ∧ matrixCartesianCNorm D r f ≤ cNorm D r f ∧
      cNorm D r f ≤ ((Fintype.card I * Fintype.card J : ℕ) *
        cartesianCNormComparisonConstant n r) * matrixCartesianCNorm D r f := by
  have hF (M : Matrix I J 𝕜) : ‖M‖ ≤ ∑ ij : I × J, ‖entryProjection ij M‖ := by
    change ‖M‖ ≤ ∑ ij : I × J, ‖M ij.1 ij.2‖
    rw [Fintype.sum_prod_type]
    exact (norm_le_coordinate_sum (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (M i)))).trans
      (Finset.sum_le_sum fun i _ ↦ norm_le_coordinate_sum (WithLp.toLp 2 (M i)))
  have hP (ij : I × J) (M : Matrix I J 𝕜) : ‖entryProjection ij M‖ ≤ ‖M‖ :=
    (PiLp.norm_apply_le (WithLp.toLp 2 (M ij.1)) ij.2).trans
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (M i))) ij.1)
  have he (ij : I × J) : entryProjection ij ∘ f = fun x ↦ f x ij.1 ij.2 := rfl
  simpa! only [he, Fintype.card_prod, matrixCartesianCNorm] using
    components_comparison (entryProjection (𝕜 := 𝕜)) hP hF hD hU hDU r hf

/-- Convergence in the actual Frobenius `cNorm` is precisely componentwise
`C^r` convergence on the compact domain. This is the convention transfer
for the stress limit in Section 4 (`app:not:fourier`). -/
theorem tendsto_matrixCartesianCNorm_zero_iff
    {A : Type*} {l : Filter A} {D U : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U) (r : ℕ)
    (f : A → EuclideanSpace ℝ (Fin n) → Matrix I J 𝕜)
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) U) :
    Tendsto (fun a ↦ matrixCartesianCNorm D r (f a)) l (𝓝 0) ↔
      Tendsto (fun a ↦ cNorm D r (f a)) l (𝓝 0) := by
  constructor
  · intro h
    have hm := h.const_mul ((Fintype.card I * Fintype.card J : ℕ) *
      cartesianCNormComparisonConstant n r)
    simp only [mul_zero] at hm
    exact squeeze_zero (fun a ↦ cNorm_nonneg D r (f a))
      (fun a ↦ (matrixCartesianCNorm_comparison hD hU hDU r (hf a)).2.2) hm
  · intro h
    exact squeeze_zero
      (fun a ↦ (matrixCartesianCNorm_comparison hD hU hDU r (hf a)).1)
      (fun a ↦ (matrixCartesianCNorm_comparison hD hU hDU r (hf a)).2.1) h

end Matrix

section Vector
variable {I : Type*} [Fintype I]

/-- The manuscript's maximum over vector components and Cartesian
multiindices on the prescribed physical domain (`app:not:fourier`). -/
def vectorCartesianCNorm (D : Set (EuclideanSpace ℝ (Fin n))) (r : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace 𝕜 I) : ℝ :=
  sSup (Set.range fun i ↦ cartesianCNorm D r (fun x ↦ f x i))

/-- The componentwise vector norm and the actual Euclidean `cNorm` are
comparable without changing derivative order (`app:not:fourier`). -/
theorem vectorCartesianCNorm_comparison
    {D U : Set (EuclideanSpace ℝ (Fin n))} (hD : IsCompact D)
    (hU : IsOpen U) (hDU : D ⊆ U) (r : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace 𝕜 I} (hf : ContDiffOn ℝ ∞ f U) :
    0 ≤ vectorCartesianCNorm D r f ∧ vectorCartesianCNorm D r f ≤ cNorm D r f ∧
      cNorm D r f ≤ (Fintype.card I * cartesianCNormComparisonConstant n r) *
        vectorCartesianCNorm D r f :=
  components_comparison (fun i ↦ PiLp.proj 2 (fun _ : I ↦ 𝕜) i)
    (fun i v ↦ PiLp.norm_apply_le v i) norm_le_coordinate_sum hD hU hDU r hf

end Vector
end JanetCartan.FourierConventions
