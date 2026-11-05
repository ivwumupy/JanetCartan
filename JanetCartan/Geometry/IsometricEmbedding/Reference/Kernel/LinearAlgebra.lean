module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs

/-!
# Linear algebra for the cube normal map

The Frobenius Gram argument used in Proposition `app:ch_seed:prop:seed-gram`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CubeKernel

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Frobenius contraction with a finite family, as in
Proposition `app:ch_seed:prop:seed-gram`. -/
def tensorContraction (R : ι → MetricTensor n) :
    MetricTensor n →ₗ[ℝ] (ι → ℝ) where
  toFun H i := tensorPairing H (R i)
  map_add' H K := by
    ext i
    simp [tensorPairing, add_mul, Finset.sum_add_distrib]
  map_smul' c H := by
    ext i
    simp [tensorPairing, mul_assoc, Finset.mul_sum]

/-- Synthesis of a tensor from coefficients, used for the Gram matrix in
Proposition `app:ch_seed:prop:seed-gram`. -/
def tensorCombination (R : ι → MetricTensor n) : (ι → ℝ) →ₗ[ℝ] MetricTensor n where
  toFun c := ∑ i, c i • R i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

/-- Positivity of the Frobenius pairing, used in
Proposition `app:ch_seed:prop:seed-gram`. -/
theorem tensorPairing_self_eq_zero_iff (H : MetricTensor n) :
    tensorPairing H H = 0 ↔ H = 0 := by
  constructor
  · intro h
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦
        Finset.sum_nonneg (fun j _ ↦ mul_self_nonneg (H i j)))).mp h
    ext i j
    exact ((Finset.sum_mul_self_eq_zero_iff _ _).mp (hrow i (Finset.mem_univ i)))
      j (Finset.mem_univ j)
  · rintro rfl
    simp [tensorPairing]

/-- The Gram quadratic form is the squared Frobenius norm of the synthesized
tensor; Proposition `app:ch_seed:prop:seed-gram`. -/
theorem tensorPairing_combination (R : ι → MetricTensor n) (H : MetricTensor n)
    (c : ι → ℝ) :
    tensorPairing H (tensorCombination R c) =
      ∑ k, c k * tensorContraction R H k := by
  simp only [tensorPairing, tensorCombination, tensorContraction, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  calc
    _ = ∑ i, ∑ k, ∑ j, c k * (H i j * R k i j) := by
      congr 1
      ext i
      rw [Finset.sum_comm]
      congr 1
      ext k
      congr 1
      ext j
      ring
    _ = _ := by rw [Finset.sum_comm]

/-- The Gram map of independent tensors is injective;
Proposition `app:ch_seed:prop:seed-gram`. -/
theorem tensorGram_injective (R : ι → MetricTensor n)
    (hR : LinearIndependent ℝ R) :
    Function.Injective ((tensorContraction R).comp (tensorCombination R)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  have hnorm : tensorPairing (tensorCombination R c) (tensorCombination R c) = 0 := by
    rw [tensorPairing_combination]
    have hc' : tensorContraction R (tensorCombination R c) = 0 := hc
    simp [hc']
  have hcomb := (tensorPairing_self_eq_zero_iff _).mp hnorm
  exact funext ((Fintype.linearIndependent_iff.mp hR) c hcomb)

/-- Independent Frobenius row tensors give a surjective contraction map.
This is the Gram-matrix step of Proposition `app:ch_seed:prop:seed-gram`. -/
theorem tensorContraction_surjective (R : ι → MetricTensor n)
    (hR : LinearIndependent ℝ R) : Function.Surjective (tensorContraction R) := by
  intro v
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp (tensorGram_injective R hR)) v
  exact ⟨tensorCombination R c, hc⟩

/-- For symmetric independent rows, surjectivity already holds on symmetric
tensors; Proposition `app:ch_seed:prop:seed-gram`. -/
theorem exists_isSymm_tensorContraction_eq (R : ι → MetricTensor n)
    (hR : LinearIndependent ℝ R) (hsymm : ∀ i, (R i).IsSymm) (v : ι → ℝ) :
    ∃ H : MetricTensor n, H.IsSymm ∧ tensorContraction R H = v := by
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp (tensorGram_injective R hR)) v
  refine ⟨tensorCombination R c, ?_, hc⟩
  apply Matrix.IsSymm.ext
  intro i j
  simp only [tensorCombination, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  congr 1
  ext k
  rw [(hsymm k).apply]

/-- Independent annihilated vectors exhaust a kernel when their number is the
dimension deficit. This is the final dimension argument of
Proposition `app:ch_seed:prop:seed-gram`. -/
theorem ker_eq_span_of_finrank {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (f : V →ₗ[ℝ] W) (s : ι → V) (hs : LinearIndependent ℝ s)
    (hzero : ∀ i, f (s i) = 0) (hf : Function.Surjective f)
    (hdim : Module.finrank ℝ V = Fintype.card ι + Module.finrank ℝ W) :
    LinearMap.ker f = Submodule.span ℝ (Set.range s) := by
  have hle : Submodule.span ℝ (Set.range s) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hzero i
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_eq_card hs]
  have hrank := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, hdim] at hrank
  omega

end JanetCartan.CubeKernel
