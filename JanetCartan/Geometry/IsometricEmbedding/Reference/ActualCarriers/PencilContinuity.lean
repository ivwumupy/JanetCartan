module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Pencil
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Smooth dependence of the current pencil data

The polynomial continuity arguments in Steps 2–3 of
`app:ch_seed:prop:seed-actual-menu`, for the literal definitions of
`app:ch_seed:setup:seed-current`.

The frame space carries the finite supremum of the Frobenius matrix norms;
covectors and quadratic contractions carry the existing Euclidean norm. The
covector differential is the actual `fderiv`, with its operator norm.

`exists_uniform_pencil_data_radius` supplies the coefficient errors used by
`exists_fderiv_zero_perturbation_gap` and `exists_detection_perturbation_radius`.
It requires only a fixed frame, a compact covector set, and a positive requested
error. Geometric consumers still have to construct their frames and carriers,
prove frame closeness, and provide the frozen gaps and detection hypotheses.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

private theorem contDiff_matrix_of_entries {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → MetricTensor n}
    (hf : ∀ i j, ContDiff ℝ ∞ (fun x ↦ f x i j)) : ContDiff ℝ ∞ f := by
  let e : (Fin n × Fin n → ℝ) ≃ₗ[ℝ] MetricTensor n :=
    { toFun := fun g i j ↦ g (i, j)
      invFun := fun A ij ↦ A ij.1 ij.2
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact e.toContinuousLinearEquiv.contDiff.comp (contDiff_pi.mpr fun ij ↦ hf ij.1 ij.2)

private theorem contDiff_frame_entry {n : ℕ} (i j k : Fin n) :
    ContDiff ℝ ∞ (fun Q : Fin n → MetricTensor n ↦ Q i j k) :=
  (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp
    (contDiff_apply ℝ (fun _ : Fin n ↦ MetricTensor n) i)

/-- Joint smoothness of the current pencil in its finite frame and covector
(`app:ch_seed:setup:seed-current`), used to preserve the matrix gaps in
Step 2 of `app:ch_seed:prop:seed-actual-menu`. -/
theorem contDiff_pencil {n : ℕ} :
    ContDiff ℝ ∞ (fun p : (Fin n → MetricTensor n) × Euclidean n ↦ pencil p.1 p.2) := by
  apply contDiff_matrix_of_entries
  intro i j
  simp only [pencil]
  apply ContDiff.sum
  intro k _
  exact ((contDiff_frame_entry i j k).comp contDiff_fst).mul
    ((contDiff_piLp_apply 2).comp contDiff_snd)

/-- Joint smoothness of the current characteristic polynomial, including
singular pencils (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem contDiff_determinant {n : ℕ} :
    ContDiff ℝ ∞ (fun p : (Fin n → MetricTensor n) × Euclidean n ↦ determinant p.1 p.2) := by
  simp only [determinant, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (Matrix.entryLinearMap ℝ ℝ (σ i) i).toContinuousLinearMap.contDiff.comp contDiff_pencil

/-- Joint smoothness of the actual covector Fréchet differential, in operator
norm, including at characteristic covectors. This supplies differential
continuity for the simple-zero gap and the incidence equation in Steps 2–3 of
`app:ch_seed:prop:seed-actual-menu`. -/
theorem contDiff_fderiv_determinant {n : ℕ} :
    ContDiff ℝ ∞ (fun p : (Fin n → MetricTensor n) × Euclidean n ↦
      fderiv ℝ (determinant p.1) p.2) := by
  have h : ContDiff ℝ ∞ (Function.uncurry
      (fun (p : (Fin n → MetricTensor n) × Euclidean n) (ξ : Euclidean n) ↦
        determinant p.1 ξ)) :=
    contDiff_determinant.comp ((contDiff_fst.fst).prodMk contDiff_snd)
  exact h.fderiv contDiff_snd (by simp)

/-- The adjugate of the current pencil depends smoothly on both inputs,
including singular pencils. Its polynomial cofactor formula supplies the
continuity needed in `app:ch_seed:prop:seed-actual-menu`, Step 2. -/
theorem contDiff_adjugate_pencil {n : ℕ} :
    ContDiff ℝ ∞ (fun p : (Fin n → MetricTensor n) × Euclidean n ↦ (pencil p.1 p.2).adjugate) := by
  apply contDiff_matrix_of_entries
  intro i j
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro k _
  by_cases h : σ k = j
  · simp only [Matrix.updateRow_apply, h, ite_true]
    exact contDiff_const
  · simp only [Matrix.updateRow_apply, h, ite_false]
    exact (Matrix.entryLinearMap ℝ ℝ (σ k) k).toContinuousLinearMap.contDiff.comp contDiff_pencil

/-- Joint smoothness of the quadratic stress contraction in the finite frame
and Euclidean covector (`app:ch_seed:setup:seed-current`), used for detector
stability in `app:ch_seed:prop:seed-actual-menu`, Step 3. -/
theorem contDiff_quadratic {n : ℕ} :
    ContDiff ℝ ∞ (fun p : (Fin n → MetricTensor n) × Euclidean n ↦ quadratic p.1 p.2) := by
  apply (contDiff_piLp 2).mpr
  intro i
  simp only [quadratic, PiLp.toLp_apply]
  apply ContDiff.sum
  intro j _
  apply ContDiff.sum
  intro k _
  exact (((contDiff_piLp_apply 2).comp contDiff_snd).mul
    ((contDiff_frame_entry i j k).comp contDiff_fst)).mul
    ((contDiff_piLp_apply 2).comp contDiff_snd)

private theorem exists_uniform_frame_radius {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {f : (Fin n → MetricTensor n) → Euclidean n → V}
    (hf : Continuous (Function.uncurry f)) (Q₀ : Fin n → MetricTensor n)
    {K : Set (Euclidean n)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ Q, ‖Q - Q₀‖ < δ → ∀ ξ ∈ K, ‖f Q ξ - f Q₀ ξ‖ < η := by
  obtain ⟨U, hU, h⟩ := hK.mem_uniformity_of_prod (s := Set.univ) hf.continuousOn
    (Set.mem_univ Q₀) (u := {p : V × V | dist p.1 p.2 < η})
    (Metric.mem_uniformity_dist.mpr ⟨η, hη, fun _ _ hab ↦ hab⟩)
  rw [nhdsWithin_univ] at hU
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, hδ, fun Q hQ ξ hξ ↦ ?_⟩
  simpa only [dist_eq_norm] using (show dist (f Q ξ) (f Q₀ ξ) < η from
    h Q (hδU (by simpa only [Metric.mem_ball, dist_eq_norm] using hQ)) ξ hξ)

/-- One positive frame radius makes all five literal current-pencil errors
strictly smaller than the requested positive error on an arbitrary compact
covector set (`app:ch_seed:prop:seed-actual-menu`, Steps 2–3).

The frame norm is the finite supremum of Frobenius norms, and the differential
error uses the operator norm of the actual covector `fderiv`. All error bounds
follow from polynomial smoothness and compactness; no coefficient-error or
geometric construction hypothesis is assumed. -/
theorem exists_uniform_pencil_data_radius {n : ℕ} (Q₀ : Fin n → MetricTensor n)
    {K : Set (Euclidean n)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ Q : Fin n → MetricTensor n, ‖Q - Q₀‖ < δ → ∀ ξ ∈ K,
      ‖pencil Q ξ - pencil Q₀ ξ‖ < η ∧
      ‖determinant Q ξ - determinant Q₀ ξ‖ < η ∧
      ‖fderiv ℝ (determinant Q) ξ - fderiv ℝ (determinant Q₀) ξ‖ < η ∧
      ‖(pencil Q ξ).adjugate - (pencil Q₀ ξ).adjugate‖ < η ∧
      ‖quadratic Q ξ - quadratic Q₀ ξ‖ < η := by
  have h := (contDiff_pencil (n := n)).continuous.prodMk (contDiff_determinant.continuous.prodMk
    (contDiff_fderiv_determinant.continuous.prodMk
      (contDiff_adjugate_pencil.continuous.prodMk contDiff_quadratic.continuous)))
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_frame_radius
    (f := fun Q ξ ↦ (pencil Q ξ, determinant Q ξ, fderiv ℝ (determinant Q) ξ,
      (pencil Q ξ).adjugate, quadratic Q ξ)) h Q₀ hK hη
  refine ⟨δ, hδ, fun Q hQ ξ hξ ↦ ?_⟩
  simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, max_lt_iff] using hbound Q hQ ξ hξ

end JanetCartan.ActualCarriers
