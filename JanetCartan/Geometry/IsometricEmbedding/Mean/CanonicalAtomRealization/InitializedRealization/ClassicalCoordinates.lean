module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.Components
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Frobenius joint jets of the reconstructed response

Reassemble the literal physical-direction/ambient-coordinate bounds from
`ClassicalReconstruction`. Only the finite number of output coordinates is
lost; no parameter derivative or carrier scale is introduced. The consumer
is the original full matrix amplitude in preparation and sampling, as in
`app:ch_response:eq:current-atomic-amplitudes`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalAtomRealization

private theorem vector_norm_le_coordinate_sum {N : ℕ}
    (v : EuclideanSpace ℂ (Fin N)) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  rw [PiLp.norm_eq_of_L2]
  exact Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _),
    Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)⟩

private theorem vectorJet_norm_le_coordinate_sum
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] {N : ℕ}
    {f : D → EuclideanSpace ℂ (Fin N)} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (r : ℕ) :
    ‖iteratedFDeriv ℝ r f x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ r (fun y ↦ f y i) x‖ := by
  classical
  let P := fun i : Fin N ↦ (PiLp.proj 2 (fun _ : Fin N ↦ ℂ) i :
    EuclideanSpace ℂ (Fin N) →L[ℝ] ℂ)
  have he (i : Fin N) (v : Fin r → D) :
      (iteratedFDeriv ℝ r f x v) i = iteratedFDeriv ℝ r (fun y ↦ f y i) x v := by
    exact (congrArg (fun T ↦ T v)
      ((P i).iteratedFDeriv_comp_left hf (i := r) (by simp))).symm
  apply ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  intro v
  calc
    _ ≤ ∑ i, ‖(iteratedFDeriv ℝ r f x v) i‖ := vector_norm_le_coordinate_sum _
    _ = ∑ i, ‖iteratedFDeriv ℝ r (fun y ↦ f y i) x v‖ := by simp_rw [he]
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ r (fun y ↦ f y i) x‖ * ∏ j, ‖v j‖ :=
      Finset.sum_le_sum (fun i _ ↦ (iteratedFDeriv ℝ r (fun y ↦ f y i) x).le_opNorm v)
    _ = _ := (Finset.sum_mul ..).symm

/-- Coordinate jets control the joint ambient displacement jet, without
changing derivative order (`app:ch_response:eq:response-graded-displacement`). -/
theorem norm_fullParameterVectorJet_le_sum_coordinates {n d N : ℕ}
    {f : Euclidean n × (Euclidean 3 × Euclidean d) → EuclideanSpace ℂ (Fin N)}
    {x : Euclidean n × (Euclidean 3 × Euclidean d)}
    (hf : ContDiffAt ℝ ∞ f x) (r : ℕ) :
    ‖iteratedFDeriv ℝ r f x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ r (fun y ↦ f y i) x‖ :=
  vectorJet_norm_le_coordinate_sum hf r

/-- The literal displacement coordinate profile gives its original joint
seminorm with the same reserve and smallness factor
(`app:ch_response:eq:response-graded-displacement`). -/
theorem fullParameterVector_cNorm_le_coordinate_profile {n d N : ℕ}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d))} (hΩ : IsOpen Ω)
    {f : Euclidean n × (Euclidean 3 × Euclidean d) → EuclideanSpace ℂ (Fin N)}
    (hf : ContDiffOn ℝ ∞ f Ω) (B : ℕ → ℝ) (hB : ∀ r, 0 ≤ B r)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 1 ≤ K) (reserve m : ℕ)
    (hcoord : ∀ i r, r ≤ m → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ f y i) x‖ ≤ B r * A * K^(r-reserve))
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean d))} (hJ : J ⊆ Ω) :
    (∀ r ≤ m, ∀ x ∈ J, ‖iteratedFDeriv ℝ r f x‖ ≤
      (N : ℝ) * B r * A * K^(r-reserve)) ∧
    cNorm J m f ≤ ((N : ℝ) * ∑ r ∈ Finset.range (m+1), B r) * A * K^(m-reserve) := by
  have hj r (hr : r ≤ m) x (hx : x ∈ J) : ‖iteratedFDeriv ℝ r f x‖ ≤
      (N : ℝ) * B r * A * K^(r-reserve) := by
    apply (norm_fullParameterVectorJet_le_sum_coordinates
      (hf.contDiffAt (hΩ.mem_nhds (hJ hx))) r).trans
    have h := Finset.sum_le_sum (fun (i : Fin N) (_ : i ∈ Finset.univ) ↦
      hcoord i r hr x (hJ hx))
    simpa [mul_assoc] using h
  refine ⟨hj, ?_⟩
  have hb r (hr : r ≤ m) x (hx : x ∈ J) : ‖iteratedFDeriv ℝ r f x‖ ≤
      (N : ℝ) * B r * A * K^(m-reserve) :=
    (hj r hr x hx).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hK (Nat.sub_le_sub_right hr reserve))
      (mul_nonneg (mul_nonneg (by positivity) (hB r)) hA))
  have h := cNorm_le_sum_of_bounds (s := J) (r := m)
    (fun r _ ↦ mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hB r)) hA)
      (pow_nonneg (zero_le_one.trans hK) _)) hb
  simpa only [Finset.sum_mul, Finset.mul_sum] using h

/-- Coordinate jets control the original complex Frobenius jet, with the
same physical/label/covector derivative order
(`app:ch_response:eq:response-graded-derivative`). -/
theorem norm_fullParameterMatrixJet_le_sum_coordinates {n d N : ℕ}
    {f : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin N) (Fin n) ℂ}
    {x : Euclidean n × (Euclidean 3 × Euclidean d)}
    (hf : ContDiffAt ℝ ∞ f x) (r : ℕ) :
    ‖iteratedFDeriv ℝ r f x‖ ≤
      ∑ ij : Fin N × Fin n, ‖iteratedFDeriv ℝ r (fun y ↦ f y ij.1 ij.2) x‖ := by
  let π : Matrix (Fin N) (Fin n) ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (N*n)) :=
    { (SingleChannel.matrixChannelEquiv N n).toLinearEquiv.restrictScalars ℝ with
      norm_map' := (SingleChannel.matrixChannelEquiv N n).norm_map }
  have h := vectorJet_norm_le_coordinate_sum (π.contDiff.contDiffAt.comp x hf) r
  rw [π.norm_iteratedFDeriv_comp_left f x r] at h
  apply h.trans_eq
  change (∑ i : Fin (N*n), ‖iteratedFDeriv ℝ r
    (fun y ↦ f y (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) x‖) = _
  exact Equiv.sum_comp finProdFinEquiv.symm
    (fun ij : Fin N × Fin n ↦ ‖iteratedFDeriv ℝ r (fun y ↦ f y ij.1 ij.2) x‖)

/-- Reassemble the sharp coordinate profiles in the full matrix seminorm.
This is the original preparation/sampling norm, and the arbitrary common
derivative reserve is unchanged (`app:ch_mean_pairs:eq:mean-prepared-scalar`,
`app:ch_waves:eq:individual-raw-slice`). -/
theorem fullParameterMatrix_cNorm_le_coordinate_profile {n d N : ℕ}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d))} (hΩ : IsOpen Ω)
    {f : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin N) (Fin n) ℂ}
    (hf : ContDiffOn ℝ ∞ f Ω) (B : ℕ → ℝ) (hB : ∀ r, 0 ≤ B r)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 1 ≤ K) (reserve m : ℕ)
    (hcoord : ∀ l i r, r ≤ m → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun y ↦ f y l i) x‖ ≤ B r * A * K^(r-reserve))
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean d))} (hJ : J ⊆ Ω) :
    (∀ r ≤ m, ∀ x ∈ J, ‖iteratedFDeriv ℝ r f x‖ ≤
      (N*n : ℕ) * B r * A * K^(r-reserve)) ∧
    cNorm J m f ≤ ((N*n : ℕ) * ∑ r ∈ Finset.range (m+1), B r) * A * K^(m-reserve) := by
  have hj r (hr : r ≤ m) x (hx : x ∈ J) : ‖iteratedFDeriv ℝ r f x‖ ≤
      (N*n : ℕ) * B r * A * K^(r-reserve) := by
    apply (norm_fullParameterMatrixJet_le_sum_coordinates
      (hf.contDiffAt (hΩ.mem_nhds (hJ hx))) r).trans
    have h := Finset.sum_le_sum (fun (ij : Fin N × Fin n) (_ : ij ∈ Finset.univ) ↦
      hcoord ij.1 ij.2 r hr x (hJ hx))
    simpa [Fintype.card_prod, mul_assoc] using h
  refine ⟨hj, ?_⟩
  have hb r (hr : r ≤ m) x (hx : x ∈ J) : ‖iteratedFDeriv ℝ r f x‖ ≤
      (N*n : ℕ) * B r * A * K^(m-reserve) :=
    (hj r hr x hx).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hK (Nat.sub_le_sub_right hr reserve))
      (mul_nonneg (mul_nonneg (by positivity) (hB r)) hA))
  have h := cNorm_le_sum_of_bounds (s := J) (r := m)
    (fun r _ ↦ mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hB r)) hA)
      (pow_nonneg (zero_le_one.trans hK) _)) hb
  simpa only [Finset.sum_mul, Finset.mul_sum] using h

end JanetCartan.CanonicalAtomRealization
