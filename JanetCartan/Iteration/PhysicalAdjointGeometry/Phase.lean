module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.Basic

/-!
# Exact identification with the raw divided phase

The phase in `app:ch_mean_pairs:eq:raw-adjoint-moments` is the literal difference
of the same Hamilton phase at `ζ + τ η` and `ζ`, divided by `τ`. The averaged
coefficient below agrees with that phase, without any homogeneity hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff InnerProductSpace

namespace JanetCartan.PhysicalAdjointGeometry

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}

/-- Identification of the jointly constructed coefficient with the original
covector gradient average (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem averagedCovector_eq_averagedPhaseGradient
    {S : X × Euclidean m → ℝ} {Ω : Set (X × Euclidean m)}
    (hΩ : IsOpen Ω) (hS : ContDiffOn ℝ ∞ S Ω) (q : Point X m)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, segment t q ∈ Ω) :
    averagedCovector S q =
      averagedPhaseGradient (fun x ζ ↦ S (x, ζ)) q.1 (q.2.1 + q.2.2) q.2.1 := by
  unfold averagedCovector averagedPhaseGradient
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [covectorGradient_eq_gradient
    ((hS.contDiffAt (hΩ.mem_nhds (hseg t (by simpa using ht)))).differentiableAt (by simp))]
  simp only [segment_apply, add_sub_cancel_left]

/-- The literal raw quotient equals `Y · η` on the original phase chart.
The same statement works for every nonzero inverse frequency of either sign;
there is no homogeneous phase substitution
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem rawPhase_eq_inner_averagedCovector
    {S : X × Euclidean m → ℝ} {B : Set X} {D : Set (Euclidean m)}
    (hB : IsOpen B) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hS : ContDiffOn ℝ ∞ S (B ×ˢ D)) {x : X} (hx : x ∈ B)
    {ζ η : Euclidean m} {τ : ℝ} (hζ : ζ ∈ D) (hshift : ζ + τ • η ∈ D)
    (hτ : τ ≠ 0) :
    (S (x, ζ + τ • η) - S (x, ζ)) / τ =
      inner ℝ (averagedCovector S (x, ζ, τ • η)) η := by
  have hs : ContDiffOn ℝ 1 (fun ξ ↦ S (x, ξ)) D :=
    (hS.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hξ ↦ ⟨hx, hξ⟩)).of_le (by simp)
  have he := averagedCovector_eq_averagedPhaseGradient (hB.prod hD) hS
    (x, ζ, τ • η) (fun t ht ↦ ⟨hx, hcD.add_smul_mem hζ hshift ht⟩)
  rw [he]
  exact (phase_div_eq_phaseShiftQuotient (S := fun x ζ ↦ S (x, ζ)) (p := x)
    hD hcD hs hζ hshift hτ).trans
    (phaseShiftQuotient_eq_inner_averagedPhaseGradient (S := fun x ζ ↦ S (x, ζ))
      (p := x) hD hcD hs hζ hshift)

/-- Normalizing by the frozen input frequency costs no physical derivative
and introduces no input-band loss. It is used by the existing binary phase
branches (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_normalized_phase_le
    {Y : Point X m → Euclidean m} {q : Point X m}
    (hY : ContDiffAt ℝ ∞ Y q) {η : Euclidean m} (hη : η ≠ 0) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun w ↦ inner ℝ (Y w) η / ‖η‖) q‖ ≤
      ‖iteratedFDeriv ℝ j Y q‖ := by
  let A : Euclidean m →L[ℝ] ℝ := ‖η‖⁻¹ • innerSL ℝ η
  have hA : ‖A‖ ≤ 1 := by
    apply A.opNorm_le_bound zero_le_one
    intro v
    change ‖‖η‖⁻¹ • inner ℝ η v‖ ≤ 1 * ‖v‖
    rw [norm_smul, norm_inv, norm_norm, one_mul]
    calc
      _ ≤ ‖η‖⁻¹ * (‖η‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hη), one_mul]
  have he : (fun w ↦ inner ℝ (Y w) η / ‖η‖) = A ∘ Y := by
    funext w
    simp [A, real_inner_comm, div_eq_mul_inv, mul_comm]
  rw [he]
  exact (A.norm_iteratedFDeriv_comp_left hY (by simp)).trans
    (by simpa using mul_le_mul_of_nonneg_right hA (norm_nonneg (iteratedFDeriv ℝ j Y q)))

end JanetCartan.PhysicalAdjointGeometry
