module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Grades.Phase

/-!
# Primitive source jets of the original carrier phases

The source integration in `app:ch_response:lem:energy-carrier-jets` uses the
actual graph phase, specialized to `EvolutionIntegral.elapsedPhase Ψ t` by the
parent. The forward affine Fourier term disappears only above first order.
The adjoint retains every derivative of that actual graph phase. These lemmas
supply the phase inputs to `Localization.norm_vector_oscillatory_integral_le`;
no differentiated kernel estimate is a premise.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Higher source jets of the forward carrier phase in
`app:ch_response:lem:energy-carrier-jets`, retaining the factor `λ`. Only local
smoothness of the original carrier at the source point is needed. -/
theorem iteratedFDeriv_forwardCarrierSourcePhase
    (Θ : E → E → ℝ) (φ : E → ℝ) (lam : ℝ) (x ξ z : E)
    (hφ : ContDiffAt ℝ ∞ φ z) (j : ℕ) (hj : 1 ≤ j) :
    iteratedFDeriv ℝ (j + 1) (forwardCarrierSourcePhase Θ φ lam x ξ) z =
      lam • iteratedFDeriv ℝ (j + 1) φ z := by
  let ℓ : E → ℝ := fun y => Θ x ξ - inner ℝ y ξ
  have hℓ : ContDiff ℝ ∞ ℓ :=
    contDiff_const.sub (contDiff_id.inner ℝ contDiff_const)
  have hd : fderiv ℝ ℓ = fun _ => -(InnerProductSpace.toDual ℝ E ξ) := by
    funext y
    have h := (hasFDerivAt_const (Θ x ξ) y).sub
      ((InnerProductSpace.toDual ℝ E ξ).hasFDerivAt (x := y))
    have he : ℓ = (fun _ => Θ x ξ) - (InnerProductSpace.toDual ℝ E ξ : E → ℝ) := by
      funext w
      simp [ℓ, real_inner_comm]
    rw [he, h.fderiv]
    simp
  have hz : iteratedFDeriv ℝ (j + 1) ℓ z = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv, hd,
      iteratedFDeriv_const_of_ne (by omega : j ≠ 0), Pi.zero_apply, norm_zero]
  change iteratedFDeriv ℝ (j + 1) (ℓ + fun y => lam • φ y) z = _
  rw [iteratedFDeriv_add_apply (hℓ.contDiffAt.of_le (by simp))
      ((hφ.const_smul lam).of_le (by simp)), hz, zero_add,
    iteratedFDeriv_const_smul_apply' (hφ.of_le (by simp))]

/-- All positive source jets of the literal adjoint phase retain the
derivatives of `Θ(z,ξ)` (`app:ch_response:lem:energy-carrier-jets`). -/
theorem iteratedFDeriv_adjointCarrierSourcePhase
    (Θ : E → E → ℝ) (φ : E → ℝ) (lam : ℝ) (x ξ z : E)
    (hΘ : ContDiffAt ℝ ∞ (fun y => Θ y ξ) z) (hφ : ContDiffAt ℝ ∞ φ z)
    (j : ℕ) (hj : 1 ≤ j) :
    iteratedFDeriv ℝ j (adjointCarrierSourcePhase Θ φ lam x ξ) z =
      lam • iteratedFDeriv ℝ j φ z - iteratedFDeriv ℝ j (fun y => Θ y ξ) z := by
  have hc : ContDiffAt ℝ ∞ (fun _ : E => inner ℝ x ξ) z := contDiffAt_const
  change iteratedFDeriv ℝ j
    (((fun _ => inner ℝ x ξ) - fun y => Θ y ξ) + fun y => lam • φ y) z = _
  rw [iteratedFDeriv_add_apply
      (f := (fun _ => inner ℝ x ξ) - fun y => Θ y ξ) (g := fun y => lam • φ y)
      ((hc.sub hΘ).of_le (by simp))
      ((hφ.const_smul lam).of_le (by simp)),
    iteratedFDeriv_sub_apply (f := fun _ => inner ℝ x ξ) (g := fun y => Θ y ξ)
      (hc.of_le (by simp))
      (hΘ.of_le (by simp)),
    iteratedFDeriv_const_of_ne (by omega : j ≠ 0), Pi.zero_apply, zero_sub,
    iteratedFDeriv_const_smul_apply' (hφ.of_le (by simp))]
  abel

/-- The primitive carrier gradient upper bound supplies the full-frequency
forward upper bound, including bounded and high-pass frequencies. -/
theorem norm_fderiv_forwardCarrierSourcePhase_le
    (Θ : E → E → ℝ) (φ : E → ℝ) {lam B : ℝ} (hlam : 0 ≤ lam)
    (x ξ z : E) (hφ : DifferentiableAt ℝ φ z) (hb : ‖fderiv ℝ φ z‖ ≤ B) :
    ‖fderiv ℝ (forwardCarrierSourcePhase Θ φ lam x ξ) z‖ ≤
      (B + 1) * (lam + ‖ξ‖) := by
  rw [fderiv_forwardCarrierSourcePhase Θ φ lam x ξ z hφ]
  have hB := (norm_nonneg _).trans hb
  calc
    _ ≤ ‖lam • fderiv ℝ φ z‖ + ‖InnerProductSpace.toDual ℝ E ξ‖ := norm_sub_le _ _
    _ = lam * ‖fderiv ℝ φ z‖ + ‖ξ‖ := by simp [norm_smul, abs_of_nonneg hlam]
    _ ≤ lam * B + ‖ξ‖ := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hB (norm_nonneg ξ)]

/-- The original radial comparison supplies the adjoint upper bound. Together
with `adjointCarrierSourcePhase_gap` this supplies both gradient hypotheses of
the existing nonstationary source calculus. -/
theorem norm_fderiv_adjointCarrierSourcePhase_le
    (Θ : E → E → ℝ) (φ : E → ℝ) {lam B M : ℝ}
    (hlam : 0 ≤ lam) (hM : 0 ≤ M) (x ξ z : E)
    (hφ : DifferentiableAt ℝ φ z) (hΘ : DifferentiableAt ℝ (fun y => Θ y ξ) z)
    (hb : ‖fderiv ℝ φ z‖ ≤ B)
    (hΘb : ‖fderiv ℝ (fun y => Θ y ξ) z‖ ≤ M * ‖ξ‖) :
    ‖fderiv ℝ (adjointCarrierSourcePhase Θ φ lam x ξ) z‖ ≤
      (B + M) * (lam + ‖ξ‖) := by
  rw [fderiv_adjointCarrierSourcePhase Θ φ lam x ξ z hφ hΘ]
  have hB := (norm_nonneg _).trans hb
  calc
    _ ≤ ‖lam • fderiv ℝ φ z‖ + ‖fderiv ℝ (fun y => Θ y ξ) z‖ := norm_sub_le _ _
    _ = lam * ‖fderiv ℝ φ z‖ + ‖fderiv ℝ (fun y => Θ y ξ) z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
    _ ≤ lam * B + M * ‖ξ‖ := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hB (norm_nonneg ξ), mul_nonneg hM hlam]

/-- Original carrier jets at scale `L` supply the forward source phase budget
at scale `K`, preserving `L ≤ K` from `app:ch_response:eq:direct-envelope-profile`.
The phase profile is independent of the integration order. -/
theorem norm_iteratedFDeriv_forwardCarrierSourcePhase_le
    (Θ : E → E → ℝ) (φ : E → ℝ) {lam L K : ℝ}
    (hlam : 0 ≤ lam) (hL : 0 ≤ L) (hLK : L ≤ K)
    (x ξ z : E) (hφ : ContDiffAt ℝ ∞ φ z)
    (Pφ : ℕ → ℝ) (hPφ : ∀ j, 0 ≤ Pφ j)
    (hφj : ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ (j + 1) φ z‖ ≤ Pφ j * L ^ j)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ (j + 1) (forwardCarrierSourcePhase Θ φ lam x ξ) z‖ ≤
      Pφ j * (lam + ‖ξ‖) * K ^ j := by
  rw [iteratedFDeriv_forwardCarrierSourcePhase Θ φ lam x ξ z hφ j hj,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
  have hp := hPφ j
  calc
    _ ≤ lam * (Pφ j * L ^ j) := mul_le_mul_of_nonneg_left (hφj j hj) hlam
    _ ≤ (lam + ‖ξ‖) * (Pφ j * K ^ j) := by
      gcongr
      exact le_add_of_nonneg_right (norm_nonneg ξ)
    _ = _ := by ring

/-- Original graph and carrier jets give the literal adjoint source phase
budget at scale `K`. All frequencies are allowed; `Θ` is never replaced by a
phase increment (`app:ch_response:lem:energy-carrier-jets`). -/
theorem norm_iteratedFDeriv_adjointCarrierSourcePhase_le
    (Θ : E → E → ℝ) (φ : E → ℝ) {lam L K : ℝ}
    (hlam : 0 ≤ lam) (hL : 0 ≤ L) (hLK : L ≤ K)
    (x ξ z : E) (hΘ : ContDiffAt ℝ ∞ (fun y => Θ y ξ) z)
    (hφ : ContDiffAt ℝ ∞ φ z) (Pφ PΘ : ℕ → ℝ)
    (hPφ : ∀ j, 0 ≤ Pφ j) (hPΘ : ∀ j, 0 ≤ PΘ j)
    (hφj : ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ (j + 1) φ z‖ ≤ Pφ j * L ^ j)
    (hΘj : ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (fun y => Θ y ξ) z‖ ≤ PΘ j * ‖ξ‖ * L ^ j)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ (j + 1) (adjointCarrierSourcePhase Θ φ lam x ξ) z‖ ≤
      (Pφ j + PΘ j) * (lam + ‖ξ‖) * K ^ j := by
  rw [iteratedFDeriv_adjointCarrierSourcePhase Θ φ lam x ξ z hΘ hφ (j + 1) (by omega)]
  have hp := hPφ j
  have hq := hPΘ j
  calc
    _ ≤ ‖lam • iteratedFDeriv ℝ (j + 1) φ z‖ +
        ‖iteratedFDeriv ℝ (j + 1) (fun y => Θ y ξ) z‖ := norm_sub_le _ _
    _ = lam * ‖iteratedFDeriv ℝ (j + 1) φ z‖ +
        ‖iteratedFDeriv ℝ (j + 1) (fun y => Θ y ξ) z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
    _ ≤ lam * (Pφ j * L ^ j) + PΘ j * ‖ξ‖ * L ^ j := by gcongr; exact hφj j hj; exact hΘj j hj
    _ ≤ (Pφ j + PΘ j) * (lam + ‖ξ‖) * L ^ j := by
      nlinarith [mul_nonneg (mul_nonneg (hPφ j) (norm_nonneg ξ)) (pow_nonneg hL j),
        mul_nonneg (mul_nonneg (hPΘ j) hlam) (pow_nonneg hL j)]
    _ ≤ _ := by gcongr

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
