module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.PhaseJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.PhaseProfiles

/-!
# Source phase budgets from original two-time derivatives

The affine time term has no derivatives of order at least two. The original
joint two-time phase therefore supplies the source grades required by repeated
integration by parts without an additional power of the physical scale.
Consumer: the literal kernel profile in `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open AmplitudeJets AmplitudeJets.PhaseProfiles
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)

set_option backward.isDefEq.respectTransparency false in
/-- At orders at least two the literal elapsed phase is bounded by the
original two-time jet at the same order, with no derivative of the affine
Fourier time term. Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_iteratedFDeriv_elapsedPhase_source_le
    {O : Set (TwoTimePoint d)} (hO : IsOpen O)
    (Ψ : TwoTimePhase d) (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) O)
    (t : ℝ) (ξ z : E) (hz : elapsedPoint t ((z, 0), ξ) ∈ O)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ (k + 1) (fun y => elapsedPhase Ψ t y ξ) z‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) (jointPhase Ψ) (elapsedPoint t ((z, 0), ξ))‖ := by
  let f : E → ℝ := fun y => jointPhase Ψ (elapsedPoint t ((y, 0), ξ))
  have hf : ContDiffAt ℝ ∞ f z := by
    change ContDiffAt ℝ ∞ (jointPhase Ψ ∘ (fun y : E => elapsedPoint t ((y, 0), ξ))) z
    apply (hΨ.contDiffAt (hO.mem_nhds hz)).comp z
    have hemap : (fun y : E => elapsedPoint t ((y, 0), ξ)) =
        fun y => (elapsedLinear.comp positionInsertion) y + elapsedPoint t ((0, 0), ξ) := by
      funext y
      exact elapsedPoint_fixedFrequency_eq t ξ y
    rw [hemap]
    exact ((elapsedLinear.comp positionInsertion).contDiff.add contDiff_const).contDiffAt
  let l : E →L[ℝ] ℝ := (ξ 0) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (d + 1)) 0
  have ht : (fun y : E => (y 0 - t) * ξ 0) = fun y => l y + (-t * ξ 0) := by
    funext y
    change (y 0 - t) * ξ 0 = ξ 0 * y 0 + (-t * ξ 0)
    ring
  have htime : ContDiff ℝ ∞ (fun y : E => (y 0 - t) * ξ 0) := by
    rw [ht]
    exact l.contDiff.add contDiff_const
  have hd : fderiv ℝ (fun y : E => (y 0 - t) * ξ 0) = fun _ => l := by
    rw [ht]
    funext y
    simp
  have hztime : iteratedFDeriv ℝ (k + 1) (fun y : E => (y 0 - t) * ξ 0) z = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv, hd,
      iteratedFDeriv_const_of_ne (by omega : k ≠ 0), Pi.zero_apply, norm_zero]
  have he : (fun y => elapsedPhase Ψ t y ξ) = (fun y : E => (y 0 - t) * ξ 0) + f := by
    funext y
    simp [elapsedPhase, f, jointPhase]
  rw [he, iteratedFDeriv_add_apply (htime.contDiffAt.of_le (by simp))
    (hf.of_le (by simp)), hztime, zero_add]
  have ha := norm_iteratedFDeriv_preAffine_le (elapsedLinear.comp positionInsertion)
    (elapsedPoint t ((0, 0), ξ)) hO hΨ
    (by rwa [← elapsedPoint_fixedFrequency_eq]) (k + 1)
  simp_rw [← elapsedPoint_fixedFrequency_eq] at ha
  have hpow := pow_le_one₀ (norm_nonneg _)
    (norm_elapsedLinear_positionInsertion_le (d := d)) (n := k + 1)
  exact ha.trans (by simpa using (mul_le_mul_of_nonneg_left hpow
    (norm_nonneg (iteratedFDeriv ℝ (k + 1) (jointPhase Ψ) (elapsedPoint t ((z, 0), ξ))))))

variable {P : Type}

set_option backward.isDefEq.respectTransparency false in
/-- Source differentiation ignores only the constant output demodulation
term; external derivatives remain in the normalized amplitude.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem fderiv_annularExternalPhase
    (adj demod : Bool) (Θ : E → E → ℝ) (φ : P → E → ℝ)
    (lam : ℝ) (ξ : E) (p : P × E) (z : E)
    (hψ : DifferentiableAt ℝ
      (if adj then adjointCarrierSourcePhase Θ (φ p.1) lam p.2 ξ
        else forwardCarrierSourcePhase Θ (φ p.1) lam p.2 ξ) z) :
    fderiv ℝ (annularExternalPhase adj demod Θ φ lam ξ p) z =
      fderiv ℝ (if adj then adjointCarrierSourcePhase Θ (φ p.1) lam p.2 ξ
        else forwardCarrierSourcePhase Θ (φ p.1) lam p.2 ξ) z := by
  have he : annularExternalPhase adj demod Θ φ lam ξ p =
      (if adj then adjointCarrierSourcePhase Θ (φ p.1) lam p.2 ξ
        else forwardCarrierSourcePhase Θ (φ p.1) lam p.2 ξ) -
      fun _ => if demod then lam * φ p.1 p.2 else 0 := by
    funext w
    cases adj <;> rfl
  rw [he, fderiv_sub hψ (differentiableAt_const (if demod then lam * φ p.1 p.2 else 0)),
    (hasFDerivAt_const (if demod then lam * φ p.1 p.2 else 0) z).fderiv, sub_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The two observations have identical positive source jets. Consumer:
the original-primitive kernel profile (`energy-carrier-jets`). -/
theorem iteratedFDeriv_annularExternalPhase_source
    (adj demod : Bool) (Θ : E → E → ℝ) (φ : P → E → ℝ)
    (lam : ℝ) (ξ : E) (p : P × E) (z : E)
    (hψ : ContDiffAt ℝ ∞
      (if adj then adjointCarrierSourcePhase Θ (φ p.1) lam p.2 ξ
        else forwardCarrierSourcePhase Θ (φ p.1) lam p.2 ξ) z)
    (k : ℕ) (hk : k ≠ 0) :
    iteratedFDeriv ℝ k (annularExternalPhase adj demod Θ φ lam ξ p) z =
      iteratedFDeriv ℝ k (if adj then adjointCarrierSourcePhase Θ (φ p.1) lam p.2 ξ
        else forwardCarrierSourcePhase Θ (φ p.1) lam p.2 ξ) z := by
  have he : annularExternalPhase adj demod Θ φ lam ξ p =
      (if adj then adjointCarrierSourcePhase Θ (φ p.1) lam p.2 ξ
        else forwardCarrierSourcePhase Θ (φ p.1) lam p.2 ξ) -
      fun _ => if demod then lam * φ p.1 p.2 else 0 := by
    funext w
    cases adj <;> rfl
  rw [he, iteratedFDeriv_sub_apply (hψ.of_le (by simp))
      (contDiffAt_const (c := if demod then lam * φ p.1 p.2 else 0)),
    iteratedFDeriv_const_of_ne hk, Pi.zero_apply, sub_zero]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
