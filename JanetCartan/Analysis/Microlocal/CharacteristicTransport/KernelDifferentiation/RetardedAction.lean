module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.RetardedCalculus
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.CompactKernel
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.RetardedFourier

/-!
# Differentiation of the literal finite-cutoff retarded Fourier action

This is the finite-frequency connection needed for
`app:ch_regular_base:eq:energy-complete-residual`. The time endpoint, the
zeroth-order coefficient, and the output-mask commutator are retained.
The datum may be exactly `graphTestToSchwartz (complexSourceMaskTest χsource hs u)`
from `integral_cut_elapsedGraph_eq_retardedFourier`; no input mask is moved.
This file does not assert the uncut solver or any residual estimate.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.KernelDifferentiation
open WKB RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ

/-- Differentiation of the actual finite-cutoff retarded kernel. The derivative
under the integral fixes source time `s` (including the initial Fourier slice).
The coefficient `C x 0` is precisely `A_t`, and `D` is `B₀` in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem firstOrderApply_retarded_cutFixedTimeFourier
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E FV)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (C : E → Fin (d + 1) → FV →L[ℂ] FV) (D : E → FV →L[ℂ] FV)
    (a : ℝ) (x : E) :
    firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ ∫ s in a..y 0, cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)) x =
      C x 0 (cutFixedTimeFourier Ψ b β θ v (x 0) (x 0) (spatialPart x)) +
        ∫ s in a..x 0,
          firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
            (fun y ↦ cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)) x :=
  firstOrderApply_retardedPrimitive
    (contDiff_cutFixedTimeFourier Ψ b β θ v hΨ hb hβ hθ hθcs) C D a x

/-- The output cutoff contributes its explicit commutator away from its
plateau. The source-masked datum is the same `v` in every term. This is a
finite-cutoff identity for `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem firstOrderApply_masked_retarded_cutFixedTimeFourier
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ χout : E → ℂ)
    (v : SchwartzMap E FV)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (C : E → Fin (d + 1) → FV →L[ℂ] FV) (D : E → FV →L[ℂ] FV)
    (a : ℝ) (x : E) (hout : DifferentiableAt ℝ χout x) :
    firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ χout y • ∫ s in a..y 0,
        cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)) x =
      (∑ j, partialDeriv χout x j • C x j
        (∫ s in a..x 0, cutFixedTimeFourier Ψ b β θ v (x 0) s (spatialPart x))) +
      χout x • (C x 0 (cutFixedTimeFourier Ψ b β θ v (x 0) (x 0) (spatialPart x)) +
        ∫ s in a..x 0,
          firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
            (fun y ↦ cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)) x) := by
  have hg := contDiff_cutFixedTimeFourier Ψ b β θ v hΨ hb hβ hθ hθcs
  have hd : DifferentiableAt ℝ (fun y ↦ ∫ s in a..y 0,
      cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)) x := by
    exact (((contDiff_retardedPrimitive hg a).comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.prodMk
        contDiff_id)).differentiable (by simp)) x
  rw [RegularSector.Characteristic.firstOrderApply_smul _ _ hout hd,
    firstOrderApply_retarded_cutFixedTimeFourier Ψ b β θ v hΨ hb hβ hθ hθcs C D a x]
  rfl

/-- On a genuine measurement plateau the output-mask commutator vanishes.
This is the local constant-mask fact used with the previous finite-cutoff
identity, not a removal of any source or low-frequency mask
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem outputMask_commutator_eq_zero_of_plateau (χout : E → ℂ)
    (C : E → Fin (d + 1) → FV →L[ℂ] FV) (x : E) (w : FV)
    (hplateau : χout =ᶠ[𝓝 x] fun _ ↦ (1 : ℂ)) :
    (∑ j, partialDeriv χout x j • C x j w) = 0 := by
  simp [partialDeriv, hplateau.fderiv_eq]

/-- The diagonal phase identifies the upper endpoint with the spatial PDO
acting on the very same temporal `θ β` Fourier slice on its right. All Fourier
normalizations are the published ones
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem cutFixedTimeFourier_diagonal (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (β θ : E → ℂ) (v : SchwartzMap E FV)
    (hdiag : ∀ t y η, Ψ t t y η = inner ℝ y η) (t : ℝ) (y : Euclidean d) :
    cutFixedTimeFourier Ψ b β θ v t t y =
      ((2 * Real.pi)^d : ℂ)⁻¹ • ∫ η,
        Complex.exp (Complex.I * (inner ℝ y η : ℂ)) •
          (b t t y η).mulVec (cutTemporalFourierSlice β θ v t η) := by
  simp only [cutFixedTimeFourier, hdiag]

end JanetCartan.CharacteristicTransport.KernelDifferentiation
