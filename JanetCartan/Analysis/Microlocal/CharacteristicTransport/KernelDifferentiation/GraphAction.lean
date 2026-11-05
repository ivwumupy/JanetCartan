module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.Cancellation

/-! # Differentiation of the published fixed-slab graph action

Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.KernelDifferentiation
open WKB FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ

/-- The complete finite-cutoff derivative identity for the literal published
fixed-slab graph integral on the open slab. The input is exactly the original
source-masked test, all masks retain their order, and the right side keeps the
upper endpoint and the output commutator. The pointwise column identity is
produced by `firstOrder_directCorrection_identity`, with residual `r = P W₁`.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
This is not an uncut residual or a residual estimate. -/
theorem firstOrderApply_cut_elapsedGraphIntegral (Ψ : TwoTimePhase d) (b r : TwoTimeAmplitude d q)
    (χout χsource β θ : E → ℂ)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hscs : HasCompactSupport χsource) (hθcs : HasCompactSupport θ)
    (a Δ : ℝ) (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (u : graphTestSpace (d + 1) q)
    (C : E → Fin (d + 1) → FV →L[ℂ] FV) (D : E → FV →L[ℂ] FV)
    (x : E) (hat : a < x 0) (htΔ : x 0 - a < Δ)
    (hcancel : ∀ s η j, firstOrderApply
      (fun y i ↦ (C y i).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ b (y 0) s (spatialPart y) η i j)) x =
      Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        (fun i ↦ r (x 0) s (spatialPart x) η i j)) :
    let v := graphTestToSchwartz (complexSourceMaskTest χsource hs u)
    firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ ∫ ρ in Icc 0 Δ, graphOperator (elapsedPhase Ψ ρ)
        (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β ρ))
        (fun z ↦ (u.val z).ofLp) y) x =
      (∑ j, partialDeriv χout x j • C x j
        (∫ s in a..x 0, cutFixedTimeFourier Ψ b β θ v (x 0) s (spatialPart x))) +
      χout x • (C x 0 (cutFixedTimeFourier Ψ b β θ v (x 0) (x 0) (spatialPart x)) +
        ∫ s in a..x 0, cutFixedTimeFourier Ψ r β θ v (x 0) s (spatialPart x)) := by
  dsimp only
  let v := graphTestToSchwartz (complexSourceMaskTest χsource hs u)
  have ht : Continuous (fun y : E ↦ y 0) := by fun_prop
  have hn : {y : E | a < y 0 ∧ y 0 - a < Δ} ∈ 𝓝 x :=
    ((isOpen_lt (continuous_const (y := a)) ht).inter
      (isOpen_lt (ht.sub continuous_const) (continuous_const (y := Δ)))).mem_nhds ⟨hat, htΔ⟩
  have he : (fun y ↦ ∫ ρ in Icc 0 Δ, graphOperator (elapsedPhase Ψ ρ)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β ρ))
      (fun z ↦ (u.val z).ofLp) y) =ᶠ[𝓝 x]
      (fun y ↦ χout y • ∫ s in a..y 0,
        cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)) := by
    filter_upwards [hn] with y hy
    rw [integral_cut_elapsedGraph_eq_retardedFourier Ψ b χout χsource β θ
      hΨ.continuous hb.continuous ho.continuous hs hβ.continuous hθ.continuous
      hscs hθcs a Δ hzero u y hy.1.le hy.2.le,
      intervalIntegral.integral_smul]
  have hp : firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ ∫ ρ in Icc 0 Δ, graphOperator (elapsedPhase Ψ ρ)
        (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β ρ))
        (fun z ↦ (u.val z).ofLp) y) x =
      firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
        (fun y ↦ χout y • ∫ s in a..y 0,
          cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)) x := by
    simp only [firstOrderApply, partialDeriv, he.fderiv_eq, he.eq_of_nhds]
  rw [hp]
  exact firstOrderApply_masked_retarded_of_column_cancellation
    Ψ b r β θ χout v hΨ hb hβ hθ hθcs C D a x
    (ho.differentiable (by simp) x) hcancel
end JanetCartan.CharacteristicTransport.KernelDifferentiation
