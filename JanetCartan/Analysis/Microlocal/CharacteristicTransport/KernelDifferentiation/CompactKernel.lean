module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.MultiplierSlices.TemporalSchwartz
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.Differential

/-!
# Smoothness of the literal finite-frequency kernel

For `app:ch_regular_base:eq:energy-complete-residual`, the common compact
frequency mask supplies local integrability and domination. The Fourier
normalization and the source-masked Schwartz input are the published ones.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.KernelDifferentiation
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral FiniteChain.Retarded.KernelDecay
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- Primitive joint smoothness gives smoothness of the full spectral integrand.
Consumer: `contDiff_cutFixedTimeFourier`, for
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_cutFixedTimeFourierIntegrand (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E V)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ (fun p : (E × ℝ) × E ↦
      cutFixedTimeFourierIntegrand Ψ b β θ v (p.1.1 0) p.1.2
        (spatialPart p.1.1) p.2) := by
  have hc : ContDiff ℝ ∞ (fun p : (E × ℝ) × E ↦
      ((p.1.1 0, p.1.2), (spatialPart p.1.1, spatialPart p.2))) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp
      contDiff_fst.fst).prodMk contDiff_fst.snd).prodMk
      ((spatialPartCLM.contDiff.comp contDiff_fst.fst).prodMk
        (spatialPartCLM.contDiff.comp contDiff_snd))
  have hv : ContDiff ℝ ∞ (fun p : (E × ℝ) × E ↦
      (θ p.2 * β p.2) • sourceInputFourierTransform v p.2) :=
    ((hθ.comp contDiff_snd).mul (hβ.comp contDiff_snd)).smul
      (((sourceInputFourierTransform v).smooth ⊤).comp contDiff_snd)
  have hm : ContDiff ℝ ∞ (fun p : (E × ℝ) × E ↦
      (b (p.1.1 0) p.1.2 (spatialPart p.1.1) (spatialPart p.2)).mulVec
        ((θ p.2 * β p.2) • sourceInputFourierTransform v p.2)) := by
    apply contDiff_pi.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply ContDiff.sum
    intro j _
    let L := (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap
    exact (L.contDiff.comp (hb.comp hc)).mul (contDiff_pi.mp hv j)
  have he : ContDiff ℝ ∞ (fun p : (E × ℝ) × E ↦
      Complex.exp (Complex.I * (Ψ (p.1.1 0) p.1.2
        (spatialPart p.1.1) (spatialPart p.2) : ℂ))) :=
    ((contDiff_const (c := Complex.I)).mul (Complex.ofRealCLM.contDiff.comp
      (hΨ.comp hc))).cexp
  have ht : ContDiff ℝ ∞ (fun p : (E × ℝ) × E ↦
      Complex.exp (Complex.I * ((p.1.2 * p.2 0 : ℝ) : ℂ))) :=
    ((contDiff_const (c := Complex.I)).mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_fst.snd.mul ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp
        contDiff_snd)))).cexp
  exact ht.smul (he.smul hm)

/-- The actual finite-cutoff fixed-time action is jointly smooth in output and
source time. Compact frequency support supplies all integral hypotheses.
Consumer: retarded differentiation in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_cutFixedTimeFourier (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (β θ : E → ℂ) (v : SchwartzMap E V)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ) :
    ContDiff ℝ ∞ (fun p : E × ℝ ↦ cutFixedTimeFourier Ψ b β θ v
      (p.1 0) p.2 (spatialPart p.1)) := by
  have he (p : E × ℝ) := integral_cutFixedTimeFourier Ψ b β θ v
    (p.1 0) p.2 (spatialPart p.1)
    (hΨ.continuous.comp (f := fun η ↦ ((p.1 0,p.2),(spatialPart p.1,η)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    (hb.continuous.comp (f := fun η ↦ ((p.1 0,p.2),(spatialPart p.1,η)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    hβ.continuous hθ.continuous hθcs
  simp_rw [← he]
  apply ContDiff.const_smul
  apply contDiff_integral_commonCarrier
    (contDiff_cutFixedTimeFourierIntegrand Ψ b β θ v hΨ hb hβ hθ) hθcs
  intro p ξ hξ
  simp [cutFixedTimeFourierIntegrand, image_eq_zero_of_notMem_tsupport hξ]
end JanetCartan.CharacteristicTransport.KernelDifferentiation
