module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedElapsed

/-!
# Continuous phase-weighted compact elapsed amplitudes

The phase is used only near the original output and conic supports, and the
elapsed parameter is clamped to the fixed slab. This auxiliary amplitude is
used only for kernel integrability, without any claim of symbol estimates.
Source: `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
/-- Supported regularity gives a globally continuous phase-weighted compact
amplitude after clamping elapsed time. Consumers: the compact forward kernels
and the reverse time-triangle Fubini in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem continuous_supported_elapsed_phaseWeightedAmplitude
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : Continuous χsource) (hβ : Continuous β)
    (θ : E → ℂ) (hθ : Continuous θ)
    : Continuous (fun p : ((ℝ × E) × E) × E ↦
      Complex.exp (Complex.I * (elapsedPhase Ψ (max 0 (min Δ p.1.1.1)) p.1.1.2 p.2 : ℂ)) •
        frequencyCutFullAmplitude θ
          (elapsedAmplitude b χout χsource β (max 0 (min Δ p.1.1.1))) p.1.1.2 p.1.2 p.2) := by
  let c : ℝ → ℝ := fun r ↦ max 0 (min Δ r)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcmem (r : ℝ) : c r ∈ Icc 0 Δ :=
    ⟨le_max_left _ _, max_le hΔ (min_le_left _ _)⟩
  let S := fun r ↦ elapsedPhase Ψ (c r)
  let A := fun r ↦ frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β (c r))
  have hS : ∀ r x ξ, x ∈ tsupport χout → ξ ∈ tsupport β →
      ContinuousAt (fun p : (ℝ × E) × E ↦ S p.1.1 p.1.2 p.2) ((r, x), ξ) := by
    intro r x ξ hx hξ
    have ht : Continuous (fun p : (ℝ × E) × E ↦ p.1.2 0) := by fun_prop
    have ht' := ht.sub (hc.comp continuous_fst.fst)
    have hp := (ht.prodMk ht').prodMk
      ((continuous_spatialPart.comp continuous_fst.snd).prodMk
        (continuous_spatialPart.comp continuous_snd))
    exact (ht'.continuousAt.mul (by fun_prop)).add
      ((hΨ (c r) (hcmem r) x hx ξ hξ).comp (x := ((r, x), ξ))
        (f := fun p : (ℝ × E) × E ↦ ((p.1.2 0, p.1.2 0 - c p.1.1),
          (spatialPart p.1.2, spatialPart p.2))) hp.continuousAt)
  have hA : ∀ r x z ξ, x ∈ tsupport χout → ξ ∈ tsupport β →
      ContinuousAt (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.1.1.2 p.1.2 p.2)
        (((r, x), z), ξ) := by
    intro r x z ξ hx hξ
    have ht : Continuous (fun p : ((ℝ × E) × E) × E ↦ p.1.1.2 0) := by fun_prop
    have hp := (ht.prodMk (ht.sub (hc.comp continuous_fst.fst.fst))).prodMk
      ((continuous_spatialPart.comp continuous_fst.fst.snd).prodMk
        (continuous_spatialPart.comp continuous_snd))
    have hb' := (hb (c r) (hcmem r) x hx ξ hξ).comp (x := (((r, x), z), ξ))
      (f := fun p : ((ℝ × E) × E) × E ↦ ((p.1.1.2 0, p.1.1.2 0 - c p.1.1.1),
        (spatialPart p.1.1.2, spatialPart p.2))) hp.continuousAt
    exact (hθ.comp continuous_snd).continuousAt.smul
      ((((ho.comp continuous_fst.fst.snd).mul (hs.comp continuous_fst.snd)).mul
        (hβ.comp continuous_snd)).continuousAt.smul hb')
  have hsF : ∀ r x z ξ, x ∉ tsupport χout ∨ ξ ∉ tsupport β → A r x z ξ = 0 := by
    intro r x z ξ h
    rcases h with h | h <;>
      simp [A, frequencyCutFullAmplitude, elapsedAmplitude, image_eq_zero_of_notMem_tsupport h]
  have hW := continuous_supported_phaseWeightedAmplitude S A
    (isClosed_tsupport χout) (isClosed_tsupport β) hS hA hsF
  exact hW

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
