module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportRegularity

/-!
# Supported regularity for the actual elapsed regularizations

The primitive phase and symbol need be continuous only near the supported
physical/covector points and elapsed times in the fixed slab. Clamping the
parameter is used solely to obtain continuous compact representatives. On the
slab these are precisely the original kernels. The uncut consequences use the
exact finite test formulas, common LOW bound, and strong limits exported by
`exists_fullGraphFamily_of_wholeImage_phase`; the parent must instantiate that
producer, including all its geometric and quantitative inputs.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Forward and literal-adjoint cutoff orbits are measurable from primitive
regularity near the supported chart. No global extension or regularity at
spatial covector zero is assumed. The inputs `hreal` and `hrealAdj` have exactly
the signatures supplied by `exists_fullGraphFamily_of_wholeImage_phase`.
Consumer: the uncut strong limits in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem aestronglyMeasurable_supported_elapsed_regularizations
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : Continuous χsource) (hβ : Continuous β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, Continuous (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j))
    (Treg : ℕ → ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z)) (j : ℕ) (u : SpacetimeL2 d q) :
    AEStronglyMeasurable (fun r ↦ Treg j r u) (volume.restrict (Icc 0 Δ)) ∧
      AEStronglyMeasurable (fun r ↦ (Treg j r).adjoint u) (volume.restrict (Icc 0 Δ)) := by
  let c : ℝ → ℝ := fun r ↦ max 0 (min Δ r)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcmem (r : ℝ) : c r ∈ Icc 0 Δ :=
    ⟨le_max_left _ _, max_le hΔ (min_le_left _ _)⟩
  have hceq (r : ℝ) (hr : r ∈ Icc 0 Δ) : c r = r := by
    simp [c, min_eq_right hr.2, max_eq_right hr.1]
  let S := fun r ↦ elapsedPhase Ψ (c r)
  let A := fun r ↦ frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β (c r))
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
    exact ((hχ j).comp continuous_snd).continuousAt.smul
      ((((ho.comp continuous_fst.fst.snd).mul (hs.comp continuous_fst.snd)).mul
        (hβ.comp continuous_snd)).continuousAt.smul hb')
  have hsF : ∀ r x z ξ, x ∉ tsupport χout ∨ ξ ∉ tsupport β → A r x z ξ = 0 := by
    intro r x z ξ h
    rcases h with h | h <;>
      simp [A, frequencyCutFullAmplitude, elapsedAmplitude, image_eq_zero_of_notMem_tsupport h]
  have hsA : ∀ r x z ξ, x ∉ tsupport χout ∨ z ∉ tsupport χsource ∨ ξ ∉ tsupport (χ j) →
      A r x z ξ = 0 := fun r ↦ cut_elapsedAmplitude_eq_zero_off_support b χout χsource β (χ j) (c r)
  constructor
  · apply aestronglyMeasurable_supported_compact_graph_apply S A hocs hscs (hχcs j)
      (isClosed_tsupport β) hS hA hsF hsA (Treg j) (volume.restrict (Icc 0 Δ)) _ u
    intro v
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simpa only [S, A, hceq r hr] using hreal j r hr v
  · apply aestronglyMeasurable_supported_compact_reverse_apply S A hocs hscs (hχcs j)
      (isClosed_tsupport β) hS hA hsF hsA (fun r ↦ (Treg j r).adjoint)
      (volume.restrict (Icc 0 Δ)) _ u
    intro v
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have he := hrealAdj j r hr v
    change _ =ᵐ[volume] (fun z ↦ WithLp.toLp 2 (reverseGraphOperator (elapsedPhase Ψ r)
      (fun x z ξ ↦ star (χ j ξ) • (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose)
      (fun x ↦ (v.val x).ofLp) z)) at he
    simpa only [S, A, hceq r hr, frequencyCutFullAmplitude, Matrix.conjTranspose_smul] using he

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
