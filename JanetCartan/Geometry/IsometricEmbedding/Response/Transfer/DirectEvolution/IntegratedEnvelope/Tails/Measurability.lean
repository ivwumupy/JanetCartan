module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Basic
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedPhaseWeighted
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedLimits

/-!
# Supported time measurability of the annular cut

The phase is used only near the original physical and beta supports, including
for the reversed kernel. The compact construction identifies the same canonical
graph before taking limits. This supplies the annular half of the measurable
operator difference in `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
open FourierIntegral FourierIntegral.FullLowBounds
open RegularSector.Characteristic.EvolutionIntegral KernelIdentification
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d r

/-- The actual compact frequency cut and its literal adjoint have measurable
elapsed orbits from support-local primitive continuity. The original phase
need not extend continuously to covector zero. In the tail assembly the cut
is `π (λ⁻¹ • ξ)` and the original beta and both physical masks remain in place.
Source: `app:ch_response:lem:energy-carrier-jets`;
consumer: time measurability of the complete complementary difference. -/
theorem aestronglyMeasurable_supported_frequencyCut_and_adjoint
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r) (χout χsource β θ : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ t ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) =>
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - t), (spatialPart x, spatialPart ξ)))
    (hb : ∀ t ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) =>
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - t), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : Continuous χsource) (hβ : Continuous β)
    (hθ : Continuous θ) (hocs : HasCompactSupport χout)
    (hscs : HasCompactSupport χsource) (hθcs : HasCompactSupport θ) (u : H) :
    AEStronglyMeasurable (fun t => fullGraphOperator (elapsedPhase Ψ t)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β t)) u)
      (volume.restrict (Icc 0 Δ)) ∧
    AEStronglyMeasurable (fun t => (fullGraphOperator (elapsedPhase Ψ t)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β t))).adjoint u)
      (volume.restrict (Icc 0 Δ)) := by
  let c : ℝ → ℝ := fun t => max 0 (min Δ t)
  let A : ℝ → FullAmplitude (d + 1) r := fun t =>
    frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β (c t))
  let W : ℝ → FullAmplitude (d + 1) r := fun t x z ξ =>
    Complex.exp (Complex.I * (elapsedPhase Ψ (c t) x ξ : ℂ)) • A t x z ξ
  have hcW : Continuous (fun p : ((ℝ × E) × E) × E => W p.1.1.1 p.1.1.2 p.1.2 p.2) :=
    continuous_supported_elapsed_phaseWeightedAmplitude Ψ b χout χsource β Δ hΔ
      hΨ hb ho hs hβ θ hθ
  have hsupport (t : ℝ) (x z ξ : E)
      (h : x ∉ tsupport χout ∨ z ∉ tsupport χsource ∨ ξ ∉ tsupport θ) :
      W t x z ξ = 0 := by
    have he := cut_elapsedAmplitude_eq_zero_off_support b χout χsource β θ (c t) x z ξ h
    simp only [W, A, he, smul_zero]
  let T : ℝ → H →L[ℂ] H := fun t => fullGraphOperator (fun _ _ => 0) (W t)
  have hreal (t : ℝ) := compact_fullGraphOperator_realizations (fun _ _ : E => 0)
    continuous_const (W t)
    (hcW.comp (((continuous_const.prodMk continuous_fst.fst).prodMk
      continuous_fst.snd).prodMk continuous_snd)) hocs hscs hθcs (hsupport t)
  have hid (t : ℝ) : fullGraphOperator (elapsedPhase Ψ (c t)) (A t) = T t := by
    apply fullGraphOperator_eq_of_realizes
    intro v
    apply (hreal t).1 v |>.trans
    exact ae_of_all _ (fun x => congrArg (fun f => WithLp.toLp 2 (f x))
      (graphOperator_eq_phaseWeighted (elapsedPhase Ψ (c t)) (A t)
        (fun z => (v.val z).ofLp)).symm)
  have hmT : AEStronglyMeasurable (fun t => T t u) (volume.restrict (Icc 0 Δ)) := by
    exact aestronglyMeasurable_compact_graph_apply (fun (_ : ℝ) (_ _ : E) => 0) W
      continuous_const hcW hocs hscs hθcs hsupport T _
      (fun v => ae_of_all _ (fun t => (hreal t).1 v)) u
  have hmTa : AEStronglyMeasurable (fun t => (T t).adjoint u)
      (volume.restrict (Icc 0 Δ)) := by
    apply aestronglyMeasurable_compact_reverse_apply (fun (_ : ℝ) (_ _ : E) => 0)
      (fun t x z ξ => (W t x z ξ).conjTranspose) continuous_const hcW.matrix_conjTranspose
      hocs hscs hθcs _ (fun t => (T t).adjoint) _
      (fun v => ae_of_all _ (fun t => (hreal t).2 v)) u
    intro t x z ξ h
    rw [hsupport t x z ξ h, Matrix.conjTranspose_zero]
  have he : ∀ᵐ t ∂volume.restrict (Icc 0 Δ),
      fullGraphOperator (elapsedPhase Ψ t)
        (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β t)) = T t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hct : c t = t := by
      simp only [c, min_eq_right ht.2, max_eq_right ht.1]
    simpa only [A, hct] using hid t
  exact ⟨hmT.congr (he.mono (fun _ h => congrArg (fun Q => Q u) h.symm)),
    hmTa.congr (he.mono (fun _ h => congrArg (fun Q => Q.adjoint u) h.symm))⟩

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
