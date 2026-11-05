module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedPhaseWeighted
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.IntegralRepresentative
/-!
# Supported compact kernels represent their L² time integrals

Only continuity near the physical and conic supports is required. Clamping
elapsed time supplies continuous representatives, and agrees with the original
kernels on the integration slab. Source:
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
/-- The original finite kernels, with elapsed time clamped to the slab,
have continuous representatives from supported primitive regularity. Consumer:
`integral_elapsed_regularization_test_representatives`, for
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_supported_elapsed_cut_outputs
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
    (θ : E → ℂ) (hθ : Continuous θ) (hθcs : HasCompactSupport θ)
    (u : graphTestSpace (d + 1) q) :
    Continuous (fun p : ℝ × E ↦ graphTestOutput
      (elapsedPhase Ψ (max 0 (min Δ p.1)))
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β (max 0 (min Δ p.1)))) u p.2) ∧
    Continuous (fun p : ℝ × E ↦ WithLp.toLp 2
      (reverseGraphOperator (elapsedPhase Ψ (max 0 (min Δ p.1)))
        (fun x z ξ ↦ (frequencyCutFullAmplitude θ
          (elapsedAmplitude b χout χsource β (max 0 (min Δ p.1))) x z ξ).conjTranspose)
        (fun x ↦ (u.val x).ofLp) p.2)) := by
  let c : ℝ → ℝ := fun r ↦ max 0 (min Δ r)
  let S := fun r ↦ elapsedPhase Ψ (c r)
  let A := fun r ↦ frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β (c r))
  have hsA : ∀ r x z ξ, x ∉ tsupport χout ∨ z ∉ tsupport χsource ∨ ξ ∉ tsupport θ →
      A r x z ξ = 0 := fun r ↦ cut_elapsedAmplitude_eq_zero_off_support b χout χsource β θ (c r)
  have hW := continuous_supported_elapsed_phaseWeightedAmplitude Ψ b χout χsource β
    Δ hΔ hΨ hb ho hs hβ θ hθ
  have hf := continuous_compact_graphTestOutput (fun _ _ _ ↦ 0)
    (fun r x z ξ ↦ Complex.exp (Complex.I * (S r x ξ : ℂ)) • A r x z ξ)
    continuous_const hW hscs hθcs
    (fun r x z ξ h ↦ by simp [hsA r x z ξ (Or.inr h)]) u
  have ha := continuous_compact_reverseGraphOutput (fun _ _ _ ↦ 0)
    (fun r x z ξ ↦ (Complex.exp (Complex.I * (S r x ξ : ℂ)) • A r x z ξ).conjTranspose)
    continuous_const hW.matrix_conjTranspose hocs hθcs
    (fun r x z ξ h ↦ by simp [hsA r x z ξ (by tauto)]) u
  constructor
  · convert hf using 1
    funext p
    exact congrArg (fun f ↦ WithLp.toLp 2 (f p.2))
      (graphOperator_eq_phaseWeighted (S p.1) (A p.1) (fun z ↦ (u.val z).ofLp))
  · convert ha using 1
    funext p
    exact congrArg (fun f ↦ WithLp.toLp 2 (f p.2))
      (reverseGraphOperator_eq_phaseWeighted (S p.1) (A p.1) (fun x ↦ (u.val x).ofLp))

/-- Integrating the finite test realizations exported by
`exists_fullGraphFamily_of_wholeImage_phase` gives precisely the pointwise
forward and literal adjoint kernel integrals. These are the producer's finite
identities, not an assumed uncut action. Consumer: the strong-limit retarded
identification in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_elapsed_regularization_test_representatives
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
    (θ : E → ℂ) (hθ : Continuous θ) (hθcs : HasCompactSupport θ)
    (T : ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hreal : ∀ r ∈ Icc 0 Δ, ∀ u : graphTestSpace (d + 1) q,
      T r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r)) u)
    (hrealAdj : ∀ r ∈ Icc 0 Δ, ∀ u : graphTestSpace (d + 1) q,
      (T r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    (u : graphTestSpace (d + 1) q) :
    ((∫ r in Icc 0 Δ, T r (graphTestToLp u)) =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (∫ r in Icc 0 Δ, graphOperator (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
        (fun z ↦ (u.val z).ofLp) x)) ∧
    ((∫ r in Icc 0 Δ, (T r).adjoint (graphTestToLp u)) =ᵐ[volume] fun z ↦ WithLp.toLp 2
      (∫ r in Icc 0 Δ, reverseGraphOperator (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
          (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
        (fun x ↦ (u.val x).ofLp) z)) := by
  have hc := continuous_supported_elapsed_cut_outputs Ψ b χout χsource β Δ hΔ
    hΨ hb ho hs hβ hocs hscs θ hθ hθcs u
  let c : ℝ → ℝ := fun r ↦ max 0 (min Δ r)
  have hceq (r : ℝ) (hr : r ∈ Icc 0 Δ) : c r = r := by
    simp [c, min_eq_right hr.2, max_eq_right hr.1]
  let L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q ↦ ℂ)).symm
  constructor
  · have he := integral_L2_eq_compact_representative
      (fun r ↦ T r (graphTestToLp u))
      (fun r x ↦ graphTestOutput (elapsedPhase Ψ (c r))
        (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β (c r))) u x)
      Δ hc.1 hocs
      (fun r x hx ↦ graphTestOutput_eq_zero_off_output _ _
        (fun x z ξ hx ↦ cut_elapsedAmplitude_eq_zero_off_support b χout χsource β θ
          (c r) x z ξ (Or.inl hx)) u x hx) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        simpa only [hceq r hr] using hreal r hr u)
    filter_upwards [he] with x hx
    rw [hx]
    change (∫ r in Icc 0 Δ, L (graphOperator (elapsedPhase Ψ (c r))
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β (c r)))
      (fun z ↦ (u.val z).ofLp) x)) = _
    rw [L.integral_comp_comm]
    apply congrArg (WithLp.toLp 2)
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [hceq r hr]
  · have he := integral_L2_eq_compact_representative
      (fun r ↦ (T r).adjoint (graphTestToLp u))
      (fun r z ↦ WithLp.toLp 2 (reverseGraphOperator (elapsedPhase Ψ (c r))
        (fun x z ξ ↦ (frequencyCutFullAmplitude θ
          (elapsedAmplitude b χout χsource β (c r)) x z ξ).conjTranspose)
        (fun x ↦ (u.val x).ofLp) z)) Δ hc.2 hscs
      (fun r z hz ↦ reverseGraphOutput_eq_zero_off_source _ _
        (fun x z ξ hz ↦ by simp [frequencyCutFullAmplitude, elapsedAmplitude,
          image_eq_zero_of_notMem_tsupport hz]) u z hz) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have h := hrealAdj r hr u
        change _ =ᵐ[volume] (fun z ↦ WithLp.toLp 2
          (reverseGraphOperator (elapsedPhase Ψ r)
            (fun x z ξ ↦ star (θ ξ) • (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose)
            (fun x ↦ (u.val x).ofLp) z)) at h
        simpa only [hceq r hr, frequencyCutFullAmplitude, Matrix.conjTranspose_smul] using h)
    filter_upwards [he] with z hz
    rw [hz]
    change (∫ r in Icc 0 Δ, L (reverseGraphOperator (elapsedPhase Ψ (c r))
      (fun x z ξ ↦ (frequencyCutFullAmplitude θ
        (elapsedAmplitude b χout χsource β (c r)) x z ξ).conjTranspose)
      (fun x ↦ (u.val x).ofLp) z)) = _
    rw [L.integral_comp_comm]
    apply congrArg (WithLp.toLp 2)
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simp only [hceq r hr, frequencyCutFullAmplitude, Matrix.conjTranspose_smul]
    rfl

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
