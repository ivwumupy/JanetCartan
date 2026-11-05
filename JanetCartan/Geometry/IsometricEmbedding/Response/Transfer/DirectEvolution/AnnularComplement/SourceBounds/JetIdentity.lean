module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Regularity

/-!
# Identifying the differentiated literal source integrals

The normalized jets and the regularity integrands are exactly the same
functions, including output demodulation. The local interchange below needs
smoothness only near the fixed source support. Consumer: the kernel profile
in `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral JanetCartan.Localization AmplitudeJets
open Complement.ParameterDerivatives
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Exact integrand identification, retaining the output demodulator before
external differentiation (`app:ch_response:lem:energy-carrier-jets`). -/
theorem annularSourceIntegrand_eq_externalPhase_amplitude
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
    (ξ : E) (p : P × E) (z : E) :
    annularSourceIntegrand adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ z =
      phaseOscillation (annularExternalPhase adj demod Θ φ lam ξ p) z •
        annularExternalAmplitude adj A π lam a ξ p z := by
  cases demod with
  | false => cases adj <;> simp [annularSourceIntegrand, phaseOscillation, annularExternalPhase,
      annularExternalAmplitude]
  | true =>
    rw [phaseOscillation_annularExternalPhase_demodulated, mul_smul]
    cases adj <;> simp [annularSourceIntegrand, phaseOscillation, annularExternalPhase,
      annularExternalAmplitude]

/-- The actual differentiated integrand is reconstructed by its normalized
jet, at every order without smoothness premises (`energy-carrier-jets`). -/
theorem iteratedFDeriv_annularSourceIntegrand_eq_externalJet
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
    (ξ : E) (j : ℕ) (v : Fin j → P × E) (p : P × E) (z : E) :
    iteratedFDeriv ℝ j (fun q : P × E =>
      annularSourceIntegrand adj demod Θ A π (φ q.1) lam (a q.1) q.2 ξ z) p v =
      phaseOscillation (annularExternalPhase adj demod Θ φ lam ξ p) z •
        annularExternalJet adj demod Θ A π φ lam a ξ j v p z := by
  simp_rw [annularSourceIntegrand_eq_externalPhase_amplitude]
  exact (phaseOscillation_smul_normalizedExternalJet _ _ j v p z).symm

/-- Local phase and amplitude smoothness suffice for the original integrand:
outside the fixed source support it vanishes on a neighborhood. Consumer:
source-integral interchange for `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_annularSourceIntegrand_sourceNeighborhood
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F) (ξ : E)
    {V : Set P} {X U S : Set E} (hV : IsOpen V) (hX : IsOpen X)
    (hU : IsOpen U) (hS : IsClosed S) (hSU : S ⊆ U)
    (hψ : ContDiffOn ℝ ∞ (Function.uncurry
      (annularExternalPhase adj demod Θ φ lam ξ)) ((V ×ˢ X) ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry
      (annularExternalAmplitude adj A π lam a ξ)) ((V ×ˢ X) ×ˢ U))
    (hs : ∀ c ∈ V, tsupport (a c) ⊆ S) :
    ContDiffOn ℝ ∞ (fun q : (P × E) × E =>
      annularSourceIntegrand adj demod Θ A π (φ q.1.1) lam (a q.1.1) q.1.2 ξ q.2)
      ((V ×ˢ X) ×ˢ univ) := by
  intro q hq
  by_cases hz : q.2 ∈ U
  · have hp := hψ.contDiffAt (((hV.prod hX).prod hU).mem_nhds ⟨hq.1, hz⟩)
    have ha := hu.contDiffAt (((hV.prod hX).prod hU).mem_nhds ⟨hq.1, hz⟩)
    simp_rw [annularSourceIntegrand_eq_externalPhase_amplitude]
    exact ((((Complex.ofRealCLM.contDiff.contDiffAt.comp q hp).mul
      contDiffAt_const).cexp).smul ha).contDiffWithinAt
  · have hn : q.2 ∉ S := fun h => hz (hSU h)
    have he : (fun w : (P × E) × E =>
        annularSourceIntegrand adj demod Θ A π (φ w.1.1) lam (a w.1.1) w.1.2 ξ w.2)
        =ᶠ[𝓝 q] fun _ => (0 : F) := by
      filter_upwards [continuousAt_fst.preimage_mem_nhds ((hV.prod hX).mem_nhds hq.1),
        continuousAt_snd.preimage_mem_nhds (hS.isOpen_compl.mem_nhds hn)] with w hw hwz
      exact annularSourceIntegrand_eq_zero_of_source_eq_zero adj demod Θ A π _ lam _ _ _ _
        (image_eq_zero_of_notMem_tsupport (fun h => hwz (hs w.1.1 hw.1 h)))
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

variable [FiniteDimensional ℝ P]

/-- Exact local source-integral interchange in normalized-jet notation. All
local dominators follow from compact source support. This is consumed by the
original-primitive kernel profile, `app:ch_response:lem:energy-carrier-jets`. -/
theorem iteratedFDeriv_annularSourceKernelObservation_sourceNeighborhood
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F) (ξ : E)
    {V : Set P} {X U S : Set E} (hV : IsOpen V) (hX : IsOpen X)
    (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (hψ : ContDiffOn ℝ ∞ (Function.uncurry
      (annularExternalPhase adj demod Θ φ lam ξ)) ((V ×ˢ X) ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry
      (annularExternalAmplitude adj A π lam a ξ)) ((V ×ˢ X) ×ˢ U))
    (hs : ∀ c ∈ V, tsupport (a c) ⊆ S)
    (j : ℕ) (v : Fin j → P × E) (p : P × E) (hp : p ∈ V ×ˢ X) :
    iteratedFDeriv ℝ j (fun q : P × E =>
      annularSourceKernelObservation adj demod Θ A π (φ q.1) lam (a q.1) q.2 ξ) p v =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
        phaseOscillation (annularExternalPhase adj demod Θ φ lam ξ p) z •
          annularExternalJet adj demod Θ A π φ lam a ξ j v p z := by
  have hJ := contDiffOn_annularSourceIntegrand_sourceNeighborhood adj demod Θ A π φ
    lam a ξ hV hX hU hS.isClosed hSU hψ hu hs
  have hJs : ∀ p ∈ V ×ˢ X, ∀ z ∉ S,
      annularSourceIntegrand adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ z = 0 := by
    intro p hp z hz
    exact annularSourceIntegrand_eq_zero_of_source_eq_zero adj demod Θ A π _ lam _ _ _ _
      (image_eq_zero_of_notMem_tsupport (fun h => hz (hs p.1 hp.1 h)))
  have hG := contDiffOn_integral_parameterCompactSupport (μ := volume)
    (hV.prod hX) hJ hS hJs
  simp_rw [annularSourceKernelObservation_eq_integral]
  rw [iteratedFDeriv_const_smul_apply'
    ((hG.contDiffAt ((hV.prod hX).mem_nhds hp)).of_le (by simp))]
  change ((2 * Real.pi) ^ n : ℂ)⁻¹ • (iteratedFDeriv ℝ j
    (fun q : P × E => ∫ z,
      annularSourceIntegrand adj demod Θ A π (φ q.1) lam (a q.1) q.2 ξ z) p v) = _
  rw [iteratedFDeriv_integral_parameterCompactSupport (hV.prod hX) hJ hS hJs j hp,
    ContinuousMultilinearMap.integral_apply
      (integrable_parameterJet_of_compactSupport (hV.prod hX) hJ hS hJs j hp)]
  simp_rw [iteratedFDeriv_annularSourceIntegrand_eq_externalJet]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
