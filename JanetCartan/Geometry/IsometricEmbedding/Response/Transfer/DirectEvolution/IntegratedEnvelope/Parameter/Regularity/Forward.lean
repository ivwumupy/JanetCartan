module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter.Regularity.Lift
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter.Regularity.Realization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.DatumBridge

/-!
# Fixed-time parameter smoothness of the actual annular envelope

The primitive hypotheses are the qualitative supported hypotheses of
`AnnularSobolev.exists_annularEnvelope_joint_sobolev_of_primitive_jets`.
No quantitative bounds are needed. Elapsed time is fixed throughout, so this
result can be applied separately at each time under the original uniform
hypotheses, without any time regularity of the critical map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
open Pseudodifferential FourierIntegral FourierIntegral.FullLowBounds
open CompactTransfer BranchAmplitudes ModifiedLow AnnularSobolev AnnularSobolev.WeakTransfer
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- The SAME physical annular envelope applied to the original datum is
smooth in the carrier parameter, in the original L² norm. All test realization
and output-smoothness obligations are discharged from primitive supported
geometry. This supplies `hf` in `orderedTransferAction_elapsedIntegral` for
`app:ch_response:eq:direct-envelope-profile` and
`app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_annularEnvelope_originalDatum
    (b : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (A : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (elapsed : ℝ)
    (hphase : ContDiff ℝ ∞ (Function.uncurry (elapsedPhase Ψ elapsed)))
    {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables (d + 1))
    {U : Set (E × P)} {D K : Set (CarrierVariables (d + 1))}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (elapsedCarrierPhase Ψ elapsed φ)) (U ×ˢ D))
    (hα : ContDiffOn ℝ ∞ (Function.uncurry
      (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p)) (U ×ˢ D))
    (hs : ∀ q ∈ U, Function.support
      (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U) (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D,
      IsUnit (averagedPhaseHessian (elapsedCarrierPhase Ψ elapsed φ) w₀ q w))
    {X Y F₀ : Set E} (hX : IsCompact X)
    (houtput : ∀ q ∈ tsupport (Function.uncurry
      (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p)), q.1.1 ∈ X)
    {C : Set P} (hC : IsOpen C) (hXU : X ×ˢ C ⊆ U)
    (hcφ : ∀ c, Continuous (fun x => φ x c))
    (hslice : ∀ c ∈ C, ∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry
      (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p)) →
        normalizedSlice c q ∈ U ×ˢ D)
    (hsupport : ∀ c ∈ C, ∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry
      (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p)) →
        q.1.1 ∈ X ∧ q.1.2 ∈ Y ∧ lam • q.2 ∈ F₀)
    (hΘ : ∀ x ∈ X, ∀ θ, lam • θ ∈ F₀ →
      elapsedPhase Ψ elapsed x (lam • θ) = lam * elapsedPhase Ψ elapsed x θ)
    {Ksource Ssource : Set E} (hKsource : IsCompact Ksource)
    (hSsource : IsOpen Ssource) (hKS : Ksource ⊆ Ssource)
    (hφ : ∀ c ∈ C, ContDiffOn ℝ ∞ (fun x => φ x c) Ssource)
    (a : E × P → V) (ha : ContDiff ℝ ∞ a)
    (has : ∀ q, q.1 ∉ Ksource → a q = 0) :
    ContDiffOn ℝ ∞
      (fun c => annularEnvelopeOperator Ψ A χout χsource β π elapsed lam
        (fun x => φ x c) (hcφ c)
        (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))) C := by
  let α := normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p
  let aPi := fun q => (a q).ofLp
  have haPi : ContDiff ℝ ∞ aPi :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).contDiff.comp ha
  have hasPi : ∀ q, q.1 ∉ Ksource → aPi q = 0 :=
    fun q hq => congrArg WithLp.ofLp (has q hq)
  have ht : initialJointTransferTerm ∈ jointTransferTerms (M := Matrix (Fin r) (Fin r) ℂ) b
      ([] : List (E × P)) := by simp [jointTransferTerms, orderedTransferAction]
  let g := normalizedBranchIntegral b (elapsedCarrierPhase Ψ elapsed φ) w₀ α aPi
    initialJointTransferTerm lam p
  have hg : ContDiffOn ℝ ∞ g (univ ×ˢ C) :=
    contDiffOn_normalizedBranchIntegral_output_strip b hU hD hcD hK hKD hf hα haPi hs
      hw₀ h₀ hinv lam p [] initialJointTransferTerm ht hX.isClosed houtput hXU
  have hgs (q : E × P) (hq : q.1 ∉ X) : g q = 0 :=
    normalizedBranchIntegral_zero_of_notMem_output b _ w₀ α aPi [] _ ht houtput lam p hq
  apply (contDiffOn_supportedJointWordClass g hC hg hX []).congr
  intro c hc
  have hreal := (initialBranch_test_realizations_of_supported_geometry b
    (elapsedPhase Ψ elapsed) hphase.continuous hU hD hcD hK hf hα hs hw₀ h₀ hinv
      hX houtput c (hslice c hc) hlam.ne' p).1
  have hhom (x z θ : E) (hn : modifiedAmplitude lam p
      (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α
        initialJointTransferTerm c) x z (lam • θ) ≠ 0) :
      elapsedPhase Ψ elapsed x (lam • θ) = lam * elapsedPhase Ψ elapsed x θ := by
    have hn' : normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α
        initialJointTransferTerm c ((x, z), θ) ≠ 0 := by
      intro hz
      apply hn
      simp [modifiedAmplitude, NearCarrierSymbol.physicalAmplitudeOfNormalized,
        smul_smul, inv_mul_cancel₀ hlam.ne', hz]
    have hsup := hsupport c hc ((x, z), θ)
      (tsupport_normalizedTermAmplitude_subset b (elapsedCarrierPhase Ψ elapsed φ) w₀ α []
        initialJointTransferTerm ht c (subset_tsupport _ hn'))
    exact hΘ x hsup.1 θ hsup.2.2
  have he := annularBranchOperator_ae_jointIntegral_of_output_support b Ψ elapsed hlam p φ w₀
    hU hD hcD hK hKD hf hα haPi hs hw₀ h₀ hinv hKsource hSsource hKS hasPi
    [] initialJointTransferTerm ht houtput c (fun x hx => hXU ⟨hx, hc⟩) (hcφ c) (hφ c hc)
    hreal hhom
  simp only [annularBranchOperator_initial_eq b Ψ A χout χsource β π elapsed
    hlam.ne' p φ w₀] at he
  exact Lp.ext ((show annularEnvelopeOperator Ψ A χout χsource β π elapsed lam
      (fun x => φ x c) (hcφ c)
      (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c)) =ᵐ[volume]
        fun x => WithLp.toLp 2 (g (x, c)) from he).trans
    (supportedJointWordClass_ae g hC hg hX hgs [] hc).symm)

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
