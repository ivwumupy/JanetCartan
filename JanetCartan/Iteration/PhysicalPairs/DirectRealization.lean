module

public import JanetCartan.Iteration.PhysicalPairs.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.DirectSolverAgreement
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledProduct

/-!
# The SAME normalized fixed solver as the original Schwartz pair response

The original correction and solve factors are retained literally. The supplied
smooth fixed solver is already the SAME corrected normalized inverse; it is not
replaced or factored through an identity operator. The existing direct-factor
agreement proves its equality with the exact source extension used by the pair
constructor. Consumers: `main:prop:pairs`, `PhysicalPairs.OriginalSize`, and the
common physical secondary field `W=b²V+S`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs
open CanonicalAtomRealization CorrectedAtoms FixedDomainInverse LocalSobolev
open PrimarySourceAdmission ResponseSourceExtension AmbientResponse UniformStep

variable {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W core chart : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (Zcorr solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (hW : MeasurableSet W) (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
    (Pphys : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ]
      Lp (Euclidean n) 2 volume)
    (hZcorr : ∀ v : smoothSource W (Euclidean n),
      Zcorr v =ᵐ[volume] SmallSupport.zeroExtend hW (Corr v))
    (hsolverAe : ∀ v : smoothSource W (Euclidean n),
      solver v =ᵐ[volume] Pphys (SmallSupport.zeroExtend hW (Corr v)))
    (χ : Euclidean n → ℝ) (hχS : tsupport χ ⊆ S)
    (Ξ : OutputCutoff core chart) (hchart : IsOpen chart)
    (hF : ContDiffOn ℝ ∞ F chart) (hi : IsImmersionOn F chart)
    (hrank : HasFullNormalRankOn F chart)

local notation "Tresp" => directStressCorrectionFactor Q η hU hQ hη hSU Zcorr
local notation "Sresp" => directPhysicalSolveFactor Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe
local notation "hsmooth" => contDiff_directProductSolve Q η hU hQ hη hSU
  Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe χ hχS
local notation "hsolve" => (fun h x (_hx : x ∈ chart) ↦ ContDiff.differentiable (hsmooth h) (by simp) x)
local notation "hregular" => (fun h ↦ ContDiff.contDiffOn (s := chart) (hsmooth h))

/-- Real Schwartz realization of the SAME original direct correction/solve
factors. Global smoothness comes from the actual normalized fixed solver, and
compact support from the original output cutoff (`main:prop:pairs`). -/
def directAmbientSchwartzResponse :
    compactSmoothSources (tsupport χ) →ₗ[ℝ] 𝓢(Euclidean n, Euclidean N) :=
  ambientSchwartzResponse F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular

/-- The original source extension and fixed smooth solver agree as actual global
fields on every admitted source; no equality of off-domain algebraic extensions
is claimed (`app:ch_response:eq:response-full-map`). -/
theorem directAmbientSchwartzResponse_eq_fixedSolver (h : compactSmoothSources (tsupport χ)) :
    ⇑(directAmbientSchwartzResponse F Q η hU hQ hη hSU Zcorr solver hsolver
      hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank h) =
      fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ h := by
  let hfull : compactSmoothSources S :=
    ⟨h, h.property.1, h.property.2.1, h.property.2.2.trans hχS⟩
  rw [fixedSmoothSolverAmbientExtension_eq_cutoff F Q η hU hQ hη hSU solver hsolver Ξ hfull]
  funext x
  change ambientSchwartzResponse F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular h x = _
  rw [ambientSchwartzResponse_apply]
  dsimp only [AmbientResponse.ambientResponse]
  rw [directPhysicalSolveFactor_correctedStressSource Q η hU hQ hη hSU
    Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe hfull]

/-- Actual admitted source, exact restricted L² class, globally smooth SAME
solution, and literal physical completedVariation identity. These are precisely
the lower inputs of the checked original signed physical-size theorem; source
membership and response regularity are conclusions (`main:prop:pairs`). -/
theorem directAmbientSchwartzResponse_source_data (h : compactSmoothSources (tsupport χ)) :
    let hfull : compactSmoothSources S :=
      ⟨h, h.property.1, h.property.2.1, h.property.2.2.trans hχS⟩
    let source := euclideanCutoffStressSource Q η h
    ∃ hmem : MemLp source 2 volume,
      let datum := ((hmem.restrict W).toLp source)
      let g := solver (cutoffStressSmoothSource Q η hU hQ hη hSU hfull)
      ContDiff ℝ ∞ g ∧
      g =ᵐ[volume] Pphys (SmallSupport.zeroExtend hW (Corr datum)) ∧
      ∀ x, directAmbientSchwartzResponse F Q η hU hQ hη hSU Zcorr solver hsolver
        hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank h x =
        Ξ.toFun x • completedVariation F g h x := by
  intro hfull source
  refine ⟨memLp_euclideanCutoffStressSource Q η hU hQ hη hSU hfull, ?_⟩
  intro datum g
  refine ⟨hsolver _, hsolverAe _, ?_⟩
  intro x
  have he := directAmbientSchwartzResponse_eq_fixedSolver F Q η hU hQ hη hSU
    Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank h
  rw [he, fixedSmoothSolverAmbientExtension_eq_cutoff F Q η hU hQ hη hSU solver hsolver Ξ hfull]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℝ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    {Uwave : Set (Euclidean n)} (hUwave : IsOpen Uwave)
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) Uwave)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχWave : tsupport χ ⊆ Uwave)

/-- The existing complete off-self constructor specialized to the original direct
factors, with no new inverse, source or signed carrier (`main:prop:pairs`). -/
def directOffSelfCorrection : 𝓢(Euclidean n, Euclidean N) :=
  offSelfCorrection F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular
    b μ hμ Z θ hUwave hZ hχ hχc hχWave

/-- Literal equality with the ORIGINAL correction/solve-factor response on the
complete signed off-self tensor (`main:prop:pairs`). -/
theorem directOffSelfCorrection_coe :
    ⇑(directOffSelfCorrection F Q η hU hQ hη hSU Zcorr solver hsolver
      hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank
      b μ hμ Z θ hUwave hZ hχ hχc hχWave) =
      -sourceCutoffAmbientResponse F Q η Tresp Sresp Ξ χ hsolve
        (ProductSum.offSelfSource b μ (sampledDerivative Z) (sampledDerivativeAmplitude Z θ)) :=
  offSelfCorrection_coe F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular
    b μ hμ Z θ hUwave hZ hχ hχc hχWave

/-- The SAME constructed Schwartz correction is also the original fixed smooth
solver's ambient response on the FULL cutoff tensor. This is the exact adapter
needed to apply the normalized source estimates, retaining every plus diagonal
and excluding only the minus diagonal (`main:prop:pairs`). -/
theorem directOffSelfCorrection_eq_fixedSolver :
    ⇑(directOffSelfCorrection F Q η hU hQ hη hSU Zcorr solver hsolver
      hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank
      b μ hμ Z θ hUwave hZ hχ hχc hχWave) =
      -fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
        (fun x ↦ χ x • ProductSum.offSelfSource b μ (sampledDerivative Z)
          (sampledDerivativeAmplitude Z θ) x) := by
  rw [directOffSelfCorrection_coe]
  rw [sourceCutoffAmbientResponse_direct_eq_fixedSolver_of_mem F Q η hU hQ hη hSU
    Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe χ hχS Ξ _
    (sampled_offSelf_source_mem b μ hμ Z θ hUwave hZ hχ hχc hχWave).1]

/-- Complete finite residual assembly on the SAME real Schwartz correction.
The lower errors are individual FULL signed fixed-solver sources, including the
plus diagonal. Response differentiability is supplied by the actual smooth
inverse, not an additional analytic premise (`main:prop:pairs`). -/
theorem directOffSelfCorrection_error_le {x : Euclidean n} {C : ℝ} (hC : 0 ≤ C)
    (hep : ∀ i j, ‖linearizedMetric F
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
        (fun y ↦ χ y • ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j y)) x -
          ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j x‖ ≤ C)
    (hem : ∀ i j, j ≠ i → ‖linearizedMetric F
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
        (fun y ↦ χ y • ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j y)) x -
          ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j x‖ ≤ C) :
    ‖linearizedMetric F
      (directOffSelfCorrection F Q η hU hQ hη hSU Zcorr solver hsolver
        hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank
        b μ hμ Z θ hUwave hZ hχ hχc hχWave) x +
      ProductSum.offSelfSource b μ (sampledDerivative Z) (sampledDerivativeAmplitude Z θ) x‖ ≤
        2 * C * b^2 * ProductSum.coefficientMass μ := by
  rw [directOffSelfCorrection_coe]
  apply sampled_product_correction_error_le F
    (sourceCutoffAmbientResponse F Q η Tresp Sresp Ξ χ hsolve)
    b μ hμ Z θ (sampledDerivativeAmplitude Z θ)
    (sampledDerivative_eq_phase_smul_amplitude Z θ) hC
  · intro i j
    change DifferentiableAt ℝ
      (signedResponse F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular
        Z θ hUwave hZ hχ hχc hχWave false i j) x
    exact (signedResponse F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular
      Z θ hUwave hZ hχ hχc hχWave false i j).smooth'.differentiable (by simp) x
  · intro i j _hij
    change DifferentiableAt ℝ
      (signedResponse F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular
        Z θ hUwave hZ hχ hχc hχWave true i j) x
    exact (signedResponse F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular
      Z θ hUwave hZ hχ hχc hχWave true i j).smooth'.differentiable (by simp) x
  · intro i j
    rw [sourceCutoffAmbientResponse_direct_eq_fixedSolver_of_mem F Q η hU hQ hη hSU
      Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe χ hχS Ξ _
      (sampled_signed_sources_mem Z θ hUwave hZ hχ hχc hχWave i j).1]
    exact hep i j
  · intro i j hij
    rw [sourceCutoffAmbientResponse_direct_eq_fixedSolver_of_mem F Q η hU hQ hη hSU
      Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe χ hχS Ξ _
      (sampled_signed_sources_mem Z θ hUwave hZ hχ hχc hχWave i j).2]
    exact hem i j hij

/-- The physical all-order size budget of the literal SAME direct Schwartz
correction from its individual full-source profiles. Those profiles are supplied
by `exists_original_physical_history_localized_normalized_sampled_size_constants` using
`directAmbientSchwartzResponse_source_data`, not assumed for the whole correction.
Every plus carrier is included and the revised forcing exponent is explicit
(`main:prop:pairs`). -/
theorem directOffSelfCorrection_size_le_revised
    (r : ℕ) {R δ C Ccount Cmass : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R^(1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hp : ∀ i j, (eLpNorm (fun ξ ↦
      Pseudodifferential.euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify
          (signedResponse F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular
            Z θ hUwave hZ hχ hχc hχWave false i j)) ξ) 2 volume).toReal ≤
              C * (R^carrierExponent)^(r+1))
    (hm : ∀ i j, j ≠ i → (eLpNorm (fun ξ ↦
      Pseudodifferential.euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify
          (signedResponse F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular
            Z θ hUwave hZ hχ hχc hχWave true i j)) ξ) 2 volume).toReal ≤
              C * (R^carrierExponent)^(r+1)) :
    (eLpNorm (fun ξ ↦ Pseudodifferential.euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
      𝓕 (PhysicalCutoff.complexify
        (directOffSelfCorrection F Q η hU hQ hη hSU Zcorr solver hsolver
          hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank
          (δ * R^RevisedScales.forcingExponent n) μ hμ Z θ hUwave hZ hχ hχc hχWave)) ξ)
      2 volume).toReal ≤ (2 * C * Ccount * Cmass) * δ^2 *
        R^(2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
          (R^carrierExponent)^(r+1) := by
  dsimp only [directOffSelfCorrection]
  rw [offSelfCorrection_eq_signed]
  exact physicalWeightedNorm_signedSum_le_revised r μ hμ _ _ hC hCmass hR hcount hmass hp hm

/-- The exact revised finite full-strain error of the SAME real Schwartz
correction. Only lower individual complete-source errors enter; their actual
producer is the corrected normalized source observation and full-strain transfer.
The final `δ² R^(2A+1+ε−(a−β)q)` is derived here, with all plus diagonals and no
old forcing exponent (`main:prop:pairs`). -/
theorem directOffSelfCorrection_error_le_revised {x : Euclidean n}
    {R δ C Ccount Cmass : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R^(1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass) (q : ℕ)
    (hep : ∀ i j, ‖linearizedMetric F
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
        (fun y ↦ χ y • ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j y)) x -
          ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j x‖ ≤
            C * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹)
    (hem : ∀ i j, j ≠ i → ‖linearizedMetric F
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
        (fun y ↦ χ y • ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j y)) x -
          ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j x‖ ≤
            C * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹) :
    ‖linearizedMetric F
      (directOffSelfCorrection F Q η hU hQ hη hSU Zcorr solver hsolver
        hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank
        (δ * R^RevisedScales.forcingExponent n) μ hμ Z θ hUwave hZ hχ hχc hχWave) x +
      ProductSum.offSelfSource (δ * R^RevisedScales.forcingExponent n) μ
        (sampledDerivative Z) (sampledDerivativeAmplitude Z θ) x‖ ≤
      (2 * C * Ccount * Cmass) * δ^2 *
        R^(2 * RevisedScales.forcingExponent n + 1 + samplingSlack -
          (carrierExponent - separationExponent) * (q : ℝ)) := by
  have he := directOffSelfCorrection_error_le F Q η hU hQ hη hSU
    Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank
    (δ * R^RevisedScales.forcingExponent n) μ hμ Z θ hUwave hZ hχ hχc hχWave
    (mul_nonneg hC (by positivity)) hep hem
  apply signedResidual_le_revised_count_mass (n := n) μ hμ hR
    (mul_nonneg (by norm_num) hC) hCmass hcount hmass q
  convert he using 1
  ring

/-- The SAME real Schwartz correction has the exact revised physical L²
budget. Individual order-zero full-source profiles are those of the already
constructed normalized response; no bound for the summed correction is a premise.
The exponent is precisely `B₀ = 2A+1+ε+a` (`main:eq:step-L2`). -/
theorem directOffSelfCorrection_physicalL2_le_revised
    {R δ C Ccount Cmass : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R^(1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hp : ∀ i j, PhysicalBernstein.physicalL2Norm
      (signedResponse F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular
        Z θ hUwave hZ hχ hχc hχWave false i j) ≤ C * R^carrierExponent)
    (hm : ∀ i j, j ≠ i → PhysicalBernstein.physicalL2Norm
      (signedResponse F Q η Tresp Sresp Ξ hsolve hchart hF hi hrank hregular
        Z θ hUwave hZ hχ hχc hχWave true i j) ≤ C * R^carrierExponent) :
    PhysicalBernstein.physicalL2Norm
      (directOffSelfCorrection F Q η hU hQ hη hSU Zcorr solver hsolver
        hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank
        (δ * R^RevisedScales.forcingExponent n) μ hμ Z θ hUwave hZ hχ hχc hχWave) ≤
      (2 * C * Ccount * Cmass) * δ^2 * R^RevisedScales.displacementLoss n := by
  have hs := directOffSelfCorrection_size_le_revised (δ := δ) F Q η hU hQ hη hSU
    Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe χ hχS Ξ hchart hF hi hrank
    μ hμ Z θ hUwave hZ hχ hχc hχWave 0 hR hC hCmass hcount hmass
    (by simpa only [Nat.cast_zero, Nat.zero_add, pow_one, physicalWeightedNorm_zero_eq_L2] using hp)
    (by simpa only [Nat.cast_zero, Nat.zero_add, pow_one, physicalWeightedNorm_zero_eq_L2] using hm)
  simpa only [Nat.cast_zero, Nat.zero_add, pow_one, physicalWeightedNorm_zero_eq_L2,
    mul_assoc, ← Real.rpow_add hR, RevisedScales.displacementLoss] using hs

end JanetCartan.PhysicalPairs
