module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.ClassicalReconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.ClassicalCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.FixedSolverReconstruction

/-!
# Joint reconstruction on the same initialized smooth solver

The ordered-parameter estimates use one total function on the original open
parameter set. Define that function from the literal fixed smooth solver and
the two original source admissions. Its value outside the parameter set is
irrelevant; all identifications are made on that set. No new solution or
ambient response is selected.

The source equality is the complete strain identity retained by
`CorrectedAtoms.InitializedTerminalSolver`. These identities insert the
normalized inverse's reduced envelopes in the reconstruction estimates for
`app:ch_response:eq:response-two-envelopes` and
`app:ch_response:cor:current-atoms`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CanonicalAtomRealization

open CompatibleResponse CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension
  FixedDomainInverse ResponseTransfer

variable {n N : ℕ} {Z : Type*}
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (V : Set Z) (source : Z → Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hre : ∀ c ∈ V, tensorFieldRealPart (source c) ∈ compactSmoothSources S)
    (him : ∀ c ∈ V, tensorFieldImagPart (source c) ∈ compactSmoothSources S)
    (τ : ℝ) (φ : Euclidean n × Z → ℝ)

/-- The actual demodulated reduced solution, totalized outside its original
parameter domain. Both original quadratures use the SAME fixed smooth solver
(`app:ch_response:eq:response-actual-solver-formula`). -/
def fixedSolverParameterEnvelope : Euclidean n × Z → EuclideanSpace ℂ (Fin n) := by
  classical
  exact fun p ↦ if hc : p.2 ∈ V then
    waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 •
      fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver (source p.2)
        (hre p.2 hc) (him p.2 hc) p.1
  else 0

/-- Remodulation gives back the literal solver, including its two source
admissions. This identity is pointwise on the whole physical space
(`app:ch_response:eq:response-two-envelopes`). -/
theorem fixedSolverParameterEnvelope_remodulated {c : Z} (hc : c ∈ V) :
    modulatedWave τ⁻¹ (fun x ↦ φ (x,c))
      (fun x ↦ fixedSolverParameterEnvelope Q η hU hQ hη hSU solver V source hre him τ φ (x,c)) =
      fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver (source c)
        (hre c hc) (him c hc) := by
  funext x
  simp only [modulatedWave, fixedSolverParameterEnvelope, dite_eq_left hc]
  rw [smul_smul, mul_comm (waveCarrier τ⁻¹ (fun x ↦ φ (x,c)) x),
    waveCarrier_neg_mul, one_smul]

/-- Spatial smoothness belongs to this same reduced envelope, for every
admitted parameter. Only the accepted smooth-solver property is used
(`app:ch_response:prop:response-ambient`). -/
theorem contDiff_fixedSolverParameterEnvelope_spatial
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    {c : Z} (hc : c ∈ V) (hφ : ContDiff ℝ ∞ (fun x ↦ φ (x,c))) :
    ContDiff ℝ ∞ (fun x ↦
      fixedSolverParameterEnvelope Q η hU hQ hη hSU solver V source hre him τ φ (x,c)) := by
  have hsol := contDiff_fixedSmoothSolverComplexSolution Q η hU hQ hη hSU
    solver hsolver (source c) (hre c hc) (him c hc)
  have hcarrier : ContDiff ℝ ∞ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,c))) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hφ)).cexp
  have heq : (fun x ↦ fixedSolverParameterEnvelope Q η hU hQ hη hSU solver
      V source hre him τ φ (x,c)) =
      (fun x ↦ waveCarrier (-τ⁻¹) (fun x ↦ φ (x,c)) x •
        fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver (source c)
          (hre c hc) (him c hc) x) := by
    funext x
    simp only [fixedSolverParameterEnvelope, dite_eq_left hc]
  rw [heq]
  exact hcarrier.smul hsol

variable (F : Euclidean n → Euclidean N)
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    {core chart : Set (Euclidean n)} (Ξ : OutputCutoff core chart)
    (χ : Euclidean n → ℝ)
    (a : Euclidean n × Z → Matrix (Fin n) (Fin n) ℂ)

/-- The whole-source ambient extension is the literal completion of the
same parameter envelope on its original core. The source equality retains
the original source cutoff and complete tensor, as supplied by
`cutoff_fullPrimaryStrain_eq_modulatedSource_of_phase_eq`
(`app:ch_response:eq:response-full-map`). -/
theorem fixedSolverParameterResponse_eq_completedVariation
    (hsource : ∀ c ∈ V, source c = fun x ↦
      waveCarrier τ⁻¹ (fun y ↦ φ (y,c)) x • ((χ x : ℂ) • a (x,c)))
    {Ω : Set (Euclidean n × Z)} (hΩ : Ω ⊆ core ×ˢ V) :
    EqOn (fun p ↦ complexifyResponse
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ)
        (source p.2) p.1)
      (fun p ↦ completedVariationComplex F
        (modulatedWave τ⁻¹ (fun x ↦ φ (x,p.2))
          (fun x ↦ fixedSolverParameterEnvelope Q η hU hQ hη hSU solver V source hre him τ φ (x,p.2)))
        (fun x ↦ waveCarrier τ⁻¹ (fun y ↦ φ (y,p.2)) x • ((χ x : ℂ) • a (x,p.2))) p.1) Ω := by
  intro p hp
  have hc := (hΩ hp).2
  dsimp only
  rw [fixedSolverParameterEnvelope_remodulated Q η hU hQ hη hSU solver V source hre him τ φ hc]
  have he := congrFun (complexify_fixedSmoothSolverAmbientExtension_eq_completedVariation
    Q η hU hQ hη hSU solver hsolver (source p.2) (hre p.2 hc) (him p.2 hc) F Ξ) p.1
  have hcut : Ξ.toFun p.1 = 1 :=
    (interior_subset : interior {x | Ξ.toFun x = 1} ⊆ {x | Ξ.toFun x = 1})
      (Ξ.plateau (hΩ hp).1)
  simp only [hcut, Complex.ofReal_one, one_smul] at he
  exact he.trans (congrArg (fun h ↦ completedVariationComplex F
    (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver (source p.2)
      (hre p.2 hc) (him p.2 hc)) h p.1) (hsource p.2 hc))

variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

set_option quotPrecheck false in
local notation "gsolver" =>
  fixedSolverParameterEnvelope Q η hU hQ hη hSU solver V source hre him τ φ

/-- The sharp joint estimates apply to the literal ambient extension of the
same fixed solver. The source and reduced-solution profiles carry their full
cubic smallness; the conclusion has the quadratic displacement and linear
physical derivative required by the prepared current. All profiles concern
the concrete fields, and no ambient-response estimate is assumed
(`app:ch_response:eq:response-graded-displacement`,
`app:ch_response:eq:response-graded-derivative`). -/
theorem fixedSolverParameterResponse_joint_graded
    (hsource : ∀ c ∈ V, source c = fun x ↦
      waveCarrier τ⁻¹ (fun y ↦ φ (y,c)) x • ((χ x : ℂ) • a (x,c)))
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω) (hΩcore : Ω ⊆ core ×ˢ V)
    (hφjoint : ContDiffOn ℝ ∞ φ Ω)
    (hφsp : ∀ c ∈ V, ContDiff ℝ ∞ (fun x ↦ φ (x,c)))
    (hg : ContDiffOn ℝ ∞ gsolver Ω)
    (ha : ∀ ij : Fin n × Fin n, ContDiffOn ℝ ∞ (fun q ↦ a q ij.1 ij.2) Ω)
    (hχ : ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦ (χ q.1 : ℂ)) Ω)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (fun q ↦
      ((partialDeriv (fun x ↦ φ (x,q.2)) q.1 i : ℝ) : ℂ)) Ω)
    (hV : ∀ l j, ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦
      reconstructionValueEntry F l j q.1) Ω)
    (hD : ∀ l ij, ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦
      reconstructionDerivativeEntry F l ij q.1) Ω)
    (hS : ∀ l ij, ContDiffOn ℝ ∞ (fun q : Euclidean n × Z ↦
      reconstructionSourceEntry F l ij q.1) Ω)
    (C B : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (hB : ∀ r, 0 ≤ B r)
    {size K : ℝ} (hsize : 0 ≤ size) (hτ : 0 < τ) (hK : 1 ≤ K) (hKτ : K ≤ τ⁻¹)
    (reserve m : ℕ)
    (hχB : ∀ r ≤ m+1, ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦ (χ p.1 : ℂ)) q‖ ≤ C r * K^(r-reserve))
    (hφB : ∀ i r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦
        ((partialDeriv (fun x ↦ φ (x,p.2)) p.1 i : ℝ) : ℂ)) q‖ ≤ C r * K^(r-reserve))
    (hVB : ∀ l j r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦
        reconstructionValueEntry F l j p.1) q‖ ≤ C r * K^(r-reserve))
    (hDB : ∀ l ij r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦
        reconstructionDerivativeEntry F l ij p.1) q‖ ≤ C r * K^(r-reserve))
    (hSB : ∀ l ij r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p : Euclidean n × Z ↦
        reconstructionSourceEntry F l ij p.1) q‖ ≤ C r * K^(r-reserve))
    (hgB : ∀ j r, r ≤ m+2 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦ gsolver p j) q‖ ≤ B r * (τ^3*size) * K^(r-reserve))
    (haB : ∀ ij : Fin n × Fin n, ∀ r ≤ m+1, ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦ a p ij.1 ij.2) q‖ ≤ B r * (τ^3*size) * K^(r-reserve)) :
    let response := fun p : Euclidean n × Z ↦ complexifyResponse
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ)
        (source p.2) p.1
    ContDiffOn ℝ ∞ response Ω ∧
      (∀ l r, r ≤ m+1 → ∀ q ∈ Ω,
        ‖iteratedFDeriv ℝ r (fun p ↦
          (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 • response p) l) q‖ ≤
          jointReconstructionDisplacementBudget n C B r * (τ^2*size) * K^(r-reserve)) ∧
      (∀ l i r, r ≤ m → ∀ q ∈ Ω,
        ‖iteratedFDeriv ℝ r (fun p ↦
          (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 •
            fderiv ℝ (fun x ↦ response (x,p.2)) p.1 (EuclideanSpace.single i 1)) l) q‖ ≤
          jointReconstructionPhysicalBudget n C B r * (τ*size) * K^(r-reserve)) := by
  let R := fun p : Euclidean n × Z ↦ reconstructionAmplitude F τ⁻¹ (fun x ↦ φ (x,p.2)) χ
    (fun x ↦ gsolver (x,p.2)) (fun x ↦ a (x,p.2)) p.1
  let completed := fun p : Euclidean n × Z ↦ completedVariationComplex F
    (modulatedWave τ⁻¹ (fun x ↦ φ (x,p.2)) (fun x ↦ gsolver (x,p.2)))
    (fun x ↦ waveCarrier τ⁻¹ (fun y ↦ φ (y,p.2)) x • ((χ x : ℂ) • a (x,p.2))) p.1
  let response := fun p : Euclidean n × Z ↦ complexifyResponse
    (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ) (source p.2) p.1
  have hgsp c (hc : c ∈ V) : ContDiff ℝ ∞ (fun x ↦ gsolver (x,c)) :=
    contDiff_fixedSolverParameterEnvelope_spatial Q η hU hQ hη hSU solver V source hre him τ φ
      hsolver hc (hφsp c hc)
  obtain ⟨hcompleted,_,hRB,_,hHB⟩ := completedVariationComplex_joint_response_graded F φ χ
    gsolver a hΩ hφjoint
    (fun q hq ↦ (hφsp q.2 (hΩcore hq).2).differentiable (by simp))
    (fun q hq ↦ (hgsp q.2 (hΩcore hq).2).differentiable (by simp))
    hg ha hχ hφ hV hD hS C B hC hB (mul_nonneg (pow_nonneg hτ.le _) hsize)
    hK hKτ reserve m hχB hφB hVB hDB hSB hgB haB
  have he : EqOn response completed Ω :=
    fixedSolverParameterResponse_eq_completedVariation Q η hU hQ hη hSU solver V source hre him
      τ φ F hsolver Ξ χ a hsource hΩcore
  have hsmall₁ : (τ^3*size)*τ⁻¹ = τ^2*size := by field_simp
  have hsmall₂ : (τ^3*size)*(τ⁻¹)^2 = τ*size := by field_simp
  refine ⟨hcompleted.congr he, ?_, ?_⟩
  · intro l r hr q hq
    have hdisp : (fun p : Euclidean n × Z ↦
        (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 • response p) l) =ᶠ[𝓝 q]
        (fun p ↦ R p l) := by
      filter_upwards [hΩ.mem_nhds hq] with p hp
      rw [he hp]
      have h := congrArg (fun z : EuclideanSpace ℂ (Fin N) ↦ z l)
        (demodulated_completedVariationComplex F (ρ := τ⁻¹) χ (fun _ ↦ 1) (fun x ↦ a (x,p.2))
          ((hφsp p.2 (hΩcore hp).2).differentiable (by simp) p.1)
          ((hgsp p.2 (hΩcore hp).2).differentiable (by simp) p.1))
      simpa only [Complex.ofReal_one, one_smul] using h
    rw [(hdisp.iteratedFDeriv ℝ r).eq_of_nhds]
    simpa only [hsmall₁] using hRB l r hr q hq
  · intro l i r hr q hq
    have hder : (fun p : Euclidean n × Z ↦
        (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 •
          fderiv ℝ (fun x ↦ response (x,p.2)) p.1 (EuclideanSpace.single i 1)) l) =ᶠ[𝓝 q]
        (fun p ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 •
          fderiv ℝ (fun x ↦ completed (x,p.2)) p.1 (EuclideanSpace.single i 1)) l) := by
      filter_upwards [hΩ.mem_nhds hq] with p hp
      have hs : (fun x ↦ response (x,p.2)) =ᶠ[𝓝 p.1] (fun x ↦ completed (x,p.2)) := by
        filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually
          (hΩ.mem_nhds hp)] with x hx
        exact he hx
      rw [hs.fderiv_eq]
    rw [(hder.iteratedFDeriv ℝ r).eq_of_nhds]
    simpa only [hsmall₂] using hHB l i r hr q hq

end JanetCartan.CanonicalAtomRealization
