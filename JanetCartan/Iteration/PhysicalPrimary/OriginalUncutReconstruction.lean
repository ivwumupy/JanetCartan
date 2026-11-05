module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalAmbientSupport
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.RetainedFamily
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.FixedSolverReconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSources
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.SameSolver
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Restriction

/-!
# Admitted-source bridge for the native uncut response

This is a deliberately narrow bridge for the actual original application.  The
proof-cutoff `Ξ` is auxiliary proof data only; the native response on the left
is the globally uncut `uncutAmbientExtension`.  Equality is established only
on the admitted source class, using the native solver support certificate.  No
second `χ₂`, no replacement inverse, and no response estimate or `Cresp`
premise is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary.OriginalUncutReconstruction

open FixedDomainInverse
open CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension
open AmbientResponse OriginalAmbientResponse

/-- The native source-mask certificate is exactly the remodulation identity
needed after the inverse: only `χ₃ = 1` on `tsupport χ₂` is used. -/
theorem source_cutoff_remodulation_eq
    {E Z : Type*} [TopologicalSpace E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (χ₂ χ₃ : E → ℝ) (f : E → Z)
    (hχ₃ : ∀ x ∈ tsupport χ₂, χ₃ x = 1) :
    (fun x ↦ χ₃ x • (χ₂ x • f x)) = fun x ↦ χ₂ x • f x := by
  funext x
  by_cases hx : χ₂ x = 0
  · simp [hx]
  · have hxs : x ∈ tsupport χ₂ := subset_tsupport χ₂ hx
    rw [hχ₃ x hxs]
    simp

/-- Turn the original eventual-one phase-germ certificate into the collar
used by the retained phase.  This does not select another phase cutoff. -/
theorem phase_cutoff_plateau_of_eventually_one
    {E : Type*} [TopologicalSpace E] {P : Set E} (χp : E → ℝ)
    (hχone : ∀ q ∈ P, χp =ᶠ[𝓝 q] fun _ ↦ 1) :
    P ⊆ interior {q | χp q = 1} := by
  intro q hq
  exact mem_interior_iff_mem_nhds.mpr (hχone q hq)

/-- On the original physical/parameter collar, multiplication by the
prescribed phase cutoff leaves the native phase unchanged. -/
theorem phase_cutoff_mul_eq_on_collared_set
    {E : Type*} [TopologicalSpace E] {P K : Set E} (χp φ : E → ℝ)
    (hK : K ⊆ P)
    (hχone : ∀ q ∈ P, χp =ᶠ[𝓝 q] fun _ ↦ 1) :
    EqOn (fun q ↦ χp q * φ q) φ K := by
  intro q hq
  have hone : χp q = 1 := (hχone q (hK hq)).self_of_nhds
  simp [hone]

/-- The actual uncut response and the proof-cutoff response agree on one
admitted real tensor source.  `Ξ` is not the native operator: it is used only
to expose the local germ where its plateau is known. -/
theorem uncutAmbientExtension_eq_fixedSmoothSolverAmbientExtension_of_native_support
    {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W core chart : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ]
      (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (Ξ : OutputCutoff core chart)
    (hsolverSupport : ∀ v, tsupport (solver v) ⊆ core)
    (hS : S ⊆ core) (h : compactSmoothSources S) :
    uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver h =
      fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ h := by
  have hsupp := uncutAmbientExtension_tsupport_subset
    F Q η hU hQ hη hSU solver hsolver hS hsolverSupport h
  rw [uncutAmbientExtension_apply] at hsupp
  rw [uncutAmbientExtension_apply,
    fixedSmoothSolverAmbientExtension_eq_cutoff]
  funext x
  by_cases hx : x ∈ core
  · have hplateau : x ∈ {y | Ξ.toFun y = 1} :=
      interior_subset (Ξ.plateau hx)
    rw [hplateau, one_smul]
  · have hnot : x ∉ tsupport
        (completedVariation F
          (solver (cutoffStressSmoothSource Q η hU hQ hη hSU h)) h) :=
      fun hxs ↦ hx (hsupp hxs)
    have hz := image_eq_zero_of_notMem_tsupport hnot
    rw [hz, smul_zero]

/-- Complexification preserves the admitted-source identity for both literal
real quadratures. -/
theorem complexifyResponse_uncut_eq_fixedSmoothSolverAmbientExtension_of_native_support
    {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W core chart : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ]
      (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (Ξ : OutputCutoff core chart)
    (hsolverSupport : ∀ v, tsupport (solver v) ⊆ core)
    (hS : S ⊆ core)
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hre : tensorFieldRealPart h ∈ compactSmoothSources S)
    (him : tensorFieldImagPart h ∈ compactSmoothSources S) :
    complexifyResponse (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver) h =
      complexifyResponse
        (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ) h := by
  have hr := uncutAmbientExtension_eq_fixedSmoothSolverAmbientExtension_of_native_support
    F Q η hU hQ hη hSU solver hsolver Ξ hsolverSupport hS ⟨_, hre⟩
  have hi := uncutAmbientExtension_eq_fixedSmoothSolverAmbientExtension_of_native_support
    F Q η hU hQ hη hSU solver hsolver Ξ hsolverSupport hS ⟨_, him⟩
  funext x
  ext j
  simp only [complexifyResponse, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hr, hi]

/-- Every spatial jet of the two admitted complex responses agrees.  This is
only a source-class identity; no graded response bound is asserted. -/
theorem iteratedFDeriv_complexifyResponse_uncut_eq_fixedSmoothSolverAmbientExtension_of_native_support
    {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W core chart : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ]
      (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (Ξ : OutputCutoff core chart)
    (hsolverSupport : ∀ v, tsupport (solver v) ⊆ core)
    (hS : S ⊆ core)
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hre : tensorFieldRealPart h ∈ compactSmoothSources S)
    (him : tensorFieldImagPart h ∈ compactSmoothSources S)
    (k : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ k
        (complexifyResponse (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver) h) x =
      iteratedFDeriv ℝ k
        (complexifyResponse
          (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ) h) x := by
  rw [complexifyResponse_uncut_eq_fixedSmoothSolverAmbientExtension_of_native_support
    F Q η hU hQ hη hSU solver hsolver Ξ hsolverSupport hS h hre him]

open CompatibleResponse ResponseTransfer CanonicalAtomRealization

/-- On the actual admitted tensor class, the native globally uncut response is
exactly the complex canonical completion of its two original reduced solutions.
No proof cutoff or support-core hypothesis is needed for this identity
(`app:ch_response:eq:response-full-map`). -/
theorem complexify_uncutAmbientExtension_eq_completedVariation
    {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hre : tensorFieldRealPart h ∈ compactSmoothSources S)
    (him : tensorFieldImagPart h ∈ compactSmoothSources S) :
    complexifyResponse (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver) h =
      completedVariationComplex F
        (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver h hre him) h := by
  have hv := contDiff_fixedSmoothSolverComplexSolution Q η hU hQ hη hSU
    solver hsolver h hre him
  have hvre : (fun y ↦ WithLp.toLp 2 (fun j ↦
      (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver h hre him y j).re)) =
      solver (cutoffStressSmoothSource Q η hU hQ hη hSU ⟨_,hre⟩) := by
    ext y j
    simp [fixedSmoothSolverComplexSolution]
  have hvim : (fun y ↦ WithLp.toLp 2 (fun j ↦
      (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver h hre him y j).im)) =
      solver (cutoffStressSmoothSource Q η hU hQ hη hSU ⟨_,him⟩) := by
    ext y j
    simp [fixedSmoothSolverComplexSolution]
  ext x j
  apply Complex.ext
  · rw [complexifyResponse_re]
    change (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver
      (⟨_,hre⟩ : compactSmoothSources S) x) j = _
    rw [uncutAmbientExtension_apply,
      completedVariationComplex_re F h (hv.differentiable (by simp) x) j, hvre]
    rfl
  · rw [complexifyResponse_im]
    change (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver
      (⟨_,him⟩ : compactSmoothSources S) x) j = _
    rw [uncutAmbientExtension_apply,
      completedVariationComplex_im F h (hv.differentiable (by simp) x) j, hvim]
    rfl

/-- The literal uncut parameter response and its remodulated canonical
completion agree on the entire original parameter window, hence in every
joint jet. The only source equation is the complete tensor remodulation,
proved below for the native primary atom. This is the algebraic input to
`completedVariationComplex_joint_response_graded`, not a response estimate
(`app:ch_response:eq:response-reconstruction-grading`). -/
theorem uncutParameterResponse_joint_reconstruction_jets
    {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (V : Set Z) (hV : IsOpen V)
    (source : Z → Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hre : ∀ c ∈ V, tensorFieldRealPart (source c) ∈ compactSmoothSources S)
    (him : ∀ c ∈ V, tensorFieldImagPart (source c) ∈ compactSmoothSources S)
    (τ : ℝ) (φ : Euclidean n × Z → ℝ) (χ : Euclidean n → ℝ)
    (a : Euclidean n × Z → Matrix (Fin n) (Fin n) ℂ)
    (hsource : ∀ c ∈ V, source c = fun x ↦
      waveCarrier τ⁻¹ (fun y ↦ φ (y,c)) x • ((χ x : ℂ) • a (x,c))) :
    let g := fixedSolverParameterEnvelope Q η hU hQ hη hSU solver V source hre him τ φ
    let response := fun p : Euclidean n × Z ↦ complexifyResponse
      (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver) (source p.2) p.1
    let completed := fun p : Euclidean n × Z ↦ completedVariationComplex F
      (modulatedWave τ⁻¹ (fun x ↦ φ (x,p.2)) (fun x ↦ g (x,p.2)))
      (fun x ↦ waveCarrier τ⁻¹ (fun y ↦ φ (y,p.2)) x • ((χ x : ℂ) • a (x,p.2))) p.1
    ∀ p : Euclidean n × Z, p.2 ∈ V →
      response =ᶠ[𝓝 p] completed ∧
      ∀ k, iteratedFDeriv ℝ k response p = iteratedFDeriv ℝ k completed p := by
  intro g response completed
  have he : EqOn response completed (univ ×ˢ V) := by
    intro p hp
    have hc := hp.2
    dsimp only [response, completed, g]
    rw [fixedSolverParameterEnvelope_remodulated Q η hU hQ hη hSU
      solver V source hre him τ φ hc]
    have hid := congrFun (complexify_uncutAmbientExtension_eq_completedVariation
      F Q η hU hQ hη hSU solver hsolver (source p.2) (hre p.2 hc) (him p.2 hc)) p.1
    exact hid.trans (congrArg (fun h ↦ completedVariationComplex F
      (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver (source p.2)
        (hre p.2 hc) (him p.2 hc)) h p.1) (hsource p.2 hc))
  intro p hp
  have hlocal : response =ᶠ[𝓝 p] completed :=
    Filter.eventuallyEq_of_mem ((isOpen_univ.prod hV).mem_nhds ⟨mem_univ _,hp⟩)
      (fun _ hq ↦ he hq)
  exact ⟨hlocal,fun k ↦ (hlocal.iteratedFDeriv ℝ k).self_of_nhds⟩

open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponsePrimarySources SourceNegative Sampling.BackgroundModulation

section PrimarySource
variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    (r : Euclidean (n-1) × Euclidean 3 → ℝ)
    (χ₂ : Euclidean n → ℝ) (τ : ℝ) (c : Euclidean 3 × Euclidean (n-1))
    (φ : Euclidean n → ℝ)
    (hφ : EqOn φ (fun x ↦ phase T Q x c.2) (tsupport χ₂))

include hφ

/-- The literal full primary tensor is remodulated using the retained phase
only on the original small source support. The complete raw strain amplitude
is kept, so no false inclusion of that support in the defect core is used
(`app:ch_response:eq:response-graded-source`). -/
theorem complexAtomicSource_eq_raw_modulated_of_phase_eq :
    complexAtomicSource F χ₂
      (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (x,c.2)) =
      modulatedSource χ₂ φ
        (fun x ↦ fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (x,c)) τ⁻¹ := by
  funext x
  by_cases hx : χ₂ x = 0
  · simp [complexAtomicSource, modulatedSource, hx]
  · have hc : carrier τ⁻¹ φ x = carrier τ⁻¹ (fun y ↦ phase T Q y c.2) x := by
      unfold carrier
      rw [hφ (subset_tsupport χ₂ hx)]
    simp only [complexAtomicSource, modulatedSource, hc,
      carrier_smul_fullPrimaryStrainAmplitude T Q F row col Φ Y r τ c x]

/-- The original envelope cutoff may be restored using exactly its native
pointwise plateau on the source support, not a source-core containment. This
is the tensor source identification used by the reserved reconstruction
(`app:ch_response:eq:response-graded-source`). -/
theorem complexAtomicSource_eq_native_envelope_modulated
    {core chart : Set (Euclidean n)} (χenv : OutputCutoff core chart)
    (henv : ∀ x ∈ tsupport χ₂, χenv.toFun x = 1) :
    complexAtomicSource F χ₂
      (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (x,c.2)) =
      modulatedSource χ₂ φ (fullStrainEnvelope T Q F row col Φ Y r χenv τ c) τ⁻¹ := by
  rw [complexAtomicSource_eq_raw_modulated_of_phase_eq T Q F row col Φ Y r χ₂ τ c φ hφ,
    fullStrainEnvelope_eq]
  funext x
  by_cases hx : χ₂ x = 0
  · simp [modulatedSource, hx]
  · simp only [modulatedSource, henv x (subset_tsupport χ₂ hx), one_smul]

/-- Both real quadratures of the actual tensor source have the same positive
complex forcing as `OriginalParameterRemainders.Source.a`. The parameter mask
is one at this admitted parameter; the measured source product and native
`χ₃_on_χ₂` remove neither an inverse nor a residual. In particular `τ³` is
only a later norm budget, not a factor inserted in this source identity
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem cutoffStress_rotated_fullPrimary_eq_native_forcing
    (χsrc χ₃ : Euclidean n → ℝ)
    (hsource : ∀ x, χsrc x * χ₂ x = χ₂ x)
    (hχ₃ : ∀ x ∈ tsupport χ₂, χ₃ x = 1)
    (θ : Euclidean 3 × Euclidean (n-1) → ℝ) (hθ : θ c = 1) (ζ : ℂ) :
    let atom := complexAtomicSource F χ₂
      (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (x,c.2))
    let a := fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
      θ w.2 • (χ₂ w.1 • ((1/2 : ℝ) • complexStressContraction (Q.1 w.1)
        (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ w)))
    euclideanCutoffStressSource Q.1 χsrc (tensorFieldRealPart (ζ • atom)) =
      fun x ↦ euclideanRealPart (ζ • modulatedSource χ₃ φ (fun y ↦ a (y,c)) τ⁻¹ x) := by
  intro atom a
  let raw := fun x ↦ fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (x,c)
  let reduced := modulatedSource χ₂ φ
    (fun x ↦ χsrc x • ((1/2 : ℝ) • complexStressContraction (Q.1 x) (raw x))) τ⁻¹
  have hraw : atom = modulatedSource χ₂ φ raw τ⁻¹ :=
    complexAtomicSource_eq_raw_modulated_of_phase_eq T Q F row col Φ Y r χ₂ τ c φ hφ
  have hred : reduced = modulatedSource χ₃ φ (fun y ↦ a (y,c)) τ⁻¹ := by
    funext x
    by_cases hx : χ₂ x = 0
    · simp [reduced, modulatedSource, a, hx]
    · simp only [reduced, modulatedSource, a, hθ, one_smul,
        hχ₃ x (subset_tsupport χ₂ hx)]
      rw [smul_comm (χ₂ x) (carrier τ⁻¹ φ x),
        smul_smul, mul_comm (χ₂ x) (χsrc x), hsource x]
  have hrot : ζ • modulatedSource χ₂ φ raw τ⁻¹ =
      modulatedSource χ₂ φ (ζ • raw) τ⁻¹ := by
    funext y
    simp only [Pi.smul_apply, modulatedSource]
    rw [smul_comm ζ (χ₂ y), smul_comm ζ (carrier τ⁻¹ φ y)]
  rw [hraw, hrot]
  refine (SignedProductEstimates.cutoff_stressSource_real_modulated_eq
    Q.1 χ₂ χsrc φ (ζ • raw) τ⁻¹).trans ?_
  rw [← hred]
  funext y
  simp only [reduced, modulatedSource, Pi.smul_apply, map_smul]
  rw [smul_comm ζ (χ₂ y), smul_comm ζ (carrier τ⁻¹ φ y),
    smul_comm ζ (χsrc y), smul_comm ζ (1/2 : ℝ)]
  exact (euclideanRealPart.map_smul (χ₂ y) _).symm

end PrimarySource

open MeasureTheory LocalSobolev RegularSector.Characteristic.RetardedLocalization

section NativeQuadratures
variable {d N : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (d+1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold})
    (F : Euclidean (d+1) → Euclidean N) (row col : Fin (d+1))
    (Φ Y : ℝ × (Euclidean d × (Euclidean 3 × Euclidean d)) →
      Euclidean d × (Euclidean 3 × Euclidean d))
    (r : Euclidean d × Euclidean 3 → ℝ)
    (χ₂ : Euclidean (d+1) → ℝ) (τ : ℝ) (c : Euclidean 3 × Euclidean d)
    (φ : Euclidean (d+1) → ℝ)
    (hφ : EqOn φ (fun x ↦ phase T Q x c.2) (tsupport χ₂))

include hφ

/-- The same native forcing class supplies BOTH actual smooth tensor-source
admissions. Tensor admission and global L² membership are proved from the
literal atom; no source-core containment, new forcing, or inverse is chosen.
This is the input-class bridge to the retained finite words and observed full
inverse (`app:ch_response:eq:response-actual-solver-formula`). -/
theorem fullPrimary_cutoffStressSmoothSource_native_quadratures
    {Ω : Set (Euclidean (d+1) × (Euclidean 3 × Euclidean d))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hn : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hχ₂ : ContDiff ℝ ∞ χ₂) (hcχ₂ : HasCompactSupport χ₂)
    (hΩc : ∀ x ∈ tsupport χ₂, (x,c) ∈ Ω)
    (χsrc χ₃ : Euclidean (d+1) → ℝ) (hχsrc : ContDiff ℝ ∞ χsrc)
    (hsource : ∀ x, χsrc x * χ₂ x = χ₂ x)
    (hχ₃ : ∀ x ∈ tsupport χ₂, χ₃ x = 1)
    (θ : Euclidean 3 × Euclidean d → ℝ) (hθ : θ c = 1) :
    let atom := complexAtomicSource F χ₂
      (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (x,c.2))
    let a := fun w : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦
      θ w.2 • (χ₂ w.1 • ((1/2 : ℝ) • complexStressContraction (Q.1 w.1)
        (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ w)))
    let forcing := modulatedSource χ₃ φ (fun y ↦ a (y,c)) τ⁻¹
    ∃ (hre : tensorFieldRealPart atom ∈ compactSmoothSources (tsupport χ₂))
      (him : tensorFieldImagPart atom ∈ compactSmoothSources (tsupport χ₂))
      (hm : MemLp forcing 2 volume), ∀ W : Set (Euclidean (d+1)),
      let admit := cutoffStressSmoothSource (W := W) Q.1 χsrc hU
        (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hχsrc
        (fun x hx ↦ hspace (x,c) (hΩc x hx))
      let u := restrictL2 W (hm.toLp forcing)
      (admit ⟨_,hre⟩ : LocalL2 W (Euclidean (d+1))) = l2RealPart (volume.restrict W) u ∧
      (admit ⟨_,him⟩ : LocalL2 W (Euclidean (d+1))) =
        l2RealPart (volume.restrict W) (-Complex.I • u) := by
  intro atom a forcing
  have hQU i := contDiffOn_pi.mp Q.property.1 i
  have hSU : tsupport χ₂ ⊆ U := fun x hx ↦ hspace (x,c) (hΩc x hx)
  have hw := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hn
  obtain ⟨hr,hi'⟩ := fullPrimaryAtom_source_mem T Q F row col Φ Y r hΩ hspace hF τ hw
    c.1 c.2 χ₂ hχ₂ hcχ₂ hΩc
  let realSource : compactSmoothSources (tsupport χ₂) := ⟨tensorFieldRealPart atom,hr⟩
  let imagSource : compactSmoothSources (tsupport χ₂) := ⟨tensorFieldImagPart atom,hi'⟩
  let R := euclideanCutoffStressSource Q.1 χsrc realSource
  let I := euclideanCutoffStressSource Q.1 χsrc imagSource
  have hrot (ζ : ℂ) : euclideanCutoffStressSource Q.1 χsrc
      (tensorFieldRealPart (ζ • atom)) = fun x ↦ euclideanRealPart (ζ • forcing x) :=
    cutoffStress_rotated_fullPrimary_eq_native_forcing T Q F row col Φ Y r χ₂ τ c φ hφ
      χsrc χ₃ hsource hχ₃ θ hθ ζ
  have hrEq : R = fun x ↦ euclideanRealPart (forcing x) := by
    simpa only [one_smul] using hrot 1
  have himag : tensorFieldImagPart atom = tensorFieldRealPart (-Complex.I • atom) := by
    ext x i j
    change (atom x i j).im = (-Complex.I * atom x i j).re
    simp
  have hiEq : I = fun x ↦ euclideanRealPart (-Complex.I • forcing x) := by
    change euclideanCutoffStressSource Q.1 χsrc (tensorFieldImagPart atom) = _
    rw [himag, hrot]
  have hmR := memLp_euclideanCutoffStressSource Q.1 χsrc hU hQU hχsrc hSU realSource
  have hmI := memLp_euclideanCutoffStressSource Q.1 χsrc hU hQU hχsrc hSU imagSource
  have hm : MemLp forcing 2 volume := by
    apply ((euclideanComplexInclusion.comp_memLp' hmR).add
      ((euclideanComplexInclusion.comp_memLp' hmI).const_smul Complex.I)).ae_eq
    filter_upwards with x
    ext i
    change ((R x i : ℝ) : ℂ) + Complex.I * ((I x i : ℝ) : ℂ) = forcing x i
    rw [hrEq,hiEq]
    simp [Complex.ext_iff]
  refine ⟨hr,hi',hm,?_⟩
  intro W admit u
  constructor
  · apply Lp.ext
    filter_upwards [cutoffStressSmoothSource_coeFn (W := W) Q.1 χsrc hU hQU hχsrc hSU realSource,
      euclideanRealPart.coeFn_compLpL u, restrictL2_coeFn W (hm.toLp forcing),
      ae_restrict_of_ae hm.coeFn_toLp] with y h1 h2 h3 h4
    exact h1.trans ((congrFun hrEq y).trans
      ((congrArg euclideanRealPart (h3.trans h4)).symm.trans h2.symm))
  · apply Lp.ext
    filter_upwards [cutoffStressSmoothSource_coeFn (W := W) Q.1 χsrc hU hQU hχsrc hSU imagSource,
      euclideanRealPart.coeFn_compLpL (-Complex.I • u), Lp.coeFn_smul (-Complex.I) u,
      restrictL2_coeFn W (hm.toLp forcing), ae_restrict_of_ae hm.coeFn_toLp] with y h1 h2 h3 h4 h5
    change (-Complex.I • u) y = -Complex.I • u y at h3
    have hpoint : (-Complex.I • u) y = -Complex.I • forcing y :=
      h3.trans (congrArg (fun v : EuclideanSpace ℂ (Fin (d+1)) ↦ -Complex.I • v) (h4.trans h5))
    exact h1.trans ((congrFun hiEq y).trans ((congrArg euclideanRealPart hpoint).symm.trans h2.symm))

end NativeQuadratures

end JanetCartan.PhysicalPrimary.OriginalUncutReconstruction
