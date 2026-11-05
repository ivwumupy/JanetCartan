module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.JointSolutionRealization
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ParameterJetRealization
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ParameterObservationAssembly
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.SmoothIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.SameSolver
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Complex

/-!
# Joint Fourier realization of the same initialized parameter envelope

The initialized physical source already contains the actual inner recut.
Use its original admission identity, the original real inverse's positive
estimates and the full solver's positive estimates to prove joint smoothness
of the literal `fixedSolverParameterEnvelope`. Its parameter derivatives are
then exactly the Fourier classes of the same observed complex inverse.

The quantitative finite-word/inverse bound is applied to these classes;
no joint output regularity, classical derivative representative, independent
solver or extra recut is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open scoped JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport Pseudodifferential RegularSector RegularSector.Realization
open RegularSector.Characteristic.RetardedLocalization
open FourierIntegral FiniteChain.Graph.KernelLimits
open CompatibleResponse CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension
open ResponseTransfer ResponseTransfer.Complement CanonicalAtomRealization
open ResponseTransfer.Complement.ParameterDerivatives.Hilbert
open ObservedParameterRemainders

variable {d p : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
local notation "E" => Euclidean (d+1)
local notation "CF" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp CF 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

variable
    (Q : (Euclidean (d+1)) → Fin (d+1) → MetricTensor (d+1)) (η : (Euclidean (d+1)) → ℝ)
    {sourceSupport U W : Set (Euclidean (d+1))} (hU : IsOpen U) (hW : MeasurableSet W)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : sourceSupport ⊆ U)
    (solver : smoothSource W (Euclidean (d+1)) →ₗ[ℝ] ((Euclidean (d+1)) → (Euclidean (d+1))))
    (S : (Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure (Euclidean (d+1)))) →L[ℂ] (Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure (Euclidean (d+1))))) (hSreal : conjugateOperator S.toLinearMap = S.toLinearMap)
    (R : LocalL2 W (EuclideanSpace ℂ (Fin (d+1))) →L[ℂ] LocalL2 W (EuclideanSpace ℂ (Fin (d+1))))
    (hRreal : conjugateOperator R.toLinearMap = R.toLinearMap) (hR : ‖R‖ < 1)
    {center : (Euclidean (d+1))} (χ₂ χ₃ : ContDiffBump center)
    (Corr : LocalL2 W (Euclidean (d+1)) →L[ℝ] LocalL2 W (Euclidean (d+1)))
    (hCorr : Corr = (neumannInverse (realOutputCompression R)).comp
      (bumpL2 (p := 2) le_rfl χ₂))
    (hfix : ∀ v : LocalL2 W (Euclidean (d+1)), bumpL2 (p := 2) le_rfl χ₃ (Corr v) = Corr v)
    (hsolverAE : ∀ v : smoothSource W (Euclidean (d+1)),
      solver v =ᵐ[volume] realCompression S (zeroExtend hW (Corr v)))
    (V : Set Z) (hV : IsOpen V)
    (tensor : Z → (Euclidean (d+1)) → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hre : ∀ c ∈ V, tensorFieldRealPart (tensor c) ∈ compactSmoothSources sourceSupport)
    (him : ∀ c ∈ V, tensorFieldImagPart (tensor c) ∈ compactSmoothSources sourceSupport)
    (τ : ℝ) (φ : Z → (Euclidean (d+1)) → ℝ)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (g : Z → (Euclidean (d+1)) → (EuclideanSpace ℂ (Fin (d+1)))) (hm : ∀ c, MemLp (g c) 2 volume)
    (hrecut : ∀ c (hc : c ∈ V),
      let re := cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, hre c hc⟩
      let im := cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, him c hc⟩
      l2ComplexInclusion (volume.restrict W) (bumpL2 (p := 2) le_rfl χ₂ (re : LocalL2 W (Euclidean (d+1)))) +
        Complex.I • l2ComplexInclusion (volume.restrict W)
          (bumpL2 (p := 2) le_rfl χ₂ (im : LocalL2 W (Euclidean (d+1)))) =
        restrictL2 W ((hm c).toLp (g c)))

set_option quotPrecheck false in
local notation "gsolver" => fixedSolverParameterEnvelope Q η hU hQ hη hSU solver
  V tensor hre him τ (fun w : E × Z ↦ φ w.2 w.1)

set_option quotPrecheck false in
local notation "observation" => (fun c ↦ carrierMultiplication (-τ⁻¹)
  (totalizedObservationPhase V φ c) (continuous_totalizedObservationPhase hφ c)
  (S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃
    (complexNeumannInverse R hR (restrictL2 W ((hm c).toLp (g c))))))))

include hSreal hRreal hCorr hfix hsolverAE hrecut

/-- The parameter envelope used by literal reconstruction is represented by
the exact observed complex inverse of the original recut source. The
admission identity is supplied by
`fullPrimary_initialized_complexRecut_eq_original_envelope`
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem fixedSolverParameterEnvelope_ae_recut_complex_inverse
    {c : Z} (hc : c ∈ V) :
    observation c =ᵐ[volume] fun x ↦ gsolver (x,c) := by
  have hs := fixedSmoothSolverComplexSolution_ae_complex_neumann_observation
    Q η hU hW hQ hη hSU solver S hSreal R hRreal hR χ₂ χ₃ Corr hCorr hfix hsolverAE
    (tensor c) (hre c hc) (him c hc)
  dsimp only at hs
  have he := congrArg (fun z : LocalL2 W CF ↦
    S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (complexNeumannInverse R hR z))))
      (hrecut c hc)
  have hs' := hs.trans (Filter.Eventually.of_forall (fun x ↦
    congrArg (fun z : H ↦ z x) he))
  have hmultiply := carrierMultiplication_ae (-τ⁻¹)
    (totalizedObservationPhase V φ c) (continuous_totalizedObservationPhase hφ c)
    (S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃
      (complexNeumannInverse R hR (restrictL2 W ((hm c).toLp (g c)))))))
  filter_upwards [hs', hmultiply] with x hx hy
  change observation c x = _ at hy ⊢
  apply hy.trans
  rw [totalizedObservationPhase_of_mem φ hc, carrier_eq_waveCarrier]
  simp only [fixedSolverParameterEnvelope, dite_eq_left hc]
  exact congrArg (fun z : CF ↦ waveCarrier (-τ⁻¹) (φ c) x • z) hx.symm

include hV

/-- Original positive estimates and the original compact physical source
construct joint smoothness and all parameter Fourier representatives of the
SAME retained smooth solver. The inverse's quantitative estimate applies to
the displayed `observation`, and all its Sobolev norms transfer without loss
to the literal classical parameter jets consumed by
`fullPrimaryResponse_fixedSolver_profile_family`
(`app:ch_response:eq:response-graded-reduced`,
`app:ch_response:thm:response-literal-transfer`). -/
theorem fixedSolverParameterEnvelope_joint_and_parameter_classes
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (hs₃ : tsupport (χ₃ : E → ℝ) ⊆ W)
    (CI highI CS highS : ℕ → ℝ)
    (hCI : ∀ s, 0 ≤ CI s) (hhighI : ∀ s, 0 ≤ highI s)
    (hCS : ∀ s, 0 ≤ CS s) (hhighS : ∀ s, 0 ≤ highS s)
    (hInv : ∀ s (u : LocalL2 W E), MemRestrictionSobolev W s u →
      MemRestrictionSobolev W s (neumannInverse (realOutputCompression R) u) ∧
        restrictionSobolevNorm W s (neumannInverse (realOutputCompression R) u) ≤
          CI s * (restrictionSobolevNorm W s u + highI s * ‖u‖))
    (hS : ∀ (s : ℕ) (u : H), MemVectorFourierSobolev (s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (S u) ∧
        vectorFourierSobolevNorm (s : ℝ) (S u) ≤
          CS s * (vectorFourierSobolevNorm (s : ℝ) u + highS s * ‖u‖))
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (coords : Euclidean p ≃L[ℝ] Z)
    {X Xφ : Set E} (hX : IsCompact X) (hXφ : IsCompact Xφ)
    (hg : ContDiff ℝ ∞ (fun w : E × Z ↦ g w.2 w.1))
    (hgs : ∀ c, tsupport (g c) ⊆ X)
    (hsφ : ∀ c ∈ V, tsupport (φ c) ⊆ Xφ) :
    ContDiffOn ℝ ∞ gsolver (univ ×ˢ V) ∧
      ContDiffOn ℝ ∞ observation V ∧
      ∀ c ∈ V, ∀ k (v : Fin k → Z),
        ∃ ug : PiLp 2 (fun _ : Fin (d+1) ↦ Lp ℂ 2 (volume : Measure E)),
          (∀ j, ug j =ᵐ[volume] fun x ↦
            (iteratedFDeriv ℝ k (fun b ↦ gsolver (x,b)) c v) j) ∧
          ug = finiteL2CoordinateIsometry volume (iteratedFDeriv ℝ k observation c v) ∧
          (∀ s : ℝ, MemMatrixFourierSobolev s ug ↔
            MemVectorFourierSobolev s (iteratedFDeriv ℝ k observation c v)) ∧
          (∀ s : ℝ, matrixFourierSobolevNorm s ug =
            vectorFourierSobolevNorm s (iteratedFDeriv ℝ k observation c v)) := by
  classical
  let solution : Z → E → CF := fun c ↦ if hc : c ∈ V then
    fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver (tensor c) (hre c hc) (him c hc)
    else 0
  have hsmooth (c : Z) (hc : c ∈ V) : ContDiff ℝ ∞ (solution c) := by
    simpa only [solution, dite_eq_left hc] using
      contDiff_fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver hsolver
        (tensor c) (hre c hc) (him c hc)
  have hidentify (c : Z) (hc : c ∈ V) : solution c =ᵐ[volume]
      complexLocalSolverObservation hW χ₃ S (complexNeumannInverse R hR)
        ((hm c).toLp (g c)) := by
    have hs := fixedSmoothSolverComplexSolution_ae_complex_neumann_observation
      Q η hU hW hQ hη hSU solver S hSreal R hRreal hR χ₂ χ₃ Corr hCorr hfix hsolverAE
      (tensor c) (hre c hc) (him c hc)
    dsimp only at hs
    have he := congrArg (fun z : LocalL2 W CF ↦
      S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (complexNeumannInverse R hR z))))
        (hrecut c hc)
    have hs' := hs.trans (Filter.Eventually.of_forall (fun x ↦
      congrArg (fun z : H ↦ z x) he))
    change solution c =ᵐ[volume]
      S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃
        (complexNeumannInverse R hR (restrictL2 W ((hm c).toLp (g c))))))
    simpa only [solution, dite_eq_left hc] using hs'
  have hsolution := contDiffOn_recut_full_solver_joint_solution W hW χ₃ hs₃ R hRreal hR S
    CI highI CS highS hCI hhighI hCS hhighS hInv hS e he coords hX g hg hgs hm V solution
    hsmooth hidentify
  have hphase : ContDiffOn ℝ ∞ (fun w : E × Z ↦ φ w.2 w.1) (univ ×ˢ V) :=
    hφ.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun w hw ↦ ⟨hw.2, hw.1⟩)
  have hcarrier : ContDiffOn ℝ ∞
      (fun w : E × Z ↦ waveCarrier (-τ⁻¹) (φ w.2) w.1) (univ ×ˢ V) :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hphase)).cexp
  have hG : ContDiffOn ℝ ∞ gsolver (univ ×ˢ V) := by
    apply (hcarrier.smul hsolution).congr
    intro w hw
    change gsolver w = waveCarrier (-τ⁻¹) (φ w.2) w.1 • solution w.2 w.1
    simp only [fixedSolverParameterEnvelope, solution, dite_eq_left hw.2]
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  have hgswap : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ) :=
    (hg.comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  have hzero : ∀ c ∈ V, ∀ x ∉ X, g c x = 0 := by
    intro c _ x hx
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hgs c h))
  have hsourceGlobal : ContDiffOn ℝ ∞ (fun c ↦ (hm c).toLp (g c)) V := by
    apply (contDiffOn_compactVectorL2Family hX hV hgswap).congr
    intro c hc
    apply Lp.ext
    exact (hm c).coeFn_toLp.trans (compactVectorL2Family_ae hX hgswap hzero hc).symm
  have hsource : ContDiffOn ℝ ∞ (fun c ↦ restrictL2 W ((hm c).toLp (g c))) V :=
    (restrictL2 W : H →L[ℝ] LocalL2 W CF).contDiff.comp_contDiffOn hsourceGlobal
  have hsTot (c : Z) (hc : c ∈ V) :
      tsupport (totalizedObservationPhase V φ c) ⊆ Xφ := by
    rw [totalizedObservationPhase_of_mem φ hc]
    exact hsφ c hc
  have hobservation : ContDiffOn ℝ ∞ observation V :=
    contDiffOn_demodulated_fixed_local_operator hW χ₃ hV hXφ τ⁻¹
      (totalizedObservationPhase V φ) (continuous_totalizedObservationPhase hφ)
      (contDiffOn_totalizedObservationPhase hφ) hsTot S
      ((complexNeumannInverse R hR).restrictScalars ℝ)
      (fun c ↦ restrictL2 W ((hm c).toLp (g c))) hsource
  refine ⟨hG, hobservation, ?_⟩
  intro c hc k v
  have hGc : ContDiffOn ℝ ∞ (Function.uncurry (fun c x ↦ gsolver (x,c))) (V ×ˢ univ) :=
    hG.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun w hw ↦ ⟨hw.2, hw.1⟩)
  exact exists_matrixFourier_parameter_jet_class_of_joint_smooth hV hGc hobservation
    (fun c hc ↦ fixedSolverParameterEnvelope_ae_recut_complex_inverse Q η hU hW hQ hη hSU
      solver S hSreal R hRreal hR χ₂ χ₃ Corr hCorr hfix hsolverAE V tensor hre him τ φ hφ g hm hrecut hc)
    k v hc

end JanetCartan.FixedDomainInverse
