module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.FixedSolverParameterRealization

/-!
# Observing the original inverse without a second source cutoff

The actual vector solver in `OriginalUncutSolver` represents the full paired
solver applied to `chi3 * Inv h`. Its input already contains the original chi2.
The older fixed-solver parameter adapter instead requires `Inv (chi2 * h)` and
cannot be applied to that solver merely from source support.

This leaf retains the existing two stress quadratures, combines them before the
same complex inverse, and reuses the existing joint graph realization and
parameter-jet identification. There is no chi2 argument, inverse-input recut,
output cutoff, or choice of a new smooth solver. The explicit source-class
identity must be proved for the literal original full-strain source by the
parent. Ordinary positive estimates give joint smoothness, not the graded
uniform `Cresp` bounds; those still require the native finite-word expansion
and observed full-inverse remainder.

Consumers: the uncut primary response reconstruction and
`app:ch_response:eq:response-actual-solver-formula`,
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Frobenius
  JanetCartan.TensorFrobenius JanetCartan.RegularSector.Realization

namespace JanetCartan.PhysicalPrimary.OriginalUncutObservation

open FixedDomainInverse LocalSobolev SmallSupport Pseudodifferential
  RegularSector RegularSector.Realization
  RegularSector.Characteristic.RetardedLocalization
  FourierIntegral FiniteChain.Graph.KernelLimits
  CompatibleResponse CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension
  ResponseTransfer ResponseTransfer.Complement CanonicalAtomRealization
  ResponseTransfer.Complement.ParameterDerivatives.Hilbert ObservedParameterRemainders

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The literal two-quadrature solution of `chi3 * Inv` is observed through
that same complex Neumann inverse. Unlike the recut adapter, this has neither
an inner chi2 nor a hypothesis that chi3 fixes the inverse output. The actual
smooth-solver representation is supplied by `OriginalUncutSolver.uncut_solver_ae`
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem fixedSmoothSolverComplexSolution_ae_uncut_neumann_observation
    {d : ℕ}
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (η : Euclidean (d+1) → ℝ)
    {sourceSupport U W : Set (Euclidean (d+1))}
    (hU : IsOpen U) (hW : MeasurableSet W)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : sourceSupport ⊆ U)
    (solver : smoothSource W (Euclidean (d+1)) →ₗ[ℝ]
      (Euclidean (d+1) → Euclidean (d+1)))
    (S : Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure (Euclidean (d+1))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin (d+1))) 2 volume)
    (hS : conjugateOperator S.toLinearMap = S.toLinearMap)
    (R : LocalL2 W (EuclideanSpace ℂ (Fin (d+1))) →L[ℂ]
      LocalL2 W (EuclideanSpace ℂ (Fin (d+1))))
    (hRreal : conjugateOperator R.toLinearMap = R.toLinearMap) (hR : ‖R‖ < 1)
    {center : Euclidean (d+1)} (χ₃ : ContDiffBump center)
    (hsolverAE : ∀ v : smoothSource W (Euclidean (d+1)),
      solver v =ᵐ[volume] realCompression S (zeroExtend hW
        (bumpL2 (p := 2) le_rfl χ₃ (neumannInverse (realOutputCompression R) v))))
    (tensor : Euclidean (d+1) → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hre : tensorFieldRealPart tensor ∈ compactSmoothSources sourceSupport)
    (him : tensorFieldImagPart tensor ∈ compactSmoothSources sourceSupport) :
    let re := cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, hre⟩
    let im := cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, him⟩
    fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver tensor hre him =ᵐ[volume]
      S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃
        (complexNeumannInverse R hR
          (l2ComplexInclusion (volume.restrict W) (re : LocalL2 W (Euclidean (d+1))) +
            Complex.I • l2ComplexInclusion (volume.restrict W)
              (im : LocalL2 W (Euclidean (d+1))))))) := by
  intro re im
  rw [neumannInverse_quadratures R hRreal hR, bumpL2_complex_quadratures]
  exact fixedSmoothSolverComplexSolution_ae_complex_observation Q η hU hW hQ hη hSU
    solver S hS ((bumpL2 (p := 2) le_rfl χ₃).comp
      (neumannInverse (realOutputCompression R))) hsolverAE tensor hre him

variable {d p : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (η : Euclidean (d+1) → ℝ)
    {sourceSupport U W : Set (Euclidean (d+1))}
    (hU : IsOpen U) (hW : MeasurableSet W)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : sourceSupport ⊆ U)
    (solver : smoothSource W (Euclidean (d+1)) →ₗ[ℝ]
      (Euclidean (d+1) → Euclidean (d+1)))
    (S : Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure (Euclidean (d+1))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin (d+1))) 2 volume)
    (hSreal : conjugateOperator S.toLinearMap = S.toLinearMap)
    (R : LocalL2 W (EuclideanSpace ℂ (Fin (d+1))) →L[ℂ]
      LocalL2 W (EuclideanSpace ℂ (Fin (d+1))))
    (hRreal : conjugateOperator R.toLinearMap = R.toLinearMap) (hR : ‖R‖ < 1)
    {center : Euclidean (d+1)} (χ₃ : ContDiffBump center)
    (hsolverAE : ∀ v : smoothSource W (Euclidean (d+1)),
      solver v =ᵐ[volume] realCompression S (zeroExtend hW
        (bumpL2 (p := 2) le_rfl χ₃ (neumannInverse (realOutputCompression R) v))))
    (V : Set Z) (hV : IsOpen V)
    (tensor : Z → Euclidean (d+1) → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hre : ∀ c ∈ V, tensorFieldRealPart (tensor c) ∈ compactSmoothSources sourceSupport)
    (him : ∀ c ∈ V, tensorFieldImagPart (tensor c) ∈ compactSmoothSources sourceSupport)
    (τ : ℝ) (φ : Z → Euclidean (d+1) → ℝ)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (g : Z → Euclidean (d+1) → EuclideanSpace ℂ (Fin (d+1)))
    (hm : ∀ c, MemLp (g c) 2 volume)
    (hsource : ∀ c (hc : c ∈ V),
      let re := cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, hre c hc⟩
      let im := cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, him c hc⟩
      l2ComplexInclusion (volume.restrict W) (re : LocalL2 W (Euclidean (d+1))) +
        Complex.I • l2ComplexInclusion (volume.restrict W)
          (im : LocalL2 W (Euclidean (d+1))) = restrictL2 W ((hm c).toLp (g c)))

set_option quotPrecheck false in
local notation "gsolver" => fixedSolverParameterEnvelope Q η hU hQ hη hSU solver
  V tensor hre him τ (fun w : Euclidean (d+1) × Z ↦ φ w.2 w.1)

set_option quotPrecheck false in
local notation "observation" => (fun c ↦ carrierMultiplication (-τ⁻¹)
  (totalizedObservationPhase V φ c) (continuous_totalizedObservationPhase hφ c)
  (S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃
    (complexNeumannInverse R hR (restrictL2 W ((hm c).toLp (g c))))))))

include hSreal hRreal hsolverAE hsource

/-- The same reduced envelope is represented by the once-localized full
inverse observation. The source equality is on the actual stress quadratures,
without another chi2 multiplier; support alone is not used to infer it
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem fixedSolverParameterEnvelope_ae_uncut_complex_inverse
    {c : Z} (hc : c ∈ V) :
    observation c =ᵐ[volume] fun x ↦ gsolver (x,c) := by
  have hs := fixedSmoothSolverComplexSolution_ae_uncut_neumann_observation
    Q η hU hW hQ hη hSU solver S hSreal R hRreal hR χ₃ hsolverAE
    (tensor c) (hre c hc) (him c hc)
  dsimp only at hs
  have he := congrArg (fun z : LocalL2 W (EuclideanSpace ℂ (Fin (d+1))) ↦
    S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (complexNeumannInverse R hR z))))
      (hsource c hc)
  have hs' := hs.trans (Filter.Eventually.of_forall (fun x ↦
    congrArg (fun z : Lp (EuclideanSpace ℂ (Fin (d+1))) 2 volume ↦ z x) he))
  have hmultiply := carrierMultiplication_ae (-τ⁻¹)
    (totalizedObservationPhase V φ c) (continuous_totalizedObservationPhase hφ c)
    (S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃
      (complexNeumannInverse R hR (restrictL2 W ((hm c).toLp (g c)))))))
  filter_upwards [hs', hmultiply] with x hx hy
  change observation c x = _ at hy ⊢
  apply hy.trans
  rw [totalizedObservationPhase_of_mem φ hc, carrier_eq_waveCarrier]
  simp only [fixedSolverParameterEnvelope, dite_eq_left hc]
  exact congrArg (fun z : EuclideanSpace ℂ (Fin (d+1)) ↦
    waveCarrier (-τ⁻¹) (φ c) x • z) hx.symm

include hV

/-- Ordinary positive estimates construct joint smoothness and the exact
ordered Fourier representatives of the unchanged uncut solver. These estimates
are not the uniform graded response bound: that later bound applies to the
literal `observation` and transfers by the displayed norm equalities. No
pointwise statement about an arbitrary zero extension is inferred from an
a.e. identity (`app:ch_response:thm:response-literal-transfer`). -/
theorem fixedSolverParameterEnvelope_joint_and_parameter_classes_of_uncut
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (hs₃ : tsupport (χ₃ : Euclidean (d+1) → ℝ) ⊆ W)
    (CI highI CS highS : ℕ → ℝ)
    (hCI : ∀ s, 0 ≤ CI s) (hhighI : ∀ s, 0 ≤ highI s)
    (hCS : ∀ s, 0 ≤ CS s) (hhighS : ∀ s, 0 ≤ highS s)
    (hInv : ∀ s (u : LocalL2 W (Euclidean (d+1))), MemRestrictionSobolev W s u →
      MemRestrictionSobolev W s (neumannInverse (realOutputCompression R) u) ∧
        restrictionSobolevNorm W s (neumannInverse (realOutputCompression R) u) ≤
          CI s * (restrictionSobolevNorm W s u + highI s * ‖u‖))
    (hS : ∀ (s : ℕ)
      (u : Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure (Euclidean (d+1)))),
      MemVectorFourierSobolev (s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (S u) ∧
        vectorFourierSobolevNorm (s : ℝ) (S u) ≤
          CS s * (vectorFourierSobolevNorm (s : ℝ) u + highS s * ‖u‖))
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d+1))
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (coords : Euclidean p ≃L[ℝ] Z)
    {X Xφ : Set (Euclidean (d+1))} (hX : IsCompact X) (hXφ : IsCompact Xφ)
    (hg : ContDiff ℝ ∞ (fun w : Euclidean (d+1) × Z ↦ g w.2 w.1))
    (hgs : ∀ c, tsupport (g c) ⊆ X)
    (hsφ : ∀ c ∈ V, tsupport (φ c) ⊆ Xφ) :
    ContDiffOn ℝ ∞ gsolver (univ ×ˢ V) ∧
      ContDiffOn ℝ ∞ observation V ∧
      ∀ c ∈ V, ∀ k (v : Fin k → Z),
        ∃ ug : PiLp 2 (fun _ : Fin (d+1) ↦ Lp ℂ 2 (volume : Measure (Euclidean (d+1)))),
          (∀ j, ug j =ᵐ[volume] fun x ↦
            (iteratedFDeriv ℝ k (fun b ↦ gsolver (x,b)) c v) j) ∧
          ug = finiteL2CoordinateIsometry volume (iteratedFDeriv ℝ k observation c v) ∧
          (∀ s : ℝ, MemMatrixFourierSobolev s ug ↔
            MemVectorFourierSobolev s (iteratedFDeriv ℝ k observation c v)) ∧
          (∀ s : ℝ, matrixFourierSobolevNorm s ug =
            vectorFourierSobolevNorm s (iteratedFDeriv ℝ k observation c v)) := by
  classical
  let solution : Z → Euclidean (d+1) → EuclideanSpace ℂ (Fin (d+1)) := fun c ↦
    if hc : c ∈ V then
      fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver (tensor c) (hre c hc) (him c hc)
    else 0
  have hsmooth (c : Z) (hc : c ∈ V) : ContDiff ℝ ∞ (solution c) := by
    simpa only [solution, dite_eq_left hc] using
      contDiff_fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver hsolver
        (tensor c) (hre c hc) (him c hc)
  have hidentify (c : Z) (hc : c ∈ V) : solution c =ᵐ[volume]
      complexLocalSolverObservation hW χ₃ S (complexNeumannInverse R hR)
        ((hm c).toLp (g c)) := by
    have hs := fixedSmoothSolverComplexSolution_ae_uncut_neumann_observation
      Q η hU hW hQ hη hSU solver S hSreal R hRreal hR χ₃ hsolverAE
      (tensor c) (hre c hc) (him c hc)
    dsimp only at hs
    have heq := congrArg (fun z : LocalL2 W (EuclideanSpace ℂ (Fin (d+1))) ↦
      S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (complexNeumannInverse R hR z))))
        (hsource c hc)
    have hs' := hs.trans (Filter.Eventually.of_forall (fun x ↦
      congrArg (fun z : Lp (EuclideanSpace ℂ (Fin (d+1))) 2 volume ↦ z x) heq))
    change solution c =ᵐ[volume]
      S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃
        (complexNeumannInverse R hR (restrictL2 W ((hm c).toLp (g c))))))
    simpa only [solution, dite_eq_left hc] using hs'
  -- "recut" in the reused name describes g's existing source localization.
  -- Its signature has only chi3 AFTER Inv and no chi2 or output cutoff.
  have hsolution := contDiffOn_recut_full_solver_joint_solution W hW χ₃ hs₃ R hRreal hR S
    CI highI CS highS hCI hhighI hCS hhighS hInv hS e he coords hX g hg hgs hm V solution
    hsmooth hidentify
  have hphase : ContDiffOn ℝ ∞ (fun w : Euclidean (d+1) × Z ↦ φ w.2 w.1) (univ ×ˢ V) :=
    hφ.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun w hw ↦ ⟨hw.2, hw.1⟩)
  have hcarrier : ContDiffOn ℝ ∞
      (fun w : Euclidean (d+1) × Z ↦ waveCarrier (-τ⁻¹) (φ w.2) w.1) (univ ×ˢ V) :=
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
  have hsourceSmooth : ContDiffOn ℝ ∞ (fun c ↦ restrictL2 W ((hm c).toLp (g c))) V :=
    (restrictL2 W :
      Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure (Euclidean (d+1))) →L[ℝ]
        LocalL2 W (EuclideanSpace ℂ (Fin (d+1)))).contDiff.comp_contDiffOn hsourceGlobal
  have hsTot (c : Z) (hc : c ∈ V) :
      tsupport (totalizedObservationPhase V φ c) ⊆ Xφ := by
    rw [totalizedObservationPhase_of_mem φ hc]
    exact hsφ c hc
  have hobservation : ContDiffOn ℝ ∞ observation V :=
    contDiffOn_demodulated_fixed_local_operator hW χ₃ hV hXφ τ⁻¹
      (totalizedObservationPhase V φ) (continuous_totalizedObservationPhase hφ)
      (contDiffOn_totalizedObservationPhase hφ) hsTot S
      ((complexNeumannInverse R hR).restrictScalars ℝ)
      (fun c ↦ restrictL2 W ((hm c).toLp (g c))) hsourceSmooth
  refine ⟨hG, hobservation, ?_⟩
  intro c hc k v
  have hGc : ContDiffOn ℝ ∞ (Function.uncurry (fun c x ↦ gsolver (x,c))) (V ×ˢ univ) :=
    hG.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun w hw ↦ ⟨hw.2, hw.1⟩)
  exact exists_matrixFourier_parameter_jet_class_of_joint_smooth hV hGc hobservation
    (fun c hc ↦ fixedSolverParameterEnvelope_ae_uncut_complex_inverse Q η hU hW hQ hη hSU
      solver S hSreal R hRreal hR χ₃ hsolverAE V tensor hre him τ φ hφ g hm hsource hc)
    k v hc

end JanetCartan.PhysicalPrimary.OriginalUncutObservation
