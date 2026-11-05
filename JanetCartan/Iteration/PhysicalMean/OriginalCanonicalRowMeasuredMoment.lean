module
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowMeasuredAmplitude
public import JanetCartan.Iteration.PhysicalMean.CanonicalLowQuadratic
public meta import JanetCartan.Iteration.PhysicalMean.OriginalPeriodicBackgroundTemplate
public meta import Lean
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowActualBridge
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowMeasuredAmplitude
/-!
# Exact actual measured moment realization

The original scalar carrier factor, literal measured D amplitude, and original
real detector identify the SAME native shell kernel with the moment convention.
This leaf neither divides a sample/frequency/carrier weight nor changes the
selected sample, prefix, full phase, or fixed Fourier normalization.
Consumers: actual `hAn` and `hrow` of `fixedSourceQuadratic_low_bound` and
`fixedSourceQuadratic_source_profile` (`app:ch_mean_pairs:defn:mean-canonical`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open SamplingKernelBounds RawInputPartition PhysicalForwardMean
open OriginalMeanQuadraticProfiles.Actual
/-- Native kernel-to-moment algebra for the actual measured realization. Its
three equalities are later discharged by the original scalar kernel factor,
`D_amplitude_eq_measuredCross`, and the literal real original detector. -/
theorem originalMeasuredShellKernel_eq_moment {n J : ℕ} {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (D D₀ : BandKernelData (Fin J × P) n) (p : P) (b : ℝ)
    (H : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → EuclideanSpace ℂ (Fin n))
    (Z : Euclidean 3) (ζ : Euclidean (n-1)) (τ : ℝ) (det : Euclidean (n-1) → ℝ)
    (hD : ∀ j η x, D.kernel (j,p) η x = (b : ℂ) • D₀.kernel (j,p) η x)
    (hA : ∀ j η x, D₀.amplitude (((j,p),η),x) =
      (((2 * Real.pi) ^ (-(n : ℝ) / 2) * radialBand n j.val η : ℝ) : ℂ) •
        H (x,Z,ζ + τ • η))
    (hm : ∀ η, D₀.mask η = (det η : ℂ))
    (L : ℕ) (a : Fin n) (x : Euclidean n) (u : RefinedIndex J × Euclidean (n-1)) :
    Complex.ofReal (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) *
        originalMeasuredShellKernel D L p a x u =
      sampledMomentKernel (fun u : RefinedIndex J × Euclidean (n-1) ↦
          fun x ↦ D₀.phase (((u.1.1,p),u.2),x))
        (halfWeightedMomentMask (prefixMask L (fun u ↦ b * singleBareScalarMask det u)))
        (fun u ↦ measuredAdjointSlice H Z ζ τ a u.2) x u := by
  have h := originalMeasuredBand_eq_moment H Z ζ τ b
    (fun j η x ↦ D₀.phase (((j.1,p),η),x)) det L a u.1 u.2 x
  rw [← h]
  unfold originalMeasuredShellKernel
  split_ifs with hu
  · rw [hD,PiLp.smul_apply,smul_eq_mul]
    simp only [BandKernelData.kernel,bandKernel,hA,hm]
  · rfl

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow.MomentGenerator
open OriginalBackgroundHermitianTemplate
private def ns := `JanetCartan.PhysicalMean.OriginalCanonicalRow
private def mp := `JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfiles
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def store (label : Name) (params : Array Expr) (term : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let env ← getEnv
  let missing := term.getUsedConstants.filter (fun n => (env.find? n).isNone)
  unless missing.isEmpty do throwError "measured slice missing value {missing.toList}"
  let inferred ← inferType term
  let t := target.getD inferred
  for e in #[inferred,t] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "measured moment missing target {missing.toList}"
  let type ← instantiateMVars (← mkForallFVars params t)
  let value ← instantiateMVars (← mkLambdaFVars params term)
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "measured slice missing closed {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "measured slice open declaration {label}"
  let name := ns ++ label
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"checked actual measured slice {label}/{params.size}"
  return app name params

elab "publish_actual_measured_native_moment" : command => liftTermElabM do
  withActualRow fun d => do
    forallBoundedTelescope (← inferType d.native64[61]!) (some 1) fun colors _ => do
      withLocalDeclNoLocalInstanceUpdate `z .default (mkConst `JanetCartan.SeparatedSampling.Point) fun z => do
        let c := colors[0]!
        let params := (d.parameters ++ colors).push z
        let raw ← bodyAt `JanetCartan.PhysicalSampling.OriginalMeasuredFamily.Row.kernel d.native64
        let r := raw.getAppArgs
        let rowType ← inferType d.row
        unless rowType.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
          throwError "actual measured kernel: original row22 changed"
        let fixed := rowType.getAppArgs
        let J := r[44]!
        let D₀ := app (ns ++ `D) d.parameters
        let D := app `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.scalarKernel
          (fixed ++ #[d.row,J,D₀])
        let hDall := app `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.scalarKernel_factor
          (fixed ++ #[d.row,J,D₀])
        let hD ← forallBoundedTelescope (← inferType hDall) (some 1) fun band _ =>
          mkLambdaFVars band (mkAppN hDall #[band[0]!,c,z])
        let p ← mkAppM ``Prod.mk #[c,z]
        let hA ← forallBoundedTelescope (← inferType hD) (some 3) fun q _ => do
          let q0 ← mkAppM ``Prod.mk #[q[0]!,p]
          let q1 ← mkAppM ``Prod.mk #[q0,q[1]!]
          let q2 ← mkAppM ``Prod.mk #[q1,q[2]!]
          mkLambdaFVars q (mkApp (app (ns ++ `D_amplitude_eq_measuredCross) d.parameters) q2)
        let some conic := r[39]!.find? (·.isAppOfArity `JanetCartan.Sampling.originalConicDetector 5)
          | throwError "actual measured kernel: original conic factor missing"
        let detectorArgs := conic.getAppArgs
        let det := app `JanetCartan.PhysicalForwardMean.originalForwardDetector detectorArgs
        let hm0 := app `JanetCartan.PhysicalForwardMean.ofReal_originalForwardDetector detectorArgs
        let hm ← forallBoundedTelescope (← inferType hm0) (some 1) fun η _ => do
          mkLambdaFVars η (← mkAppM ``Eq.symm #[mkAppN hm0 η])
        let b ← forallBoundedTelescope (← inferType hD) (some 3) fun q eq => do
          unless eq.isAppOfArity ``Eq 3 do throwError "actual factor equality head changed"
          let rhs := eq.getAppArgs[2]!
          unless rhs.isAppOfArity ``HSMul.hSMul 6 do throwError "actual factor scalar head changed"
          let scalar := rhs.getAppArgs[4]!
          unless scalar.isAppOfArity ``Complex.ofReal 1 do throwError "actual factor no longer real"
          let factor := scalar.getAppArgs[0]!
          if (factor.find? (fun e => q.contains e)).isSome then
            throwError "actual carrier factor unexpectedly depends on frequency/point"
          return factor
        let H := app (ns ++ `measuredCross) (d.parameters ++ colors)
        let Z ← nodeAt z
        let ζ ← mkAppM `JanetCartan.Sampling.MeasuredAmplitude.extendedRetainedCarrier
          #[r[5]!,r[34]!,r[36]!,Z]
        let τ := mkApp d.native64[61]! c
        logInfo "actual native moment: literal factors prepared"
        let P ← inferType p
        let top ← synthInstance (← mkAppM ``TopologicalSpace #[P])
        let first ← synthInstance (mkAppN (mkConst ``FirstCountableTopology [.zero]) #[P,top])
        let compact ← synthInstance (mkAppN (mkConst ``LocallyCompactSpace [.zero]) #[P,top])
        let n := mkApp (mkConst ``Nat.succ) d.parameters[0]!
        let args := #[n,J,P,top,first,compact,D,D₀,p,b,H,Z,ζ,τ,det,hD,hA,hm]
        let ci ← getConstInfo ``originalMeasuredShellKernel_eq_moment
        let mut expected := ci.type.instantiateLevelParams ci.levelParams [.zero]
        for k in [:args.size] do
          let .forallE _ domain rest _ := expected.consumeMData
            | throwError "native measured moment theorem ABI ended at{k}"
          IO.println s!"native moment checking factor {k}"
          unless ← isDefEq (← inferType args[k]!) domain do
            throwError "native measured moment factor type mismatch at {k}"
          expected := rest.instantiate1 args[k]!
        let proof := mkAppN (mkConst ``originalMeasuredShellKernel_eq_moment [.zero]) args
        IO.println "actual native moment: checked factors, storing declaration"
        let t ← inferType proof
        let some amp := t.find? (·.isAppOfArity ``measuredAdjointSlice 5)
          | throwError "actual moment: exact measuredAdjointSlice subtree missing"
        let actualAmp := app (ns ++ `ameasAtPoint) params
        unless ← isDefEq amp actualAmp do
          throwError "actual moment: measured slice differs from the original named amplitude"
        let t := t.replace fun e => if e == amp then some actualAmp else none
        discard <| store `nativeMeasuredKernel_eq_moment params proof false (some t)
publish_actual_measured_native_moment
end JanetCartan.PhysicalMean.OriginalCanonicalRow.MomentGenerator
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.nativeMeasuredKernel_eq_moment

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open MeasureTheory Filter
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open RawInputPartition PhysicalSamplingShells
/-- Transport the actual native coordinate formula on its unchanged shell
measure. No integrability premise is introduced; both integrals are related
pointwise (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem measured_native_integral_transport {n J : ℕ}
    (f : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))))
    {g : Euclidean n → ℂ}
    {K K' : Euclidean n → RefinedIndex J × Euclidean (n-1) → ℂ}
    (h : g =ᵐ[volume] fun x ↦ ∫ u, K x u * f u
      ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (hK : ∀ x u, K x u = K' x u) :
    g =ᵐ[volume] fun x ↦ ∫ u, K' x u * f u
      ∂annularShellMeasure (n := n) (refinedRadius (J := J)) := by
  filter_upwards [h] with x hx
  rw [hx]
  apply integral_congr_ae
  exact Eventually.of_forall fun u ↦ congrArg (fun z : ℂ ↦ z * f u) (hK x u)
end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow.SelectedMomentGenerator
open OriginalBackgroundHermitianTemplate
private def ns := `JanetCartan.PhysicalMean.OriginalCanonicalRow
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
elab "publish_actual_selected_measured_moment" : command => liftTermElabM do
  OriginalPeriodicBackgroundTemplate.withActualCanonicalSample fun xs ξ _si _J _fI _hU _hξ => do
    withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
      let params := xs.push L
      let hnative := app (ns ++ `hAn_originalKernel) params
      let body ← bodyAt (ns ++ `An) (xs.push ξ |>.push L)
      unless body.isAppOfArity ``sampledAnnularComponent 11 do
        throwError "selected moment: original sampledAnnularComponent11 changed"
      let abi := body.getAppArgs
      let proof ← forallBoundedTelescope (← inferType hnative) (some 3) fun qfa _ => do
        let q := qfa[0]!
        let f := qfa[1]!
        let a := qfa[2]!
        let row ← mkAppM ``Sigma.fst #[q]
        let sample ← mkAppM ``Sigma.snd #[q]
        let sampleVal ← mkAppM ``Subtype.val #[sample]
        let lattice ← mkAppM ``Prod.fst #[sampleVal]
        let color ← mkAppM `JanetCartan.SeparatedSampling.color #[abi[3]!,lattice]
        let node ← mkAppM `JanetCartan.SeparatedSampling.node #[abi[7]!,mkApp abi[8]! row,sampleVal]
        let hkernel := app (ns ++ `nativeMeasuredKernel_eq_moment) (xs ++ #[row,color,node,L,a])
        let h := mkAppN hnative qfa
        let ht ← inferType h
        unless ht.isAppOfArity ``Filter.EventuallyEq 5 do
          throwError "selected moment: original coordinate AE shape changed"
        let g := ht.getAppArgs[3]!
        let pair ← forallBoundedTelescope (← inferType hkernel) (some 2) fun xu eq => do
          unless eq.isAppOfArity ``Eq 3 do
            throwError "selected moment: native kernel equality shape changed"
          return (← mkLambdaFVars xu eq.getAppArgs[1]!, ← mkLambdaFVars xu eq.getAppArgs[2]!)
        let proof := mkAppN (mkConst ``measured_native_integral_transport)
          #[abi[1]!,abi[2]!,f,g,pair.1,pair.2,h,hkernel]
        mkLambdaFVars qfa proof
      let t ← inferType proof
      let type ← instantiateMVars (← mkForallFVars params t)
      let value ← instantiateMVars (← mkLambdaFVars params proof)
      let env ← getEnv
      for e in #[proof,t,type,value] do
        let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
        unless missing.isEmpty do throwError "selected measured moment missing {missing.toList}"
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
          throwError "selected measured moment retained open proof data"
      let name := ns ++ `hAn_sampledMoment
      addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
      logInfo "checked actual same-An hAn_sampledMoment51"
publish_actual_selected_measured_moment
end JanetCartan.PhysicalMean.OriginalCanonicalRow.SelectedMomentGenerator
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.hAn_sampledMoment

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open MeasureTheory Filter
open scoped BigOperators ContDiff
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open RawInputPartition PhysicalSamplingShells RawInputRealization Pseudodifferential
variable {ν : Type*} [Fintype ν] [MeasurableSpace ν] [MeasurableSingletonClass ν] {n J : ℕ}

/-- Group only original sample labels; both sharp shell copies remain in the
native integral (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_sampledShell_group_samples
    {F : ((ν × RefinedIndex J) × Euclidean (n-1)) → ℂ}
    (hF : Integrable F (sampledShellMeasure (ι := ν) n J)) :
    (∫ z, F z ∂sampledShellMeasure (ι := ν) n J) =
      ∑ i : ν, ∫ u, F ((i,u.1),u.2)
        ∂annularShellMeasure (n := n) (refinedRadius (J := J)) := by
  have hf (i : ν × RefinedIndex J) :
      Integrable F ((annularMeasure n (refinedRadius i.2)).map (Prod.mk i)) := by
    have hh := hF
    rw [sampledShellMeasure,annularShellMeasure,Measure.sum_fintype] at hh
    exact integrable_finsetSum_measure.mp hh i (Finset.mem_univ i)
  have hi (i : ν) : Integrable (fun u : RefinedIndex J × Euclidean (n-1) ↦ F ((i,u.1),u.2))
      (annularShellMeasure (n := n) (refinedRadius (J := J))) := by
    rw [annularShellMeasure,Measure.sum_fintype]
    apply integrable_finsetSum_measure.mpr
    intro j _
    apply (measurableEmbedding_prodMk_left j).integrable_map_iff.mpr
    exact (measurableEmbedding_prodMk_left (i,j)).integrable_map_iff.mp (hf (i,j))
  rw [show sampledShellMeasure (ι := ν) n J =
    Measure.sum (fun i : ν × RefinedIndex J ↦
      (annularMeasure n (refinedRadius i.2)).map (Prod.mk i)) from rfl]
  rw [integral_sum_measure hF,tsum_fintype,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [show annularShellMeasure (n := n) (refinedRadius (J := J)) =
    Measure.sum (fun j : RefinedIndex J ↦
      (annularMeasure n (refinedRadius j)).map (Prod.mk j)) from rfl]
  rw [integral_sum_measure (hi i),tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [(measurableEmbedding_prodMk_left (i,j)).integral_map,
    (measurableEmbedding_prodMk_left j).integral_map]

/-- The unchanged sampled isometry yields the literal original sample section,
not a weighted or renormalized input. -/
theorem sampled_local_annular_ae
    (f : Lp ℂ 2 (sampledShellMeasure (ι := ν) n J)) (i : ν) :
    (annularShellEquiv (n := n) (refinedRadius (J := J))).symm (sampledShellEquiv n J f i) =ᵐ[
      annularShellMeasure (n := n) (refinedRadius (J := J))]
      fun u ↦ f ((i,u.1),u.2) := by
  apply Measure.ae_sum_iff.mpr
  intro j
  apply (measurableEmbedding_prodMk_left j).ae_map_iff.mpr
  have hs := annularShellEquiv_ae (n := n) (refinedRadius (J := J))
    ((annularShellEquiv (n := n) (refinedRadius (J := J))).symm (sampledShellEquiv n J f i)) j
  rw [(annularShellEquiv (n := n) (refinedRadius (J := J))).apply_symm_apply] at hs
  exact hs.symm.trans (sampledShellEquiv_ae n J f i j)
section
variable [MetricSpace ν] [DiscreteTopology ν] [BorelSpace ν]

/-- Exact assembly of the already given component kernels on the SAME unweighted
sampled-shell measure. The scalar weight is never divided out. -/
theorem nativeMeasuredRow_eq_original_components
    (φ : ((ν × RefinedIndex J) × Euclidean (n-1)) → Euclidean n → ℝ)
    (m : ((ν × RefinedIndex J) × Euclidean (n-1)) → ℝ)
    (a : Fin n → (ν × RefinedIndex J) → Euclidean (n-1) → Euclidean n → ℂ)
    (weight : ν → ℝ) (hφ : Continuous (Function.uncurry φ))
    (hm : Continuous m) (hms : HasCompactSupport m)
    (ha : ∀ b i, ContDiff ℝ ∞ (Function.uncurry (a b i)))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (haK : ∀ b i η, tsupport (a b i η) ⊆ K)
    (An : ν → Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hAn : ∀ i f b, finiteL2CoordinateIsometry volume (An i f) b =ᵐ[volume]
      fun x ↦ ∫ u, sampledMomentKernel (fun u ↦ φ ((i,u.1),u.2))
        (halfWeightedMomentMask (fun u ↦ m ((i,u.1),u.2)))
        (fun u ↦ a b (i,u.1) u.2) x u * f u
        ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (f : Lp ℂ 2 (sampledShellMeasure (ι := ν) n J)) :
    nativeMeasuredRow (sampledShellMeasure (ι := ν) n J) φ (originalWeightedHalfMask weight m) a
      hφ (originalWeightedHalfMask_continuous weight m hm)
      (originalWeightedHalfMask_hasCompactSupport weight m hms) ha hK haK f =
        ∑ i : ν, (Real.sqrt (weight i) : ℂ) • An i
          ((annularShellEquiv (n := n) (refinedRadius (J := J))).symm (sampledShellEquiv n J f i)) := by
  classical
  let fi (i : ν) := (annularShellEquiv (n := n) (refinedRadius (J := J))).symm
    (sampledShellEquiv n J f i)
  apply (finiteL2CoordinateIsometry volume).injective
  apply PiLp.ext
  intro b
  simp only [map_sum,map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    nativeMeasuredRow,nativeScalarRowsToVector_coordinate]
  apply Lp.ext
  let g (i : ν) := finiteL2CoordinateIsometry volume (An i (fi i)) b
  have hc (i : ν) := hAn i (fi i) b
  have hs (i : ν) := Lp.coeFn_smul (Real.sqrt (weight i) : ℂ) (g i)
  have hn := sampledMomentOperator_ae_kernel (sampledShellMeasure (ι := ν) n J)
    φ (originalWeightedHalfMask weight m) (fun z ↦ a b z.1 z.2) hφ
    (originalWeightedHalfMask_continuous weight m hm)
    (continuous_originalSampledAmplitude (a b) (ha b))
    (originalWeightedHalfMask_hasCompactSupport weight m hms) hK (fun z ↦ haK b z.1 z.2) f
  filter_upwards [hn,Lp.coeFn_finsetSum Finset.univ (fun i ↦ (Real.sqrt (weight i) : ℂ) • g i),
    eventually_all.mpr hc,eventually_all.mpr hs] with x hx hsum hci hsi
  rw [hx,hsum]
  have ht := continuous_sampledMomentKernel φ (originalWeightedHalfMask weight m)
    (fun z ↦ a b z.1 z.2) hφ (originalWeightedHalfMask_continuous weight m hm)
    (continuous_originalSampledAmplitude (a b) (ha b))
  have hts := hasCompactSupport_sampledMomentKernel φ (originalWeightedHalfMask weight m)
    (fun z ↦ a b z.1 z.2) (originalWeightedHalfMask_hasCompactSupport weight m hms)
    hK (fun z ↦ haK b z.1 z.2)
  have hi := ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel.integrable_compactKernel_mul_L2 ht hts f x
  rw [integral_sampledShell_group_samples hi]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsi i,Pi.smul_apply,smul_eq_mul,hci i,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [sampled_local_annular_ae f i] with u hu
  simp only [sampledMomentKernel,originalWeightedHalfMask,halfWeightedMomentMask,Complex.ofReal_mul]
  change _ = _ * (_ * _ * star (a b (i,u.1) u.2 x) * fi i u)
  rw [show fi i u = f ((i,u.1),u.2) from hu]
  ring
end

section
variable [MetricSpace ν] [DiscreteTopology ν] [BorelSpace ν]
open PeriodicLocalL2
/-- The exact `hrow` consumer follows from its actual component kernels and
`hArep`, without any new phase, sampler, input, or normal-operator premise. -/
theorem measured_hrow_of_hAn
    (φ : ((ν × RefinedIndex J) × Euclidean (n-1)) → Euclidean n → ℝ)
    (m : ((ν × RefinedIndex J) × Euclidean (n-1)) → ℝ)
    (a : Fin n → (ν × RefinedIndex J) → Euclidean (n-1) → Euclidean n → ℂ)
    (weight : ν → ℝ) (hφ : Continuous (Function.uncurry φ))
    (hm : Continuous m) (hms : HasCompactSupport m)
    (ha : ∀ b i, ContDiff ℝ ∞ (Function.uncurry (a b i)))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (haK : ∀ b i η, tsupport (a b i η) ⊆ K)
    (An : ν → Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hAn : ∀ i f b, finiteL2CoordinateIsometry volume (An i f) b =ᵐ[volume]
      fun x ↦ ∫ u, sampledMomentKernel (fun u ↦ φ ((i,u.1),u.2))
        (halfWeightedMomentMask (fun u ↦ m ((i,u.1),u.2)))
        (fun u ↦ a b (i,u.1) u.2) x u * f u
        ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (A : ν → RefinedInput n J →L[ℝ] (Lp (Euclidean n) 2 (volume : Measure (Torus n))))
    (hArep : ∀ i, (A i).comp
      ((annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J))).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      transferOutputOperator (realQuadratureChannel (An i))) :
    (CanonicalRow.weightedRow weight A).comp
      ((sampledShellEquiv (V := ℂ) (ι := ν) n J).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      transferOutputOperator (realQuadratureChannel
        (nativeMeasuredRow (sampledShellMeasure (ι := ν) n J) φ (originalWeightedHalfMask weight m) a
          hφ (originalWeightedHalfMask_continuous weight m hm)
          (originalWeightedHalfMask_hasCompactSupport weight m hms) ha hK haK)) := by
  classical
  ext1 f
  let fi (i : ν) := (annularShellEquiv (n := n) (refinedRadius (J := J))).symm
    (sampledShellEquiv n J f i)
  have hN := nativeMeasuredRow_eq_original_components φ m a weight hφ hm hms ha hK haK An hAn f
  have hNr : nativeMeasuredRow (sampledShellMeasure (ι := ν) n J) φ (originalWeightedHalfMask weight m) a
      hφ (originalWeightedHalfMask_continuous weight m hm)
      (originalWeightedHalfMask_hasCompactSupport weight m hms) ha hK haK f =
      ∑ i : ν, Real.sqrt (weight i) • An i (fi i) := by
    simpa only [fi,RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal] using hN
  simp only [ContinuousLinearMap.comp_apply,CanonicalRow.weightedRow_apply,
    transferOutputOperator,realQuadratureChannel_apply]
  change (∑ i : ν, Real.sqrt (weight i) • A i (sampledShellEquiv n J f i)) =
    toTorus (𝕜 := ℝ) ((2 : ℝ) • l2RealPart volume
      (nativeMeasuredRow (sampledShellMeasure (ι := ν) n J) φ (originalWeightedHalfMask weight m) a
        hφ (originalWeightedHalfMask_continuous weight m hm)
        (originalWeightedHalfMask_hasCompactSupport weight m hms) ha hK haK f))
  rw [hNr]
  simp only [map_sum,map_smul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun B ↦ B (fi i)) (hArep i)
  change A i ((annularShellEquiv (n := n) (refinedRadius (J := J))) (fi i)) =
    toTorus (𝕜 := ℝ) ((2 : ℝ) • l2RealPart volume (An i (fi i))) at h
  have he : A i (sampledShellEquiv n J f i) =
      toTorus (𝕜 := ℝ) ((2 : ℝ) • l2RealPart volume (An i (fi i))) := by
    simpa only [fi,LinearIsometryEquiv.apply_symm_apply] using h
  rw [he,map_smul,smul_comm]
end

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.nativeMeasuredRow_eq_original_components
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.measured_hrow_of_hAn
