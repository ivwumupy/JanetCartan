module

public import JanetCartan.Iteration.PhysicalMean.OriginalPeriodicBackground
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSampledBaseline
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMeasurement
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSampledApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaselineApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public meta import Lean

/-!
# The signed quadrature of the actual sampled positive baseline

Regroup the value of the quadrature summand in `new:eq:mean-source`. The
colored continuum is exactly the one in `familyBackgroundError`, with NO
replacement by the transported leading mean. On the original sample the
auxiliary observation is one wherever the actual measurement is nonzero;
thus the term subtracted here is the measured physical Hermitian self tensor
of the genuine canonical baseline, with each original weight exactly once.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalMean.OriginalCompleteForcing
open SeparatedSampling LatticeQuadrature Sampling.Realization Sampling.BackgroundQuadrature CanonicalRowComparison CurrentMean

/-- The actual corrected colored continuum: keep the exact masks, color and
patch factor from the original family quadrature. -/
def correctedColoredValue {n : ℕ} {I : Type} [Fintype I]
    (p : ℕ) (B h : ℝ) (ψ : I → Point → ℝ) (w : ℝ → ℝ)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n) (x : Torus n) : Euclidean n :=
  ∑ i, ∑ c, ∫ z : Point, coloredBlockMask p (integerCube (blockCutoff p B h)) w h c z •
    (ψ i z • H i c (x,z))

/-- An observation introduced for periodicity does not change a measured
Hermitian self tensor. No positivity or division by a weight is involved. -/
theorem measured_observed_self {n N : ℕ} (C : MetricTensor n →L[ℝ] Euclidean n)
    (a : ℝ) (A D : Matrix (Fin N) (Fin n) ℂ) (h : C ≠ 0 → a = 1) (hD : D = a • A) :
    C (hermitianTensor A) = C (hermitianTensor D) := by
  by_cases hz : C = 0
  · simp only [hz, zero_apply]
  · rw [hD, h hz, one_smul]

/-- Exact value of the original quadrature constructor on the unmodified
sample index. The actual observed-node identification is instantiated below.
The colored continuum, not `H_F`, is the positive term in this identity. -/
theorem signed_quadrature_value {n N : ℕ} {I : Type} [Fintype I] {κ : ℝ → ℝ}
    (hκc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ) (p : ℕ) (B h : ℝ)
    (ψ : I → Point → ℝ) (hψc : ∀ i, HasCompactSupport (ψ i)) (U : I → Lattice → Point)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hH : ∀ i c, ContDiff ℝ ∞ (fun y : Euclidean n × Point ↦ ψ i y.2 • H i c (torusQuotient y.1,y.2)))
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n)
    (base : SmoothPeriodicFamily n (SampleIndex p B ψ (convolvedBoxWindow κ p) h U)
        (Matrix (Fin N) (Fin n) ℂ))
    (hnode : ∀ x (i : SampleIndex p B ψ (convolvedBoxWindow κ p) h U),
      H i.1 (color p i.2.val.1) (x,node h (U i.1) i.2) = C x (hermitianTensor (base.val x i)))
    (x : Torus n) :
    (weightedOriginalBackgroundQuadratureForcing hκc hκ p B h ψ hψc U H hH).val x () =
      correctedColoredValue p B h ψ (convolvedBoxWindow κ p) H x -
        C x (weightedHermitianTensor (sampleWeight (p := p) B ψ (convolvedBoxWindow κ p) h U) base.val x) := by
  classical
  rw [weightedOriginalBackgroundQuadratureForcing_apply, familyBackgroundError, Finset.sum_sub_distrib, neg_sub]
  congr 1
  simp only [weightedHermitianTensor, map_sum, map_smul, ← hnode x]
  simp only [SampleIndex, sampleWeight, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_subtype (samples p B (ψ i) (convolvedBoxWindow κ p) h (U i))
    (fun _ ↦ Iff.rfl) (fun a ↦ weight (ψ i) (convolvedBoxWindow κ p) h (U i) a •
      H i (color p a.1) (x,node h (U i) a))

end JanetCartan.PhysicalMean.OriginalCompleteForcing
end

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalCompleteSampleApplication
open Lean Meta Elab Command
open OriginalCanonicalSampledApplication (withActualSample)
open OriginalBackgroundHermitianTemplate (bodyAt)

private def ns := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def pos := `JanetCartan.PhysicalMean.OriginalCanonicalBaseline
private def sampled := `JanetCartan.PhysicalMean.OriginalCanonicalSampled
private def cm := `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement
private def quad := `JanetCartan.PhysicalMean.OriginalPeriodicBackground
private def app (c : Name) (xs : Array Expr) := mkAppN (mkConst c) xs

private def nativeTel (type : Expr) (count : Nat) (go : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,t,p => go p t
    | k+1,t,p => do
      let .forallE name dom body bi := t.consumeMData | throwError "sample identity: missing binder {p.size}"
      if bi == .instImplicit then withLocalDecl name bi dom fun a => loop k (body.instantiate1 a) (p.push a)
      else withLocalDeclNoLocalInstanceUpdate name bi dom fun a => loop k (body.instantiate1 a) (p.push a)

private def save (short : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "sample identity {short}: missing original constants {missing}"
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry then
      throwError "sample identity {short}: leaked native data"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ short
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual same-sample decomposition of the corrected quadrature in new:eq:mean-source. The corrected colored continuum is retained explicitly and is NOT identified with the leading transported mean."
  logInfo m!"original signed Hermitian quadrature {short}/{p.size}"

run_cmd liftTermElabM <| withTransparency .reducible <| nativeTel (← getConstInfo (pos ++ `positiveBaseline_native)).type 55 fun p _ => do
  let fixed := p[:50].toArray
  let z := p[54]!
  let n := (← inferType z).appArg!
  let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
  let hb := app (pos ++ `positiveBaseline_native) p
  let h := (← inferType hb).getAppArgs
  unless h.size == 3 && h[2]!.isAppOfArity ``HSMul.hSMul 6 do throwError "not a literal observed positive amplitude"
  let a := h[2]!.getAppArgs
  let hp := app (cm ++ `Cper_native) (fixed.push z)
  let c := (← inferType hp).getAppArgs
  unless c.size == 3 do throwError "not the original centered measurement"
  let obs := app (cm ++ `observation_eq_one) (fixed.push c[2]!.appArg!)
  let proof := app (ns ++ `measured_observed_self) #[n,N,c[2]!,a[4]!,a[5]!,h[1]!,obs,hb]
  let t ← inferType proof
  let args := t.getAppArgs
  let lhs := app (quad ++ `actual_periodicH) (p[:52].toArray.push (← mkAppM ``Prod.mk #[z,p[52]!]))
  let rhs := args[2]!.replace fun e => if e == c[2]! then some c[1]! else none
  unless rhs != args[2]! do throwError "could not name global torus measurement"
  let target := mkAppN t.getAppFn #[args[0]!,lhs,rhs]
  save `measured_corrected_node p proof target

run_cmd liftTermElabM <| withTransparency .reducible <| withActualSample fun p ξ sa _ fI => do
  let raw ← bodyAt (quad ++ `forcing) (p.push ξ)
  unless raw.isAppOfArity `JanetCartan.PhysicalMean.weightedOriginalBackgroundQuadratureForcing 14 do throwError "different original quadrature constructor"
  let a := raw.getAppArgs
  unless a[2]! == fI && a[11]! == sa[6]! do throwError "different actual row sum or shift"
  let win := app `JanetCartan.LatticeQuadrature.convolvedBoxWindow #[a[3]!,a[6]!]
  let partialValue := app (ns ++ `correctedColoredValue) #[a[0]!,a[1]!,a[2]!,a[6]!,a[7]!,a[8]!,a[9]!,win,a[12]!]
  if partialValue.containsFVar ξ.fvarId! then throwError "a sampled shift entered the colored integral"
  save `correctedContinuum p partialValue (← inferType partialValue) true

private def withQuadrature (next : Array Expr → Expr → Expr → Array Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  withActualSample fun p ξ sa _ fI => do
    let raw ← bodyAt (quad ++ `forcing) (p.push ξ)
    unless raw.isAppOfArity `JanetCartan.PhysicalMean.weightedOriginalBackgroundQuadratureForcing 14 do throwError "changed original forcing"
    let a := raw.getAppArgs
    unless a[2]! == fI && a[11]! == sa[6]! do throwError "different actual sum or shift"
    let base := app (sampled ++ `base) (p.push ξ)
    let N := mkApp (mkConst `JanetCartan.embeddingDimension) a[0]!
    let Cper := app (cm ++ `Cper) p
    let partialProof := app (ns ++ `signed_quadrature_value) (#[a[0]!,N] ++ a[1:].toArray ++ #[Cper,base])
    next p ξ raw a base partialProof sa[0]!

run_cmd liftTermElabM <| withTransparency .reducible <| withQuadrature fun p ξ _ _ _ partialProof I => do
  let params := p.push ξ
  let baseVal ← bodyAt (sampled ++ `base) params
  unless baseVal.isAppOf (sampled ++ `sampledPositiveBaseline) do throwError "changed canonical sampled baseline"
  let nodeType := (← inferType partialProof).bindingDomain!
  nativeTel nodeType 2 fun xi _ => do
    let z := xi[0]!
    let i := xi[1]!
    let it ← inferType i
    unless it.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 && it.getAppArgs[0]! == I do throwError "wrong original node index"
    let rawName := sampled ++ `sampledPositiveBaseline_apply
    let b := mkAppN (mkConst rawName ((← getConstInfo rawName).levelParams.map fun _ => Level.zero)) (baseVal.getAppArgs ++ #[z,i])
    let rhs := (← inferType b).getAppArgs[2]!
    let some slice := rhs.find? (·.isAppOfArity (pos ++ `positiveBaseline) 54) | throwError "lost original54 positive amplitude on the actual node"
    let h := app (ns ++ `measured_corrected_node) (slice.getAppArgs.push z)
    save `measured_sample_nodes params (← mkLambdaFVars xi h) nodeType

run_cmd liftTermElabM <| withTransparency .reducible <| withQuadrature fun p ξ raw _ _ partialProof _ => do
  let params := p.push ξ
  let partialValue ← bodyAt (ns ++ `correctedContinuum) p
  let v := mkApp partialProof (app (ns ++ `measured_sample_nodes) params)
  let expected := (← inferType v).replace fun e =>
    if e == raw then some (app (quad ++ `forcing) params) else
    if e == partialValue then some (app (ns ++ `correctedContinuum) p) else none
  unless (expected.find? (·.isAppOfArity (ns ++ `correctedContinuum) 50)).isSome do throwError "not exactly the same named colored continuum"
  save `quadrature_eq_continuum_sub_sample params v expected

end JanetCartan.PhysicalMean.OriginalCompleteSampleApplication
end
