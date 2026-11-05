module
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageLag
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledSchwartz

/-! # Exact self/off splitting of the same original real primary

The residual in the physical pair theorem uses the metric of the literal
uncut real Schwartz sum. Its diagonal part is the full weighted Hermitian
sample of the differentiated corrected waves. Even the angle family used to
identify the two formulations is taken before the sign and nodes from the
original radial phase. `main:eq:self-off`, `main:prop:pairs`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
open scoped SchwartzMap Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.OriginalStageMetric
open UniformStep PhysicalPrimary
variable {n N : ℕ} {I : Type} [Fintype I]
local notation "E" => Euclidean n

def diagonal (δ R : ℝ) (μ : I → ℝ) (Z : I → 𝓢(E,EuclideanSpace ℂ (Fin N))) : MetricField n :=
  (δ*R^RevisedScales.forcingExponent n)^2 • CurrentMean.weightedHermitianTensor μ (fun x i ↦ sampledDerivative (fun k ↦ (Z k : E → EuclideanSpace ℂ (Fin N))) i x)

theorem metric_formula (δ R : ℝ) (μ : I → ℝ) (Z : I → 𝓢(E,EuclideanSpace ℂ (Fin N))) (θ : I → E → ℝ) :
    OriginalLagAlgebra.offSelf δ R μ Z θ = inducedMetric (uncutSampledPrimary (δ*R^RevisedScales.forcingExponent n) μ Z) - diagonal δ R μ Z := by
  rw [uncut_sampled_self_off _ _ _ θ]
  unfold OriginalLagAlgebra.offSelf diagonal
  abel

theorem transfer (off a b : MetricField n) (h : off = a-b) (v : MetricTensor n) (x : E) (price : ℝ) (hv : ‖v+off x‖ ≤ price) : ‖v+(a-b) x‖ ≤ price := by rwa [←h]
end JanetCartan.PhysicalPairs.OriginalStageMetric
end
public meta section
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalStageMetric
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalStageMetric
private def hs := `JanetCartan.PhysicalPairs.SampledHistory
private def sum := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
run_cmd liftTermElabM do
  let ang := `JanetCartan.PhysicalPairs.OriginalSignedData.angles
  forallBoundedTelescope (← getConstInfo (hs ++ `index)).type (some 49) fun p _ => do
    let stem := p[:45].toArray
    let native := ((← getConstInfo ang).value! (allowOpaque := true)).beta p
    let reached := Expr.proj ``And 0 (a (hs ++ `measured_history) p)
    let index := ((← getConstInfo (hs ++ `index)).value! (allowOpaque := true)).beta p
    let both := index.getAppArgs[7]!
    let ma := (← inferType both).getAppArgs[2]!.getAppArgs
    let hG ← mkAppM ``le_trans #[← mkAppM ``le_max_left #[ma[ma.size-2]!,ma.back!],both]
    let safe := native.replace fun e => if e == reached then some hG else none
    let named ← store (ns ++ `angles) stem safe true
    discard <| store (ns ++ `angles_at_pair) p (← mkEqRefl safe) false (some (← mkEq (a ang p) named))
run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo (sum ++ `correction)).type (some 47) fun p _ => do
    let stem := p[:45].toArray
    let Z := p[45]!
    let δ := p[46]!
    let corr := ((← getConstInfo (sum ++ `correction)).value! (allowOpaque := true)).beta p
    let sa := corr.getAppArgs
    let args := sa[:4].toArray ++ #[δ,sa[7]!,sa[8]!,Z]
    let off := a (ns ++ `metric_formula) (args.push (a (ns ++ `angles) stem))
    let rh := (← inferType off).appArg!.getAppArgs
    let metric := rh[rh.size-2]!
    let diag := rh.back!
    let some primary := metric.find? (fun e => e.isAppOfArity `JanetCartan.PhysicalPrimary.uncutSampledPrimary 7) | throwError "not the unchanged real Schwartz sum"
    let P ← store (ns ++ `primary) p primary true
    let H ← store (ns ++ `self) p diag true
    discard <| store (ns ++ `off_metric) p off false (some ((← inferType off).replace fun e => if e == primary then some P else if e == diag then some H else none))
run_cmd liftTermElabM do
  let lag := `JanetCartan.PhysicalPairs.OriginalStageLag.lag
  forallBoundedTelescope (← getConstInfo lag).type (some 52) fun p _ => do
    let dyn := p[43:51].toArray
    let stem := p[:37].toArray ++ dyn
    let Z := mkAppN p[38]! dyn
    let eq := a (ns ++ `off_metric) (stem ++ #[Z,p[51]!])
    let per := a lag (p.push (a (ns ++ `angles) stem))
    let ee := (← inferType eq).getAppArgs
    let rh := ee[2]!.getAppArgs
    let result ← forallBoundedTelescope (← inferType per) (some 2) fun y _ => do
      let hv := mkAppN per y
      let ty := (← inferType hv).getAppArgs
      let norm := ty[2]!.appArg!.getAppArgs
      let term := a (ns ++ `transfer) #[mkApp (mkConst ``Nat.succ) p[0]!,ee[1]!,rh[rh.size-2]!,rh.back!,eq,norm[norm.size-2]!,y[0]!,ty.back!,hv]
      mkLambdaFVars y term
    discard <| store (ns ++ `lag) p result
end JanetCartan.PhysicalPairs.OriginalStageMetric
end
