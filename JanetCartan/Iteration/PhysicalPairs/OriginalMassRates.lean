module
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageMetric

/-! # Keep the exact original sample coefficient mass in the physical lag

Before replacing (∑√μ)² by its common sampling bound, the actual metric
residual already has precisely b²(∑√μ)²(λh)^(-q). In particular no carrier
bound for an unrelated or altered pair is being used. Companion to
`OriginalStageSize.coefficient_mass_size`. `main:eq:pair-error`,
`app:ch_pairs:eq:pairs-lag-sum-error`.
-/
@[expose] public noncomputable section
namespace JanetCartan.PhysicalPairs.OriginalMassRates
open UniformStep
variable {n : ℕ}
def price (hn : 5 ≤ n) (A : ℝ) (q : ℕ) := 2*(projectedStressResidualConstant hn*A)*(2:ℝ)^q
private theorem keep_mass (hn : 5 ≤ n) (A R δ : ℝ) (q : ℕ) (mass x : ℝ) (hR : 1 ≤ R)
    (hx : x ≤ 2*OriginalStageLag.singlePrice hn A R q*(δ*R^(RevisedScales.forcingExponent n))^2*mass) :
    x ≤ price hn A q*(δ*R^(RevisedScales.forcingExponent n))^2*mass*(R^carrierExponent*R^(-separationExponent))^(-(q:ℝ)) := by
  have h := zero_lt_one.trans_le hR
  have he : (R^carrierExponent*R^(-separationExponent))^(-(q:ℝ)) = R^(-((carrierExponent-separationExponent)*(q:ℝ))) := by
    rw [←Real.rpow_add h,←Real.rpow_mul h.le]; congr 1; ring
  exact hx.trans_eq (by rw [he]; unfold OriginalStageLag.singlePrice price; ring)
end JanetCartan.PhysicalPairs.OriginalMassRates
end
public meta section
set_option maxHeartbeats 1600000
set_option maxRecDepth 18000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalMassRates
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalMassRates
private def lag := `JanetCartan.PhysicalPairs.OriginalStageLag
private def met := `JanetCartan.PhysicalPairs.OriginalStageMetric
private def sum := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
run_cmd liftTermElabM do
  let val ← getConstInfo (lag ++ `constant)
  forallBoundedTelescope val.type (some 42) fun p _ => do
    let raw := (val.value! (allowOpaque := true)).beta p
    unless raw.isAppOfArity (lag ++ `totalPrice) 5 do throwError "lost the original lag price before the coefficient-mass envelope"
    let args := raw.getAppArgs
    discard <| store (ns ++ `constant) p (a (ns ++ `price) (args[:3].toArray.push args[4]!)) true
run_cmd liftTermElabM do
  let old ← getConstInfo (lag ++ `lag)
  forallBoundedTelescope old.type (some 52) fun p _ => do
    let dyn := p[43:51].toArray
    let stem := p[:37].toArray ++ dyn
    let fixed := p[:37].toArray ++ p[38:43].toArray
    let native := stem ++ #[mkAppN p[38]! dyn,p[51]!]
    let C := a (ns ++ `constant) fixed
    let unprice := ((← getConstInfo (ns ++ `constant)).value! (allowOpaque := true)).beta fixed
    let S := a (sum ++ `correction) native
    let rawS := ((← getConstInfo (sum ++ `correction)).value! (allowOpaque := true)).beta native
    let eq := a (met ++ `off_metric) native
    let θ := a (met ++ `angles) stem
    let ee := (← inferType eq).getAppArgs
    let sub := ee[2]!.getAppArgs
    let proof ← forallBoundedTelescope (← inferType (a (lag ++ `lag) (p.push θ))) (some 2) fun y _ => do
      let priced := (old.value! (allowOpaque := true)).beta ((p.push θ) ++ y)
      unless priced.isAppOfArity (lag ++ `total) 13 do throwError "lost the original exact all-carrier sum before pricing its actual mass"
      let s := priced.getAppArgs
      let full := a ``keep_mass (s[:3].toArray ++ s[4:9].toArray ++ #[s[10]!,s[11]!])
      let ty := (← inferType full).getAppArgs
      let add := ty[2]!.appArg!.getAppArgs
      let rhs := ty.back!
      let pr := a (met ++ `transfer) #[s[0]!,ee[1]!,sub[sub.size-2]!,sub.back!,eq,add[add.size-2]!,y[0]!,rhs,full]
      mkLambdaFVars y pr
    let out := (← inferType proof).replace fun e => if e == rawS then some S else if e == unprice then some C else none
    discard <| store (ns ++ `metric_lag) p proof false (some out)
end JanetCartan.PhysicalPairs.OriginalMassRates
end
