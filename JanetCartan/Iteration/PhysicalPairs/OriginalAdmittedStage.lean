module
public import JanetCartan.Iteration.PhysicalPairs.OriginalPairStage
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedWaves

/-! # The actual primary and pair correction on a selected external sample

The derivative cost comes directly from the upstream corrected primary at its
actual admitted nodes. A failed auxiliary trial does not impose a norm bound
on the primary. On the chosen trial all three conclusions contain the literal
supplied Schwartz family, not the zero extension used to prove uniformity.
This is the interface to the stage13 final primary, not a construction of it.
The secondary is exactly b²V+S with no new cutoff. `main:prop:pairs`,
`main:eq:joint-physical-profile`.
-/
public meta section
set_option maxHeartbeats 1600000
set_option maxRecDepth 18000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalAdmittedStage
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalAdmittedStage
private def sw := `JanetCartan.PhysicalPairs.OriginalSelectedWaves
private def pair := `JanetCartan.PhysicalPairs.OriginalPairStage
private def sum := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
run_cmd liftTermElabM do
  let est := pair ++ `estimates
  forallBoundedTelescope (← getConstInfo est).type (some 37) fun chosen _ => do
    let native := a est chosen
    let ty ← whnfR (← inferType native)
    let waves := ty.bindingDomain!
    unless waves.isAppOfArity `JanetCartan.PhysicalPairs.OriginalCommonWaves.Waves 37 do throwError "not the numerically selected original full-wave domain"
    let b := waves.getAppArgs
    withLocalDeclD `admittedEvent (a (sw ++ `Gate) b) fun G => withLocalDeclD `truePrimary (a (sw ++ `AdmittedWaves) (b.push G)) fun W => do
      let gw := b ++ #[G,W]
      let allW := a (sw ++ `extend) gw
      let root := mkApp native allW
      forallBoundedTelescope (← inferType root) (some 2) fun c _ => do
        withLocalDeclD `trueNodeJets (a (sw ++ `GenuineNodeProfile) (gw.push c[0]!)) fun hJ => do
          let jets := a (sw ++ `full_profile) (gw ++ c ++ #[hJ])
          let priced := mkAppN root (c.push jets)
          forallBoundedTelescope (← inferType priced) (some 10) fun h _ => do
            let all := mkAppN priced h
            let conclusion ← inferType all
            let some corr := conclusion.find? (fun e => e.isAppOfArity (sum ++ `correction) 47) | throwError "lost original common sampled Schwartz correction"
            let sa := corr.getAppArgs
            let actualRow := sa[37:45].toArray
            let z0 := mkAppN allW actualRow
            unless ← isDefEq z0 sa[45]! do throwError "source and metric do not share the same original family"
            withLocalDeclD `onChosenEvent (mkAppN G actualRow) fun he => do
              let got := a (sw ++ `at_genuine_sample) (gw ++ actualRow ++ #[he])
              let predicate ← withLocalDeclD `wavesAtThisSample (← inferType z0) fun z => do
                let t := conclusion.replace fun e => if e.isAppOfArity (sw ++ `extend) 47 && e.getAppArgs[39]! == actualRow[0]! && e.getAppArgs[46]! == actualRow[7]! then some z else none
                unless t != conclusion do throwError "chosen full waves did not occur at the actual event"
                mkLambdaFVars #[z] t
              let result ← mkAppM ``Eq.mp #[← mkAppM ``congrArg #[predicate,got],all]
              let target := predicate.beta #[mkApp (mkAppN W actualRow) he]
              discard <| store (ns ++ `estimates) (chosen ++ #[G,W] ++ c ++ #[hJ] ++ h[:9].toArray ++ #[he,h[9]!]) result false (some target)
run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo (sum ++ `correction)).type (some 47) fun p typ => do
    let C := a (sum ++ `correction) p
    let raw := ((← getConstInfo (sum ++ `correction)).value! (allowOpaque := true)).beta p
    let ra := raw.getAppArgs
    let n := ra[0]!
    let N := ra[1]!
    let A := a `JanetCartan.RevisedScales.forcingExponent #[n]
    let scale ← mkAppM ``HPow.hPow #[ra[7]!,A]
    let b ← mkAppM ``HMul.hMul #[p[46]!,scale]
    withLocalDeclD `actualMean typ fun V => do
      let ex := a `JanetCartan.PhysicalPairs.physicalSecondary #[n,N,b,V,C]
      let W ← store (ns ++ `secondary) (p.push V) ex true
      let rhs := ((← getConstInfo `JanetCartan.PhysicalPairs.physicalSecondary).value! (allowOpaque := true)).beta #[n,N,b,V,C]
      discard <| store (ns ++ `secondary_identity) (p.push V) (← mkEqRefl rhs) false (some (← mkEq W rhs))
end JanetCartan.PhysicalPairs.OriginalAdmittedStage
end
