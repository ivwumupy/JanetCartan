module
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformCorrectedLag
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedWaves
/-! # The SAME finite signed correction with uniform-before-source lag prices

Choose the decay constant on the universal bounded-wave family FIRST. Only then
accept an original history, shift, and complete Schwartz wave family satisfying
the fixed single-node derivative price. The unchanged finite correction retains
all plus diagonals and only omits the minus diagonal. Both the exact unpriced
coefficient mass and the original prehistory mass budget are retained
(`main:prop:pairs`, `app:ch_pairs:eq:pairs-lag-sum-error`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalUniformStageLagTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalUniformStageLag
private def uni := `JanetCartan.PhysicalPairs.OriginalUniformWaveData
private def lag := `JanetCartan.PhysicalPairs.OriginalStageLag
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def sum := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def metric := `JanetCartan.PhysicalPairs.OriginalStageMetric
private def mass := `JanetCartan.PhysicalPairs.OriginalSampleMass
private def one := `JanetCartan.PhysicalPairs.OriginalTensorLag.strain_to_original_error
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def part (e : Expr) (j : Nat) : Expr := Expr.proj ``And 0 (Nat.rec e (fun _ v => .proj ``And 1 v) j)
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "uniform actual signed lag: misplaced later wave/history/target in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking uniform actual signed sum {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME actual original finite signed correction obeys its physical lag bound with ONE constant chosen before every later history, shift, complete source wave, target and smoothing scale; all plus diagonals and original coefficient mass retained (main:prop:pairs; app:ch_pairs:eq:pairs-lag-sum-error)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "uniform actual signed lag: nonstandard axioms {axioms}"
  logInfo m!"uniform actual signed sum {key}/{p.size}: {axioms}"
elab "prove_original_uniform_stage_lag " mode:num : command => liftTermElabM do
  unless mode.getNat < 4 do throwError "uniform actual signed lag: unknown mode"
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun pt _ => do
    let b := pt[:37].toArray
    let stem := pt[:45].toArray
    let dyn := pt[37:45].toArray
    let signs := pt[45:].toArray
    let n := mkApp (mkConst ``Nat.succ) pt[0]!
    let hn := pt[1]!
    let N := app `JanetCartan.embeddingDimension #[n]
    let M := app (mass ++ `constant) pt[:22].toArray
    forallBoundedTelescope (← inferType (app `JanetCartan.PhysicalPairs.OriginalUniformFirstMask.first_mask b)) (some 2) fun prices _ => do
      let C := prices[0]!
      let hC := prices[1]!
      withLocalDeclD `accuracyOrder (mkConst ``Nat) fun q => do
        let fixed := b ++ #[C,hC,q]
        let fixedSource := b.push C
        let rapid := app `JanetCartan.PhysicalPairs.OriginalUniformCorrectedLag.pointwise
          (b ++ #[C,hC,app (lag ++ `accuracy) #[q]])
        let A ← mkAppM ``Classical.choose #[rapid]
        let spec ← mkAppM ``Classical.choose_spec #[rapid]
        let hA := Expr.proj ``And 0 spec
        let price := app (lag ++ `totalPrice) #[n,hn,A,M,q]
        if mode.getNat == 0 then
          save `constant fixed price (← inferType price) true
          return
        if mode.getNat == 1 then
          let proof := app (lag ++ `total_nonneg) #[n,hn,A,M,q,hA]
          let target := (← inferType proof).replace fun e => if e == price then some (app (root ++ `constant) fixed) else none
          save `constant_nonneg fixed proof target
          return
        let width := (← inferType (app one b)).bindingDomain!
        withLocalDeclD `prehistoryFrameWidth width fun hγ => do
          let wt := (← inferType (app (sum ++ `correction) stem)).bindingDomain!
          withLocalDeclD `completePrimaryWaves wt fun Z => do
            let θ := app (metric ++ `angles) stem
            let index := ((← getConstInfo (hist ++ `index)).value! (allowOpaque := true)).beta pt
            unless index.isAppOfArity (hist ++ `enter) 15 do throwError "uniform signed sum: original history entry changed"
            let both := index.getAppArgs[7]!
            let merged := (← inferType both).getAppArgs[2]!
            let ma := merged.getAppArgs
            let hG ← mkAppM ``le_trans #[← mkAppM ``le_max_left #[ma[ma.size-2]!,ma.back!],both]
            let now := pt[:36].toArray ++ #[pt[37]!,hG] ++ pt[39:43].toArray
            let F := Expr.proj ``Subtype 0 (app `JanetCartan.PhysicalInitialization.OriginalSampledPairs.projected now)
            let g := (← inferType (app (hist ++ `index) pt)).getAppArgs
            let chart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart g[:23].toArray
            let hR := app `JanetCartan.PhysicalPairs.OriginalWindow.stage_one #[pt[36]!,pt[37]!,index.getAppArgs[8]!,pt[39]!]
            let R := (← inferType hR).appArg!
            let fine := app `JanetCartan.PhysicalPairs.OriginalWindow.fineScale #[b[36]!,R]
            let nodeProfile := app `JanetCartan.PhysicalPairs.OriginalSelectedWaves.nodeJets
              #[n,N,← inferType pt[46]!,chart,C,fine,θ,Z]
            withLocalDeclD `trueCompleteNodeJets nodeProfile fun hJ =>
              withLocalDeclD `δ (mkConst ``Real) fun δ => do
                let all := fixed ++ #[hγ] ++ dyn ++ #[Z,hJ,δ]
                let correction := app (sum ++ `correction) (stem ++ #[Z,δ])
                let raw := ((← getConstInfo (sum ++ `correction)).value! (allowOpaque := true)).beta (stem ++ #[Z,δ])
                unless raw.isAppOfArity (sum ++ `sum) 9 do throwError "uniform signed sum: not the SAME finite correction"
                let sa := raw.getAppArgs
                let μ := sa[8]!
                let per := app one (b ++ #[hγ] ++ pt[37:].toArray ++ #[Z])
                if mode.getNat == 3 then
                  let earlier := app (root ++ `coefficient_mass_lag) all
                  let result ← forallBoundedTelescope (← inferType earlier) (some 2) fun y _ => do
                    let whole := mkAppN earlier y
                    let hmass := part (app (mass ++ `coefficient_budgets) stem) 1
                    let mv := (← inferType hmass).getAppArgs[2]!
                    let wv := (← inferType whole).getAppArgs[2]!
                    let proof := app (lag ++ `total) #[n,hn,A,M,R,δ,q,mv,wv,hA,hR,whole,hmass]
                    mkLambdaFVars y proof
                  let target := (← inferType result).replace fun e => if e == price then some (app (root ++ `constant) fixed) else none
                  save `lag all result target
                  return
                let label := app (hist ++ `label) pt
                let pairType := app (uni ++ `DerivativeProfile) (fixedSource ++ #[label,Z])
                let hp ← forallBoundedTelescope (← whnf pairType) (some 4) fun y _ => do
                  let left := mkAppN hJ (#[pt[46]!] ++ y[1:].toArray)
                  let right := mkAppN hJ (#[pt[47]!] ++ y[1:].toArray)
                  mkLambdaFVars y (← mkAppM ``And.intro #[left,right])
                let labels := ((← getConstInfo (uni ++ `Labels)).value! (allowOpaque := true)).beta fixedSource
                unless labels.isAppOfArity ``Sigma 2 do throwError "uniform signed sum: original universal Sigma changed"
                let la := labels.getAppArgs
                let fiber := la[1]!.beta #[label]
                unless fiber.isAppOfArity ``Subtype 2 do throwError "uniform signed sum: original source fiber changed"
                let bounded := mkAppN (mkConst ``Subtype.mk fiber.getAppFn.constLevels!) (fiber.getAppArgs ++ #[Z,hp])
                let sourceLabel := mkAppN (mkConst ``Sigma.mk labels.getAppFn.constLevels!) (la ++ #[label,bounded])
                let cert := app (hist ++ `native_window) pt
                let hb := part (part cert 1) 0
                let beat := (← inferType hb).appArg!
                let tensor := ((← getConstInfo `JanetCartan.PhysicalPairs.OriginalSignedPackets.tensor).value! (allowOpaque := true)).beta (pt.push Z)
                let η := tensor.appArg!
                let angles ← mkLambdaFVars signs (app `JanetCartan.PhysicalPairs.OriginalSignedData.angles pt)
                let cutoffs := app `JanetCartan.RevisedUniform.OriginalCore.original_cutoffs g[:23].toArray
                let alg := app `JanetCartan.PhysicalPairs.OriginalLagAlgebra.sum_strain (sa[:5].toArray ++ #[F,sa[5]!,Z])
                let result ← forallBoundedTelescope (← inferType per) (some 2) fun y _ => do
                  let hsx := mkAppN per y
                  let hex := mkAppN (.proj ``And 1 spec) (#[sourceLabel] ++ y)
                  let wv := (← inferType hsx).getAppArgs[2]!
                  let ev := (← inferType hex).getAppArgs[2]!
                  let each := app (lag ++ `single) #[n,hn,A,R,beat,q,wv,ev,hA,hR,hb,hsx,hex]
                  let hsingle ← mkLambdaFVars signs each
                  let onePrice := app (lag ++ `singlePrice) #[n,hn,A,R,q]
                  let hnPrice := app (lag ++ `single_nonneg) #[n,hn,A,R,q,hA,hR]
                  let hη ← mkAppM `JanetCartan.PhysicalPairs.OriginalStageLag.plateau #[part (mkAppN cutoffs y) 2]
                  let whole := mkAppN alg #[θ,angles,η,δ,R,μ,app (sum ++ `weight_nonneg) stem,y[0]!,hη,onePrice,hnPrice,hsingle]
                  mkLambdaFVars y whole
                let target := (← inferType result).replace fun e => if e == raw then some correction else none
                save `coefficient_mass_lag all result target
elab "identify_original_uniform_metric_lag" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (root ++ `lag)).type (some 52) fun p _ => do
    let stem := p[:37].toArray ++ p[41:49].toArray
    let eq := app (metric ++ `off_metric) (stem ++ #[p[49]!,p[51]!])
    let per := app (root ++ `lag) p
    let ee := (← inferType eq).getAppArgs
    let rh := ee[2]!.getAppArgs
    let result ← forallBoundedTelescope (← inferType per) (some 2) fun y _ => do
      let hv := mkAppN per y
      let ty := (← inferType hv).getAppArgs
      let norm := ty[2]!.appArg!.getAppArgs
      let proof := app (metric ++ `transfer)
        #[mkApp (mkConst ``Nat.succ) p[0]!,ee[1]!,rh[rh.size-2]!,rh.back!,eq,
          norm[norm.size-2]!,y[0]!,ty.back!,hv]
      mkLambdaFVars y proof
    save `metric_lag p result (← inferType result)
end JanetCartan.PhysicalPairs.OriginalUniformStageLagTemplate
end
