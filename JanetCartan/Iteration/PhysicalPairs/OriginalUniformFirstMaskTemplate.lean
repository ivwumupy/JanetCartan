module
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformWaveData
public import JanetCartan.Iteration.PhysicalPairs.OriginalObservedPairs
/-! # One original signed first-mask estimate before ALL bounded source data

Use the fixed-price universal complete-wave labels, not a wave family selected
at one current target or smoothing scale. Every phase, current, operator, and
PSigma×12 signed label is the unchanged original one. Only the source is an
extra label. `main:prop:pairs` consumes the resulting uniform constants.
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalUniformFirstMaskTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalUniformFirstMask
private def waves := `JanetCartan.PhysicalPairs.OriginalUniformWaveData
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def rows := `JanetCartan.PhysicalPairs.OriginalMaskRows
private def geo := `JanetCartan.PhysicalPairs.OriginalMaskGeometry
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def cost := `JanetCartan.PhysicalPairs.MeasuredSourceCost
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def down (e : Expr) : Nat → Expr | 0 => e | k+1 => down (.proj ``And 1 e) k
private def part (e : Expr) (k : Nat) := Expr.proj ``And 0 (down e k)
private def point (b : Array Expr) (t : Expr) : Array Expr := Id.run do
  let mut p := b
  let mut q := t
  for _ in [:12] do
    p := p.push (.proj ``PSigma 0 q)
    q := .proj ``PSigma 1 q
  return p
private def save (key : Name) (p : Array Expr) (proof : Expr) (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "uniform original first mask: later input escaped fixed price {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking universal original source {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original complete signed source is estimated uniformly over ALL fixed-price Schwartz source waves, before history/shift/target/smoothing inputs; original labels and noninjective history projection are retained (main:prop:pairs; new:sec:order-of-choices)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "uniform original source has nonstandard axioms: {axioms}"
  logInfo m!"universal original source {key}/{p.size}: {axioms}"
elab "prove_original_uniform_first_mask " mode:num : command => liftTermElabM do
  unless mode.getNat < 6 do throwError "uniform original first mask: unknown mode"
  forallBoundedTelescope (← getConstInfo (waves ++ `Labels)).type (some 38) fun fixed _ => do
    let b := fixed[:37].toArray
    let C := fixed[37]!
    let d := b[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let N := app `JanetCartan.embeddingDimension #[n]
    let β := app (waves ++ `Labels) fixed
    let graph := (← inferType (app (hist ++ `historyMap) b)).bindingBody!
    let fix := graph.getAppArgs[:23].toArray
    let V := app (masks ++ `chart) fix
    let W := app (world ++ `W) fix
    let hW := app (world ++ `W_measurable) fix
    let field (key : Name) := app (waves ++ key) fixed
    let A := field `left
    let B := field `right
    let M := field `fine
    let ledger := app (fm ++ `FullDerivativeProfile) #[d,N,β,V,A,B,C,M]
    if mode.getNat == 0 then
      let proof ← forallBoundedTelescope (← whnf ledger) (some 4) fun x _ => do
        let prop := Expr.proj ``Subtype 1 (.proj ``Sigma 1 x[0]!)
        mkLambdaFVars x (mkAppN prop (#[mkConst ``Unit.unit] ++ x[1:].toArray))
      save `full_profile fixed proof (some ledger)
      return
    let hCType ← withLocalDeclD `jet (mkConst ``Nat) fun j => do
      mkForallFVars #[j] (← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,mkApp C j])
    withLocalDeclD `nonnegativePrice hCType fun hC => do
      let p := fixed.push hC
      let early := b ++ #[C,hC]
      let u := field `measured
      let ρ := field `frequency
      let label ← withLocalDeclD `sourceLabel β fun t => do
        let old := Expr.proj ``Sigma 0 t
        let pt := point b old
        let row := pt.push (.proj ``Subtype 0 (.proj ``Sigma 1 t))
        let family (e : Expr) := mkLambdaFVars #[t] e
        if mode.getNat == 3 then
          let proof ← family (app (cost ++ `native_support) row)
          save `support fixed proof
          return
        if mode.getNat == 4 then
          let hu ← family (.proj ``And 0 (mkApp (app (root ++ `norms) p) t))
          let proof ← mkAppM `JanetCartan.PhysicalPairs.OriginalObservedPairs.flat_price
            #[u,ρ,app (fm ++ `sourceNormCost) early,app (fm ++ `sourceNormCost_nonneg) early,hu]
          save `source_polynomial p proof
          return
        if mode.getNat == 5 then
          let proof := app `JanetCartan.PhysicalInitialization.OriginalSampledChains.observed_residual_powers
            (b[:36].toArray ++ #[β,field `historyMap,u,app (root ++ `support) fixed,app (root ++ `source_polynomial) p])
          forallBoundedTelescope (← inferType proof) (some 2) fun obs _ =>
            save `observed_powers (p ++ obs) (mkAppN proof (obs.push (app (root ++ `first_mask) p)))
          return
        let history := app (hist ++ `measured_history) pt
        let window := part (app (hist ++ `native_window) pt) 0
        let hχ := app (masks ++ `χ₂_smooth) fix
        let hψ := app (masks ++ `χsrc_smooth) fix
        let χ := (← inferType hχ).appArg!
        let ψ := (← inferType hψ).appArg!
        let hχV := app (masks ++ `χ₂_support_chart) fix
        let hc := app (masks ++ `χ₂_compact) fix
        let hV := app (masks ++ `chart_open) fix
        let graphBody := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.GraphFamily).value! (allowOpaque := true)).beta graph.getAppArgs
        let coeff := graphBody.getAppArgs.back!.getAppArgs
        let AQ := app (op ++ `AQ) coeff
        let hAQ := app (op ++ `fact1) coeff
        let Dphase := app `JanetCartan.PhysicalPairs.OriginalSignedFrames.jointProfile b[:36].toArray
        let P := app (fm ++ `phaseCost) #[Dphase]
        let hp := app (fm ++ `phaseCost_nonneg) #[Dphase,app `JanetCartan.PhysicalPairs.OriginalSignedFrames.jointProfile_nonneg b[:36].toArray]
        let X := app (rows ++ `bumpProfile) b
        let Y := app (rows ++ `sourceProfile) b
        let hX := app (rows ++ `bumpProfile_nonneg) b
        let hY := app (rows ++ `sourceProfile_nonneg) b
        let chart (f h : Expr) := app (fm ++ `on_chart) #[d,V,f,h]
        let left := app (fm ++ `left_bound) #[d,N,β,V,A,B,C,M,app (root ++ `full_profile) fixed]
        let right := app (fm ++ `right_bound) #[d,N,β,V,A,B,C,M,app (root ++ `full_profile) fixed]
        let one := app (fm ++ `one_of_two) #[mkApp ρ t,part window 2]
        if mode.getNat == 1 then
          let Ksrc := app `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.Ksource b[:22].toArray
          let phase := field `phase
          let hgrad := app (fm ++ `on_support) #[d,V,Ksrc,χ,mkApp phase t,hχV,app (geo ++ `gradient_in_source) pt]
          let hj := app (fm ++ `jets_on_support) #[d,V,χ,mkApp phase t,hχV,P,mkApp M t,app (geo ++ `higher_jets) pt]
          let proof := app `JanetCartan.PhysicalPairs.SampledMask.first_mask
            #[d,N,β,V,W,hV,hW,χ,ψ,hc,hχV,chart χ hχ,chart ψ hψ,Ksrc,
              field `frame,A,B,field `minus,phase,ρ,M,u,
              ← family (app (rows ++ `row_smooth) pt),← family (app (rows ++ `left_smooth) row),← family (app (rows ++ `right_smooth) row),
              ← family (chart (mkApp phase t) (app (geo ++ `smooth) pt)),← family (part history 3),← family one,← family (part window 3),
              mkApp P (mkNatLit 0),P,X,Y,AQ,C,hp,hX,hY,hAQ,hC,
              ← family (app (rows ++ `bump_jets) pt),← family (app (rows ++ `source_jets) pt),← family (app (rows ++ `row_jets) pt),left,right,
              ← family hgrad,← family (app (geo ++ `gradient_upper) pt),← family hj,← family (app (rows ++ `represented_realization) row)]
          let type ← inferType proof
          let target := app `JanetCartan.PhysicalInitialization.OriginalSampledObserved.FirstMaskInput
            #[d,β,ρ,field `complexSource,type.getAppArgs.back!]
          save `first_mask p proof (some target)
        else
          let low := app (fm ++ `cost_before_sources) early
          let budget := down (← mkAppM ``Classical.choose_spec #[low]) 1
          let bounds := mkAppN budget #[V,W,hV,hW,χ,ψ,mkApp (field `frame) t,mkApp A t,mkApp B t,chart χ hχ,chart ψ hψ,
            app (rows ++ `row_smooth) pt,app (rows ++ `left_smooth) row,app (rows ++ `right_smooth) row,
            app (fm ++ `support_refl) #[d,χ],hχV,mkApp M t,part history 3,
            app (rows ++ `bump_jets) pt,app (rows ++ `source_jets) pt,app (rows ++ `row_jets) pt,
            mkApp left t,mkApp right t,mkApp (field `minus) t,mkApp (field `phase) t,mkApp ρ t,mkApp u t,
            app (rows ++ `represented_realization) row]
          let price ← mkAppM ``Classical.choose #[low]
          let proof ← family bounds
          let target := (← inferType proof).replace fun e => if e == price then some (app (fm ++ `sourceNormCost) early) else none
          save `norms p proof (some target)
      pure label
end JanetCartan.PhysicalPairs.OriginalUniformFirstMaskTemplate
end
