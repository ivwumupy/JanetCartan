module
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformFirstMask
public import JanetCartan.Iteration.PhysicalPairs.OriginalNeumannTail
/-! # Uniform original negative moments and inverse tails

The original negative-moment price, coefficient price, depth and inverse-tail
constant already precede the source waves. Apply those SAME prices to the
universal bounded-source labels. The current, measured source, forward and
literal adjoint, and original residual operator are unchanged. Consumer:
`main:prop:pairs`, `app:ch_regular:eq:inverse-remainder`.
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalUniformTailTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalUniformTail
private def waves := `JanetCartan.PhysicalPairs.OriginalUniformWaveData
private def uniform := `JanetCartan.PhysicalPairs.OriginalUniformFirstMask
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def rows := `JanetCartan.PhysicalPairs.OriginalMaskRows
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def nm := `JanetCartan.PhysicalPairs.OriginalNegativeMoments
private def nt := `JanetCartan.PhysicalPairs.OriginalNeumannTail
private def sh := `JanetCartan.PhysicalPairs.OriginalShiftedCoefficients
private def native := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Native
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
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
      throwError "uniform original tail: source escaped fixed-price telescope {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking universal original inverse tail {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME once-measured original signed source has the original negative moments and native inverse tail, uniformly over all fixed-price complete waves before history/shift/target/smoothing; original current and adjoint preserved (main:prop:pairs; app:ch_regular:eq:inverse-remainder)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "uniform original tail: nonstandard axioms {axioms}"
  logInfo m!"universal original inverse tail {key}/{p.size}: {axioms}"
private def existsAt (e h : Expr) : MetaM Expr := do
  let α ← inferType e
  let type ← inferType h
  let f ← withLocalDeclD `bound α fun x => mkLambdaFVars #[x] (type.replace fun t => if t == e then some x else none)
  mkAppOptM ``Exists.intro #[some α,some f,some e,some h]
elab "prove_original_uniform_tail " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "uniform original tail: unknown mode"
  forallBoundedTelescope (← getConstInfo (uniform ++ `first_mask)).type (some 39) fun p _ => do
    let b := p[:37].toArray
    let fixed := p[:38].toArray
    let C := p[37]!
    let d := b[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let N := app `JanetCartan.embeddingDimension #[n]
    let β := app (waves ++ `Labels) fixed
    let field (key : Name) := app (waves ++ key) fixed
    let gf := (← inferType (app (hist ++ `historyMap) b)).bindingBody!
    let fix := gf.getAppArgs[:23].toArray
    let V := app (masks ++ `chart) fix
    let W := app (world ++ `W) fix
    let hW := app (world ++ `W_measurable) fix
    if mode.getNat == 0 then
      let proof ← withLocalDeclD `sourceLabel β fun t => do
        let old := Expr.proj ``Sigma 0 t
        let pt := point b old
        let row := pt.push (.proj ``Subtype 0 (.proj ``Sigma 1 t))
        let low := app (nm ++ `price_before_waves) p
        let h := down (← mkAppM ``Classical.choose_spec #[low]) 1
        let window := part (app (hist ++ `native_window) pt) 0
        let hη := app (masks ++ `χsrc_smooth) fix
        let η := (← inferType hη).appArg!
        let ρ := mkApp (field `frequency) t
        let la := #[d,N,β,V,field `left,field `right,C,field `fine,app (uniform ++ `full_profile) fixed]
        let args := #[V,W,app (masks ++ `chart_open) fix,hW,app (masks ++ `χ₃_support_chart) fix,
          η,mkApp (field `phase) t,mkApp (field `fine) t,ρ,
          mkApp (app (nm ++ `source_geometry) b) old,app (fm ++ `one_of_two) #[ρ,part window 2],part window 3,
          mkApp (field `frame) t,mkApp (field `left) t,mkApp (field `right) t,
          app (fm ++ `on_chart) #[d,V,η,hη],app (rows ++ `row_smooth) pt,
          app (rows ++ `left_smooth) row,app (rows ++ `right_smooth) row,
          app (rows ++ `source_jets) pt,app (rows ++ `row_jets) pt,
          mkApp (app (fm ++ `left_bound) la) t,mkApp (app (fm ++ `right_bound) la) t,pt[45]!,
          mkApp (field `measured) t,app (rows ++ `represented_realization) row]
        mkLambdaFVars #[t] (mkAppN h args)
      let price ← mkAppM ``Classical.choose #[app (nm ++ `price_before_waves) p]
      let target := (← inferType proof).replace fun e => if e == price then some (app (nm ++ `CN) p) else none
      save `negative_moments p proof (some target)
      return
    withLocalDeclD `observationOrder (mkConst ``Nat) fun s =>
      withLocalDeclD `accuracy (mkConst ``Nat) fun q => do
        let e := p ++ #[s,q]
        let dep := app (nt ++ `depth) e
        let cost := app (nt ++ `cost) e
        if mode.getNat == 2 then
          let h ← mkAppM ``And.intro #[app (nt ++ `cost_nonneg) e,app (root ++ `actual_tail) e]
          let proof ← existsAt dep (← existsAt cost h)
          save `unobserved_remainder (p.push s) (← mkLambdaFVars #[q] proof)
          return
        let proof ← withLocalDeclD `sourceLabel β fun t => do
          let pt := point b (.proj ``Sigma 0 t)
          let hi := app (hist ++ `measured_history) pt
          let now := pt[:36].toArray ++ #[pt[37]!,part hi 0] ++ pt[39:43].toArray
          let current := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPairs.projected).value! (allowOpaque := true)).beta now
          unless current.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalRegular.Current.projected 38 do
            throwError "uniform original tail: actual current changed"
          let weak := current.getAppArgs
          let dyn (key : Name) := app (native ++ key) weak
          let hK := dyn `real_half_bound
          let ka := (← inferType hK).getAppArgs
          let K := ka[ka.size-2]!.appArg!
          let hm := dyn `coefficient_monotone
          let A := (← inferType hm).appArg!
          let ρ := mkApp (field `frequency) t
          let L := app `JanetCartan.currentCoefficientScale #[pt[37]!,pt[39]!]
          let window := part (app (hist ++ `native_window) pt) 0
          let lc := app (sh ++ `current_window) pt
          let beta := mkApp2 (mkConst ``Nat.add)
            (app `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[d])
            (mkApp2 (mkConst ``Nat.add) d (mkNatLit 2))
          let spec := Expr.proj ``And 1 (app (nt ++ `cost.spec) e)
          let result := mkAppN spec #[W,hW,K,hK,L,ρ,part lc 0,
            app (fm ++ `one_of_two) #[ρ,part window 2],Expr.proj ``And 1 lc,
            A,beta,dyn `coefficient_nonneg,hm,app (sh ++ `actual_bound) pt,dyn `gain,
            mkApp (field `measured) t,mkAppN (app (root ++ `negative_moments) p) #[t,dep]]
          let priced ← mkAppM `JanetCartan.PhysicalPairs.OriginalNeumannTail.unit_price #[Expr.proj ``And 1 result]
          let bound ← mkAppM ``And.intro #[Expr.proj ``And 0 result,priced]
          mkLambdaFVars #[t] bound
        save `actual_tail e proof
end JanetCartan.PhysicalPairs.OriginalUniformTailTemplate
end
