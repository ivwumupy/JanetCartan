module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Actual all-history current specialization of the native letter geometry.
No operator, phase, current frame or source cutoff is reselected. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalLetterCurrentTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalLetterCurrent
private def geo := `JanetCartan.PhysicalPrimary.OriginalLetterGeometry
private def cur := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
private def wp := `JanetCartan.PhysicalPrimary.OriginalWordProfiles
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def symbols := `JanetCartan.PhysicalPrimary.OriginalRetardedSymbols
private def ranges := `JanetCartan.PhysicalPrimary.OriginalRetardedRanges
private def stationary := `JanetCartan.PhysicalPrimary.OriginalRetardedStationary
private def primitive := `JanetCartan.PhysicalPrimary.OriginalRetardedPrimitives

private def normalize (type : Expr) : MetaM Expr := do
  let type ← Core.betaReduce type
  transform type
    (pre := fun expr => do
      let args := expr.getAppArgs
      if args.size ≥ 1 && [`Q,`B,`Φ,`C,`G,`Op,`W₁,`Inv].any (fun name => expr.isAppOf (cur ++ name)) then
        let some value := (← getConstInfo expr.getAppFn.constName!).value? (allowOpaque := true)
          | return .continue
        return .visit (value.beta args)
      return .continue)
    (post := fun expr => do
    let args := expr.getAppArgs
    let nativeNat := args.size > 0 && args[0]! == mkConst ``Nat
    if (nativeNat && (expr.isAppOf ``HAdd.hAdd || expr.isAppOf ``HSub.hSub ||
        expr.isAppOf ``OfNat.ofNat)) || (args.size ≥ 2 && (expr.isAppOf ``Nat.add || expr.isAppOf ``Nat.sub)) then
      let value ← whnf expr
      if value != expr then return .visit value
    return .continue)

private partial def nextBinder (type : Expr) : MetaM Expr := do
  match type with
  | .mdata _ body => nextBinder body
  | .letE _ _ value body _ => nextBinder (body.instantiate1 value)
  | _ => return type

private def applyOne (label : Name) (proof value : Expr) : MetaM Expr := do
  let .forallE name domain _ _ ← nextBinder (← inferType proof)
    | throwError "actual original family {label}: expected another native binder"
  if label == `residual.field1 || label == `solver.field1 then
    return mkApp proof value
  let actual ← withTransparency .reducible do normalize (← inferType value)
  let native ← withTransparency .reducible do normalize domain
  let same ← withTransparency .reducible do isDefEq actual native
  unless same do
    throwError "actual original family {label}: supplied primitive does not match {name}\nACTUAL {← inferType value}\nNATIVE {domain}"
  logInfo m!"native geometry applied {label} / {name}"
  return mkApp proof value

/-- Choose the two already initialized thresholds only after the arbitrary
history index, and join the SAME actual current/coefficient/phase threshold.
Then discharge every native geometric dynamic argument on literal histories. -/
elab "apply_original_current_letter_geometry" : command => liftTermElabM do
  let some currentBody := (← getConstInfo (cur ++ `normalized_solver)).value? (allowOpaque := true)
    | throwError "actual original family: missing exposed normalized current"
  forallBoundedTelescope (← getConstInfo (geo ++ `residual_initialized)).type (some 49) fun fixed _ => do
    unless fixed.size == 49 do throwError "actual original family: native static49 changed"
    let hCoeffType ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[mkNatLit 2,fixed[37]!],fixed[27]!]
    withLocalDeclD `hCoeff hCoeffType fun hCoeff => do
      let reserve ← mkAppM (ns ++ `native_profile_reserves) #[hCoeff,fixed[43]!,fixed[41]!]
      let profileArgs := fixed[:32].toArray ++ #[fixed[32]!,fixed[37]!,hCoeff,fixed[38]!,
        .proj ``And 0 reserve,.proj ``And 1 reserve]
      unless profileArgs.size == 38 do throwError "actual original family: word-profile38 changed"
      let params := fixed.push hCoeff
      let mut nativeS : Array Expr := #[]
      let mut nativeSpec : Array Expr := #[]
      for label in [`residual,`solver] do
        let initialized := mkAppN (mkConst (geo ++ Name.mkSimple s!"{label}_initialized")) fixed
        let threshold ← store (ns ++ label ++ `S) params (← mkAppM ``Classical.choose #[initialized]) true
        let specification ← mkAppM ``Classical.choose_spec #[initialized]
        let type ← inferType initialized
        let specification ← store (ns ++ label ++ `spec) params specification false
          (some (type.appArg!.beta #[threshold]))
        nativeS := nativeS.push threshold
        nativeSpec := nativeSpec.push specification
      let profileS := mkAppN (mkConst (wp ++ `S)) profileArgs
      let nativeMax ← mkAppM ``Max.max #[nativeS[0]!,nativeS[1]!]
      let S ← store (ns ++ `S) params (← mkAppM ``Max.max #[profileS,nativeMax]) true
      let hProfile ← store (ns ++ `profile_threshold) params (← mkAppM `le_max_left #[profileS,nativeMax])
      let hNative ← mkAppM `le_max_right #[profileS,nativeMax]
      let hResidual ← store (ns ++ `residual_threshold) params (← mkAppM `le_trans
        #[← mkAppM `le_max_left #[nativeS[0]!,nativeS[1]!],hNative])
      let hSolver ← store (ns ++ `solver_threshold) params (← mkAppM `le_trans
        #[← mkAppM `le_max_right #[nativeS[0]!,nativeS[1]!],hNative])
      let hCurrent ← store (ns ++ `current_threshold) params (← mkAppM `le_trans
        #[mkAppN (mkConst (wp ++ `current_threshold)) profileArgs,hProfile])
      discard <| store (ns ++ `hS) params (← mkAppM `le_trans
        #[mkAppN (mkConst (wp ++ `hS)) profileArgs,hProfile])
      let initializedContinuation := .proj ``And 1 nativeSpec[0]!
      forallBoundedTelescope (← inferType initializedContinuation) (some 4) fun data _ => do
        unless data.size == 4 do throwError "actual original family: raw history data changed"
        let R₀ := data[0]!
        let hRType ← withLocalDeclD `i fixed[34]! fun i => do
          mkForallFVars #[i] (← mkAppM ``LE.le #[S,mkApp R₀ i])
        withLocalDeclD `hR₀ hRType fun hR₀ => do
          let nativeLower (h : Expr) : MetaM Expr := withLocalDeclD `i fixed[34]! fun i => do
            mkLambdaFVars #[i] (← mkAppM `le_trans #[h,mkApp hR₀ i])
          let residualLower ← nativeLower hResidual
          let first := mkAppN initializedContinuation (data.push residualLower)
          forallBoundedTelescope (← inferType first) (some 1) fun admission _ => do
            let all := params ++ data ++ #[hR₀] ++ admission
            let sectorType := (← inferType (mkAppN (mkConst (reg ++ `fact11)) fixed[:23].toArray)).bindingDomain!
            withLocalDeclD `p sectorType fun p => do
              withLocalDeclD `negative (mkConst ``Bool) fun negative => do
                withLocalDeclD `i fixed[34]! fun i => do
                  let hCurrentR ← mkAppM `le_trans #[hCurrent,mkApp hR₀ i]
                  let now := fixed[:32].toArray ++ #[mkApp R₀ i,hCurrentR,
                    mkApp data[1]! i,mkApp data[2]! i,mkApp data[3]! i,mkApp admission[0]! i]
                  let weak := currentBody.beta now
                  unless weak.isAppOfArity (reg ++ `Current.normalized_solver) 38 do
                    throwError "actual original family: same normalized current38 disappeared"
                  let weakArgs := weak.getAppArgs
                  let current (name : Name) := mkAppN (mkConst (cur ++ name)) now
                  let sy (name : Name) := mkAppN (mkConst (symbols ++ name)) (weakArgs.push p)
                  let signedArgs := weakArgs ++ #[p,negative,fixed[32]!,mkConst ``Bool.false]
                  let st (name : Name) := mkAppN (mkConst (stationary ++ name)) signedArgs
                  let pr (name : Name) := mkAppN (mkConst (primitive ++ name)) signedArgs
                  let pi (value : Expr) := mkLambdaFVars #[p,i] value
                  let pni (value : Expr) := mkLambdaFVars #[p,negative,i] value
                  let each (value : Expr) := mkLambdaFVars #[i] value
                  let chart := mkAppN (mkConst (reg ++ `Sector.chart)) (fixed[:23].toArray.push p)
                  let index ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.index #[chart]
                  let root ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.root #[chart]
                  let coordinates ← mkAppM `JanetCartan.RegularSector.Characteristic.coordinateSplit #[index]
                  let h ← mkAppM `JanetCartan.RegularSector.Characteristic.RootFamily.fieldRoot
                    #[coordinates,current `Q,root]
                  let hκ := st `κ_smooth
                  let κ := (← inferType hκ).appFn!.appArg!
                  let frameValue := mkApp (current `sourceFrame) fixed[32]!
                  let frameValueEq ← mkEqRefl (Expr.proj ``Subtype 0 frameValue)
                  let mut known : Array Expr := #[
                    ← each frameValue,← each frameValueEq,
                    ← pi h,← pi (mkApp (current `Φ) p),← pi (mkApp (current `C) p),← pi (mkApp (current `G) p)]
                  for label in [`chart_buffer,`chart_phase_smooth,`chart_phase_differential,
                      `chart_mixed_near,`chart_phase_profile,`chart_source_time,
                      `buffered_smooth,`collared_smooth,`collared_support,
                      `solver_phase_germ,`residual_phase_germ,`conic_seminorms] do
                    known := known.push (← pi (sy label))
                  known := known ++ #[
                    ← pni (mkAppN (mkConst (ranges ++ `active_source_band)) (now ++ #[p,negative,fixed[32]!])),
                    ← pi (mkAppN (mkConst (ranges ++ `whole_source_band)) (now ++ #[p,fixed[32]!])),
                    ← pi (mkAppN (mkConst (ranges ++ `radial_gradient_range)) (now.push p))]
                  let op ← withLocalDeclD `o (mkApp (mkConst ``Fin) (mkNatLit 2)) fun o =>
                    mkLambdaFVars #[p,i,o] (mkAppN (current `Op) #[o,p])
                  known := known ++ #[op,← pi (sy `retained_signed_bounds),← pni κ,
                    ← pni (st `phase_smooth),← pni hκ,← pni (pr `critical),
                    ← pni (pr `hessian),← pni (pr `segments)]
                  unless known.size == 29 do throwError "actual original family: geometric dynamic29 changed"
                  for (label,specification,lower) in [
                      (`residual,nativeSpec[0]!,residualLower),
                      (`solver,nativeSpec[1]!,← nativeLower hSolver)] do
                    let mut proof := mkAppN (.proj ``And 1 specification) (data ++ #[lower] ++ admission)
                    for j in [:known.size] do
                      if j < 8 then
                        proof ← applyOne (label ++ Name.mkSimple s!"field{j}") proof known[j]!
                      else
                        proof := mkApp proof known[j]!
                    let .forallE _ domain _ _ ← nextBinder (← inferType proof)
                      | throwError "actual original family: native inactive-angle input missing"
                    let inactive ← forallBoundedTelescope domain (some 8) fun q _ => do
                      unless q.size == 8 do throwError "actual original family: inactive angle binder count changed"
                      let i' := q[2]!
                      let hRi ← mkAppM `le_trans #[hCurrent,mkApp hR₀ i']
                      let actual := fixed[:32].toArray ++ #[mkApp R₀ i',hRi,mkApp data[1]! i',
                        mkApp data[2]! i',mkApp data[3]! i',mkApp admission[0]! i']
                      let gap := mkAppN (mkConst (ranges ++ `inactive_forward_gap))
                        (actual ++ #[q[0]!,q[1]!,fixed[32]!])
                      mkLambdaFVars q (mkAppN gap #[q[3]!,q[4]!,Expr.proj ``And 1 q[5]!])
                    proof := mkApp proof inactive
                    discard <| store (ns ++ label ++ `geometric_family) all proof
  logInfo "actual SAME history families close every dynamic geometric native53/native50 argument; all source/profile estimates remain explicit at the parent boundary"

end JanetCartan.PhysicalPrimary.OriginalLetterCurrentTemplate
