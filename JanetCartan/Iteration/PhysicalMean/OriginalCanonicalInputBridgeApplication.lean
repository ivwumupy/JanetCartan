module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceInput
public meta import Lean

/-! Exact, original-data input identifications for the actual finite source.
These consume93's checked A/An/native-row identities, not analytic premises. -/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalInputBridgeApplication
open Lean Meta Elab Command OriginalCanonicalSampledApplication

private def save (short : Name) (params : Array Expr) (term : Expr)
    (data := false) (target : Option Expr := none) : MetaM Unit := do
  let target ← match target with | some t => pure t | none => inferType term
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params term)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual source input bridge: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual source input bridge: unresolved original argument"
  let name := `JanetCartan.PhysicalMean.OriginalCanonicalSource ++ short
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The exact original-data fixed-source input identity, with the same actual finite run, component adjoint, inverse, prefix and sample. Unweighted individual input and weighted native aggregate are not interchanged (app:ch_mean_pairs:defn:mean-canonical; app:ch_mean_pairs:eq:raw-adjoint-moments)."
  logInfo m!"actual source input bridge {short}: native{params.size}, no new analytic input"

elab "construct_actual_canonical_input_bridge " mode:num : command => liftTermElabM do
  withActualSample fun xs ξ _ _ _ => do
    withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
      withLocalDeclNoLocalInstanceUpdate `steps .default (mkConst ``Nat) fun steps => do
        let root := `JanetCartan.PhysicalMean.OriginalCanonicalSource
        let row := `JanetCartan.PhysicalMean.OriginalCanonicalRow
        let gen := `JanetCartan.PhysicalMean.OriginalCanonicalInput
        let trial := xs ++ #[ξ,L]
        let params := trial.push steps
        let A := mkAppN (mkConst (row ++ `A)) trial
        let Q0 := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalCurrent.Q0) xs
        let source := mkAppN (mkConst (root ++ `iterate)) params
        let n := mkApp (mkConst ``Nat.succ) xs[0]!
        let toL2 := mkApp (mkConst `JanetCartan.CurrentMean.smoothResidualToL2) n
        let sourceL2 ← mkAppM ``DFunLike.coe #[toL2,source]
        let q ← mkAppM ``DFunLike.coe #[Q0,sourceL2]
        if mode.getNat == 2 then
          let identity := mkAppN (mkConst (row ++ `adjoint_input)) (trial.push q)
          let type ← inferType identity
          unless type.isAppOfArity ``Eq 3 do throwError "native weighted input lost its exact value"
          save `finalWeightedNativeInput params type.getAppArgs[2]! true
          return
        if mode.getNat == 3 then
          let proof := mkAppN (mkConst (row ++ `adjoint_input)) (trial.push q)
          let type ← inferType proof
          unless type.isAppOfArity ``Eq 3 do throwError "native weighted input lost its exact equality"
          let target ← mkEq type.getAppArgs[1]!
            (mkAppN (mkConst (root ++ `finalWeightedNativeInput)) params)
          save `finalWeightedNativeInput_eq params proof false (some target)
          return
        let raw := mkAppN (mkConst (root ++ `finalRawInput)) params
        let .forallE label I _ bi := (← inferType raw).consumeMData
          | throwError "actual source input bridge: original sample domain missing"
        withLocalDeclNoLocalInstanceUpdate label bi I fun i => do
          let inputAt (name : Name) := mkApp (mkAppN (mkConst (root ++ name)) params) i
          match mode.getNat with
          | 0 =>
            let An := mkApp (mkAppN (mkConst (row ++ `An)) trial) i
            let real ← mkAppM `JanetCartan.realQuadratureChannel #[An]
            let T ← mkAppM `JanetCartan.PeriodicLocalL2.transferOutputOperator #[real]
            let hA := mkApp (mkAppN (mkConst (row ++ `hArep)) trial) i
            let proof ← mkAppM (gen ++ `nativeInput_eq_adjoint) #[A,Q0,source,i,T,hA]
            let type ← inferType proof
            unless type.isAppOfArity ``Eq 3 do throwError "individual native input lost its exact equality"
            let target ← mkEq (inputAt `finalNativeInput) type.getAppArgs[2]!
            save `finalNativeInput_eq_adjoint (params.push i) proof false (some target)
          | 1 =>
            let G := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalSampled.G)
              (xs ++ #[ξ,i])
            let Gprefix := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalSampled.Gprefix)
              (trial.push i)
            let proof ← mkAppM (gen ++ `wideInput_realization) #[A,Q0,L,source,i,G]
            let left ← mkAppM ``DFunLike.coe #[Gprefix,inputAt `finalRawInput]
            let right ← mkAppM ``DFunLike.coe #[G,inputAt `finalWideInput]
            save `finalWideInput_realization (params.push i) proof false (some (← mkEq left right))
          | _ => throwError "actual source input bridge: unknown field"

end JanetCartan.PhysicalMean.OriginalCanonicalInputBridgeApplication
end
