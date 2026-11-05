module

public meta import Lean

/-! Fill the actual strong source and coefficient inputs of the current inverse,
retaining the same shared capped extra and the same source operator. -/

public meta section
namespace JanetCartan.PhysicalNormalInverse.StrongCurrentSourceApplication
open Lean Meta Elab Command

elab "apply_actual_strong_source_to_current_inverse" : command => liftTermElabM do
  let current := `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap.continuation
  let source := `JanetCartan.PhysicalNormalInverse.StrongSource.exists_history_coercivity
  let sourceNS := `JanetCartan.PhysicalNormalInverse.StrongSource
  let selectedNS := `JanetCartan.PhysicalSeed.SelectedBoundary
  let inverseNS := `JanetCartan.PhysicalSeed.SourceInverseBoundary
  let info ← getConstInfo current
  forallBoundedTelescope info.type (some 21) fun original _ => do
    unless original.size == 21 do
      throwError "actual strong current: expected original21"
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[original[0]!, original[1]!, original[20]!]
    let selected := original.set! 20 capped
    let currentOriginal := mkAppN (mkConst current) original
    forallBoundedTelescope (← inferType currentOriginal) (some 2) fun scale _ => do
      unless scale.size == 2 do
        throwError "actual strong current: expected scale and inverse-cap proof"
      let sourceAtScale := mkApp (mkAppN (mkConst source) selected) scale[0]!
      forallBoundedTelescope (← inferType sourceAtScale) (some 1) fun sourceScale _ => do
        let sourceFixed := mkAppN sourceAtScale sourceScale
        forallBoundedTelescope (← inferType sourceFixed) (some 6) fun physical _ => do
          unless physical.size == 6 do
            throwError "actual strong current: expected the six physical order inputs"
          let sourceParams := selected ++ #[scale[0]!, sourceScale[0]!] ++ physical
          let currentOrders := mkAppN currentOriginal (scale ++ physical)
          forallBoundedTelescope (← inferType currentOrders) (some 3) fun leading _ => do
            unless leading.size == 3 do
              throwError "actual strong current: expected the uniform leading budgets"
            let currentBudgets := mkAppN currentOrders leading
            let (args, _, _) ← forallMetaTelescopeReducing (← inferType currentBudgets)
            unless args.size == 20 do
              throwError "actual strong current: expected20 source inputs, got {args.size}"
            let assign (index : Nat) (value : Expr) : MetaM Unit := do
              let arg := args[index]!
              unless ← isDefEq (← inferType arg) (← inferType value) do
                throwError "actual strong current: source input {index} type mismatch\nexpected: {← inferType arg}\nactual: {← inferType value}"
              unless ← isDefEq arg value do
                throwError "actual strong current: source input {index} witness mismatch"
            let selectedValue (field : Name) := mkAppN (mkConst (selectedNS ++ field)) selected
            let inverseValue (field : Name) := mkAppN (mkConst (inverseNS ++ field)) selected
            let sourceValue (field : Name) := mkAppN (mkConst (sourceNS ++ field)) sourceParams
            assign 2 (selectedValue `hrMeasure)
            assign 3 (selectedValue `hMeasureCell)
            assign 4 (inverseValue `hrInner)
            assign 5 (inverseValue `hInnerCell)
            assign 6 (selectedValue `fact58)
            assign 7 (selectedValue `fact59)
            assign 8 (selectedValue `χcoeff)
            assign 9 (selectedValue `fact62)
            assign 10 (selectedValue `fact65)
            assign 13 (inverseValue `fact8)
            assign 15 (sourceValue `Sgap)
            assign 16 (sourceValue `hSgap)
            assign 17 (sourceValue `coeffHistory)
            let formula := sourceValue `formula
            let formula ← forallBoundedTelescope (← inferType formula) (some 6) fun history _ => do
              unless history.size == 6 do
                throwError "actual strong current: expected six coefficient history inputs"
              mkLambdaFVars history (← instantiateMVars (← mkAppM ``And.left #[mkAppN formula history]))
            assign 18 formula
            let (hcarriers, rowBound) ← forallTelescopeReducing
                (← instantiateMVars (← inferType args[19]!)) fun history target => do
              unless history.size == 12 do
                throwError "actual strong current: expected history6/current1/density5"
              let raw := mkAppN (mkConst (sourceNS ++ `source_continuation))
                (sourceParams ++ history[7:12].toArray ++ history[:7].toArray)
              let witness ← mkAppM ``Classical.choose #[raw]
              let spec ← mkAppM ``Classical.choose_spec #[raw]
              let actions ← mkAppM ``And.left #[spec]
              let mut rest := spec
              for _ in [:2] do
                rest ← mkAppM ``And.right #[rest]
              let rowNorm ← mkAppM ``And.left #[rest]
              let rowNormType ← instantiateMVars (← inferType rowNorm)
              unless rowNormType.isAppOfArity ``LE.le 4 do
                throwError "actual strong current: expected source row LE.le, got {rowNormType.getAppFn} with {rowNormType.getAppNumArgs} inputs"
              let rowBound ← Core.betaReduce (← zetaReduce rowNormType.appArg!)
              let allowed := original
              if let some escaped := rowBound.find? (fun e => e.isFVar && !allowed.contains e) then
                throwError "actual strong current: row bound is not pre-scale; escaped local {(← escaped.fvarId!.getDecl).userName}"
              for _ in [:3] do
                rest ← mkAppM ``And.right #[rest]
              let adjointGap ← mkAppM ``And.left #[rest]
              let bundle ← mkAppM ``And.intro #[actions,
                ← mkAppM ``And.intro #[rowNorm, adjointGap]]
              let target ← whnf target
              let target := target.replace fun e =>
                if e == args[14]! then some rowBound else none
              unless target.isAppOfArity ``Exists 2 do
                throwError "actual strong current: expected actual carrier existential"
              let predicate := target.appArg!
              unless ← isDefEq (← inferType bundle) (predicate.beta #[witness]) do
                throwError "actual strong current: same-current carrier projection mismatch\nexpected: {predicate.beta #[witness]}\nactual: {← inferType bundle}"
              let result ← mkAppOptM ``Exists.intro
                #[none, some predicate, some witness, some bundle]
              pure (← mkLambdaFVars history (← instantiateMVars result), rowBound)
            unless ← isDefEq (← inferType args[14]!) (← inferType rowBound) do
              throwError "actual strong current: extracted row bound is not a real source constant"
            args[14]!.mvarId!.assign rowBound
            assign 19 hcarriers
            let args ← args.mapM instantiateMVars
            for index in [:args.size] do
              if args[index]!.hasMVar then
                throwError "actual strong current: unresolved source input {index}"
            let result := mkAppN currentBudgets args
            let allParams := original ++ scale ++ sourceScale ++ physical ++ leading
            let value ← instantiateMVars (← mkLambdaFVars allParams result)
            let type ← instantiateMVars (← mkForallFVars allParams (← inferType result))
            if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar ||
                value.hasSorry || type.hasSorry then
              throwError "actual strong current: incomplete source application; value M/F/S={value.hasMVar}/{value.hasFVar}/{value.hasSorry}, type M/F/S={type.hasMVar}/{type.hasFVar}/{type.hasSorry}; value local={value.find? (fun e => e.isFVar)}; type local={type.find? (fun e => e.isFVar)}"
            addDecl (.thmDecl {
              name := `JanetCartan.PhysicalNormalInverse.StrongCurrent.source_continuation,
              levelParams := [], type, value }) (forceExpose := true)
            logInfo "kernel-checked all20 actual source/current inputs on the identical shared capped callback"

end JanetCartan.PhysicalNormalInverse.StrongCurrentSourceApplication
