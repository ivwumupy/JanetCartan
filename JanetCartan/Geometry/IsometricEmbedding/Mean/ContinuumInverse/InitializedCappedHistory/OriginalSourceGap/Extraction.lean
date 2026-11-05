module

public meta import Lean

/-!
# Checked projection of the original source inverse at a fixed scale

Only ordinary kernel-checked declarations are generated. The producer is the
actual selected source-inverse continuation, not a supplied source-gap premise.
The projection first keeps its density-dependent `Vzero`, then its operator at
the same source scale, and finally the six literal fields needed by the history
gap consumer. The complete operator specification is retained separately.
-/

public meta section
namespace JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalSourceGap.Generator
open Lean Meta Elab Command

private def resultNamespace : Name :=
  `JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalSourceGap

private def addDefinition (shortName : Name) (params : Array Expr)
    (type value : Expr) : MetaM Expr := do
  let name := resultNamespace ++ shortName
  addDecl (.defnDecl {
    name, levelParams := [], type := ← mkForallFVars params type,
    value := ← mkLambdaFVars params value,
    hints := .abbrev, safety := .safe }) (forceExpose := true)
  return mkAppN (mkConst name) params

private def addTheorem (shortName : Name) (params : Array Expr)
    (type value : Expr) : MetaM Expr := do
  let name := resultNamespace ++ shortName
  addDecl (.thmDecl {
    name, levelParams := [], type := ← mkForallFVars params type,
    value := ← mkLambdaFVars params value }) (forceExpose := true)
  return mkAppN (mkConst name) params

/-- The conjunction of exactly the first six original source-operator fields. -/
private def sixFieldType (type : Expr) : MetaM Expr := do
  let mut rest := type
  let mut fields : Array Expr := #[]
  for _ in [:6] do
    rest ← whnf rest
    unless rest.isAppOfArity ``And 2 do
      throwError "original source gap: expected six source conjunction fields"
    fields := fields.push rest.appFn!.appArg!
    rest := rest.appArg!
  let mut result := fields[5]!
  for index in [0:5] do
    result := mkApp2 (mkConst ``And) fields[4 - index]! result
  return result

/-- Keep each literal source field on the chosen operator, in the original order. -/
private def sixFieldProof (params : Array Expr) (proof : Expr) : MetaM Expr := do
  let names : Array Name := #[`unique, `actions, `row_norm, `local_gap,
    `augmented_normal_gap, `augmented_adjoint_gap]
  let mut rest := proof
  let mut fields : Array Expr := #[]
  for index in [:6] do
    let type ← whnf (← inferType rest)
    unless type.isAppOfArity ``And 2 do
      throwError "original source gap: expected source field {index}"
    let field ← mkAppM ``And.left #[rest]
    let field ← addTheorem names[index]! params type.appFn!.appArg! field
    fields := fields.push field
    let right ← mkAppM ``And.right #[rest]
    rest ← addTheorem (.mkSimple s!"operatorTail{index + 1}") params type.appArg! right
  let mut result := fields[5]!
  for index in [0:5] do
    result ← mkAppM ``And.intro #[fields[4 - index]!, result]
  return result

/-- From the actual original continuation, select the same `Vzero` and same-scale
`Vop`, retain the complete specification, and rearrange only universal inputs. -/
elab "project_original_fixed_scale_source_gap" : command => liftTermElabM do
  let source := `JanetCartan.ContinuumInverse.InitializedCappedHistory.SourceInverseBoundary.continuation
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "original source gap: unexpected universe parameters"
  forallBoundedTelescope info.type (some 21) fun originalParams densityTail => do
    unless originalParams.size == 21 do
      throwError "original source gap: expected all 21 original parameters"
    forallTelescopeReducing densityTail fun densityParams zeroExists => do
      unless densityParams.size == 5 do
        throwError "original source gap: expected density and its four original hypotheses"
      let zeroExists ← whnf zeroExists
      unless zeroExists.isAppOfArity ``Exists 2 do
        throwError "original source gap: expected the density-dependent Vzero"
      let densityAll := originalParams ++ densityParams
      let original := mkAppN (mkConst source) densityAll
      let zeroPredicate := zeroExists.appArg!
      let zeroValue ← mkAppM ``Classical.choose #[original]
      let zero ← addDefinition `Vzero densityAll zeroExists.appFn!.appArg! zeroValue
      let zeroSpecValue ← mkAppM ``Classical.choose_spec #[original]
      let zeroSpec ← addTheorem `frozen_spec densityAll
        (zeroPredicate.beta #[zero]) zeroSpecValue
      let mut scaleProof := zeroSpec
      -- actions, norm, local gap, augmented-normal gap, augmented-adjoint gap,
      -- and the frozen exterior clause precede the original scale continuation.
      for index in [:6] do
        let type ← whnf (← inferType scaleProof)
        unless type.isAppOfArity ``And 2 do
          throwError "original source gap: expected frozen field {index}"
        let right ← mkAppM ``And.right #[scaleProof]
        scaleProof ← addTheorem (.mkSimple s!"frozenTail{index + 1}") densityAll type.appArg! right
      let scaleContinuation ← addTheorem `scale_continuation densityAll (← inferType scaleProof) scaleProof
      forallBoundedTelescope (← inferType scaleContinuation) (some 2) fun scaleParams operatorExists => do
        unless scaleParams.size == 2 do
          throwError "original source gap: expected the original scale and its interval proof"
        let operatorExists ← whnf operatorExists
        unless operatorExists.isAppOfArity ``Exists 2 do
          throwError "original source gap: expected the same-scale Vop"
        let fixedParams := originalParams ++ scaleParams
        let allParams := fixedParams ++ densityParams
        let atScale := mkAppN scaleContinuation scaleParams
        let operatorPredicate := operatorExists.appArg!
        let operatorValue ← mkAppM ``Classical.choose #[atScale]
        let operator ← addDefinition `Vop allParams operatorExists.appFn!.appArg! operatorValue
        let operatorSpecValue ← mkAppM ``Classical.choose_spec #[atScale]
        let operatorSpec ← addTheorem `operator_spec allParams
          (operatorPredicate.beta #[operator]) operatorSpecValue
        let gapPredicate ← withLocalDeclD `Vop operatorExists.appFn!.appArg! fun witness => do
          mkLambdaFVars #[witness] (← sixFieldType (operatorPredicate.beta #[witness]))
        let gapProof ← sixFieldProof allParams operatorSpec
        let gapProof ← addTheorem `gap_spec allParams (gapPredicate.beta #[operator]) gapProof
        let existsType ← mkAppM ``Exists #[gapPredicate]
        let existsProof ← mkAppOptM ``Exists.intro
          #[none, some gapPredicate, some operator, some gapProof]
        let inputType ← mkForallFVars densityParams existsType
        let inputProof ← mkLambdaFVars densityParams existsProof
        let cached ← addDefinition `FixedScaleSourceInput fixedParams (mkSort 0) inputType
        discard <| addTheorem `source_input fixedParams cached inputProof

end JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalSourceGap.Generator
