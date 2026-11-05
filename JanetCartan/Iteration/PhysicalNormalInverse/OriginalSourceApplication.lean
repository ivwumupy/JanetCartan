module

public meta import Lean

/-!
# Apply the actual original source to the physical-history consumer

Every argument is instantiated on the checked original callback witnesses.
The only new inputs are the admitted source scale, physical band constant,
fixed reserve and literal revised history order.
Generated declarations are safe, ordinary kernel-checked definitions/theorems.
-/

public meta section
namespace JanetCartan.PhysicalNormalInverse.OriginalSourceApplication
open Lean Meta Elab Command Term

private def resultNamespace : Name :=
  `JanetCartan.PhysicalNormalInverse.OriginalSource

private def addTheorem (name : Name) (params : Array Expr) (type value : Expr) : MetaM Expr := do
  let fullName := resultNamespace ++ name
  addDecl (.thmDecl {
    name := fullName, levelParams := [], type := ← mkForallFVars params type,
    value := ← mkLambdaFVars params value }) (forceExpose := true)
  return mkAppN (mkConst fullName) params

private def addDefinition (name : Name) (params : Array Expr) (type value : Expr) : MetaM Expr := do
  let fullName := resultNamespace ++ name
  addDecl (.defnDecl {
    name := fullName, levelParams := [], type := ← mkForallFVars params type,
    value := ← mkLambdaFVars params value, hints := .abbrev, safety := .safe }) (forceExpose := true)
  return mkAppN (mkConst fullName) params

private partial def withAliases (bindings : List (Name × Expr))
    (fvars values : Array Expr) (k : Array Expr → Array Expr → TermElabM Unit) : TermElabM Unit := do
  match bindings with
  | [] => k fvars values
  | (name, value) :: rest =>
    withLetDecl name (← inferType value) value fun x =>
      withAliases rest (fvars.push x) (values.push value) k

private def parseTerm (code : String) : TermElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term code with
  | .ok stx => return stx
  | .error message => throwError "original history argument syntax: {message}"

/-- Instantiate every original-data premise, then keep the whole history tail
on the same actual source row (`new:sec:order-of-choices`). -/
elab "apply_original_physical_source_history_gap" : command => liftTermElabM do
  let base := `JanetCartan.ContinuumInverse.InitializedCappedHistory
  let original := base.str "OriginalBoundary"
  let selected := base.str "SelectedBoundary"
  let inverse := base.str "SourceInverseBoundary"
  let reference := base.str "ReferenceBoundary"
  let conic := base ++ `OriginalHistoryGap.Conic
  let source := base ++ `OriginalSourceGap.source_input
  let consumer := `JanetCartan.PhysicalNormalInverse.exists_prescribed_source_history_coercivity
  let info ← getConstInfo source
  forallTelescope info.type fun sourceParams sourceType => do
    unless sourceParams.size == 23 do
      throwError "original history: expected 21 callbacks plus the scale and its interval proof"
    withLocalDecl `Bband .implicit (mkConst `Real) fun Bband => do
      withLocalDecl `rStar .implicit (mkConst ``Nat) fun rStar => do
        withLocalDecl `kMin .implicit (mkConst ``Nat) fun kMin => do
          let (orderArgs, _, _) ← forallMetaTelescopeReducing (← getConstInfo consumer).type
          let lookupOrder (name : Name) : MetaM Expr := do
            for arg in orderArgs do
              if (← arg.mvarId!.getDecl).userName == name then return arg
            throwError "physical history: missing order argument {name}"
          orderArgs[0]!.mvarId!.assign sourceParams[0]!
          (← lookupOrder `Bband).mvarId!.assign Bband
          (← lookupOrder `rStar).mvarId!.assign rStar
          (← lookupOrder `kMin).mvarId!.assign kMin
          let bandType ← instantiateMVars (← inferType (← lookupOrder `hBband))
          let reserveType ← instantiateMVars (← inferType (← lookupOrder `hStar))
          let orderType ← instantiateMVars (← inferType (← lookupOrder `horder))
          if bandType.hasMVar || reserveType.hasMVar || orderType.hasMVar then
            throwError "physical history: revised order unexpectedly depends on extra data"
          withLocalDeclD `hBband bandType fun hBband => do
            withLocalDeclD `hStar reserveType fun hStar => do
              withLocalDeclD `horder orderType fun horder => do
                let (args, _, _) ← forallMetaTelescopeReducing (← getConstInfo consumer).type
                unless args.size == 134 do
                  throwError "original history: original consumer parameter list changed"
                unless ← isDefEq (← inferType args.back!) sourceType do
                  throwError "original history: actual source_input does not match the exact consumer"
                args.back!.mvarId!.assign (mkAppN (mkConst source) sourceParams)
                let value (ns field : Name) (count : Nat) := mkAppN (mkConst (ns ++ field)) sourceParams[:count]
                let lookup (name : Name) : MetaM Expr := do
                  for arg in args do
                    if (← arg.mvarId!.getDecl).userName == name then return arg
                  throwError "original history: missing consumer argument {name}"
                let assign (name : Name) (proof : Expr) : MetaM Unit := do
                  let arg ← lookup name
                  unless ← isDefEq (← inferType arg) (← inferType proof) do
                    throwError "original history: argument type mismatch for {name}\nexpected: {← inferType arg}\nactual: {← inferType proof}"
                  unless ← isDefEq arg proof do
                    throwError "original history: original witness mismatch for {name}"
                for (name, field) in [( `rOuter, `r), (`aOuter, `a), (`D, `Dc), (`p₀, `p₀),
                    (`q₀, `q₀), (`ρi, `ρ), (`τi, `τ), (`W, `W), (`Bi, `Bi), (`Q, `Qc),
                    (`Ωi, `Ωi), (`It, `It), (`A, `A), (`gap, `gap), (`η, `ε), (`χcoeff, `χcoeff)] do
                  assign name (value selected field 21)
                assign `Rwork (value original `R 2)
                let indexType ← instantiateMVars args[1]!
                withLocalDeclD `i indexType fun i => do
                  assign `δgeometry (← mkLambdaFVars #[i] (value selected `δ 21))
                for (name, field) in [(`hηb, `hηb), (`hrOuter, `_hr), (`hr, `ha'), (`hcell, `hcell),
                    (`hrAngular, `hr'), (`hμ, `hrMeasure), (`hμcell, `hMeasureCell),
                    (`hRchart, `fact58), (`hcoeffCell, `fact59), (`hχcoeff, `fact62),
                    (`hχrange, `fact63), (`hsCoeff, `fact65)] do
                  assign name (value selected field 21)
                for (name, field) in [(`hrInner, `hrInner), (`hInnerCell, `hInnerCell),
                    (`hg, `fact1), (`hglobalGap, `fact8)] do
                  assign name (value inverse field 21)
                for name in [`hρi, `hτi, `hW, `hKiW, `hBi, `hWBi, `hQ, `hΩi, `hQΩi,
                    `hIt, `hIIt, `hsegT, `hseg, `hgap, `hη, `hfreq, `hcontains, `hBiDom,
                    `hQradius, `hne, `hscale, `hDregion, `hsupportD] do
                  assign name (value conic name 21)
                assign `Bband Bband
                assign `hBband hBband
                assign `rStar rStar
                assign `hStar hStar
                assign `kMin kMin
                assign `horder horder
                let allParams := sourceParams ++ #[Bband, hBband, rStar, kMin, hStar, horder]
                let aliases : List (Name × Expr) := [
                  (`rawPhysical, value original `stateDomain_subset_ball 2),
                  (`rawGeometry, value original `innerState_certificate 2),
                  (`rawCover, value original `hD 2),
                  (`rawPositive, value original `comparison_pos 2),
                  (`rawTransport, value original `transport_cells 2),
                  (`rawProduct, value original `density_product_geometry 2),
                  (`rawbPos, value original `b_pos 2),
                  (`rawbR, value original `b_lt_R 2),
                  (`rawChart, value original `R_lt_chartRadius 2),
                  (`referenceDomain, value reference `fact5 18),
                  (`selectedCell, value selected `cell 21),
                  (`selectedOuter, value selected `fact23 21),
                  (`selectedCurrent, value selected `fact94 21),
                  (`selectedCoeff, value selected `fact79 21),
                  (`selectedGeometry, value conic `geometry 21),
                  (`sourceDensityCap, value inverse `hcapSource 21),
                  (`sourceCoeffCap, value inverse `fact12 21),
                  (`sourceUnitCap, value inverse `fact13 21),
                  (`sourceFamily, ← instantiateMVars args[6]!),
                  (`sourceRow, ← instantiateMVars args[13]!),
                  (`sourceCol, ← instantiateMVars args[14]!),
                  (`scale, sourceParams[21]!), (`scaleProof, sourceParams[22]!)]
                withAliases aliases #[] #[] fun aliasVars aliasValues => do
                  let prove (name : Name) (code : String) : TermElabM Unit := do
                    let arg ← lookup name
                    let expected ← instantiateMVars (← inferType arg)
                    let proof ← elabTermEnsuringType (← parseTerm code) expected
                    synthesizeSyntheticMVarsNoPostponing
                    let proof := (← instantiateMVars proof).replaceFVars aliasVars aliasValues
                    let type := (← instantiateMVars (← inferType proof)).replaceFVars aliasVars aliasValues
                    if proof.hasMVar || type.hasMVar then
                      throwError "original history: unresolved metavariable in actual proof {name}"
                    if proof.hasSorry || type.hasSorry then
                      throwError "original history: elaboration recovery is not an actual proof of {name}"
                    let cached ← addTheorem (`Arguments ++ name) allParams type proof
                    assign name cached
                  prove `hdomain "by intro i z hz; exact ball_subset_ball rawbR.le (rawPhysical ⟨i.1.1.1.1, i.2⟩ z hz)"
                  prove `hgeometry "fun i ↦ rawGeometry ⟨i.1.1.1.1, i.2⟩"
                  prove `hP "fun i ↦ (rawCover.2.2.2.2.1 i.1.1.1.1 i.2).1"
                  prove `hΩ "fun i ↦ (rawTransport ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.1"
                  prove `hK "fun _ ↦ isCompact_closedBall _ _"
                  prove `hKΩ "fun i ↦ (rawTransport ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.1"
                  prove `hRc "fun i ↦ (rawPositive ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.1"
                  prove `hB "fun i ↦ (rawTransport ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.1.le"
                  prove `hτ "fun i ↦ (rawPositive ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.1"
                  prove `hbuffer "fun i ↦ (rawTransport ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.2.2.2.1"
                  prove `hτeq "fun i ↦ (rawTransport ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.2.2.2.2.1"
                  prove `hKFU "fun i ↦ (frameBall_subset_of_stateDomain (sourceFamily i).data.localReference (rawPhysical ⟨i.1.1.1.1, i.2⟩)).trans (ball_subset_ball rawbR.le)"
                  prove `hΩpatch "by intro i z hz; obtain ⟨⟨hT, hK⟩, hP⟩ := (rawTransport ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.2.1 hz; exact ⟨⟨closedBall_subset_ball rawbR (interior_subset hK), hT⟩, hP⟩"
                  prove `hx "fun i ↦ (rawTransport ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.2.2.1"
                  prove `hσ "scaleProof.1"
                  prove `hσone "scaleProof.2.trans sourceUnitCap"
                  prove `hRwork "rawbPos.trans rawbR"
                  prove `hworkChart "lt_of_lt_of_eq rawChart (congrArg LocalDomain.chartRadius referenceDomain).symm"
                  prove `hUwork "Subset.rfl"
                  prove `hR "fun i ↦ (rawPositive ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.1"
                  prove `hMc "fun i ↦ (rawProduct ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).1"
                  prove `hforward "fun i F current ↦ ((rawProduct ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.2.2.2.2.2.2.2.2 F (sourceRow i) (sourceCol i) current).1"
                  prove `hrr "fun i ↦ (selectedOuter i).2.2.1"
                  prove `haa "fun i ↦ (selectedOuter i).2.2.2.1"
                  prove `har "fun i ↦ (selectedOuter i).2.2.2.2.1"
                  prove `hframeSource "fun i ↦ (selectedCurrent scale ⟨scaleProof.1, scaleProof.2.trans sourceDensityCap⟩ i).choose_spec.2.2.2.2.2.1"
                  prove `hselected "by intro i F hF hi hrank hlow hclose; obtain ⟨_, hspectral, hcur, _⟩ := selectedGeometry i F hF hi hrank hlow hclose; obtain ⟨hspec, houtput, hrange, hhalf, hjac, hpunct, hshell, hupper⟩ := hspectral; obtain ⟨hdom, _, _, hnormalizedRange, _, _, _, _, _, _, _, hmask, _⟩ := hcur; exact ⟨hspec, hdom, hnormalizedRange, hhalf, hjac, fun z hz ↦ (hmask z hz).2.2.1, houtput, hrange, hpunct, hshell, hupper⟩"
                  prove `hV "fun _ ↦ isOpen_ball"
                  prove `hVP "fun i ↦ (rawProduct ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.2.2.2.2.1"
                  prove `hRT "fun i ↦ (rawProduct ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.1"
                  prove `hRU "fun i ↦ (rawProduct ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.1"
                  prove `hRtime "fun i ↦ (rawProduct ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.2.1"
                  prove `hflow "fun i ↦ (rawProduct ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.2.2.2.2.2.1"
                  prove `hlabelProduct "fun i ↦ (rawProduct ⟨i.1.1.1.1, i.2⟩ (selectedCell i.1.1 i.2)).2.2.2.2.2.2.2.2.2.2.1"
                  prove `haR "fun i ↦ (selectedOuter i).2.2.2.2.2"
                  prove `houter "fun i ↦ (selectedOuter i).2.1"
                  prove `hcoeff₀ "selectedCoeff scale ⟨scaleProof.1, scaleProof.2.trans sourceCoeffCap⟩"
                  for arg in args do
                    unless ← arg.mvarId!.isAssigned do
                      throwError "original history: unfilled original consumer argument {(← arg.mvarId!.getDecl).userName}"
                  let proof := (← instantiateMVars (mkAppN (mkConst consumer) args)).replaceFVars aliasVars aliasValues
                  let type ← inferType proof
                  if proof.hasMVar || type.hasMVar then
                    throwError "original history: unresolved final consumer application"
                  let statement ← addDefinition `Statement allParams (mkSort 0) type
                  let existsProof ← addTheorem `exists_history_coercivity allParams statement proof
                  let S ← addDefinition `Sgap allParams (mkConst `Real) (← mkAppM ``Classical.choose #[existsProof])
                  let sSpec ← mkAppM ``Classical.choose_spec #[existsProof]
                  let statementBody ← whnf statement
                  let sSpec ← addTheorem `threshold_spec allParams (statementBody.appArg!.beta #[S]) sSpec
                  discard <| addTheorem `hSgap allParams (← inferType (← mkAppM ``And.left #[sSpec]))
                    (← mkAppM ``And.left #[sSpec])
                  let coeffExists ← mkAppM ``And.right #[sSpec]
                  let coeffType ← whnf (← inferType coeffExists)
                  unless coeffType.isAppOfArity ``Exists 2 do
                    throwError "original history: coefficient history existential changed"
                  let coeff ← addDefinition `coeffHistory allParams coeffType.appFn!.appArg!
                    (← mkAppM ``Classical.choose #[coeffExists])
                  let coeffSpec ← mkAppM ``Classical.choose_spec #[coeffExists]
                  let coeffSpec ← addTheorem `coefficient_spec allParams
                    (coeffType.appArg!.beta #[coeff]) coeffSpec
                  let formula ← mkAppM ``And.left #[coeffSpec]
                  discard <| addTheorem `formula allParams (← inferType formula) formula
                  let continuation ← mkAppM ``And.right #[coeffSpec]
                  let continuation ← addTheorem `continuation allParams (← inferType continuation) continuation
                  forallBoundedTelescope (← inferType continuation) (some 5) fun densityParams _ => do
                    unless densityParams.size == 5 do
                      throwError "original history: expected density and its four original certificates"
                    let actualParams := sourceParams ++ densityParams
                    let sourceOperator := mkAppN (mkConst (base ++ `OriginalSourceGap.Vop)) actualParams
                    let sourceActions := mkAppN (mkConst (base ++ `OriginalSourceGap.actions)) actualParams
                    let tests ← forallBoundedTelescope (← inferType sourceActions) (some 1) fun indices _ => do
                      mkLambdaFVars indices (← mkAppM ``And.left #[mkAppN sourceActions indices])
                    let history := mkAppN (mkAppN continuation densityParams) #[sourceOperator, tests]
                    discard <| addTheorem `source_continuation (allParams ++ densityParams)
                      (← inferType history) history
                  unless ← isDefEq S (← mkAppM ``Classical.choose #[existsProof]) do
                    throwError "original history: threshold witness changed"
                  logInfo "kernel-checked all 134 original physical history-coercivity arguments and retained the complete history tail"

end JanetCartan.PhysicalNormalInverse.OriginalSourceApplication
