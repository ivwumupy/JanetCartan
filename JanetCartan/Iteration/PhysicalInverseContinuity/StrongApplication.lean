module

public meta import Lean

/-!
# Specialization of the strong adjoint to the original fixed source

Read the already kernel-checked applied arguments of the exact prescribed
history theorem. Reuse its static arguments by binder name for the prescribed
adjoint theorem, then deliberately discard all six history/frequency order
parameters. Finally use the original zero-density action, inverse regularity
and uncorrected adjoint bounds at its fixed normal solution. Every exported
statement is checked by the kernel as a proof term, without additional
geometry, scale-order, density, or operator premises.
-/

public meta section
namespace JanetCartan.PhysicalInverseContinuity.StrongApplication
open Lean Meta Elab Command

private def parseTerm (s : String) : TermElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term s with
  | .ok stx => return stx
  | .error e => throwError "strong raw source: term parser: {e}"

private def termAt (s : String) (type : Expr) : TermElabM Expr := Term.withoutErrToSorry do
  let t ← Term.elabTermEnsuringType (← parseTerm s) type
  Term.synthesizeSyntheticMVarsNoPostponing
  let t ← instantiateMVars t
  if t.hasMVar then throwError "strong raw source: metavariables remain in {s}"
  return t

private def ns : Name := `JanetCartan.PhysicalInverseContinuity.StrongRaw

private def store (name : Name) (params : Array Expr) (value : Expr) (defn := false) : MetaM Expr := do
  let name := ns ++ name
  let type ← mkForallFVars params (← inferType value)
  let value ← mkLambdaFVars params value
  if type.hasFVar || value.hasFVar then
    let t := if type.hasFVar then type else value
    let some x := t.find? (·.isFVar) | throwError "strong raw source: open declaration {name}"
    throwError "strong raw source: unexpected dependence on {(← x.fvarId!.getDecl).userName} while closing {name}"
  if defn then
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  return mkAppN (mkConst name) params

/-- Match each real static selector to the cached application, not merely to
another witness of the same type. Stop before the first row continuation. -/
private def specializeStatic (cachedType consumerType : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let mut cache : Array (Name × Expr) := #[]
  let mut type := cachedType
  for arg in args do
    let .forallE n _ body _ := type | throwError "strong raw source: cached telescope ended before hcoeff₀"
    cache := cache.push (n.eraseMacroScopes, arg)
    if n == `hcoeff₀ then break
    type := body.instantiate1 arg
  type := consumerType
  let mut selected : Array Expr := #[]
  for _ in [:args.size] do
    let .forallE n _ body _ := type | throwError "strong raw source: unexpected prescribed adjoint telescope"
    let some (_, arg) := cache.find? (fun p ↦ p.1 == n.eraseMacroScopes) |
      throwError "strong raw source: missing exact static selector {n}"
    selected := selected.push arg
    if n == `hcoeff₀ then return selected
    type := body.instantiate1 arg
  throwError "strong raw source: missing end of static selectors"

/-- Reuse the selected static fields, the same actual positive source at
`v=0`, and the exact reference normal solution for arbitrary regular data. -/
elab "realize_strong_raw_fixed_source_adjoint" : command => liftTermElabM do
  let original := `JanetCartan.PhysicalNormalInverse.StrongSource.exists_history_coercivity
  let old := `JanetCartan.PhysicalNormalInverse.exists_prescribed_source_history_coercivity
  let new := `JanetCartan.PhysicalInverseContinuity.exists_prescribed_source_adjoint_tolerance
  let src := `JanetCartan.PhysicalNormalInverse.StrongSourceGap
  let info ← getConstInfo original
  unless info.levelParams.isEmpty do throwError "strong raw source: unexpected level parameters"
  forallBoundedTelescope info.type (some 29) fun params _ => do
    unless params.size == 29 do throwError "strong raw source: expected original 23 + six order arguments"
    let cached := (info.value! (allowOpaque := true)).beta params
    let args := cached.getAppArgs
    unless cached.getAppFn.isConstOf old && args.size == 134 do
      throwError "strong raw source: fixed construction no longer a direct application of the 134 original selectors"
    let selected₀ ← specializeStatic (← getConstInfo old).type (← getConstInfo new).type args
    let params₀ := params[:23].toArray
    let extra := params[23:].toArray
    let occurs := fun (t : Expr) ↦ t.hasAnyFVar (fun id ↦ extra.any (fun p ↦ p.fvarId! == id))
    let selected ← selected₀.mapM fun arg => do
      if !occurs arg then return arg
      let some name := arg.getAppFn.constName? | throwError "strong raw source: nonstatic composite selector"
      unless (`JanetCartan.PhysicalNormalInverse.StrongSource.Arguments).isPrefixOf name do
        throwError "strong raw source: nonstatic selector {name}"
      let value := ((← getConstInfo name).value! (allowOpaque := true)).beta arg.getAppArgs
      if occurs value then throwError "strong raw source: genuinely order-dependent geometric proof {name}"
      return value
    let static := mkAppN (mkConst new) selected
    let mut density : Array Expr := #[]
    let mut v := mkAppN (mkConst (src ++ `Vop)) params₀
    for s in #["fun _ _ ↦ (0 : ℝ)", "fun _ ↦ contDiffOn_const",
        "by intro i p hp; norm_num", "by intro i p hp; constructor <;> norm_num",
        "by intro i; change cNorm _ _ (0 : (Euclidean (n - 1) × Euclidean 3) → ℝ) ≤ 1; rw [cNorm_zero]; norm_num"] do
      let type ← whnf (← inferType v)
      let .forallE _ dom _ _ := type | throwError "strong raw source: five original density fields expected"
      let t ← termAt s dom
      density := density.push t
      v := mkApp v t
    let all := params₀ ++ density
    let V₀ ← store `referenceCarrier params₀ v true
    let actions := mkAppN (mkConst (src ++ `actions)) all
    let mut rest := mkAppN (mkConst (src ++ `operatorTail6)) all
    -- Invertibility, self-adjointness, both inverse identities, inverse norm,
    -- the row identity, the base estimate, and both elliptic clauses precede it.
    for _ in [:9] do rest ← mkAppM ``And.right #[rest]
    let inverseReg ← store `reference_inverse_regularity params₀ (← mkAppM ``And.left #[rest])
    let raw := mkApp (mkAppN (mkConst (src ++ `reference_uncorrected_raw)) all) (← mkEqRefl density[0]!)
    let raw ← store `reference_uncorrected params₀ raw
    let byV := mkApp static V₀
    let type ← whnf (← inferType byV)
    let .forallE _ dom _ _ := type | throwError "strong raw source: missing same carrier adjoint action"
    let haction ← withLetDecl `actualActions (← inferType actions) actions fun a => do
      let t ← termAt "by intro i y; unfold StrongRaw.referenceCarrier; simpa only [positiveDensityAmplitude_zero] using (((actualActions i).2 y).2)" dom
      return t.replaceFVar a actions
    let haction ← store `reference_adjoint_action params₀ haction
    let byAction := mkApp byV haction
    let atOne := mkApp inverseReg (mkNatLit 1)
    forallBoundedTelescope (← inferType atOne) (some 2) fun input _ => do
      unless input.size == 2 do throwError "strong raw source: expected e₀ and its exact level-one membership"
      let hw ← mkAppM ``And.left #[mkAppN atOne input]
      let w := (← inferType hw).appArg!
      let adj ← mkAppM ``And.left #[raw]
      let raw₀ ← mkAppM ``And.left #[mkAppN adj #[mkNatLit 1, w, hw]]
      let proof := mkAppN byAction #[w, hw, raw₀]
      discard <| store `exists_source_adjoint_tolerance (params₀ ++ input) proof
      logInfo m!"checked {selected.size} literal retained static selectors; original23 only, v=0, wref=(A₀A₀*)⁻¹ e₀; no history, reference regularity, or carrier-action premise"

end JanetCartan.PhysicalInverseContinuity.StrongApplication
