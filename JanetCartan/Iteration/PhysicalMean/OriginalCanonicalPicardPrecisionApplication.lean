module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourcePicardProfiles
public import JanetCartan.Iteration.PhysicalMean.FixedPicardCoefficientSelection
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# Original fixed operators with an explicit complete-source DATA argument

The frozen background-quadrature run is only a test case, not the full forcing
in paper-v2 5404–5416. This additive interface keeps E, Q, the global inverse,
ONE original shift and fixed prefix, and accepts g : SmoothResidual n as DATA.
No successful-source condition is imposed. The parent must supply the actual
complete source and its forcing profile. Generic input kernels accept the
resulting r directly; no background-only input publisher is cloned.

Consumers: the true `app:ch_mean_pairs:prop:mean-iteration`, Step5, and86's
source-parametric whole-wave callback.
-/

public noncomputable section
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean
open CurrentMean
/-- A small scalar consequence used without expensive Meta normalization of
the original polynomial. The middle bound is already deduced from primitives. -/
theorem originalFixedForcing_cNorm_of_middle {n : ℕ} (u : SmoothResidual n) (M ε : ℝ)
    (hm : residualSobolevSeminorm n (n/2+2) u ≤ M)
    (hnumeric : (2*fourierInterpolationConstant n 1 (n/2+2))*M ≤ ε) :
    cNorm (fundamentalCell n) 1 (periodicLift (fun x ↦ u.val x ())) ≤ ε := by
  exact (cNorm_residualRepresentative_le_middle u).trans
    ((mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num)
      (fourierInterpolationConstant_nonneg _ _ _))).trans hnumeric)
end JanetCartan.PhysicalMean
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalPicardPrecisionApplication
open Lean Meta Elab Command
open OriginalCanonicalPicardApplication (withActualSelectedPicardData applyKnownUntil)
private def root := `JanetCartan.PhysicalMean.OriginalCanonicalSource
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def get (known : Array (Name × Expr)) (name : Name) : MetaM Expr := do
  let some (_,e) := known.find? (fun pair => pair.1 == name)
    | throwError "original fixed-forcing precision missing actual {name}"
  return e
private def replace (known : Array (Name × Expr)) (name : Name) (value : Expr) :=
  known.map (fun pair => if pair.1 == name then (name,value) else pair)
private def save (name : Name) (params : Array Expr) (value target : Expr)
    (isDefinition := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for ex in #[type,value] do
    let used := ex.getUsedConstants
    let missing := used.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "fixed-forcing declaration missing {missing.toList}"
    for old in #[root ++ `iterate,root ++ `selected_iterate,
        `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing] do
      if used.contains old then throwError "background-only source escaped into {name}: {old}"
    if ex.hasFVar || ex.hasMVar || ex.hasLevelMVar || ex.hasLooseBVars || ex.hasSorry then
      throwError "fixed-forcing declaration has an unclosed parameter"
  let name := root ++ name
  if isDefinition then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original selected E/Q/global inverse and fixed prefix, with an explicit forcing DATA argument. No background-only forcing substitution and no successful-source premise. Static constants precede history (app:ch_mean_pairs:prop:mean-iteration, Step5)."
private partial def finalInputs (remaining : Nat) (type : Expr) (xs : Array Expr)
    (next : Array Expr → MetaM Unit) : MetaM Unit := do
  match type.consumeMData with
  | .letE _ _ value body _ => finalInputs remaining (body.instantiate1 value) xs next
  | .forallE label domain body bi =>
    if remaining == 0 then next xs
    else withLocalDeclNoLocalInstanceUpdate label bi domain fun x =>
      finalInputs (remaining-1) (body.instantiate1 x) (xs.push x) next
  | _ => if remaining == 0 then next xs else throwError "fixed-forcing numerical boundary changed"
private def groupArgs (known : Array (Name × Expr)) : MetaM (Array Expr) := do
  return #[← get known `Y, ← get known `originalAddCommGroup, ← get known `originalModule,
    ← get known `E, ← get known `Q, ← get known `g]

/-- Add only a source DATA parameter to the frozen original operator tuple. -/
def withActualSelectedForcingData
    (next : Array Expr → Array (Name × Expr) → MetaM Unit) : MetaM Unit :=
  withActualSelectedPicardData fun p known => do
    withLocalDeclNoLocalInstanceUpdate `forcing .default (← get known `Y) fun g =>
      next (p.push g) (replace known `g g)

elab "construct_original_fixed_forcing_source" : command => liftTermElabM do
  withActualSelectedForcingData fun p known => do
    let args ← groupArgs known
    withLocalDeclNoLocalInstanceUpdate `steps .default (mkConst ``Nat) fun steps => do
      let params := p.push steps
      let runValue := mkAppN (mkConst ``sourceIterate [.zero]) (args.push steps)
      save `selected_iterateWithForcing params runValue (← inferType runValue) true
      let run := app (root ++ `selected_iterateWithForcing) params
      let value := mkAppN (mkConst ``sourceResidual [.zero]) (args.push run)
      save `selected_residualWithForcing params value (← inferType value) true
      let proof := mkAppN (mkConst ``sourceResidual_eq_difference [.zero]) (args.push steps)
      let target := (← inferType proof).replace fun ex =>
        if ex.isAppOfArity ``sourceResidual 7 then some (app (root ++ `selected_residualWithForcing) params)
        else if ex.isAppOfArity ``sourceIterate 7 then
          some (app (root ++ `selected_iterateWithForcing) (p.push ex.getAppArgs.back!))
        else none
      save `selected_residualWithForcing_eq_difference params proof target
    let producer := ``sourceIterate_seminorm_profile
    let info ← getConstInfo producer
    let term := mkConst producer (info.levelParams.map (fun _ => .zero))
    applyKnownUntil `hquadratic term (← inferType term) known #[] fun proof extras => do
      unless extras.size == 9 do throwError "fixed-forcing profile primitive boundary changed"
      finalInputs 2 (← inferType proof) #[] fun orders => do
        let value := mkAppN proof orders
        let raw := mkAppN (mkConst ``sourceIterate [.zero]) (args.push orders[0]!)
        let actual := app (root ++ `selected_iterateWithForcing) (p.push orders[0]!)
        let target := (← inferType value).replace fun ex => if ex == raw then some actual else none
        unless target.getUsedConstants.contains (root ++ `selected_iterateWithForcing) do
          throwError "fixed-forcing profile lost its named source"
        let params := p[:44].toArray ++ extras[:6].toArray ++ p[44:].toArray ++
          extras[6:].toArray ++ orders
        save `selected_iterateWithForcing_profile_of_primitive_profiles params value target
  logInfo "fixed-forcing data53/profile63: SAME E/Q, ONE shift, fixed L; g is DATA, no background-only iterate/forcing leakage"

elab "construct_original_fixed_forcing_middle_precision" : command => liftTermElabM do
  withActualSelectedForcingData fun original known₀ => do
    let xs := original[:50].toArray
    let g := original[51]!
    let n ← get known₀ `n
    let hR ← get known₀ `hR
    let h01 ← mkAppOptM ``zero_lt_one #[some (mkConst ``Real),none,none,none,none,none]
    let hRp ← mkAppM ``lt_of_lt_of_le #[h01,hR]
    let hK ← mkAppM ``Real.rpow_pos_of_pos #[hRp,mkConst `JanetCartan.fineExponent]
    let K := (← inferType hK).getAppArgs[3]!
    let L := app `JanetCartan.RawInputPartition.cutoffCount #[K]
    let p := xs ++ #[L,g]
    let ξ := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift xs
    let trial := xs ++ #[ξ,L]
    let E := app (root ++ `linear) trial
    let Q := app (root ++ `quadratic) trial
    let some qbody := (← getConstInfo (root ++ `quadratic)).value?
      | throwError "fixed-forcing precision lost the fixed quadratic body"
    let rawQ := (mkAppN qbody trial).headBeta
    unless rawQ.isAppOf ``fixedSourceQuadratic do
      throwError "fixed-forcing precision changed the original quadratic polynomial"
    let commInfo ← getConstInfo ``fixedSourceQuadratic_comm
    let hQ := mkAppN (mkConst ``fixedSourceQuadratic_comm (commInfo.levelParams.map (fun _ => .zero)))
      rawQ.getAppArgs
    let half := app ``Nat.div #[n,mkNatLit 2]
    let hm₀ := app ``Nat.succ_pos #[app ``Nat.succ #[half]]
    let gaps := app ``source_iteration_fixed_gaps #[n]
    let hω := Expr.proj ``And 0 (Expr.proj ``And 1 gaps)
    let ω := (← inferType hω).getAppArgs[3]!
    let known := replace (replace known₀ `E E) `Q Q ++
      #[(`K,K),(`hK,hK),(`hQ,hQ),(`hm₀,hm₀),(`ω,ω)]
    let producer := ``sourceResidual_fixedCutoff_middle_le_with_coefficient
    let info ← getConstInfo producer
    let term := mkConst producer (info.levelParams.map (fun _ => .zero))
    applyKnownUntil `hlowQuadratic term (← inferType term) known #[] fun proof extras => do
      unless extras.size == 21 do throwError "fixed-forcing precision primitive boundary changed: {extras.size}"
      let names ← extras.mapM fun x => return (← getFVarLocalDecl x).userName
      let some index := names.idxOf? `N | throwError "fixed-forcing precision lost the finite step count"
      let steps := extras[index]!
      finalInputs 2 (← inferType proof) #[] fun numeric => do
        let value := mkAppN proof numeric
        let actual := app (root ++ `selected_residualWithForcing) (p.push steps)
        let target := (← inferType value).replace fun ex =>
          if ex.isAppOfArity ``sourceResidual 7 then some actual else none
        unless target.getUsedConstants.contains (root ++ `selected_residualWithForcing) do
          throwError "fixed-forcing middle precision lost the SAME named residual"
        let pureNames := #[`q,`N,`Cg,`CE,`CQ,`hCg,`hCE,`hCQ,`b,`c₀,`Cρ,`hb,`hc₀,`hCρ]
        let mut pure := #[]
        for name in pureNames do
          let some ix := names.idxOf? name | throwError "fixed-forcing precision lost static {name}"
          pure := pure.push extras[ix]!
        let mut dependent := #[]
        for i in [:extras.size] do
          if !pureNames.contains names[i]! then dependent := dependent.push extras[i]!
        let params := xs[:44].toArray ++ pure ++ xs[44:].toArray ++ #[g] ++ dependent ++ numeric
        save `selected_residualWithForcing_middle_le_of_primitive_profiles params value target
        logInfo "fixed-forcing middle74 checked: original omega and coefficient power retained"

elab "construct_original_fixed_forcing_cnorm_precision" : command => liftTermElabM do
  let middleName := root ++ `selected_residualWithForcing_middle_le_of_primitive_profiles
  finalInputs 74 (← getConstInfo middleName).type #[] fun params => do
    let mut target := (← getConstInfo middleName).type
    for param in params do
      let .forallE _ _ body _ := target.consumeMData
        | throwError "fixed-forcing C1 original static telescope changed"
      target := body.instantiate1 param
    unless target.isAppOfArity ``LE.le 4 do throwError "fixed-forcing middle inequality changed"
    let some actual := target.find? (·.isAppOfArity (root ++ `selected_residualWithForcing) 53)
      | throwError "fixed-forcing C1 lost the actual named residual"
    let n := app ``Nat.succ #[params[0]!]
    let upper := target.getAppArgs[3]!
    let R := app `JanetCartan.historyScale
      #[params[58]!,mkConst `JanetCartan.growthExponent,params[60]!]
    let middle := app middleName params
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Real) fun accuracy => do
      let negAccuracy ← mkAppM ``Neg.neg #[accuracy]
      let power ← mkAppM ``HPow.hPow #[R,negAccuracy]
      let arguments := #[n,actual,upper,power,middle]
      let afterMiddle := app ``originalFixedForcing_cNorm_of_middle arguments
      let mut helperType := (← getConstInfo ``originalFixedForcing_cNorm_of_middle).type
      for argument in arguments do
        let .forallE _ _ body _ := helperType.consumeMData
          | throwError "fixed-forcing C1 scalar helper telescope changed"
        helperType := body.instantiate1 argument
      let .forallE _ sufficient conclusion _ := helperType.consumeMData
        | throwError "fixed-forcing C1 numerical boundary changed"
      withLocalDeclNoLocalInstanceUpdate `numericalPrecision .default sufficient fun numerical => do
        let precise := mkApp afterMiddle numerical
        let all := params[:44].toArray ++ #[accuracy] ++ params[44:].toArray ++ #[numerical]
        save `selected_residualWithForcing_cNorm_le_of_primitive_profiles all precise
          (conclusion.instantiate1 numerical)
    logInfo "fixed-forcing C1 precision76 checked from saved middle74; complete source/primitive bounds remain parent obligations"

end JanetCartan.PhysicalMean.OriginalCanonicalPicardPrecisionApplication
end
