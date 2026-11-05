module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-!
# Literal selected leading-cell principal profiles

Consumer: the whole-outer-chi mean profile in `app:ch_background:prop:bg-current`.
No principal bound, smoothness of a successful solution, or replacement chart
is an input. This specializes the existing constant-initial profile to the
actual `CurrentLeading.Selected.current` and its exact retained leading data.
The profile constant and original whole-product graph close before history.
-/

public meta section
namespace JanetCartan.PhysicalBackground.NativeLeadingProfilesTemplate
open Lean Meta Elab Command Term
open NativeReferenceSourceTemplate (termWith)

private def targetNS := `JanetCartan.PhysicalBackground.NativeLeadingProfiles

private def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq actual target do
    throwError "native leading profiles: changed same-cell target {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params target)
  if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar ||
      value.hasLevelMVar || type.hasLevelMVar || value.hasSorry || type.hasSorry then
    throwError "native leading profiles: open or future-history dependence in {name}"
  let name := targetNS ++ name
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  pure (mkAppN (mkConst name) params)

private def component (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do proof ← mkAppM ``And.right #[proof]
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``And 2 then mkAppM ``And.left #[proof] else pure proof

/-- The SAME current cell supplies the principal profile, scalar null-field
smoothness and compatibility. The only new input is the numerical reserve
`rSource+14<=rStar`; it precedes the history in the exported profile ABI. -/
elab "realize_native_leading_profiles" : command => liftTermElabM do
  let leading := `JanetCartan.PhysicalInitialization.CurrentLeading
  let selected := leading ++ `Selected
  let cellNS := `JanetCartan.PhysicalPrimary.LeadingCell
  let currentInfo ← getConstInfo (selected ++ `current)
  forallBoundedTelescope currentInfo.type (some 38) fun all _ => do
    unless all.size == 38 do
      throwError "native leading profiles: expected fixed31/history6/native index"
    let fixed := all[:31].toArray
    let static := fixed.push all[37]!
    let current := mkAppN (mkConst (selected ++ `current)) all
    let currentBody := ((currentInfo.value! (allowOpaque := true)).beta all).headBeta
    unless currentBody.isAppOfArity (cellNS ++ `current) 36 do
      throwError "native leading profiles: changed actual leading current36"
    let args := currentBody.getAppArgs
    let hdata := args[34]!
    unless hdata.isAppOfArity (leading ++ `AtPatch.fact0) 38 do
      throwError "native leading profiles: current did not retain its actual AtPatch data"
    let patchArgs := hdata.getAppArgs
    let patch := patchArgs.back!
    let atPatch (name : Name) := mkAppN (mkConst (leading ++ name)) (fixed.push patch)
    let Amap := atPatch `Amap
    let E := atPatch `E
    logInfo "native leading: extracted unchanged cell36 and AtPatch budgets"
    unless ← isDefEq E args[26]! do
      throwError "native leading profiles: history-dependent or changed E budget"
    let hAmap := atPatch `fact1
    let hEpos := atPatch `fact3
    let hE ← termWith [(`hEpos, hEpos)] "fun s : ℕ ↦ (hEpos s).le"
    let Cvalue ← termWith [(`E, E), (`Amap, Amap)]
      "fun s : ℕ ↦ E s * (2 + Amap (s + 14))"
    let C ← store `C static Cvalue true
    discard <| store `C_pos static (← termWith
      [(`C, C), (`hEpos, hEpos), (`hAmap, hAmap)]
      "(by intro s; change 0 < _ * _; exact mul_pos (hEpos s) (by linarith [hAmap (s + 14)]) : ∀ s, 0 < C s)")
    let originalCell (name : Name) := mkAppN
      (mkConst (`JanetCartan.PhysicalSeed.OriginalBoundary ++ name))
      #[fixed[0]!, fixed[1]!, patch, args[35]!]
    let hProduct ← component (originalCell `density_product_geometry) 6
    let hGraphBall ← mkAppM `Set.MapsTo.mono_left
      #[← component (originalCell `carrier_cells) 2, hProduct]
    let graphType ← inferType hGraphBall
    unless graphType.isAppOfArity `Set.MapsTo 5 do
      throwError "native leading profiles: missing original product graph"
    let graphArgs := graphType.getAppArgs
    let ballArgs := graphArgs[4]!.getAppArgs
    unless graphArgs[4]!.isAppOfArity `Metric.ball 4 do
      throwError "native leading profiles: original graph target is not its comparison ball"
    let hClosed ← mkAppOptM `Metric.ball_subset_closedBall
      #[some graphArgs[1]!, none, some ballArgs[2]!, some ballArgs[3]!]
    let hGraph ← mkAppM `Set.MapsTo.mono_right #[hGraphBall, hClosed]
    let JfullValue := (← inferType hGraph).getAppArgs[4]!
    let Jfull ← store `Jfull static JfullValue true
    discard <| store `outer_product static graphArgs[3]! true
    discard <| store `graph static graphArgs[2]! true
    discard <| store `graph_into_full static hGraph
    let jArgs := JfullValue.getAppArgs
    discard <| store `Jfull_compact static
      (← mkAppM `ProperSpace.isCompact_closedBall #[jArgs[jArgs.size - 2]!, jArgs.back!])
    discard <| store `Jfull_radius_pos static (← component (originalCell `comparison_pos) 8)
    logInfo "native leading: retained static constant and original whole-product graph"
    discard <| store `current all current true
    discard <| store `geometry all (mkAppN (mkConst (selected ++ `geometry)) all)
    discard <| store `map all args[30]! true
    discard <| store `map_smooth all
      (mkAppN (mkConst (leading ++ `AtPatch.hF)) patchArgs)
    let sigma := fixed[21]!
    let hSigma ← mkAppM `le_of_lt #[← mkAppM ``And.left #[fixed[22]!]]
    let capNS := `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap
    let hSigmaOne ← mkAppM `le_trans
      #[← mkAppM ``And.right #[fixed[22]!], mkAppN (mkConst (capNS ++ `fact2)) fixed[:21].toArray]
    let hCscalarOne := mkAppN (mkConst (capNS ++ `fact5)) fixed[:21].toArray
    let hM ← termWith [(`hCscalarOne, hCscalarOne), (`hSigma, hSigma)]
      "by simpa only [mul_one] using mul_le_mul_of_nonneg_left hCscalarOne hSigma"
      (some (← mkAppM ``LE.le #[sigma, args[23]!]))
    let hm ← termWith [(`sigma, sigma), (`hSigma, hSigma)]
      ("by\n" ++
       "  have h : Real.sqrt (1 / 2 : ℝ) ≤ 1 := by\n" ++
       "    simpa using Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ≤ 1 by norm_num)\n" ++
       "  exact (mul_le_mul_of_nonneg_left h hSigma).trans_eq (mul_one sigma)")
      (some (← mkAppM ``LE.le #[args[24]!, sigma]))
    let hProfile := mkAppN (mkConst (leading ++ `AtPatch.continuation)) patchArgs
    discard <| store `map_profile all hProfile
    let scale := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[all[31]!, all[33]!]
    let hScale ← termWith [(`R0, all[31]!), (`stage, all[33]!),
        (`hThreshold, mkAppN (mkConst (leading ++ `fact0)) fixed), (`hReached, all[32]!)]
      "(JanetCartan.one_le_currentCoefficientScale (by linarith [hThreshold.trans hReached]) stage : 1 ≤ JanetCartan.currentCoefficientScale R0 stage)"
    logInfo "native leading: retained map profile and literal coefficient scale"
    withLocalDeclD `rSource (mkConst ``Nat) fun reserve => do
      let hReserveType ← termWith [(`rSource, reserve), (`rStar, fixed[26]!)]
        "rSource + 14 ≤ rStar"
      withLocalDeclD `hReserve hReserveType fun hReserve => do
        let producer := `JanetCartan.PhysicalBackground.retained_constant_initial_principal_profile
        let producerArgs := args ++ #[sigma, hSigma, hSigmaOne, hM, hm, Amap, hAmap, hE,
          fixed[26]!, reserve, hReserve, scale, hScale, hProfile]
        let proof := mkAppN (mkConst producer) producerArgs
        logInfo "native leading: applying constant-initial principal producer"
        let mut profileType ← inferType proof
        while profileType.isLet do
          profileType := profileType.letBody!.instantiate1 profileType.letValue!
        logInfo "native leading: principal type extracted"
        unless profileType.isAppOf `JanetCartan.HasDerivativeProfile do
          throwError "native leading profiles: changed constant-initial profile result"
        let pArgs := profileType.getAppArgs
        unless ← isDefEq pArgs[pArgs.size - 5]! Jfull do
          throwError "native leading profiles: full profile left the original graph target"
        logInfo "native leading: principal on same original comparison ball"
        unless ← isDefEq pArgs.back! C do
          throwError "native leading profiles: changed prehistory constant"
        let principal ← store `full_principal all pArgs[pArgs.size - 4]! true
        let target := mkAppN profileType.getAppFn
          (((pArgs.set! (pArgs.size - 5) Jfull).set! (pArgs.size - 4) principal).set! (pArgs.size - 1) C)
        discard <| store `profile (fixed ++ #[reserve, hReserve] ++ all[31:].toArray)
          proof false (some target)
        -- Reuse the same constant-initial solution already proved inside the
        -- shared adapter. Its expression must close WITHOUT reserve/history
        -- choices beyond the existing all38 parameters.
        let body := ((← getConstInfo producer).value! (allowOpaque := true)).beta producerArgs
        let body ← Core.betaReduce (← zetaReduce body)
        let some solution := body.find? (·.isAppOfArity (cellNS ++ `solution) 40) |
          throwError "native leading profiles: same constant solution not retained in producer body"
        if solution.hasLooseBVars then
          throwError "native leading profiles: solution extraction retained a bound proof-local"
        let initial := solution.getAppArgs[36]!
        let solution ← store `constant_solution all solution
        discard <| store `null_smooth all (.proj ``And 0 solution)
        discard <| store `constant_compatible all
          (mkAppN (mkConst (cellNS ++ `compatible)) (args.push initial))
  logInfo "same native leading principal: loss14, static constants/whole-product graph, literal scale, no analytic admission inputs"

end JanetCartan.PhysicalBackground.NativeLeadingProfilesTemplate
end
