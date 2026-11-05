module

public import Mathlib.Basic.Real.Basic
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Actual native38 ordinary residual costs, with no new current or analytic
success premise. Every static/current input of the native cost producer is
closed; only the literal letter and independent adjoint/sign indices remain. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalWordOrdinaryTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalWordOrdinary
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def current := regular ++ `Current
private def pdo := `JanetCartan.PhysicalPrimary.OriginalPdoProfiles
private def symbols := `JanetCartan.PhysicalPrimary.OriginalRetardedSymbols
private def words := `JanetCartan.RegularSector.FiniteResidual.FiniteIdentity

private def normalizeType (type : Expr) : MetaM Expr := do
  let type ← Core.betaReduce type
  transform type
    (pre := fun expr => do
      if expr.isAppOf (current ++ `W₁) && expr.getAppArgs.size >= 38 then
        let some body := (← getConstInfo (current ++ `W₁)).value?
          | throwError "original ordinary: missing actual W1 abbreviation"
        return .visit (body.beta expr.getAppArgs)
      return .continue)
    (post := fun expr => do
      let args := expr.getAppArgs
      let nativeNat := args.size > 0 && args[0]! == mkConst ``Nat
      if (nativeNat && (expr.isAppOf ``HAdd.hAdd || expr.isAppOf ``HSub.hSub ||
          expr.isAppOf ``OfNat.ofNat)) || expr.isAppOf ``Nat.add || expr.isAppOf ``Nat.sub then
        let reduced ← whnf expr
        if reduced != expr then return .visit reduced
      return .continue)

private def checked (proof : Expr) (args : Array Expr) : MetaM Expr := do
  let mut result := proof
  let mut type ← inferType proof
  for arg in args do
    let exposed ← whnf type
    let .forallE name dom body _ := exposed | throwError "original ordinary application ended early"
    unless ← isDefEq (← normalizeType (← inferType arg)) (← normalizeType dom) do
      throwError "original ordinary actual input mismatch at {name}"
    result := mkApp result arg
    type := body.instantiate1 arg
  return result

private def byName (name : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec options (type : Expr) : Array (Option Expr) :=
    match type with
    | .forallE n _ body _ =>
      #[(known.find? (fun entry => entry.1 == n)).map Prod.snd] ++ options body
    | .mdata _ body => options body
    | _ => #[]
  mkAppOptM name (options (← getConstInfo name).type)

private def smoothOn (domain proof : Expr) : MetaM Expr := do
  let name := `ContDiff.contDiffOn
  let rec options (type : Expr) : Array (Option Expr) :=
    match type with
    | .forallE n _ body _ =>
      #[if n == `s then some domain else if n == `h then some proof else none] ++ options body
    | .mdata _ body => options body
    | _ => #[]
  mkAppOptM name (options (← getConstInfo name).type)

private partial def applyMap (known : Array (Name × Expr))
    (finish : Array Expr → Expr → MetaM Unit) (proof type : Expr)
    (retained : Array Expr := #[]) (count : Nat := 0) : MetaM Unit := do
  match type with
  | .mdata _ body => applyMap known finish proof body retained count
  | .letE _ _ value body _ => applyMap known finish proof (body.instantiate1 value) retained count
  | .forallE name dom body bi =>
    if let some (_,value) := known.find? (fun item => item.1 == name) then
      unless ← isDefEq (← normalizeType (← inferType value)) (← normalizeType dom) do
        throwError "original ordinary fixed/current input {name} has the wrong type"
      applyMap known finish (mkApp proof value) (body.instantiate1 value) retained (count+1)
    else
      unless name == `a || name == `backward do
        throwError "original ordinary unclosed native analytic/static input {name}"
      withLocalDecl name bi dom fun value =>
        applyMap known finish (mkApp proof value) (body.instantiate1 value) (retained.push value) count
  | _ =>
    unless type.isAppOfArity ``And 2 && retained.size == 2 do
      throwError "original ordinary: changed paired/real/signed native result"
    finish retained proof
    logInfo m!"actual ordinary native cost: {count} fixed/current inputs closed; only literal letter and independent backward orientation retained"

private def operatorOfUnitCost (proof : Expr) : MetaM Expr := do
  let type ← Core.betaReduce (← zetaReduce (← inferType proof))
  unless type.isAppOf `JanetCartan.ResponseTransfer.HasPolynomialSobolevCost do
    throwError "original ordinary: expected the exact polynomial cost conclusion"
  let family := type.getAppArgs.back!
  let body ← Core.betaReduce (← zetaReduce (mkApp family (mkConst ``Unit.unit)))
  let some localOperator := body.find? (fun e =>
      e.isAppOfArity `JanetCartan.RegularSector.Characteristic.RetardedLocalization.localRetardedOperator 6)
    | throwError "original ordinary: native singleton cost lost its literal local complex operator"
  unless ← isDefEq (.proj `ContinuousLinearMap 0 localOperator) body do
    throwError "original ordinary: native local operator is not the whole singleton cost factor"
  return localOperator.getAppArgs[5]!

private def bodyAt (name : Name) (params : Array Expr) : MetaM Expr := do
  let some body := (← getConstInfo name).value? | throwError "missing actual original body {name}"
  return body.beta params

elab "apply_original_ordinary_residual_letters" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `normalized_solver)).type (some 38) fun params _ => do
    unless params.size == 38 do throwError "original ordinary: expected exact native current38"
    let fixed := params[:23].toArray
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let cur (name : Name) := mkAppN (mkConst (current ++ name)) params
    let d := params[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let hn := params[1]!
    let original := #[n] ++ params[1:21].toArray
    let f := stat `f
    let fa := (← inferType f).getAppArgs
    unless fa.size == 7 do throwError "original ordinary: original mask family changed"
    let Ω := fa[1]!
    let center := fa[2]!
    let RQ := fa[3]!
    let hK := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalProtected.fact14) original
    let hr := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalProtected.fact2) original
    let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,hn,original[20]!]
    let hμ := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure) (original.set! 20 cap)
    let screened ← mkAppM (regular ++ `screened_pos) #[hn,hr,hμ]
    let core ← mkAppM (regular ++ `core_spec) #[hn,screened]
    let hRQΩ := Expr.proj ``And 0 (.proj ``And 1 (.proj ``And 1 core))
    let hΩ ← byName `Metric.isOpen_ball
      #[(`α,← inferType center),(`x,center),(`ε,Ω.appArg!)]
    let KQ ← mkAppM `Metric.closedBall #[center,RQ]
    let hKQ ← mkAppM `ProperSpace.isCompact_closedBall #[center,RQ]
    let low ← checked (cur `fact2) #[KQ,hKQ]
    let algebraicLow ← mkAppM (ns ++ `algebraic_low_bounds)
      #[KQ,cur `Q,cur `B,.proj ``And 0 low,.proj ``And 0 (.proj ``And 1 low)]
    let hQon ← smoothOn Ω (cur `hQ)
    let hBon ← smoothOn Ω (cur `hB)
    let hmap ← mkAppM `Set.MapsTo.mono_left #[cur `fact0,← mkAppM `Set.subset_univ #[Ω]]
    let qprofile ← mkAppM (ns ++ `unit_coefficient_profile) #[KQ,cur `Q]
    let bprofile ← mkAppM (ns ++ `unit_coefficient_profile) #[KQ,cur `B]
    let profile (field : Expr) : MetaM Expr := withLocalDeclD `m (mkConst ``Nat) fun m => do
      mkLambdaFVars #[m] (← mkAppM `JanetCartan.cNorm #[KQ,m,field])
    let AQ ← profile (cur `Q)
    let AB ← profile (cur `B)
    let realOne ← mkNumeral (mkConst ``Real) 1
    let hOne ← mkAppM `le_refl #[realOne]
    let natOne := mkNatLit 1
    let hNatOne ← mkAppM `le_refl #[natOne]
    let fin2 := mkApp (mkConst ``Fin) (mkNatLit 2)
    let one ← mkNumeral fin2 1
    let op1 := mkApp (cur `Op) one
    let base1 := mkApp (stat `base) one
    let cost1 := mkApp (stat `cost) one
    let hcost ← forallBoundedTelescope (← inferType (mkApp (stat `fact27) one)) (some 2) fun args _ => do
      mkLambdaFVars args (← mkAppM `le_of_lt #[mkAppN (mkApp (stat `fact27) one) args])
    let bump (name : Name) : MetaM (Expr × Expr × Expr × Expr × Expr) := do
      let b := stat name
      let smooth ← mkAppM (ns ++ `bump_smooth) #[b]
      let smoothType ← inferType smooth
      unless smoothType.isAppOf `ContDiff do throwError "original ordinary: expected complete smooth bump proof"
      let value := smoothType.appArg!
      let compact ← byName `ContDiffBump.hasCompactSupport #[(`f,b)]
      let normBound ← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[b]
      let continuous ← mkAppM `ContDiff.continuous #[smooth]
      return (value,smooth,compact,normBound,continuous)
    let (χ₂,hχ₂,hcχ₂,hbχ₂,ctχ₂) ← bump `χ₂
    let (χ₃,hχ₃,hcχ₃,hbχ₃,ctχ₃) ← bump `χ₃
    let μUniv ← mkAppM `Set.subset_univ #[← mkAppM `tsupport #[χ₂]]
    let νUniv ← mkAppM `Set.subset_univ #[← mkAppM `tsupport #[χ₃]]
    let univ := mkApp (mkConst `Set.univ [.zero]) (← inferType center)
    let measurable ← synthInstance (mkApp (mkConst `MeasurableSpace [.zero]) (← inferType center))
    let hUniv ← byName `MeasurableSet.univ #[(`α,← inferType center),(`m,measurable)]
    forallBoundedTelescope (← inferType (cur `fact4)) (some 1) fun sectors _ => do
      let p := sectors[0]!
      let here := params.push p
      let lambdaP (value : Expr) := mkLambdaFVars #[p] value
      let hendpoint := mkAppN (mkConst (symbols ++ `endpoint_native)) here
      let hretarded := mkAppN (mkConst (symbols ++ `physical_residual_retarded_bounds)) here
      let ra := (← inferType hretarded).getAppArgs
      unless ra.size == 17 do throwError "original ordinary: retained physical retarded spine changed"
      let Ψ ← lambdaP ra[7]!
      let algebraic := mkAppN (mkConst (pdo ++ `algebraic_bounds)) (here.push one)
      let hnormal := Expr.proj ``And 0 algebraic
      let hjet := Expr.proj ``And 1 algebraic
      let normalArgs := (← inferType hnormal).getAppArgs
      let Ralg ← lambdaP normalArgs[normalArgs.size-2]!
      let Malg ← lambdaP normalArgs[normalArgs.size-1]!
      let C ← lambdaP (mkAppN (mkConst (pdo ++ `Dalgebraic)) fixed)
      let hC ← lambdaP (mkAppN (mkConst (pdo ++ `Dalgebraic_nonneg)) fixed)
      let allNormal ← lambdaP hnormal
      let allJets ← lambdaP hjet
      let raw (a : Expr) := mkAppM (words ++ `selectedFullPairedResidualTerm)
        #[f,hK,stat `L,cur `Q,cur `B,cur `W₁,stat `output,cur `ho,cur `hob,cur `hib,op1,a]
      let measured (operator : Expr) := mkAppM `JanetCartan.RegularSector.FiniteAssembly.measuredOperator
        #[χ₂,χ₃,ctχ₂,ctχ₃,hbχ₂,hbχ₃,operator]
      withLocalDeclD `i (mkConst ``Unit) fun i => do
        let single (value : Expr) := mkLambdaFVars #[i] value
        let unitScale ← single realOne
        let known : Array (Name × Expr) := #[
          (`d,d),(`ι,mkConst ``Unit),(`Ω,Ω),(`x,center),(`RQ,RQ),(`M,fa[6]!),(`A₀,fa[4]!),(`K,fa[5]!),
          (`f,f),(`hK,hK),(`hΩ,hΩ),(`hRQΩ,hRQΩ),(`threshold,stat `L),(`ht,stat `hL),
          (`output,stat `output),(`ho,stat `fact17),(`hoc,stat `fact19),(`hob,cur `hob),(`hos,stat `fact20),(`hib,cur `hib),
          (`Rbox,stat `Rbox),(`Ralg,Ralg),(`Malg,Malg),(`base,base1),(`D,stat `Dpdo),
          (`Dgain,stat `Dgain),(`Gain,stat `Gain),(`cost,cost1),(`C,C),(`AQ,AQ),(`AB,AB),
          (`hDgain,stat `fact31),(`hGain,stat `fact32),(`hcost,hcost),(`hC,hC),
          (`hAQ,.proj ``And 0 qprofile),(`hAB,.proj ``And 0 bprofile),
          (`ρ,unitScale),(`L,unitScale),(`hL,← single hOne),(`hLρ,← single hOne),(`Rstar,natOne),(`hRstar,hNatOne),
          (`Q,← single (cur `Q)),(`B,← single (cur `B)),(`hQ,← single hQon),(`hB,← single hBon),
          (`hmap,← single hmap),(`hQl,← single (.proj ``And 0 algebraicLow)),(`hBl,← single (.proj ``And 1 algebraicLow)),
          (`hQp,.proj ``And 1 qprofile),(`hBp,.proj ``And 1 bprofile),
          (`W₁,← single (cur `W₁)),(`T,← single op1),(`Ψ,← single Ψ),
          (`χout,stat `χout),(`χsource,stat `χsource),(`hs,stat `hs),
          (`hendpoint,← single (← lambdaP hendpoint)),(`hretarded,← single (← lambdaP hretarded)),
          (`hnormal,← single allNormal),(`hjets,← single allJets),
          (`μ,χ₂),(`ν,χ₃),(`hμ,hχ₂),(`hν,hχ₃),(`hμc,hcχ₂),(`hνc,hcχ₃),(`hμb,hbχ₂),(`hνb,hbχ₃),
          (`U,univ),(`hU,hUniv),(`hνU,νUniv),(`hμU,μUniv)]
        let native := words ++ `selectedFullPairedResidualTerm_measured_hasPolynomialRestrictionCost_with_signed
        let info ← getConstInfo native
        unless info.levelParams.length == 1 do throwError "original ordinary: native universe changed"
        let application := mkConst native [.zero]
        applyMap known (fun rest proof => do
          let all := params ++ rest
          discard <| store (ns ++ `measured_cost) all proof
          let a := rest[0]!
          let rawValue ← raw a
          let measuredValue ← measured rawValue
          let complexCost := Expr.proj ``And 0 proof
          let directed ← operatorOfUnitCost complexCost
          let ordinary ← mkAppM (ns ++ `ordinary_from_unit_cost) #[directed,complexCost]
          discard <| store (ns ++ `ordinary) all ordinary
          let rawTerm ← store (ns ++ `raw) (params.push a) rawValue true
          discard <| store (ns ++ `measured) (params.push a) measuredValue true
          let signedProof := Expr.proj ``And 1 (.proj ``And 1 proof)
          withLocalDeclD `reflected (mkConst ``Bool) fun reflected => do
            let signedCost := mkApp signedProof reflected
            let directed ← operatorOfUnitCost signedCost
            let result ← mkAppM (ns ++ `ordinary_from_unit_cost) #[directed,signedCost]
            discard <| store (ns ++ `ordinary_signed) (all.push reflected) result
          let allRaw ← mkLambdaFVars #[a] rawTerm
          let sum ← mkAppM (words ++ `selectedFullResidual_eq_sum_paired_terms)
            #[f,hK,stat `L,cur `Q,cur `B,cur `W₁,stat `output,cur `ho,cur `hob,cur `hib,
              stat `fact20,Ralg,Malg,allNormal,op1]
          let sum ← store (ns ++ `paired_sum) params sum
          let sumType ← whnf (← inferType sum)
          let rawResidual := sumType.getAppArgs[1]!
          let measuredSum ← mkAppM (ns ++ `measured_sum_of_eq)
            #[χ₂,χ₃,ctχ₂,ctχ₃,hbχ₂,hbχ₃,allRaw,rawResidual,sum]
          discard <| store (ns ++ `measured_sum) params measuredSum
          let rawR ← bodyAt (current ++ `R) params
          unless rawR.isAppOfArity `JanetCartan.ArbitraryAccuracy.ResidualLocalization.localRealCompression 6 do
            throwError "original ordinary: current residual local-domain body changed"
          let hW := rawR.getAppArgs[3]!
          let W := rawR.getAppArgs[2]!
          let allMeasured ← mkLambdaFVars #[a] measuredValue
          let measuredResidual ← measured rawResidual
          let localSum ← mkAppM (ns ++ `local_complex_sum_of_eq)
            #[hW,W,allMeasured,measuredResidual,measuredSum]
          discard <| store (ns ++ `local_complex_sum) params localSum
        ) application (info.type.instantiateLevelParams info.levelParams [.zero])
  logInfo "actual original current38: all four paired letters and every independent reflected/adjoint orientation have ordinary global Fourier-Sobolev bounds at singleton scale one; the SAME measured complex residual is exactly their finite sum, before and after local complex restriction"

end JanetCartan.PhysicalPrimary.OriginalWordOrdinaryTemplate
