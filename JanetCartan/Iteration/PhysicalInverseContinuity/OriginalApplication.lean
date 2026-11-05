module

public meta import JanetCartan.Iteration.PhysicalInverseContinuity.DatumApplication
public meta import JanetCartan.Iteration.PhysicalInverseContinuity.NativeApplication

/-! The final fixed admission-grade comparison consumes the actual original
leading geometry and inverse. It constructs the coefficient from the same
physical source family, applies the unchanged native inverse at zero density,
and retains its entire continuation for the later positive density. -/

public meta section
namespace JanetCartan.PhysicalInverseContinuity.OriginalApplication
open Lean Meta Elab Command Term
open DatumApplication NativeApplication

private def originalNS := `JanetCartan.PhysicalInitialization.OriginalCurrent
private def sourceNS := `JanetCartan.PhysicalNormalInverse.StrongSource
private def congruenceNS := `JanetCartan.PhysicalInverseContinuity.StrongRaw

private def actualSource (x : Array Expr) : Array Expr := Id.run do
  let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[x[0]!, x[1]!, x[20]!]
  return (x[:21].toArray.set! 20 capped) ++ #[x[21]!, x[23]!] ++ x[24:30].toArray

private def applyField (ns name : Name) (params : Array Expr) := mkAppN (mkConst (ns ++ name)) params

/-- `app:ch_background:prop:bg-current`: no leading chart, coefficient,
solution, carrier, inverse, measured error or mean regularity is an input.
The positive branch is kept on the very same current and geometric coefficient.
The Sobolev grade is the exact `κ + (3 + (n−1)) + 2` used by admission, with
`κ` a *fixed* finite order, not future perturbation/iteration accuracy. -/
elab "apply_original_leading_measured_raw_admission" : command => liftTermElabM do
  let info ← getConstInfo (originalNS ++ `continuation)
  forallBoundedTelescope info.type (some 31) fun params _ => do
    unless params.size == 31 do throwError "actual raw admission: expected original30 and numerical leading smallness"
    let source := actualSource params
    let fixed := source[:23].toArray
    let original (name : Name) := applyField originalNS name params
    let src (name : Name) := applyField sourceNS name source
    let src0 := ((← getConstInfo (congruenceNS ++ `referenceCarrier)).value! (allowOpaque := true)).beta fixed
    unless src0.isAppOfArity `JanetCartan.PhysicalNormalInverse.StrongSourceGap.Vop 28 do
      throwError "actual raw admission: expected the unchanged original zero-density proof"
    let zeroArgs := src0.getAppArgs[23:].toArray
    let scales := params[:22].toArray ++ #[params[23]!]
    let originalRow := applyField (congruenceNS ++ `History) `referenceRow fixed
    let Aref ← store `Original.referenceRow scales originalRow true
    let prescribed := applyField datumNS `reference fixed
    forallBoundedTelescope (← inferType prescribed) (some 6) fun fields _ => do
      let seedParams := scales ++ fields
      let seedDatum := mkAppN prescribed fields
      let eRef ← store `Original.reference seedParams seedDatum true
      let mem := applyField datumNS `reference_mem (fixed ++ fields)
      let memType := (← inferType mem).replace fun e => if e == seedDatum then some eRef else none
      discard <| store `Original.reference_mem seedParams mem false (some memType)
      withLocalDeclD `κ (mkConst ``Nat) fun κ => do
        let n := params[0]!
        let carriers := mkApp2 (mkConst ``Nat.add) (mkNatLit 3) (mkApp2 (mkConst ``Nat.sub) n (mkNatLit 1))
        let m := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) κ carriers) (mkNatLit 2)
        let s := mkApp (mkConst ``Nat.succ) m
        let atM := source ++ fields ++ #[m]
        let transfer (name : Name) := applyField (datumNS ++ `History) name atM
        forallBoundedTelescope (← inferType (transfer `S)) (some 1) fun reserve _ => do
          let costs := #[mkApp (original `Cadj) (mkNatLit 1), mkApp (original `Czero) s,
            mkApp (original `nonnegative1) (mkNatLit 1), mkApp (original `nonnegative3) s]
          let atBudget := mkAppN (transfer `S) (reserve ++ costs)
          forallBoundedTelescope (← inferType atBudget) (some 2) fun accuracy _ => do
            let full := params ++ fields ++ #[κ] ++ reserve ++ accuracy
            let stage (name : Name) := mkAppN (transfer name) (reserve ++ costs ++ accuracy)
            let Sraw := stage `S
            let Snative := original `S
            let Scoeff := src `Sgap
            let nativeAndCoeff ← mkAppM ``Max.max #[Snative, Scoeff]
            let aRaw ← mkAppM `le_max_left #[Sraw, nativeAndCoeff]
            let aOther ← mkAppM `le_max_right #[Sraw, nativeAndCoeff]
            let aNative ← mkAppM `le_trans #[← mkAppM `le_max_left #[Snative, Scoeff], aOther]
            let aCoeff ← mkAppM `le_trans #[← mkAppM `le_max_right #[Snative, Scoeff], aOther]
            let S ← store `Original.S full (← mkAppM ``Max.max #[Sraw, nativeAndCoeff]) true
            let hS ← store `Original.hS full (← mkAppM `le_trans #[stage `hS, aRaw])
            let hSraw ← store `Original.measured_threshold_le full aRaw
            let hSnative ← store `Original.current_threshold_le full aNative
            let hScoeff ← store `Original.coeff_threshold_le full aCoeff
            let continuation ← forallBoundedTelescope (← inferType (original `continuation)) (some 1) fun r _ => do
              let R₀ := r[0]!
              withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S, R₀]) fun hR => do
                let hRaw ← mkAppM `le_trans #[hSraw, hR]
                let hNative ← mkAppM `le_trans #[hSnative, hR]
                let hCoeff ← mkAppM `le_trans #[hScoeff, hR]
                let initialized := mkAppN (original `continuation) #[R₀, hNative]
                let out ← forallBoundedTelescope (← inferType initialized) (some 4) fun history _ => do
                  let fullHist := full ++ #[R₀, hR] ++ history
                  let nativeHist := #[R₀, hNative] ++ history
                  let coeffHist := #[R₀, hCoeff] ++ history
                  let cur ← store `Original.current fullHist (mkAppN (original `current) nativeHist) true
                  let coeff ← store `Original.coefficient fullHist (mkAppN (src `coeffHistory) coeffHist) true
                  let spec := mkAppN (src `formula) coeffHist
                  let formula ← store `Original.coefficient_formula fullHist (.proj ``And 0 spec)
                  let dens := mkAppN initialized (history ++ #[coeff, formula])
                  let dens ← store `Original.all_densities fullHist dens
                  let compare := mkAppN (stage `continuation) (#[R₀, hRaw] ++ history ++ #[cur, coeff, formula])
                  let family := mkAppN dens zeroArgs
                  let familyType ← whnf (← inferType family)
                  unless familyType.isAppOfArity ``Exists 2 do throwError "actual raw admission: missing original operator"
                  let W ← store `Original.Vzero fullHist (← mkAppM ``Classical.choose #[family]) true
                  let nativeSpec ← store `Original.Vzero_spec fullHist (← mkAppM ``Classical.choose_spec #[family]) false
                    (some (familyType.appArg!.beta #[W]))
                  let literal ← closeNativeZero compare W nativeSpec s
                  let t ← inferType literal
                  unless t.isAppOfArity ``LE.le 4 do throwError "actual raw admission: missing native fixed-grade inequality"
                  let diff := t.getAppArgs[2]!.appArg!
                  unless diff.isAppOfArity ``HSub.hSub 6 do throwError "actual raw admission: expected the two uncut raw corrections"
                  let curRaw := diff.getAppArgs[4]!
                  let seedRaw := diff.appArg!
                  let e := curRaw.appArg!
                  unless e.isAppOf `JanetCartan.PhysicalBackground.measuredSourceToL2 do
                    throwError "actual raw admission: expected the literal current measured physical residual"
                  let measured ← store `Original.measuredDatum fullHist e true
                  let curRawDef := curRaw.replace fun x => if x == e then some measured else none
                  let raw ← store `Original.rawCurrent fullHist curRawDef true
                  let seedRawDef := seedRaw.replace fun x =>
                    if x == originalRow then some Aref else if x == seedDatum then some eRef else none
                  let seed ← store `Original.rawSeed seedParams seedRawDef true
                  let prefixRights (p : Expr) (j : Nat) := (List.range j).foldl (fun z _ ↦ Expr.proj ``And 1 z) p
                  let row := Expr.proj ``And 1 nativeSpec
                  let pair := Expr.proj ``And 0 (prefixRights row 8)
                  let zero := prefixRights row 12
                  let eqType := (← whnf (← inferType zero)).bindingDomain!
                  unless eqType.isAppOfArity ``Eq 3 do throwError "actual raw admission: expected the original zero-density clause"
                  let vzero ← mkEqRefl eqType.getAppArgs[1]!
                  let seedEstimate := Expr.proj ``And 1 (applyField congruenceNS `reference_uncorrected fixed)
                  let sourceBounds ← withLocalDeclD `order (mkConst ``Nat) fun q => do
                    mkLambdaFVars #[q] (mkAppN seedEstimate #[q, eRef, mkApp mem q])
                  discard <| store `Original.rawSeed_preScale_estimate seedParams sourceBounds
                  let emem ← withLocalDeclD `order (mkConst ``Nat) fun q => do
                    mkLambdaFVars #[q] (mkAppN (mkConst `JanetCartan.PhysicalBackground.measuredSourceToL2_mem) (e.getAppArgs ++ #[q]))
                  let ememType := (← inferType emem).replace fun x => if x == e then some measured else none
                  let emem ← store `Original.measuredDatum_mem fullHist emem false (some ememType)
                  let rawMem ← withLocalDeclD `order (mkConst ``Nat) fun q => do
                    mkLambdaFVars #[q] (.proj ``And 0 (mkAppN pair #[q, e, mkApp emem q]))
                  let rawMemType := (← inferType rawMem).replace fun x => if x == curRaw then some raw else none
                  discard <| store `Original.rawCurrent_mem fullHist rawMem false (some rawMemType)
                  let zeroBudget ← withLocalDeclD `order (mkConst ``Nat) fun q => do
                    mkLambdaFVars #[q] (mkAppN zero #[vzero, q, e, mkApp emem q])
                  let zeroType := (← inferType zeroBudget).replace fun x =>
                    if x == curRaw then some raw else if x == e then some measured else none
                  discard <| store `Original.current_zero_estimate fullHist zeroBudget false (some zeroType)
                  let namedType := t.replace fun x =>
                    if x == curRaw then some raw else if x == seedRaw then some seed else none
                  let literal ← store `Original.literal_raw_half fullHist literal
                  discard <| store `Original.raw_half fullHist literal false (some namedType)
                  let bundle ← mkAppM ``And.intro #[nativeSpec, literal]
                  let bundleType ← inferType bundle
                  let pred ← withLocalDeclD `W (← inferType W) fun V =>
                    mkLambdaFVars #[V] (bundleType.replace fun x => if x == W then some V else none)
                  let result ← mkAppOptM ``Exists.intro #[none, some pred, some W, some bundle]
                  mkLambdaFVars history result
                mkLambdaFVars #[R₀, hR] out
            let actual ← store `Original.continuation full continuation
            discard <| store `original_current_admission_raw_half full (← mkAppM ``And.intro #[hS, actual])
    logInfo "actual original31 and literal admission grade: derived coefficient, selected leading charts, full original inverse, actual measured data and raw half-tolerance; all density branches retained"

end JanetCartan.PhysicalInverseContinuity.OriginalApplication
end
