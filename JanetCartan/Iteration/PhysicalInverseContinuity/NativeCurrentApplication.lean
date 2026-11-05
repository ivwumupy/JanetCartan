module

public meta import JanetCartan.Iteration.PhysicalInverseContinuity.DatumApplication
public meta import JanetCartan.Iteration.PhysicalInverseContinuity.NativeApplication

/-! Actual application of the original signed current inverse to the measured
history comparison, preserving all its native output fields. The only leading
arguments at this layer are exactly those of `StrongCurrent.source_continuation`,
consumed at the parent by the original physical leading-chart producer. -/

public meta section
namespace JanetCartan.PhysicalInverseContinuity.NativeCurrentApplication
open Lean Meta Elab Command Term
open DatumApplication NativeApplication

private def src := `JanetCartan.PhysicalNormalInverse.StrongCurrent.source_continuation
private def rawNS := `JanetCartan.PhysicalInverseContinuity.StrongRaw

private def selectedSource (x : Array Expr) : Expr × Array Expr := Id.run do
  let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[x[0]!, x[1]!, x[20]!]
  let selected := x[:21].toArray.set! 20 capped
  return (capped, selected ++ #[x[21]!, x[23]!] ++ x[24:30].toArray)

private def chooseNative (name : Name) (params : Array Expr) (value : Expr) : TermElabM (Expr × Expr) := do
  let type ← whnf (← inferType value)
  unless type.isAppOfArity ``Exists 2 do throwError "actual native inverse: missing original choice {name}"
  let v ← store (`Native ++ name) params (← mkAppM ``Classical.choose #[value]) true
  let spec ← store (`Native ++ name ++ `spec) params (← mkAppM ``Classical.choose_spec #[value]) false
    (some (type.appArg!.beta #[v]))
  return (v, spec)

private def rights (value : Expr) (n : Nat) : MetaM Expr := do
  let mut v := value
  for _ in [:n] do v ← mkAppM ``And.right #[v]
  return v

/-- Retain the **actual** prehistory constants and threshold of the complete
original current inverse, without changing its leading budgets, source
scale, or the order of any of its geometric fields. -/
elab "prepare_actual_native_measured_inverse" : command => liftTermElabM do
  let info ← getConstInfo src
  forallBoundedTelescope info.type (some 33) fun x _ => do
    unless x.size == 33 do throwError "native source: expected original30 and three actual leading budgets"
    let source := mkAppN (mkConst src) x
    let (_, pinv) ← chooseNative `Cinv x source
    let (_, padj) ← chooseNative `Cadj x pinv
    let (_, ppair) ← chooseNative `Cpair x padj
    let (_, pzero) ← chooseNative `Czero x ppair
    let hCadj ← mkAppM ``And.left #[← rights pzero 1]
    let hCzero ← mkAppM ``And.left #[← rights pzero 3]
    discard <| store `Native.hCadj x hCadj
    discard <| store `Native.hCzero x hCzero
    let (_, pS) ← chooseNative `inverseFrequency x (← rights pzero 4)
    discard <| store `Native.inverse_frequency_ge_two x (← mkAppM ``And.left #[pS])
    discard <| store `Native.inverse_continuation x (← mkAppM ``And.right #[pS])
    logInfo "retained the actual prehistory adjoint and zero-density high constants from the complete current inverse"

/-- Instantiate the measured comparison on the actual zero-density `Vop` and
**all** the native gap, domain membership, adjoint and high output clauses of
`StrongCurrent.source_continuation`. The Vop is returned with its entire
original specification and the measured raw difference. At this level only
the original leading-cell/solution inputs of that theorem remain to the
geometric parent; there is no input requiring a current inverse estimate. -/
elab "join_actual_native_measured_inverse" : command => liftTermElabM do
  let info ← getConstInfo src
  forallBoundedTelescope info.type (some 33) fun x _ => do
    let (_, source) := selectedSource x
    let fixed := source[:23].toArray
    let src0 := ((← getConstInfo (rawNS ++ `referenceCarrier)).value! (allowOpaque := true)).beta fixed
    unless src0.isAppOfArity `JanetCartan.PhysicalNormalInverse.StrongSourceGap.Vop 28 do
      throwError "actual native: expected original zero-density source proof"
    let zeroDensity := src0.getAppArgs[23:].toArray
    let native (name : Name) := mkAppN (mkConst (datumNS ++ `Native ++ name)) x
    let maskStage := mkAppN (mkConst (datumNS ++ `reference)) fixed
    forallBoundedTelescope (← inferType maskStage) (some 6) fun masks _ => do
      let beginning := source ++ masks
      let measured (field : Name) := mkAppN (mkConst (datumNS ++ `History ++ field)) beginning
      forallBoundedTelescope (← inferType (measured `S)) (some 2) fun budgets _ => do
        let m := budgets[0]!
        let s := mkApp (mkConst ``Nat.succ) m
        let costs := #[mkApp (native `Cadj) (mkNatLit 1), mkApp (native `Czero) s,
          mkApp (native `hCadj) (mkNatLit 1), mkApp (native `hCzero) s]
        let atCosts := mkAppN (measured `S) (budgets ++ costs)
        forallBoundedTelescope (← inferType atCosts) (some 2) fun acc _ => do
          let full := x ++ masks ++ budgets ++ acc
          let terms := budgets ++ costs ++ acc
          let measuredAt (field : Name) := mkAppN (measured field) terms
          let Sraw := measuredAt `S
          let Sinv := native `inverseFrequency
          let S ← store `Native.S full (← mkAppM ``max #[Sraw, Sinv]) true
          let rawLe ← mkAppM `le_max_left #[Sraw, Sinv]
          let nativeLe ← mkAppM `le_max_right #[Sraw, Sinv]
          let hS ← store `Native.hS full (← mkAppM `le_trans #[measuredAt `hS, rawLe])
          let actual := native `inverse_continuation
          let proof ← forallBoundedTelescope (← inferType actual) (some 1) fun r _ => do
            let R₀ := r[0]!
            withLocalDeclD `hReached (← mkAppM ``LE.le #[S, R₀]) fun hReached => do
              let h1 ← mkAppM `le_trans #[rawLe, hReached]
              let h2 ← mkAppM `le_trans #[nativeLe, hReached]
              let history := mkAppN actual #[R₀, h2]
              let raw := mkAppN (measuredAt `continuation) #[R₀, h1]
              let result ← forallBoundedTelescope (← inferType history) (some 14) fun z _ => do
                unless z.size == 14 do throwError "current inverse: original history, leading data or coefficient arguments changed"
                let actualRows := mkAppN history (z ++ zeroDensity)
                let transfer := mkAppN raw (z[:5].toArray ++ #[z[12]!, z[13]!])
                let out ← joinNativeZero transfer actualRows s
                mkLambdaFVars z (← instantiateMVars out)
              mkLambdaFVars #[R₀, hReached] result
          let cont ← store `Native.continuation full proof
          let bundle ← mkAppM ``And.intro #[hS, cont]
          discard <| store `native_measured_history_raw_tolerance full bundle
          logInfo "instantiated every native current inverse clause on the identical zero-density row; only original leading inputs remain"

end JanetCartan.PhysicalInverseContinuity.NativeCurrentApplication
end
