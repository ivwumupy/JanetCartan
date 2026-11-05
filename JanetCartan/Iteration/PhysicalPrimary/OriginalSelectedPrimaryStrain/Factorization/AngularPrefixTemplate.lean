module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularData
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
/-! Exact original prefix transport, deduced independently from the unprefixed
raw differential statement. Its sole identity premise is discharged by the
native-to-actual AngularBridge in the final Angular module; the actual endpoint
adds no premise (main:eq:primary-strain; main:eq:lag-strain). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalPrimary.OriginalRawAngularActualApplication
open OriginalRawPrimaryRealizationApplication

elab "check_actual_original_raw_prefix " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "original raw prefix: unknown stage"
  actualTelescope (← getConstInfo actualG).type fun p _ => do
    if mode.getNat == 2 then
      let unprefixed := app (actual ++ `unprefixed_forward) p
      let proof := app (actual ++ `prefixed_forward_of_unprefixed) (p.push unprefixed)
      forallBoundedTelescope (← inferType proof) (some 4) fun tail _ => do
        unless tail.size == 4 do throwError "original raw prefix: original cut/input/point/chart tail changed"
        let all := p ++ tail
        publish `prefixed_forward all (mkAppN proof tail)
          (app (actual ++ `prefixed_forward_statement) all)
      return
    let (n,N,J,φ,m,A) ← sumData p
    let statement := app (actual ++ `unprefixed_forward_statement) p
    let initialType ← forallBoundedTelescope (← inferType statement) (some 3) fun tail _ => do
      unless tail.size == 3 do throwError "original raw prefix: unprefixed original tail changed"
      mkForallFVars tail (mkAppN statement tail)
    withLocalDeclD `hUnprefixed initialType fun base => do
      withLocalDeclD `cut (mkConst ``Nat) fun cut => do
        forallBoundedTelescope (← inferType base) (some 3) fun tail _ => do
          let w := tail[0]!
          let x := tail[1]!
          let rw ← mkAppM ``DFunLike.coe
            #[app `JanetCartan.RawInputPartition.refinedPrefix #[n,J,cut],w]
          let initial := mkAppN base (tail.set! 0 rw)
          let hp := app ``forwardSum_prefix #[n,N,J,φ,m,A,cut,w,x]
          let sourceType ← bodyAt
            (app (actual ++ `unprefixed_forward_statement) (p ++ tail.set! 0 rw))
          let hpType ← inferType hp
          unless sourceType.isAppOfArity ``Eq 3 && hpType.isAppOfArity ``Eq 3 do
            throwError "original raw prefix: original annular equations changed"
          let ia := sourceType.getAppArgs
          let both := mkAppN (mkConst ``Eq.trans sourceType.getAppFn.constLevels!)
            #[ia[0]!,ia[1]!,ia[2]!,hpType.getAppArgs[2]!,initial,hp]
          let oldwide := wideInput n J rw
          let eq := (← inferType both).getAppArgs
          let hwide := app ``wide_prefix_eq #[n,J,cut,w]
          let hwideType ← inferType hwide
          let hwa := hwideType.getAppArgs
          let context ← withLocalDeclD `v (← inferType oldwide) fun v =>
            mkLambdaFVars #[v] (eq[1]!.replace fun e => if e == oldwide then some v else none)
          let transfer ← mkAppM ``congrArg #[context,hwide]
          let transferType ← inferType transfer
          unless transferType.isAppOfArity ``Eq 3 do
            throwError "original raw prefix: original input transport changed"
          let ta := transferType.getAppArgs
          let proof := mkAppN (mkConst ``Eq.trans transferType.getAppFn.constLevels!)
            #[ta[0]!,ta[1]!,ta[2]!,eq[2]!,transfer,both]
          let proofType ← inferType proof
          unless proofType.getAppArgs[1]!.find? (· == hwa[1]!) |>.isSome do
            throwError "original raw prefix: same wide prefix disappeared"
          let all := p ++ #[cut] ++ tail
          if mode.getNat == 0 then
            publish `prefixed_forward_statement all proofType (mkSort .zero) true
          else
            publish `prefixed_forward_of_unprefixed (p ++ #[base,cut] ++ tail) proof
              (app (actual ++ `prefixed_forward_statement) all)
            addDocStringCore (actual ++ `prefixed_forward_of_unprefixed)
              "Conditional original fixed-prefix transport from the exact unprefixed raw differential. The final Actual.prefixed_forward supplies the completed native-to-actual unprefixed producer; this helper introduces no new source, phase, mask, adjoint, or response premise (main:eq:primary-strain)."

end JanetCartan.PhysicalPrimary.OriginalRawAngularActualApplication
end
