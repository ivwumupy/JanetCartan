module
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedInputMassData
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
public meta import Lean
/-!
# The exact actual full-source input mass statement

Canonical reproduction of the checked native-first scalar factoring. SAME
native/selected unweighted input, full forcing, Picard source, sample and fixed
J; M_N=Cmass44*COMMON D_N(n+1) precedes history. The separate proof leaf applies
the actual mass and common-profile producers, not a mass-success premise
(`main:eq:primary-fixed-scales`). No scratch proof dependency is imported.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalMean.OriginalFullSourcePicardMassTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalFullSourcePicard
private def source := `JanetCartan.PhysicalMean.OriginalCanonicalSource
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)
private def saveMass (mode : Nat) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  unless p.size == 55 do throwError "actual Picard mass: selected55 ABI changed"
  let statement := root ++ `input_fourierMass_statement
  let resultType := if mode == 0 then mkSort .zero else app statement p
  let resultValue := if mode == 0 then target else proof
  let type ← instantiateMVars (← mkForallFVars p resultType)
  let value ← instantiateMVars (← mkLambdaFVars p resultValue)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual Picard mass: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual Picard mass: unresolved or extra source/analytic field"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := if mode == 0 then statement else root ++ `input_fourierMass_le
  liftM <| IO.eprintln s!"actual Picard mass: kernel checking {name}/55"
  if mode == 0 then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual SAME full-forcing Picard source has literal original unweighted input mass at most M_N*h, where M_N=Cmass44*COMMON D_N(n+1) precedes the original history. All source analytic inputs are proved; only the original initial auxiliary reach is numeric. No inverse weight or sample-count factor (main:eq:primary-fixed-scales)."
  logInfo m!"actual Picard unweighted mass {name}/55: named statement/proof, exact common M_N*h, no analytic premise"
elab "prove_actual_full_source_mass " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "actual Picard mass: unknown statement/proof mode"
  OriginalFullSourcePicard.withFullData fun native selected _ high L => do
    withTransparency .default do
      forallBoundedTelescope (← inferType high) (some 1) fun numeric _ => do
        unless numeric.size == 1 do throwError "actual Picard mass: initial auxiliary gate changed"
        let hAux := numeric[0]!
        withLocalDeclNoLocalInstanceUpdate `N .default (mkConst ``Nat) fun N => do
          let stage := selected ++ #[hAux,N]
          let fixed := native[:44].toArray
          let early := selected[:33].toArray
          let n := app ``Nat.succ #[native[0]!]
          let q := app ``Nat.succ #[n]
          let R := app `JanetCartan.historyScale #[native[44]!,mkConst `JanetCartan.growthExponent,native[46]!]
          let full := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSource selected
          let run := app (source ++ `selected_iterateWithForcing) (native ++ #[L,full,N])
          let stem := app `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.selected_fourierMassValue_le
            (selected[:39].toArray ++ #[L,run])
          forallBoundedTelescope (← inferType stem) (some 1) fun index _ => do
            unless index.size == 1 do throwError "actual Picard mass: original sampled index changed"
            let hmass := mkAppN stem index
            let actualMass ← inferType hmass
            unless actualMass.isAppOfArity ``LE.le 4 do throwError "actual Picard mass: literal unweighted statement changed"
            let profile := app (root ++ `iterate_profile_uniform)
              (selected ++ #[hAux,N,N,← mkAppM ``le_refl #[N],q])
            let profileType ← inferType profile
            let v := profileType.getAppArgs[2]!
            let rhs := profileType.getAppArgs[3]!
            unless rhs.isAppOfArity ``HMul.hMul 6 && rhs.getAppArgs[4]!.isAppOfArity ``HMul.hMul 6 do
              throwError "actual Picard mass: common source profile factors changed"
            let h := rhs.getAppArgs[4]!.getAppArgs[5]!
            let D := app (root ++ `D) (early.push N)
            let cm := app `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.Cmass fixed
            let hcm := app `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.Cmass_nonneg fixed
            let proof := app ``OriginalFullSourcePicard.mass_from_low_profile
              #[n,actualMass.getAppArgs[2]!,v,cm,mkApp D q,h,R,hcm,hmass,profile]
            let cost ← termWith [(`CM,cm),(`D,D),(`q,q)] "CM * D q"
            let target := (← inferType proof).replace fun e =>
              if e == cost then some (app (root ++ `M) (early.push N)) else none
            unless (target.find? (·.isAppOf (root ++ `M))).isSome do
              throwError "actual Picard mass: exact prehistory M_N disappeared"
            saveMass mode.getNat (stage ++ index) proof target
end JanetCartan.PhysicalMean.OriginalFullSourcePicardMassTemplate
end
prove_actual_full_source_mass 0
