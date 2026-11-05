module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalSynthesis
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalMassValue
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardMass
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-! The genuine physical sampled primary at the actual full-forcing finite
Picard source. The common mass cost is exactly Cmass*sum_{j≤N} P_j(n+1), fixed
before history. The uncut positive baseline, all labels, one sample and the
original whole-source inverse remain unchanged. Consumer: main:eq:primary-fixed-scales.
This leaf publishes the exact field and named physical norm proposition only.
The separate proof leaf supplies the genuine mass producer; no primary STRAIN
decay is asserted here. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryApplication
open Lean Meta Elab Command
open PhysicalMean.OriginalCanonicalMomentAdmissionTemplate (withSelectedAtPoint)
private def root := `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary
private def profiles := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def picard := `JanetCartan.PhysicalMean.OriginalFullSourcePicard
private def source := `JanetCartan.PhysicalMean.OriginalCanonicalSource
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ value body _ => head (body.instantiate1 value)
  | v => v
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "full-source physical primary: unavailable original body {key}"
  return head (value.beta p)
private def next (value type argument : Expr) : MetaM (Expr × Expr) := do
  let .forallE _ _ body _ := head type |
    throwError "full-source physical primary: frozen synthesis argument boundary changed"
  return (mkApp value argument,body.instantiate1 argument)
private def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "full-source physical primary: missing {missing.toList}"
    for old in #[source ++ `iterate,source ++ `selected_iterate,
        `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing] do
      if e.getUsedConstants.contains old then throwError "full-source physical primary: background-only run escaped"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "full-source physical primary: unresolved history/source input in {key}"
  if !data && !(value.getUsedConstantsAsSet.contains (picard ++ `input_fourierMass_le)) then
    throwError "full-source physical primary: the genuine full-forcing mass producer disappeared"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  let out ← liftM IO.getStdout
  liftM <| out.putStrLn s!"checking full-source physical primary {key}/{p.size}"
  liftM <| out.flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "SAME actual physical sampled primary on the genuine complete-forcing finite Picard source, ONE fixed J, common M_N=Cmass*D_N(n+1) before history, revised b and literal physical cutoff. No source/profile/mass success premise. The distinct angular-strain producer is not asserted here (main:eq:primary-fixed-scales; new:eq:source-bound)."
  logInfo m!"checked full-source physical primary {key}/{p.size}: full g, common D_N, original sample and baseline"

private def withFullData
    (go : Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  PhysicalMean.OriginalFullSourcePicard.withFullData fun native selected _ high L => do
    unless native.size == 50 && selected.size == 52 do
      throwError "full-source physical primary: released native50/selected52 changed"
    go native selected high L

elab "prove_actual_full_source_physical_primary " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "full-source physical primary: unknown mode"
  withFullData fun native selected high L => do
    withLocalDeclNoLocalInstanceUpdate `N .default (mkConst ``Nat) fun N => do
      let full := app (forcing ++ `selectedFullSource) selected
      let run := app (source ++ `selected_iterateWithForcing) (native ++ #[L,full,N])
      let sourceArgs := native ++ #[L,run]
      if mode.getNat == 0 then
        withLocalDeclNoLocalInstanceUpdate `δ .default (mkConst ``Real) fun δ => do
          let value := app (profiles ++ `selectedSourcePrimary) (sourceArgs.push δ)
          save `field (selected ++ #[N,δ]) value (← inferType value) true
      else
        forallBoundedTelescope (← inferType high) (some 1) fun numeric _ => do
          unless numeric.size == 1 do throwError "full-source physical primary: numeric initial reach changed"
          let hAux := numeric[0]!
          let fixed := native[:44].toArray
          let static := selected[:33].toArray.push N
          let M := app (picard ++ `M) static
          let hM := app (picard ++ `M_nonneg) static
          let synthesisArgs := fixed ++ #[M,hM]
          let synthesis := app (profiles ++ `selectedSourcePrimary_physicalProfiles_of_mass_bound) synthesisArgs
          let existsType ← bodyAt (profiles ++ `selectedSourcePrimary_physicalProfiles_statement) synthesisArgs
          unless existsType.isAppOfArity ``Exists 2 do throwError "full-source physical primary: prehistory synthesis lost Exists"
          let Ctype := existsType.getAppArgs[0]!
          let predicate := existsType.getAppArgs[1]!
          let .sort level ← whnf (← inferType Ctype) | throwError "full-source physical primary: coefficient type is not a sort"
          let C := mkAppN (mkConst ``Classical.choose [level]) #[Ctype,predicate,synthesis]
          let spec := mkAppN (mkConst ``Classical.choose_spec [level]) #[Ctype,predicate,synthesis]
          let pairType := head (predicate.beta #[C])
          unless pairType.isAppOfArity ``And 2 do throwError "full-source physical primary: synthesis lost positivity"
          let hC := Expr.proj ``And 0 spec
          let mut value := Expr.proj ``And 1 spec
          let mut type := pairType.getAppArgs[1]!
          for argument in native[44:50].toArray ++ #[L,run] do
            let applied ← next value type argument
            value := applied.1
            type := applied.2
          let .forallE _ massGoal _ _ := head type |
            throwError "full-source physical primary: literal mass premise changed"
          let hMass ← forallBoundedTelescope massGoal (some 1) fun index inequality => do
            unless index.size == 1 && inequality.isAppOfArity ``LE.le 4 do
              throwError "full-source physical primary: original sampled mass index changed"
            let upper := inequality.getAppArgs[3]!
            let actual := app (picard ++ `input_fourierMass_le) (selected ++ #[hAux,N] ++ index)
            let physical := app `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalMassValue.physicalMass_le_of_inputValue
              (sourceArgs ++ index ++ #[upper,actual])
            mkLambdaFVars index physical
          let applied ← next value type hMass
          value := applied.1
          type := applied.2
          forallBoundedTelescope type (some 2) fun amplitude result => do
            unless amplitude.size == 2 do throwError "full-source physical primary: external amplitude DATA changed"
            let δ := amplitude[0]!
            let rawP := app (profiles ++ `selectedSourcePrimary) (sourceArgs.push δ)
            let P := app (root ++ `field) (selected ++ #[N,δ])
            let result := result.replace fun e => if e == rawP then some P else none
            unless result.getUsedConstantsAsSet.contains (root ++ `field) do
              throwError "full-source physical primary: actual physical field was not retained"
            let tail := selected[33:].toArray ++ #[hAux] ++ amplitude
            let allProof ← mkLambdaFVars tail (mkAppN value amplitude)
            let allType ← mkForallFVars tail result
            let positive := pairType.getAppArgs[0]!
            let pair := mkAppN (mkConst ``And.intro) #[positive,allType,hC,allProof]
            let target := mkApp2 (mkConst ``And) positive allType
            let predicate ← withLocalDeclNoLocalInstanceUpdate `C .default Ctype fun c => do
              mkLambdaFVars #[c] (target.replace fun e => if e == C then some c else none)
            let target := mkApp2 (mkConst ``Exists [level]) Ctype predicate
            let proof := mkAppN (mkConst ``Exists.intro [level]) #[Ctype,predicate,C,pair]
            if mode.getNat == 1 then
              save `physical_profiles_statement static target (mkSort .zero) true
            else
              save `physical_profiles static proof (app (root ++ `physical_profiles_statement) static)
end JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryApplication
end
prove_actual_full_source_physical_primary 0
prove_actual_full_source_physical_primary 1
#print axioms JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.field
#print axioms JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.physical_profiles_statement
