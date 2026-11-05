module

public import JanetCartan.Iteration.PhysicalNormalInverse.RetainedProfiles
public import JanetCartan.Iteration.PhysicalInitialization.CurrentInverse
public import JanetCartan.Iteration.PhysicalInitialization.OriginalGeometry
public meta import Lean

/-!
# Instantiate the five coefficient profiles on the original current parent

The fixed31 current prefix and its selected original cell determine every
retained datum. Only an initial-density derivative budget is supplied; no
leading data, flow, frame, or correction estimate is reselected.
Consumer: the actual corrected colored normal comparison
(`app:ch_waves:eq:colored-normal-comparison`).
-/

public meta section
namespace JanetCartan.PhysicalNormalInverse.OriginalRetainedProfilesApplication
open Lean Meta Elab Command

private def saveDef (name : Name) (params : Array Expr) (value : Expr) : MetaM Expr := do
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← inferType value)
  if value.hasFVar || value.hasMVar || value.hasSorry || type.hasFVar || type.hasMVar || type.hasSorry then
    throwError "original retained profiles: incomplete definition {name}"
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
    (forceExpose := true)
  return mkAppN (mkConst name) params

private def saveThm (name : Name) (params : Array Expr) (value : Expr)
    (target : Option Expr := none) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars params (target.getD (← inferType value)))
  let value ← instantiateMVars (← mkLambdaFVars params value)
  if value.hasFVar || value.hasMVar || value.hasSorry || type.hasFVar || type.hasMVar || type.hasSorry then
    throwError "original retained profiles: incomplete theorem {name}"
  addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  return mkAppN (mkConst name) params

private partial def cache (base : Name) (params : Array Expr) (proof : Expr)
    (index : Nat := 0) : MetaM Unit := do
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``Exists 2 then
    let .lam name _ body _ := type.appArg! | throwError "expected coefficient witness"
    let value ← saveDef (base ++ name) params (← mkAppM ``Classical.choose #[proof])
    let next ← saveThm (base ++ Name.mkSimple s!"afterChoice_{name}") params
      (← mkAppM ``Classical.choose_spec #[proof]) (some (body.instantiate1 value))
    cache base params next index
  else if type.isAppOfArity ``And 2 then
    discard <| saveThm (base ++ Name.mkSimple s!"fact{index}") params (← mkAppM ``And.left #[proof])
    let next ← saveThm (base ++ Name.mkSimple s!"afterFact{index}") params (← mkAppM ``And.right #[proof])
    cache base params next (index + 1)
  else
    discard <| saveThm (base ++ `continuation) params proof

private def component (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do
    proof ← mkAppM ``And.right #[proof]
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``And 2 then mkAppM ``And.left #[proof] else pure proof

/-- Read the literal retained application behind the actual current getter. -/
private def retainedArgs (params : Array Expr) : MetaM (Array Expr) := do
  let mut value := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalCurrent.current) params
  for _ in [:4] do
    if value.getAppFn.isConstOf `JanetCartan.PhysicalPrimary.LeadingCell.current then break
    let some body := (← getConstInfo value.getAppFn.constName!).value?
      | throwError "original retained profiles: current alias has no body"
    value := body.beta value.getAppArgs
  unless value.getAppFn.isConstOf `JanetCartan.PhysicalPrimary.LeadingCell.current && value.getAppArgs.size == 36 do
    throwError "original retained profiles: expected exact LeadingCell.current36"
  return value.getAppArgs

/-- Cache original before-history budgets and instantiate the actual current's
retained data at one combined threshold; never compare independently chosen
leading witnesses. -/
elab "cache_original_retained_profiles" : command => liftTermElabM do
  let currentNS := `JanetCartan.PhysicalInitialization.OriginalCurrent
  let leadingNS := `JanetCartan.PhysicalInitialization.CurrentLeading
  let originalNS := `JanetCartan.PhysicalSeed.OriginalBoundary
  let capNS := `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap
  let root := `JanetCartan.PhysicalNormalInverse.OriginalRetained
  let budgets := root ++ `Budgets
  let producer := `JanetCartan.PhysicalNormalInverse.exists_history_retained_normal_coefficient_profiles
  let info ← getConstInfo (currentNS ++ `current)
  forallBoundedTelescope info.type (some 38) fun all _ => do
    unless all.size == 38 do throwError "original retained profiles: expected31+6+index"
    let fixed := all[:31].toArray
    let original := fixed[:21].toArray
    let args ← retainedArgs all
    let n := fixed[0]!
    let hn := fixed[1]!
    let patch := args[4]!.getAppArgs.back!
    let hSigma ← mkAppM ``And.left #[fixed[22]!]
    let hSigmaCap ← mkAppM ``And.right #[fixed[22]!]
    let hSigmaOne ← mkAppM `le_trans #[hSigmaCap, mkAppN (mkConst (capNS ++ `fact2)) original]
    let H := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.H) fixed[:18].toArray
    let G ← mkAppM ``JanetCartan.sourceDilationReference #[H, hSigma, hSigmaOne]
    let domainEq := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) fixed[:18].toArray
    let radiusEq ← mkAppM ``congrArg #[mkConst ``JanetCartan.LocalDomain.chartRadius, domainEq]
    let hRgeom ← mkAppM `lt_of_lt_of_eq
      #[mkAppN (mkConst (originalNS ++ `R_lt_chartRadius)) #[n, hn], ← mkAppM ``Eq.symm #[radiusEq]]
    let hball := mkAppN (mkConst `JanetCartan.PhysicalInitialization.original_frameBall_subset) #[n, hn, patch]
    let positivity := mkAppN (mkConst (originalNS ++ `comparison_pos)) #[n, hn, patch, args[35]!]
    let cover := mkAppN (mkConst (originalNS ++ `comparison_cover)) #[n, hn, patch, args[35]!]
    let hc := mkAppN (mkConst (leadingNS ++ `fact2)) (fixed.push patch)
    let hE := mkAppN (mkConst (leadingNS ++ `fact3)) (fixed.push patch)
    let h14 ← mkAppM ``Nat.le_trans
      #[mkAppN (mkConst `JanetCartan.PhysicalInitialization.leading_reserve_le_canonical_low_order) #[n], fixed[28]!]
    withLocalDeclD `Ar (← mkArrow (mkConst ``Nat) (mkConst ``Real)) fun Ar => do
      let zero ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkNatLit 0), none]
      let hArType ← withLocalDeclD `j (mkConst ``Nat) fun j => do
        mkForallFVars #[j] (← mkAppM ``LE.le #[zero, mkApp Ar j])
      withLocalDeclD `hAr hArType fun hAr => do
        let params := fixed ++ #[all[37]!, Ar, hAr]
        let inputs := #[n, G,
            mkAppN (mkConst (originalNS ++ `b)) #[n, hn],
            mkAppN (mkConst (originalNS ++ `R)) #[n, hn],
            mkAppN (mkConst (originalNS ++ `b_pos)) #[n, hn],
            mkAppN (mkConst (originalNS ++ `b_lt_R)) #[n, hn], hRgeom,
            args[1]!, args[4]!, hball] ++ args[6:26].toArray ++
          #[hc, args[26]!, args[27]!, args[28]!, args[29]!, hE, Ar, hAr, args[35]!,
            ← component positivity 0, ← component positivity 1, ← component positivity 2,
            ← component positivity 8, ← component cover 0, ← component cover 1,
            fixed[24]!, fixed[25]!, fixed[26]!, fixed[27]!, h14, fixed[29]!]
        unless inputs.size == 51 do throwError "original retained profiles: expected51 physical producer arguments"
        let initialized ← saveThm (root ++ `initialized) params (mkAppN (mkConst producer) inputs)
        cache budgets params initialized
        let nativeS := mkAppN (mkConst (currentNS ++ `S)) fixed
        let profileS := mkAppN (mkConst (budgets ++ `threshold)) params
        let S ← saveDef (root ++ `S) params (← mkAppM ``Max.max #[nativeS, profileS])
        let hNative ← saveThm (root ++ `S_native) params (← mkAppM `le_max_left #[nativeS, profileS])
        let hProfiles ← saveThm (root ++ `S_profiles) params (← mkAppM `le_max_right #[nativeS, profileS])
        discard <| saveThm (root ++ `hS) params
          (← mkAppM `le_trans #[mkAppN (mkConst (budgets ++ `fact0)) params, hProfiles])
        let jointType ← mkAppM ``LE.le #[S, all[31]!]
        withLocalDeclD `hRzero jointType fun hRzero => do
          let hNativeReached ← mkAppM `le_trans #[hNative, hRzero]
          let hProfilesReached ← mkAppM `le_trans #[hProfiles, hRzero]
          let actual := all.set! 32 hNativeReached
          let actualArgs ← retainedArgs actual
          let proof := mkAppN (mkConst (budgets ++ `continuation))
            (params ++ #[all[31]!, hProfilesReached] ++ all[33:37].toArray ++ actualArgs[31:35].toArray)
          let publicParams := params ++ #[all[31]!, hRzero] ++ all[33:37].toArray
          let application ← saveThm (root ++ `application) publicParams proof
          forallBoundedTelescope (← inferType application) (some 1) fun initialArgs tail => do
            unless initialArgs.size == 1 do throwError "original retained profiles: expected initial scalar input"
            let initialType ← inferType initialArgs[0]!
            let smoothType := tail.bindingDomain!
            let neighborhood := smoothType.getAppArgs.back!
            let neighborhoodArgs := neighborhood.getAppArgs
            let center := neighborhoodArgs[neighborhoodArgs.size - 2]!
            let radius := mkApp actualArgs[10]! actualArgs[35]!
            withLocalDeclD `v initialType fun v => do
              let scalar := mkAppN (mkConst (capNS ++ `fact6))
                (original ++ #[center, radius, ← component positivity 1, fixed[21]!, hSigma, v])
              forallBoundedTelescope (← inferType scalar) (some 4) fun density _ => do
                unless density.size == 4 do throwError "original retained profiles: expected four actual density conditions"
                let low := mkAppN scalar density
                let hInitial ← component low 0
                let hFifteen ← component low 1
                let hLower ← component low 2
                let smoothArgs := (← inferType hInitial).getAppArgs
                let initial := smoothArgs[smoothArgs.size - 2]!
                let normBoundArgs := (← inferType hFifteen).getAppArgs
                let normFifteen := normBoundArgs[normBoundArgs.size - 2]!
                unless normFifteen.getAppFn.isConstOf ``JanetCartan.cNorm do
                  throwError "original retained profiles: expected literal scalar C15 norm"
                let normArgs := normFifteen.getAppArgs
                let normFourteen := mkAppN normFifteen.getAppFn
                  (normArgs.set! (normArgs.size - 2) (mkNatLit 14))
                let monoType ← mkAppM ``LE.le #[normFourteen, normFifteen]
                let mono ← Term.elabTermEnsuringType
                  (← `(by exact JanetCartan.cNorm_mono_order (by decide))) monoType
                Term.synthesizeSyntheticMVarsNoPostponing
                let hFourteen ← mkAppM `le_trans #[mono, hFifteen]
                discard <| saveThm (root ++ `positive_continuation)
                  (publicParams ++ #[v] ++ density)
                  (mkAppN application #[initial, hInitial, hFourteen, hLower])
          logInfo "kernel-checked actual original31 retained data and SAME cap C15 admission; fixed index/Ar/hAr and one max threshold precede history"

end JanetCartan.PhysicalNormalInverse.OriginalRetainedProfilesApplication
