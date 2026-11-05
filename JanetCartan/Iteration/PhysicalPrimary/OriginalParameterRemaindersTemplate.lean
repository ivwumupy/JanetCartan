module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Close the original normalized-inverse primitives by their existing native
proofs and exact measured-complex-residual identification. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalParameterRemaindersTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def current := regular ++ `Current
private def ns := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders
private def native := ns ++ `Native
private def paired := ns ++ `Paired

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | k+1 => part (.proj ``And 1 e) k

/-- Store an actual source with its supplied type without eagerly inferring
its large literal body. The kernel still checks the full safe declaration. -/
private def storeExpectedSource (name : Name) (params : Array Expr) (v target : Expr)
    (isDef := false) : MetaM Expr := do
  let value ← instantiateMVars (← mkLambdaFVars params v)
  let type ← instantiateMVars (← mkForallFVars params target)
  if type.hasFVar || type.hasMVar || type.hasSorry || value.hasFVar || value.hasMVar || value.hasSorry then
    throwError "actual source: open or incomplete typed declaration {name}"
  if isDef then
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }) (forceExpose := true)
  else
    addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  return mkAppN (mkConst name) params

private def sourceForallResult (input : Expr) (args : Array Expr) : MetaM Expr := do
  let mut type := input
  for arg in args do
    let .forallE _ _ body _ := type | throwError "actual source: changed native application spine"
    type := body.instantiate1 arg
  return type

private partial def sourceZetaHead : Expr → Expr
  | .letE _ _ value body _ => sourceZetaHead (body.instantiate1 value)
  | e => e

private def sourceConj (e : Expr) (right := false) : MetaM Expr := do
  let type := sourceZetaHead e
  unless type.isAppOfArity ``And 2 do throwError "actual source: expected literal conjunction"
  return type.getAppArgs[if right then 1 else 0]!

private def retain (name : Name) (params : Array Expr) (proof : Expr)
    (isDef := false) (type : Option Expr := none) : MetaM Expr := do
  let name := native ++ name
  let result ← store name params proof isDef type
  addDocStringCore name "Exact original normalized-solver primitive for the SAME measured complex residual, native real Kloc, full Q/B and paired solver. No operator, inverse, mask or contraction is chosen (app:ch_regular:eq:inverse-remainder; app:ch_response:eq:response-graded-reduced)."
  return result

private def bodyAt (name : Name) (params : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "native remainder: missing actual body {name}"
  return value.beta params

private def smoothOn (h domain : Expr) : MetaM Expr := do
  let mut type := (← getConstInfo `ContDiff.contDiffOn).type
  let mut args : Array (Option Expr) := #[]
  while type.isForall do
    let .forallE name _ body _ := type | unreachable!
    args := args.push (if name == `s then some domain else none)
    type := body
  args := args.set! (args.size-1) (some h)
  mkAppOptM `ContDiff.contDiffOn args

/-- Close the real/complex residual, native gain and adjoint, and full paired
solver on the unchanged original38 input telescope. Only tame constants are
selected, before all current/history inputs. -/
elab "retain_original_normalized_remainder_primitives" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `normalized_solver)).type (some 38) fun params _ => do
    unless params.size == 38 do throwError "native remainder: expected original38 current"
    let fixed := params[:23].toArray
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let cur (name : Name) := mkAppN (mkConst (current ++ name)) params
    let n := mkApp (mkConst ``Nat.succ) params[0]!
    let original := #[n] ++ params[1:21].toArray
    let hK := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalProtected.fact14) original
    let fin2 := mkApp (mkConst ``Fin) (mkNatLit 2)
    let zero ← mkNumeral fin2 0
    let one ← mkNumeral fin2 1
    let rawR ← bodyAt (current ++ `R) params
    unless rawR.isAppOfArity `JanetCartan.ArbitraryAccuracy.ResidualLocalization.localRealCompression 6 do
      throwError "native remainder: real residual argument spine changed"
    let hW := rawR.getAppArgs[3]!
    let bridge ← mkAppM `JanetCartan.FixedDomainInverse.initialized_complexResidual_identification
      #[stat `f,hK,stat `L,cur `Q,cur `B,stat `output,cur `ho,cur `hob,
        cur `W₁,mkApp (cur `retarded) one,hW,stat `hrU,stat `hUW,
        cur `hmem,stat `hbudget,cur `hbound,stat `χ₂,stat `χ₃,stat `fact42]
    let lhs := (← inferType (part bridge 0)).getAppArgs[1]!
    unless lhs.isAppOf `JanetCartan.realOutputCompression do
      throwError "native remainder: expected exact real compression"
    let rawComplex := lhs.appArg!
    let Rcomplex ← retain `Rcomplex params rawComplex true
    discard <| retain `Rreal params (cur `Kloc) true
    let bridgeType := (← inferType bridge).replace fun e => if e == rawComplex then some Rcomplex else none
    let bridge ← retain `identification params bridge false (some bridgeType)
    let same ← retain `real_compression params (part bridge 0)
    discard <| retain `residual_real params (part bridge 1)
    let normEq ← retain `residual_norm params (part bridge 2)
    discard <| retain `corrected_source_identity params (.proj ``And 1 (.proj ``And 1 (.proj ``And 1 bridge)))
    let hle ← mkAppM `le_trans #[← mkAppM `le_of_eq #[normEq],cur `fact6]
    discard <| retain `residual_half_bound params hle
    discard <| retain `residual_contraction params (← mkAppM (ns ++ `lt_one_of_half_bound) #[hle])
    let realBound ← mkAppM `le_trans
      #[← mkAppM `JanetCartan.realOutputCompression_norm_le #[Rcomplex],hle]
    discard <| retain `real_half_bound params realBound
    let nativeNorm := (← inferType (cur `fact6)).getAppArgs
    let literalKloc := nativeNorm[nativeNorm.size-2]!.appArg!
    let gainType ← inferType (cur `fact12)
    unless (gainType.find? fun e => e == literalKloc).isSome do
      throwError "native remainder: native gain lost literal Kloc"
    let predicate ← withLocalDeclD `Kloc (← inferType literalKloc) fun Kloc =>
      mkLambdaFVars #[Kloc] (gainType.replace fun e => if e == literalKloc then some Kloc else none)
    let hEq ← mkAppM ``congrArg #[predicate,same]
    let gain ← mkAppM ``Eq.mpr #[hEq,cur `fact12]
    discard <| retain `gain params gain
    discard <| retain `gain_cost_nonneg fixed (stat `fact50)
    let Ω := (← inferType (stat `f)).getAppArgs[1]!
    let hQon ← smoothOn (cur `hQ) Ω
    let hBon ← smoothOn (cur `hB) Ω
    let coefficient := mkAppN (stat `fact41) #[cur `Q,cur `B,hQon,hBon]
    let mono ← mkAppM (ns ++ `coefficient_pair_nonneg_monotone)
      #[cur `uQ,cur `uB,part coefficient 0]
    discard <| retain `coefficient_nonneg params (part mono 0)
    discard <| retain `coefficient_monotone params (.proj ``And 1 mono)
    let some uqValue := (← getConstInfo (current ++ `uQ)).value? (allowOpaque := true)
      | throwError "native remainder: missing original coefficient-class value"
    let uq := uqValue.beta params
    unless uq.isAppOfArity `JanetCartan.RegularSector.FiniteAssembly.CoefficientNorms.smoothCoefficientL2 12 do
      throwError "native remainder: changed original coefficient-class construction"
    let ua := uq.getAppArgs
    for (name,value) in [(`coefficient_domain_open,ua[7]!),(`norm_radius_pos,ua[8]!),(`norm_ball_subset,ua[9]!)] do
      discard <| retain name fixed value
    let fargs := (← inferType (stat `f)).getAppArgs
    unless fargs.size == 7 do throwError "native remainder: original family spine changed"
    let Kcoeff ← mkAppM `Metric.closedBall #[fargs[2]!,fargs[3]!]
    let shift := mkApp (mkConst `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder) params[0]!
    let ho ← mkAppM `ContDiff.continuous #[stat `fact17]
    let hob ← forallBoundedTelescope (← inferType (stat `fact18)) (some 1) fun y _ => do
      let hy := mkAppN (stat `fact18) y
      let hn ← mkAppM `Real.norm_of_nonneg #[part hy 0]
      let hb ← mkAppM `le_trans #[← mkAppM `le_of_eq #[hn],.proj ``And 1 hy]
      mkLambdaFVars y hb
    let constants ← mkAppM `JanetCartan.FixedDomainInverse.exists_initialized_pairedSolver_fourier_tame_constants
      #[stat `f,hK,stat `L,stat `output,ho,hob,
        mkApp (stat `completeCost) zero,mkApp (stat `fact38) zero,Kcoeff,shift]
    let constants ← store (paired ++ `exists_constants) fixed constants
    select paired fixed constants
    let hpositive := part (part (part (cur `fact5) 0) 0) 3
    let orderZero := mkApp hpositive zero
    let half ← forallBoundedTelescope (← inferType orderZero) (some 1) fun orders _ => do
      let Tzero := mkApp (cur `Tplus) zero
      let use := mkAppN orderZero (orders.push Tzero)
      let .forallE _ needed _ _ ← whnf (← inferType use)
        | throwError "native remainder: missing half-solver membership"
      unless needed.isAppOfArity ``Or 2 do throwError "native remainder: changed solver/adjoint alternatives"
      let hleft := mkAppN (mkConst ``Or.inl)
        #[needed.getAppArgs[0]!,needed.getAppArgs[1]!,← mkEqRefl Tzero]
      mkLambdaFVars orders (mkApp use hleft)
    discard <| retain `half_solver_tame params half
    let full := mkAppN (mkConst (paired ++ `continuation))
      (fixed ++ #[cur `Q,cur `B,mkApp (cur `retarded) zero,half])
    discard <| retain `paired_solver_tame params full
    let literalSolverType ← inferType full
    let solverName := `JanetCartan.RegularSector.NormalizedSolver.pairedSolver
    let some solver := literalSolverType.find? fun e => e.isAppOf solverName
      | throwError "native remainder: paired solver disappeared"
    discard <| retain `pairedSolver params solver true
  logInfo "actual original38 inverse primitives: identical complex measured residual/real Kloc, half-contraction, native gain plus adjoint, monotone full Q/B restriction profile, and SAME uncut paired solver; all ordinary tame constants before history; no new inverse or operator"

/-- Close every source-jet input and the chi3-neutral forcing identity on the
literal original51 producer. Only its existing primitive scalar profile remains
in the input telescope; no source-response estimate is assumed. -/
elab "retain_original_parameter_source_identity" : command => liftTermElabM do
  let sourceNS := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
  let outputNS := ns ++ `Source
  forallBoundedTelescope (← getConstInfo (sourceNS ++ `full_source_profiles)).type (some 53) fun params both => do
    unless params.size == 53 do throwError "native remainder source: changed actual original53 input spine"
    logInfo "SOURCE: original53 telescope ready"
    let prior := params[:39].toArray
    let source (name : Name) := mkAppN (mkConst (sourceNS ++ name)) prior
    let original := mkAppN (mkConst (sourceNS ++ `full_source_profiles)) params
    let originalType ← sourceConj both
    unless originalType.isAppOfArity `JanetCartan.PhysicalPrimary.LeadingReducedSourceFourierBounds 7 do
      throwError "native remainder source: expected literal normalized full-source Fourier profile"
    let args := originalType.getAppArgs
    let .forallE _ _ sourceTail _ :=
        (← getConstInfo `JanetCartan.PhysicalPrimary.LeadingReducedSourceFourierBounds).type
      | throwError "native remainder source: missing physical dimension binder"
    let .forallE _ amplitudeType _ _ := sourceTail.instantiate1 args[0]!
      | throwError "native remainder source: missing explicit amplitude type"
    let a ← storeExpectedSource (outputNS ++ `a) params args[1]! amplitudeType true
    logInfo "SOURCE: literal normalized amplitude retained"
    let folded := both.replace fun e =>
      if e == args[1]! then some a else if e == args[3]! then some (source `Csource) else none
    discard <| storeExpectedSource (outputNS ++ `original_profiles) params original folded

/-- Preserve the actual joint smoothness and both zero clauses without
normalizing the scalar span or any full native inverse object. -/
elab "retain_original_parameter_source_masks" : command => liftTermElabM do
  let outputNS := ns ++ `Source
  forallBoundedTelescope (← getConstInfo (outputNS ++ `original_profiles)).type (some 53) fun params both => do
    let original := mkAppN (mkConst (outputNS ++ `original_profiles)) params
    let full := part original 0
    let native ← sourceConj both
    unless native.isAppOfArity `JanetCartan.PhysicalPrimary.LeadingReducedSourceFourierBounds 7 do
      throwError "actual source masks: lost the original seven bound arguments"
    let info ← getConstInfo `JanetCartan.PhysicalPrimary.LeadingReducedSourceFourierBounds
    let some value := info.value? (allowOpaque := true) | throwError "actual source masks: missing native definition"
    let conjunction := value.beta native.getAppArgs
    discard <| storeExpectedSource (outputNS ++ `joint_smooth) params (part full 0) (← sourceConj conjunction)
    discard <| storeExpectedSource (outputNS ++ `physical_zero) params (part full 1)
      (← sourceConj (← sourceConj conjunction true))
    discard <| storeExpectedSource (outputNS ++ `parameter_zero) params (.proj ``And 1 original)
      (← sourceConj both true)
    logInfo "SOURCE: original joint smoothness and both zero clauses retained"

/-- The fixed prehistory threshold supplies the original source scale normalization. -/
elab "retain_original_parameter_source_scale" : command => liftTermElabM do
  let outputNS := ns ++ `Source
  let sourceNS := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
  forallBoundedTelescope (← getConstInfo (outputNS ++ `a)).type (some 53) fun params _ => do
    let source (name : Name) := mkAppN (mkConst (sourceNS ++ name)) params[:39].toArray
    let real := mkConst `Real
    let order ← synthInstance (mkApp (mkConst `Preorder [Level.zero]) real)
    let realTrans (a b c hab hbc : Expr) :=
      mkAppN (mkConst `le_trans [Level.zero]) #[real,order,a,b,c,hab,hbc]
    let hTwo := realTrans (← mkNumeral real 2) (source `S) params[39]! (source `hS) params[40]!
    let hscale := mkAppN (mkConst (ns ++ `coefficient_scale_one_le_of_two_le))
      #[params[39]!,hTwo,params[41]!]
    let scale := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[params[39]!,params[41]!]
    let hK := realTrans (← mkNumeral real 1) scale params[45]! hscale params[46]!
    discard <| storeExpectedSource (outputNS ++ `scale_one_le) params hK
      (← mkAppM ``LE.le #[← mkNumeral real 1,params[45]!])

/-- Nonnegativity of the original Fourier COST; this is not a pointwise
factorization of the native amplitude. -/
elab "retain_original_parameter_source_budget" : command => liftTermElabM do
  let outputNS := ns ++ `Source
  forallBoundedTelescope (← getConstInfo (outputNS ++ `original_profiles)).type (some 53) fun params both => do
    let native ← sourceConj both
    unless native.isAppOfArity `JanetCartan.PhysicalPrimary.LeadingReducedSourceFourierBounds 7 do
      throwError "actual source budget: changed original Fourier cost"
    let hA ← mkAppM `mul_nonneg
      #[← mkAppM `pow_nonneg #[← mkAppM `le_of_lt #[params[48]!],mkNatLit 3],params[51]!]
    discard <| storeExpectedSource (outputNS ++ `amplitude_nonneg) params hA
      (← mkAppM ``LE.le #[← mkNumeral (mkConst `Real) 0,native.getAppArgs[4]!])

/-- The ordinary parameter-list Fourier estimate on the actual source;
all quantitative inputs come from the very same native source53. -/
elab "retain_original_parameter_source_bundle" : command => liftTermElabM do
  let outputNS := ns ++ `Source
  let sourceNS := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
  forallBoundedTelescope (← getConstInfo (outputNS ++ `original_profiles)).type (some 53) fun params both => do
    let fixed := params[:23].toArray
    let source (name : Name) := mkAppN (mkConst (sourceNS ++ name)) params[:39].toArray
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let full := part (mkAppN (mkConst (outputNS ++ `original_profiles)) params) 0
    let native ← sourceConj both
    let args := native.getAppArgs
    unless args.size == 7 do throwError "actual source bundle: changed native Fourier bound"
    let a := mkAppN (mkConst (outputNS ++ `a)) params
    let hK := mkAppN (mkConst (outputNS ++ `scale_one_le)) params
    let hA := mkAppN (mkConst (outputNS ++ `amplitude_nonneg)) params
    let helper := ns ++ `full_source_parameter_primitives
    let inputs := #[args[0]!,stat `χ₂,a,args[3]!,args[4]!,args[5]!,args[6]!,source `Csource_nonneg,hA,hK,full]
    let bundle := mkAppN (mkConst helper) inputs
    let type ← sourceForallResult (← getConstInfo helper).type inputs
    discard <| storeExpectedSource (outputNS ++ `parameter_primitives) params bundle (sourceZetaHead type)

/-- Named projections of the native parameter-jet bundle at the unchanged
source. Their displayed MemLp witness is the same class by proof irrelevance. -/
elab "retain_original_parameter_source_fields" : command => liftTermElabM do
  let outputNS := ns ++ `Source
  forallBoundedTelescope (← getConstInfo (outputNS ++ `parameter_primitives)).type (some 53) fun params conjunction => do
    let bundle := mkAppN (mkConst (outputNS ++ `parameter_primitives)) params
    let mut body := conjunction
    let mut proof := bundle
    for name in [`smooth,`support,`parameter_jet_memLp,`parameter_jet_fourier] do
      discard <| storeExpectedSource (outputNS ++ name) params (.proj ``And 0 proof) (← sourceConj body)
      body ← sourceConj body true
      proof := .proj ``And 1 proof
    discard <| storeExpectedSource (outputNS ++ `parameter_jet_profile) params proof body

/-- The auxiliary cutoff is neutral on this ORIGINAL amplitude, which already
contains chi2. No second source multiplication or output recut is taken. -/
elab "retain_original_parameter_source_primitives" : command => liftTermElabM do
  let outputNS := ns ++ `Source
  forallBoundedTelescope (← getConstInfo (outputNS ++ `a)).type (some 53) fun params amplitudeType => do
    let fixed := params[:23].toArray
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let a := mkAppN (mkConst (outputNS ++ `a)) params
    let zero := mkAppN (mkConst (outputNS ++ `physical_zero)) params
    let .forallE _ product _ _ := amplitudeType
      | throwError "native remainder source: missing original joint amplitude"
    unless product.isAppOfArity ``Prod 2 do throwError "native remainder source: changed full parameter type"
    let E := product.getAppArgs[0]!
    let Par := product.getAppArgs[1]!
    let χ₂ ← mkAppM `ContDiffBump.toFun #[stat `χ₂]
    let χ₃ ← mkAppM `ContDiffBump.toFun #[stat `χ₃]
    withLocalDeclD `c Par fun c => do
      let amplitude ← withLocalDeclD `y E fun y => do
        mkLambdaFVars #[y] (mkApp a (← mkAppM ``Prod.mk #[y,c]))
      let hz ← withLocalDeclD `y E fun y => do
        mkLambdaFVars #[y] (mkApp zero (← mkAppM ``Prod.mk #[y,c]))
      withLocalDeclD `φ (← mkArrow E (mkConst `Real)) fun φ => do
        withLocalDeclD `ρ (mkConst `Real) fun ρ => do
          let leaf := ns ++ `auxiliary_cutoff_preserves_forcing
          let inputs := #[mkApp (mkConst ``Nat.succ) params[0]!,χ₂,χ₃,stat `fact44,amplitude,hz,φ,ρ]
          let equality := mkAppN (mkConst leaf) inputs
          let equation ← sourceForallResult (← getConstInfo leaf).type inputs
          unless equation.isAppOfArity ``Eq 3 do throwError "actual forcing: changed native equality"
          let point := params ++ #[c,φ,ρ]
          let eqArgs := equation.getAppArgs
          let raw ← storeExpectedSource (outputNS ++ `rawForcing) point eqArgs[2]! eqArgs[0]! true
          discard <| storeExpectedSource (outputNS ++ `forcing_eq) point equality
            (mkAppN equation.getAppFn #[eqArgs[0]!,eqArgs[1]!,raw])
    for name in [`a,`original_profiles,`joint_smooth,`physical_zero,`parameter_zero,
        `parameter_primitives,`smooth,`support,`parameter_jet_memLp,
        `parameter_jet_fourier,`parameter_jet_profile,`scale_one_le,`amplitude_nonneg,`forcing_eq] do
      unless (← getEnv).isImportedConst (outputNS ++ name) do
        addDocStringCore (outputNS ++ name) "Actual original51 normalized full-strain source, with SAME theta and existing chi2 forcing. Its all-order list jets are provided by the original source producer; the existing chi3 plateau is neutral, with no output recut (app:ch_response:eq:response-graded-source; app:ch_regular:eq:inverse-remainder)."
  logInfo "actual original51 source: literal chi2-localized half-stress full-strain amplitude with SAME theta; all parameter-list jets and Fourier bounds; existing chi3 leaves forcing unchanged for every phase/frequency, no chi2 squared or response recut"

/-- Retain inverse and ordinary-tame coefficient profiles from the SAME
original global Q/full-B producer. All constants and its threshold precede
histories; only the existing scalar reserve inequalities are added. -/
elab "retain_original_inverse_coefficient_profiles" : command => liftTermElabM do
  let operator := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
  let out := ns ++ `Coefficients
  let inv := out ++ `Inverse
  forallBoundedTelescope (← getConstInfo (current ++ `normalized_solver)).type (some 32) fun base _ => do
    unless base.size == 32 do throwError "inverse coefficient profiles: changed original32 prefix"
    let fixed := base[:23].toArray
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let primitive (name : Name) := mkAppN (mkConst (ns ++ `Native ++ name)) fixed
    let n := mkApp (mkConst ``Nat.succ) base[0]!
    let low := mkApp (mkConst `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder) base[0]!
    let dimensionShift := mkApp2 (mkConst ``Nat.add) base[0]! (mkNatLit 2)
    let beta := mkApp2 (mkConst ``Nat.add) low dimensionShift
    let profileBase := mkAppN (mkConst (operator ++ `exists_profiles))
      (base[:25].toArray ++ #[base[25]!,base[26]!,base[27]!])
    forallBoundedTelescope (← inferType profileBase) (some 1) fun reserve _ => do
      let withReserve := mkAppN profileBase (reserve ++ #[base[28]!,base[29]!])
      forallBoundedTelescope (← inferType withReserve) (some 1) fun hreserve _ => do
        withLocalDeclD `hbeta (← mkAppM ``LE.le #[beta,reserve[0]!]) fun hbeta => do
          let params := base ++ reserve ++ hreserve ++ #[hbeta]
          let cp := base[:25].toArray ++ #[base[25]!,base[26]!,base[27]!,reserve[0]!,
            base[28]!,base[29]!,hreserve[0]!,base[31]!]
          unless params.size == 35 && cp.size == 33 do
            throwError "inverse coefficient profiles: changed coefficient reserve prefix"
          let get (name : Name) := mkAppN (mkConst (operator ++ name)) cp
          let S ← store (out ++ `S) params (get `S) true
          let hS ← store (out ++ `hS) params (get `fact0)
          for (name,value) in [(`AQ,get `AQ),(`AB,get `AB)] do
            discard <| store (out ++ name) params value true
          let fargs := (← inferType (stat `f)).getAppArgs
          unless fargs.size == 7 do throwError "inverse coefficient profiles: changed original family geometry"
          let center := fargs[2]!
          let radius := stat `normRadius
          let one ← mkAppOptM ``OfNat.ofNat #[mkConst `Real,mkNatLit 1,none]
          let profileRadius ← mkAppM ``HAdd.hAdd #[radius,one]
          let buffer ← mkAppM `lt_add_one #[radius]
          let existsInverse := mkAppN
            (mkConst `JanetCartan.FixedDomainInverse.exists_coefficient_pair_inverse_profile)
            #[n,center,radius,profileRadius,primitive `norm_radius_pos,buffer,
              get `AQ,get `AB,get `fact1,get `fact2,beta,reserve[0]!,hbeta]
          let existsInverse ← store (out ++ `exists_inverse_profile) params existsInverse
          select inv params existsInverse
          let ig (name : Name) := mkAppN (mkConst (inv ++ name)) params
          discard <| store (out ++ `Dcoeff) params (ig `D) true
          discard <| store (out ++ `Dcoeff_pos) params (ig `fact0)
          let hlow ← mkAppM `Nat.le_trans
            #[← mkAppM `Nat.le_add_right #[low,dimensionShift],hbeta]
          let high := mkAppN (mkConst (ns ++ `paired_solver_high_profile))
            #[n,get `AQ,get `AB,get `fact1,get `fact2,low,reserve[0]!,hlow]
          let high ← store (out ++ `high_profiles) params high
          let highNonneg := part high 0
          discard <| store (out ++ `Dhigh_nonneg) params highNonneg
          let Dhigh ← forallBoundedTelescope (← inferType highNonneg) (some 1) fun order body => do
            let args := body.getAppArgs
            mkLambdaFVars order args[args.size-1]!
          discard <| store (out ++ `Dhigh) params Dhigh true
          let native := mkAppN (mkConst (current ++ `normalized_solver)) base
          forallBoundedTelescope (← inferType native) (some 6) fun data _ => do
            unless data.size == 6 do throwError "inverse coefficient profiles: changed native history telescope"
            withLocalDeclD `hCoefficient (← mkAppM ``LE.le #[S,data[0]!]) fun hc => do
              let now := params ++ data ++ #[hc]
              let currentArgs := base ++ data
              let cur (name : Name) := mkAppN (mkConst (current ++ name)) currentArgs
              let profiles := mkAppN (get `continuation)
                (#[data[0]!,hc] ++ data[2:6].toArray)
              let profileFamily := .proj ``And 1 (.proj ``And 1 profiles)
              let L := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[data[0]!,data[2]!]
              let hL ← mkAppM (ns ++ `coefficient_scale_one_le_of_two_le)
                #[← mkAppM `le_trans #[hS,hc],data[2]!]
              let Kplus ← mkAppM `Metric.closedBall #[center,profileRadius]
              let hKplus ← mkAppM `ProperSpace.isCompact_closedBall #[center,profileRadius]
              let plusProfiles := mkAppN profileFamily #[Kplus,hKplus]
              let inverseBound := mkAppN (ig `continuation)
                #[fargs[1]!,primitive `coefficient_domain_open,primitive `norm_ball_subset,
                  cur `Q,cur `B,cur `hQ,cur `hB,L,hL,part plusProfiles 0,.proj ``And 1 plusProfiles]
              let inverseBound ← forallBoundedTelescope (← inferType inverseBound) (some 1) fun order _ => do
                let bound ← mkAppM (ns ++ `inverse_coefficient_profile_reassociate)
                  #[mkAppN inverseBound order]
                mkLambdaFVars order bound
              discard <| store (out ++ `inverse_bound) now inverseBound
              let Kcore ← mkAppM `Metric.closedBall #[center,fargs[3]!]
              let hKcore ← mkAppM `ProperSpace.isCompact_closedBall #[center,fargs[3]!]
              let coreProfiles := mkAppN profileFamily #[Kcore,hKcore]
              let highBound := mkAppN (.proj ``And 1 high)
                #[Kcore,cur `Q,cur `B,L,hL,part coreProfiles 0,.proj ``And 1 coreProfiles]
              discard <| store (out ++ `high_nonneg) now (part highBound 0)
              discard <| store (out ++ `high_bound) now (.proj ``And 1 highBound)
              discard <| store (out ++ `coefficient_profiles) now profiles
  logInfo "actual original35 coefficient reserve: inverse Dcoeff and separate ordinary Dhigh before histories, same native Q/full B and original norm/core balls; dynamic fields require only the existing coefficient threshold and original history"

/-- Close the auxiliary-mask geometry on the actual sector-independent
original current and the same positive whole-word phase, at reserve two. -/
elab "construct_original_auxiliary_source_geometry" : command => liftTermElabM do
  let strong := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
  let phaseNS := `JanetCartan.PhysicalPrimary.OriginalPhaseProfiles
  let gradient := `JanetCartan.PhysicalPrimary.OriginalWordGradient
  let masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
  let whole := `JanetCartan.PhysicalPrimary.OriginalIncidence.Whole
  let out := ns ++ `Geometry
  let cut := out ++ `Cutoff
  forallBoundedTelescope (← getConstInfo (strong ++ `S)).type (some 32) fun base _ => do
    unless base.size == 32 do throwError "original auxiliary geometry: expected strong32 prefix"
    let fixed := base[:23].toArray
    let ref := base[:25].toArray
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let mask (name : Name) := mkAppN (mkConst (masks ++ name)) fixed
    let n := mkApp (mkConst ``Nat.succ) base[0]!
    let regularRef := fixed ++ #[base[23]!,mkAppN (mkConst (strong ++ `regular_scale)) ref]
    let cutoffProfiles ← mkAppM (ns ++ `exists_auxiliary_cutoff_profiles) #[stat `χ₃]
    let cutoffProfiles ← store (cut ++ `exists_profiles) fixed cutoffProfiles
    select cut fixed cutoffProfiles
    let cg (name : Name) := mkAppN (mkConst (cut ++ name)) fixed
    let h58 ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit 5,mkNatLit 8])
    let h5 ← mkAppM `Nat.le_trans #[h58,base[29]!]
    let h2 ← mkAppM `Nat.le_refl #[mkNatLit 2]
    let cutoff := mkAppN (mkConst (regular ++ `Phase.χ)) fixed
    forallBoundedTelescope (← inferType cutoff) (some 1) fun patch _ => do
      let params := base ++ patch
      let phaseParams := regularRef ++ patch ++ #[base[25]!,base[26]!,base[27]!,mkNatLit 2,
        base[28]!,base[29]!,h5,h2,base[31]!]
      unless phaseParams.size == 35 do throwError "original auxiliary geometry: changed reserved phase prefix"
      let pg (name : Name) := mkAppN (mkConst (phaseNS ++ name)) phaseParams
      let oldS := mkAppN (mkConst (strong ++ `S)) base
      let profileS := pg `S
      let S ← store (out ++ `S) params (← mkAppM ``max #[oldS,profileS]) true
      let currentThreshold ← store (out ++ `current_threshold) params
        (← mkAppM `le_max_left #[oldS,profileS])
      let profileThreshold ← store (out ++ `phase_threshold) params
        (← mkAppM `le_max_right #[oldS,profileS])
      let hS ← store (out ++ `hS) params (← mkAppM `le_trans #[pg `fact0,profileThreshold])
      discard <| store (out ++ `Aphase) params (pg `Aphase) true
      discard <| store (out ++ `Aphase_nonneg) params (pg `fact1)
      let wa := #[base[0]!,base[1]!,patch[0]!]
      let wg (name : Name) := mkAppN (mkConst (whole ++
        (if name == `lo then `wholeLo else if name == `hi then `wholeHi else name))) wa
      for name in [`lo,`hi] do
        discard <| store (out ++ name) params (wg name) true
      withLocalDeclD `R₀ (mkConst `Real) fun R₀ => do
        withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S,R₀]) fun hR₀ => do
          let hCurrent ← mkAppM `le_trans #[currentThreshold,hR₀]
          let hPhase ← mkAppM `le_trans #[profileThreshold,hR₀]
          let frameBase := mkAppN (mkConst (strong ++ `sourceFrame)) (base ++ #[R₀,hCurrent])
          forallBoundedTelescope (← inferType frameBase) (some 4) fun history _ => do
            unless history.size == 4 do throwError "original auxiliary geometry: changed current history"
            let now := params ++ #[R₀,hR₀] ++ history
            let currentArgs := base ++ #[R₀,hCurrent] ++ history ++ patch
            let frame := mkAppN frameBase (history ++ patch)
            let hFrame := mkAppN (mkConst (strong ++ `sourceFrame_val)) currentArgs
            let profile := mkApp (pg `continuation) frame
            let smooth := part profile 0
            let rawPhase := (← inferType smooth).appArg!
            let bounds := mkAppN (.proj ``And 1 (.proj ``And 1 profile))
              (#[R₀,hPhase] ++ history ++ #[hFrame])
            let subset := mkAppN (mkConst (phaseNS ++ `word_box_subset)) (fixed ++ patch)
            let sets := (← inferType subset).getAppArgs
            let small := sets[sets.size-2]!
            let scale := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[R₀,history[0]!]
            let restricted := mkAppN (mkConst (phaseNS ++ `restrict_original_joint_profiles))
              #[base[0]!,base[1]!,patch[0]!,small,subset,rawPhase,pg `Aphase,scale,mkNatLit 2,smooth,bounds]
            let restricted ← store (out ++ `word_profiles) now restricted
            let jets := .proj ``And 1 (.proj ``And 1 restricted)
            let φ := mkAppN (mkConst (gradient ++ `φ)) currentArgs
            let hgrad := mkAppN (mkConst (gradient ++ `physical_gradient_range)) currentArgs
            let V := small.getAppArgs[small.getAppArgs.size-1]!.appArg!
            let physicalRadius := Expr.proj
              `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily 6 (stat `f)
            let hL ← mkAppM (ns ++ `coefficient_scale_one_le_of_two_le)
              #[← mkAppM `le_trans #[hS,hR₀],history[0]!]
            let hcut := mkAppN (cg `continuation) #[scale,hL]
            let actual := mkAppN (mkConst (ns ++ `source_geometry_of_joint_profiles))
              #[n,stat `χ₃,φ,smooth,V,stat `r,physicalRadius,wg `lo,wg `hi,scale,
                pg `Aphase,cg `X,stat `hrU,mask `χ₃_support_chart,wg `fact0,wg `fact1,
                hL,pg `fact1,cg `fact0,hcut,hgrad,jets]
            discard <| store (out ++ `source_geometry) now actual
  logInfo "actual original39 auxiliary source geometry: SAME chi3, canonical positive phase and whole gradient band; reserve2 jets, original min-r/physical-radius support, all constants and maximum before history"


/-- Name-directed application of a concrete leaf while retaining its own
inferred types and instances. This is metadata, not a mathematical hypothesis. -/
private def sourceRealizationLeaf (name : Name) (values : Array (Name × Expr)) : MetaM Expr := do
  let inputs ← forallTelescope (← getConstInfo name).type fun args _ => do
    args.mapM fun arg => do
      let userName ← arg.fvarId!.getUserName
      return (values.find? (fun item => item.1 == userName)).map Prod.snd
  mkAppOptM name inputs

/-- The exact native inverse ball, before source, history, and orders. -/
elab "retain_original_source_domain" : command => liftTermElabM do
  let output := ns ++ `Source
  forallBoundedTelescope (← getConstInfo (regular ++ `χ₃)).type (some 23) fun fixed cutoffType => do
    unless fixed.size == 23 && cutoffType.getAppNumArgs > 0 do
      throwError "actual source domain: changed original23 cutoff type"
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let center := cutoffType.getAppArgs.back!
    let W ← mkAppM `Metric.ball #[center,stat `normRadius]
    let openW ← sourceRealizationLeaf `Metric.isOpen_ball #[(`x,center),(`ε,stat `normRadius)]
    let hW ← mkAppM `IsOpen.measurableSet #[openW]
    discard <| store (output ++ `W) fixed W true
    discard <| store (output ++ `W_measurable) fixed hW

/-- Open the literal original amplitude at ONE parameter, retaining the raw
original53 witnesses rather than synthesizing any native analytic data. -/
private def withActualSourceSlice
    (k : Array Expr → Expr → Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  let output := ns ++ `Source
  forallBoundedTelescope (← getConstInfo (output ++ `a)).type (some 53) fun p amplitudeType => do
    unless p.size == 53 do throwError "actual source slice: expected original53"
    let .forallE _ product _ _ := amplitudeType | throwError "actual source slice: missing joint amplitude"
    unless product.isAppOfArity ``Prod 2 do throwError "actual source slice: changed original product domain"
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let E := product.getAppArgs[0]!
    let Par := product.getAppArgs[1]!
    let a := mkAppN (mkConst (output ++ `a)) p
    withLocalDeclD `c Par fun c => do
      let amplitude ← withLocalDeclD `x E fun x => do
        mkLambdaFVars #[x] (mkApp a (← mkAppM ``Prod.mk #[x,c]))
      k p n E Par c amplitude

/-- The existing source's empty parameter jet is the literal physical
amplitude; no new representative is selected. -/
elab "retain_original_source_amplitude_memLp" : command => liftTermElabM do
  let output := ns ++ `Source
  withActualSourceSlice fun p n _ Par c _ => do
    let nil := mkApp (mkConst ``List.nil [Level.zero]) Par
    let member := mkAppN (mkConst (output ++ `parameter_jet_memLp)) (p ++ #[c,nil])
    let leaf := ns ++ `amplitude_memLp_of_empty_source_jet
    let inputs := #[n,mkAppN (mkConst (output ++ `a)) p,c,member]
    discard <| storeExpectedSource (output ++ `amplitude_memLp) (p.push c) (mkAppN (mkConst leaf) inputs)
      (← sourceForallResult (← getConstInfo leaf).type inputs)

/-- A type-directed application at the actual original forcing. In particular
neither the volume measure, the topologies for phase continuity, nor the
physical amplitudes are re-inferred from the large native choice terms. -/
private def withActualSourceForcing
    (k : Array Expr → Array Expr → Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  let output := ns ++ `Source
  let leaf := ns ++ `original_source_memberships_of_forcing_eq
  let leafType := (← getConstInfo leaf).type
  withActualSourceSlice fun p n E _ c amplitude => do
    let χ := mkAppN (mkConst (regular ++ `χ₃)) p[:23].toArray
    let member := mkAppN (mkConst (output ++ `amplitude_memLp)) (p.push c)
    withLocalDeclD `φ (← mkArrow E (mkConst `Real)) fun φ => do
      let pre := #[n,χ,amplitude,member,φ]
      let .forallE _ continuity _ _ ← sourceForallResult leafType pre
        | throwError "actual source: changed original phase-continuity interface"
      withLocalDeclD `hφ continuity fun hφ => do
        withLocalDeclD `ρ (mkConst `Real) fun ρ => do
          let forcing := p ++ #[c,φ,ρ]
          let physical := p ++ #[c,φ,hφ,ρ]
          let raw := mkAppN (mkConst (output ++ `rawForcing)) forcing
          let he := mkAppN (mkConst (output ++ `forcing_eq)) forcing
          let inputs := pre ++ #[hφ,ρ,raw]
          let .forallE _ equality result _ ← sourceForallResult leafType inputs
            | throwError "actual source: missing supplied native forcing identity"
          let pair := mkAppN (mkConst leaf) (inputs.push he)
          k p physical pair (result.instantiate1 he) he equality

/-- Membership of both descriptions of this single actual carrier forcing. -/
elab "retain_original_source_memberships" : command => liftTermElabM do
  let output := ns ++ `Source
  withActualSourceForcing fun _ physical pair pairType _ _ => do
    discard <| storeExpectedSource (output ++ `forcing_memLp) physical (.proj ``And 0 pair) (← sourceConj pairType)
    discard <| storeExpectedSource (output ++ `modulated_memLp) physical (.proj ``And 1 pair) (← sourceConj pairType true)

/-- Export precisely restrictL2 W (the actual raw carrier class) and its
exact identity with the chi3-neutral source required by the full inverse. -/
elab "retain_original_source_realization" : command => liftTermElabM do
  let output := ns ++ `Source
  withActualSourceForcing fun p physical _ _ he equality => do
    unless equality.isAppOfArity ``Eq 3 do throwError "actual source: changed carrier equality"
    let f := equality.getAppArgs
    let W := mkAppN (mkConst (output ++ `W)) p[:23].toArray
    let rawMem := mkAppN (mkConst (output ++ `forcing_memLp)) physical
    let modMem := mkAppN (mkConst (output ++ `modulated_memLp)) physical
    let reverse := mkAppN (mkConst ``Eq.symm [Level.one]) #[f[0]!,f[1]!,f[2]!,he]
    let leaf := ns ++ `restrict_original_source_classes_of_eq
    let inputs := #[p[0]!,W,f[2]!,f[1]!,rawMem,modMem,reverse]
    let classEq := mkAppN (mkConst leaf) inputs
    let classType ← sourceForallResult (← getConstInfo leaf).type inputs
    unless classType.isAppOfArity ``Eq 3 do throwError "actual source: changed local class equality"
    let sides := classType.getAppArgs
    let realization ← storeExpectedSource (output ++ `realization) physical sides[1]! sides[0]! true
    discard <| storeExpectedSource (output ++ `realization_eq) physical classEq
      (mkAppN classType.getAppFn #[sides[0]!,realization,sides[2]!])
    for name in [`W,`W_measurable,`amplitude_memLp,`rawForcing,`forcing_memLp,`realization,
        `modulated_memLp,`realization_eq] do
      unless (← getEnv).isImportedConst (output ++ name) do
        addDocStringCore (output ++ name) "Same unmasked original positive carrier forcing and its exact class on the native inverse ball, shared by the finite positive words and full-inverse tail (app:ch_regular:eq:inverse-remainder)."
  logInfo "actual original53 source realization: literal existing raw positive carrier, same original local L2 class and chi3-neutral class identity"

/-- Fix the data-only original index and its primitive scalar admission BEFORE
selecting one common threshold. This is preparation, not the observed remainder. -/
elab "retain_original_source_family_window" : command => liftTermElabM do
  let actual := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
  let masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
  let family := ns ++ `Family
  forallBoundedTelescope (← getConstInfo (actual ++ `full_source_profiles)).type (some 53) fun p _ => do
    unless p.size == 53 do throwError "original remainder family: expected unchanged source53"
    let fixed := p[:39].toArray
    let original := mkAppN (mkConst (actual ++ `full_source_profiles)) p
    let parameterZeroType ← inferType (.proj ``And 1 original)
    let cutoffName := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.parameterCutoff
    let some cutoff := parameterZeroType.find? (fun e => e.isAppOfArity cutoffName 4)
      | throwError "original remainder family: cannot identify SAME original parameter cutoff"
    let cutoffArgs := cutoff.getAppArgs
    let patch := cutoffArgs[2]!
    let cell := cutoffArgs[3]!
    for value in #[patch,cell] do
      if (value.find? (fun e => p[39:].toArray.contains e)).isSome then
        throwError "original remainder family: original patch/cell depends on history"
    discard <| store (family ++ `patch) fixed patch true
    discard <| store (family ++ `cell) fixed cell true
    let maskArgs := p[:23].toArray ++ #[patch,cell]
    for (name,asDef) in [(`V,true),(`V_open,false)] do
      discard <| store (family ++ name) fixed (mkAppN (mkConst (masks ++ name)) maskArgs) asDef
  logInfo "fixed original39 selected patch, cell and observation window"

/-- The actual scalar subtype is already an explicit Subtype; extracting its
arguments preserves the original span predicate without unfolding the span. -/
elab "retain_original_source_family_admission" : command => liftTermElabM do
  let actual := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
  let historyNS := `JanetCartan.PhysicalPrimary.OriginalHistoryFamily
  let family := ns ++ `Family
  forallBoundedTelescope (← getConstInfo (actual ++ `full_source_profiles)).type (some 53) fun p _ => do
    let fixed := p[:39].toArray
    let scalarType ← inferType p[49]!
    unless scalarType.isAppOfArity ``Subtype 2 do
      throwError "original remainder family: original scalar is not the expected span subtype"
    let scalarArgs := scalarType.getAppArgs
    let scalarSpace := scalarArgs[0]!
    let scalarPredicate := scalarArgs[1]!
    discard <| store (family ++ `ScalarSpace) fixed scalarSpace true
    discard <| store (family ++ `scalarPredicate) fixed scalarPredicate true
    if (scalarType.find? (fun e => p[39:].toArray.contains e)).isSome then
      throwError "original remainder family: scalar ambient type depends on history"
    let payload := mkApp2 (mkConst ``Prod [Level.zero,Level.zero]) (mkConst `Real) scalarSpace
    let I := mkApp2 (mkConst (historyNS ++ `RawIndex)) p[0]! payload
    let I ← store (family ++ `RawIndex) fixed I true
    withLocalDeclD `i I fun i => do
      let field (name : Name) := mkAppN (mkConst (historyNS ++ `RawIndex ++ name)) #[p[0]!,payload,i]
      let datum := field `datum
      let tau := Expr.proj ``Prod 0 datum
      let scalar := Expr.proj ``Prod 1 datum
      let highType ← inferType p[52]!
      let highType := highType.replace fun e =>
        if e.isAppOfArity ``Subtype.val 3 && e.getAppArgs.back! == p[49]! then some scalar
        else match e with
          | .proj ``Subtype 0 value => if value == p[49]! then some scalar else none
          | _ => none
      let highType := highType.replaceFVars #[p[45]!,p[50]!] #[field `K,field `amplitude]
      if (highType.find? (fun e => p[39:].toArray.contains e)).isSome then
        throwError "original remainder family: scalar profile retains current/history/proof data"
      let positive ← mkAppM ``LT.lt #[← mkNumeral (mkConst `Real) 0,tau]
      let member := mkApp scalarPredicate scalar
      let primitive := mkApp2 (mkConst ``And) positive (mkApp2 (mkConst ``And) member highType)
      let primitive ← mkLambdaFVars #[i] primitive
      discard <| store (family ++ `SourceAdmission) fixed primitive true
  logInfo "fixed original39 raw source data and primitive admission before any threshold"

/-- Join the actual source, observation, geometry and coefficient thresholds
on the already fixed original raw family, before any history or response order. -/
elab "prepare_original_remainder_family" : command => liftTermElabM do
  let actual := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
  let strong := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
  let observation := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
  let family := ns ++ `Family
  forallBoundedTelescope (← getConstInfo (actual ++ `S)).type (some 39) fun p _ => do
    unless p.size == 39 do throwError "original remainder threshold: changed fixed original39"
    let fixed := p
    let patch := mkAppN (mkConst (family ++ `patch)) fixed
    let partialStrong := mkAppN (mkConst (strong ++ `S)) p[:24].toArray
    let .forallE _ sigmaType _ _ ← whnf (← inferType partialStrong)
      | throwError "original remainder family: missing common strong source admission"
    withLocalDeclD `hStrongSigma sigmaType fun hStrongSigma => do
      let low := mkApp (mkConst `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder) p[0]!
      let beta := mkApp2 (mkConst ``Nat.add) low (mkApp2 (mkConst ``Nat.add) p[0]! (mkNatLit 2))
      let betaPlus := mkApp2 (mkConst ``Nat.add) beta (mkNatLit 2)
      withLocalDeclD `hInverseReserve (← mkAppM ``LE.le #[betaPlus,p[28]!]) fun hInverseReserve => do
        let params := fixed ++ #[hStrongSigma,hInverseReserve]
        let orders := mkAppN (mkConst (ns ++ `native_orders_of_inverse_reserve))
          #[p[0]!,p[28]!,hInverseReserve]
        let reference := p[:24].toArray.push hStrongSigma
        let numeric := #[p[26]!,p[27]!,p[28]!,p[29]!,part orders 0,part orders 1,p[31]!]
        let currentBase := reference ++ numeric
        let regularReference := p[:24].toArray.push
          (mkAppN (mkConst (strong ++ `regular_scale)) reference)
        let regularBase := regularReference ++ numeric
        let phaseBase := currentBase.push patch
        let hbeta ← mkAppM `Nat.le_refl #[beta]
        let coefficientBase := regularBase ++ #[beta,.proj ``And 1 (.proj ``And 1 orders),hbeta]
        unless currentBase.size == 32 && phaseBase.size == 33 && coefficientBase.size == 35 do
          throwError "original remainder family: changed fixed original data spines"
        let sourceS := mkAppN (mkConst (actual ++ `S)) fixed
        let observationS := mkAppN (mkConst (observation ++ `S)) phaseBase
        let geometryS := mkAppN (mkConst (ns ++ `Geometry.S)) phaseBase
        let coefficientS := mkAppN (mkConst (ns ++ `Coefficients.S)) coefficientBase
        let right ← mkAppM ``max #[geometryS,coefficientS]
        let tail ← mkAppM ``max #[observationS,right]
        let S ← store (family ++ `S) params (← mkAppM ``max #[sourceS,tail]) true
        let hSource ← store (family ++ `source_threshold) params
          (← mkAppM `le_max_left #[sourceS,tail])
        let hTail ← mkAppM `le_max_right #[sourceS,tail]
        let hObservation ← mkAppM `le_trans #[← mkAppM `le_max_left #[observationS,right],hTail]
        discard <| store (family ++ `observation_threshold) params hObservation
        let hRight ← mkAppM `le_trans #[← mkAppM `le_max_right #[observationS,right],hTail]
        discard <| store (family ++ `geometry_threshold) params
          (← mkAppM `le_trans #[← mkAppM `le_max_left #[geometryS,coefficientS],hRight])
        discard <| store (family ++ `coefficient_threshold) params
          (← mkAppM `le_trans #[← mkAppM `le_max_right #[geometryS,coefficientS],hRight])
        discard <| store (family ++ `current_threshold) params
          (← mkAppM `le_trans #[mkAppN (mkConst (observation ++ `current_threshold)) phaseBase,hObservation])
        discard <| store (family ++ `hS) params
          (← mkAppM `le_trans #[mkAppN (mkConst (actual ++ `hS)) fixed,hSource])
        let type ← inferType S
        unless type.isConstOf `Real do throwError "original remainder family: common threshold is not real"
  logInfo "original source family PREPARATION ONLY: fixed data-only RawIndex39, primitive SourceAdmission39, ONE S41 before all response orders/histories; same original patch/cell/source scalar and native current, coefficient and phase objects; no remainder conclusion yet"

/-- Compose concrete real inequalities without a metavariable comparison of
large native threshold choice expressions. -/
private def familyRealTrans (a b c hab hbc : Expr) : MetaM Expr := do
  let real := mkConst `Real
  let order ← synthInstance (mkApp (mkConst `Preorder [Level.zero]) real)
  return mkAppN (mkConst `le_trans [Level.zero]) #[real,order,a,b,c,hab,hbc]

private def familyTail (e : Expr) : Nat → Expr
  | 0 => e
  | k+1 => familyTail (.proj ``And 1 e) k

private def familyNonnegativeFunction (h : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType h) (some 1) fun order body => do
    let args := body.getAppArgs
    mkLambdaFVars order args[args.size-1]!

/-- Metadata-only assembly of the unchanged actual objects at an ALREADY
admitted raw tuple. The mathematical index remains OriginalHistoryFamily.RawIndex.
This creates no new phase, scalar, current, residual, solver or reference. -/
private def actualRemainderContext (p : Array Expr) (hStrongSigma hInverseReserve : Expr)
    (i hAdmitted hSource : Expr) : MetaM (Array (Name × Expr)) := do
  let strong := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
  let observation := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
  let actual := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
  let historyNS := `JanetCartan.PhysicalPrimary.OriginalHistoryFamily
  let family := ns ++ `Family
  unless p.size == 39 do throwError "original family context: expected fixed original39 data"
  let fixed := p
  let prior := fixed ++ #[hStrongSigma,hInverseReserve]
  let fg (name : Name) := mkAppN (mkConst (family ++ name)) prior
  let scalarSpace := mkAppN (mkConst (family ++ `ScalarSpace)) fixed
  let scalarPredicate := mkAppN (mkConst (family ++ `scalarPredicate)) fixed
  let payload := mkApp2 (mkConst ``Prod [Level.zero,Level.zero]) (mkConst `Real) scalarSpace
  let field (name : Name) := mkAppN (mkConst (historyNS ++ `RawIndex ++ name)) #[p[0]!,payload,i]
  let R₀ := field `R₀
  let stage := field `length
  let K := field `K
  let datum := field `datum
  let tau := Expr.proj ``Prod 0 datum
  let rawScalar := Expr.proj ``Prod 1 datum
  let scalar := mkAppN (mkConst ``Subtype.mk [Level.one])
    #[scalarSpace,scalarPredicate,rawScalar,part hSource 1]
  let hR₀ := part hAdmitted 0
  let data := #[stage,field `u,field `ell,part hAdmitted 1]
  let low := mkApp (mkConst `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder) p[0]!
  let beta := mkApp2 (mkConst ``Nat.add) low (mkApp2 (mkConst ``Nat.add) p[0]! (mkNatLit 2))
  let orders := mkAppN (mkConst (ns ++ `native_orders_of_inverse_reserve))
    #[p[0]!,p[28]!,hInverseReserve]
  let reference := p[:24].toArray.push hStrongSigma
  let numeric := #[p[26]!,p[27]!,p[28]!,p[29]!,part orders 0,part orders 1,p[31]!]
  let currentBase := reference ++ numeric
  let regularReference := p[:24].toArray.push
    (mkAppN (mkConst (strong ++ `regular_scale)) reference)
  let regularBase := regularReference ++ numeric
  let patch := mkAppN (mkConst (family ++ `patch)) fixed
  let phaseBase := currentBase.push patch
  let hbeta ← mkAppM `Nat.le_refl #[beta]
  let coefficientBase := regularBase ++ #[beta,familyTail orders 2,hbeta]
  let sourceS := mkAppN (mkConst (actual ++ `S)) fixed
  let currentS := mkAppN (mkConst (strong ++ `S)) currentBase
  let observationS := mkAppN (mkConst (observation ++ `S)) phaseBase
  let geometryS := mkAppN (mkConst (ns ++ `Geometry.S)) phaseBase
  let coefficientS := mkAppN (mkConst (ns ++ `Coefficients.S)) coefficientBase
  let hSourceR ← familyRealTrans sourceS (fg `S) R₀ (fg `source_threshold) hR₀
  let hCurrentR ← familyRealTrans currentS (fg `S) R₀ (fg `current_threshold) hR₀
  let hObservationR ← familyRealTrans observationS (fg `S) R₀ (fg `observation_threshold) hR₀
  let hGeometryR ← familyRealTrans geometryS (fg `S) R₀ (fg `geometry_threshold) hR₀
  let hCoefficientR ← familyRealTrans coefficientS (fg `S) R₀ (fg `coefficient_threshold) hR₀
  let hRegularR := mkAppN (mkConst (strong ++ `regular_reached)) (currentBase ++ #[R₀,hCurrentR])
  let regArgs := regularBase ++ #[R₀,hRegularR] ++ data
  let obsArgs := phaseBase ++ #[R₀,hObservationR] ++ data
  let geoArgs := phaseBase ++ #[R₀,hGeometryR] ++ data
  let coeffArgs := coefficientBase ++ #[R₀,hRegularR] ++ data ++ #[hCoefficientR]
  let srcArgs := fixed ++ #[R₀,hSourceR] ++ data ++
    #[K,part hAdmitted 3,tau,part hSource 0,scalar,field `amplitude,familyTail hAdmitted 5,familyTail hSource 2]
  unless regArgs.size == 38 && obsArgs.size == 39 && geoArgs.size == 39 && coeffArgs.size == 42 && srcArgs.size == 53 do
    throwError "original family context: changed unchanged-object argument spines"
  let native (name : Name) := mkAppN (mkConst (ns ++ `Native ++ name)) regArgs
  let obs (name : Name) := mkAppN (mkConst (observation ++ name)) obsArgs
  let geo (name : Name) := mkAppN (mkConst (ns ++ `Geometry ++ name)) geoArgs
  let coeff (name : Name) := mkAppN (mkConst (ns ++ `Coefficients ++ name)) coeffArgs
  let source (name : Name) := mkAppN (mkConst (ns ++ `Source ++ name)) srcArgs
  let L := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[R₀,stage]
  let amplitude ← withLocalDeclD `c (← inferType (obs `φ)).bindingDomain! fun c => do
    let .forallE _ E _ _ ← whnf (← inferType (mkApp (obs `φ) c))
      | throwError "original family context: missing physical phase domain"
    withLocalDeclD `x E fun x => do
      mkLambdaFVars #[c,x] (mkApp (source `a) (← mkAppM ``Prod.mk #[x,c]))
  let result := #[
    (`d,p[0]!),(`R₀,R₀),(`stage,stage),(`ρ,field `lam),(`K,K),(`L,L),(`τsource,tau),(`size,field `amplitude),
    (`hρ,part hAdmitted 2),(`hLK,part hAdmitted 3),(`hwindow,part hAdmitted 4),
    (`R,native `Rcomplex),(`hreal,native `residual_real),(`hR,native `residual_contraction),
    (`hKloc,native `real_half_bound),(`ha,native `coefficient_nonneg),(`ham,native `coefficient_monotone),
    (`hgain,native `gain),(`Op,native `pairedSolver),(`hsolver,native `paired_solver_tame),
    (`φ,obs `φ),(`joint_phase_smooth,obs `joint_smooth),(`phase_support,obs `support),(`global_phase_profiles,obs `joint_profiles),
    (`geometry,geo `source_geometry),(`hcoeff,coeff `inverse_bound),(`hhigh,coeff `high_nonneg),(`hcoefficient,coeff `high_bound),
    (`f,amplitude),(`joint_source_smooth,source `smooth),(`source_support,source `support),
    (`source_jet_memLp,source `parameter_jet_memLp),(`source_jet_fourier,source `parameter_jet_fourier),
    (`source_jet_profile,source `parameter_jet_profile),(`hK,source `scale_one_le),(`hA,source `amplitude_nonneg),
    (`amplitude_memLp,source `amplitude_memLp),(`rawForcing,source `rawForcing),
    (`forcing_memLp,source `forcing_memLp),(`realization,source `realization),
    (`modulated_memLp,source `modulated_memLp),(`realization_eq,source `realization_eq),
    (`forcing_eq,source `forcing_eq)]
  let coefficient ← familyNonnegativeFunction (native `coefficient_nonneg)
  let high ← familyNonnegativeFunction (coeff `high_nonneg)
  let aType ← inferType (source `amplitude_nonneg)
  let A := aType.getAppArgs.back!
  let hL ← mkAppM (ns ++ `coefficient_scale_one_le_of_two_le)
    #[← familyRealTrans (← mkNumeral (mkConst `Real) 2) (fg `S) R₀ (fg `hS) hR₀,stage]
  return result ++ #[(`a,coefficient),(`high,high),(`A,A),(`hL,hL)]

private def familyGet (values : Array (Name × Expr)) (key : Name) : MetaM Expr := do
  match values.find? (fun item => item.1 == key) with
  | some (_,value) => return value
  | none => throwError "original remainder family: missing actual field {key}"

/-- Every native full-tail forcing field is a direct specialization of the
same named Source.realization/class identity as the finite positive words. -/
private def actualOriginalForcing (ctx : Array (Name × Expr)) (c : Expr) : MetaM (Array (Name × Expr)) := do
  let get := familyGet ctx
  let φ := mkApp (← get `φ) c
  let continuous ← mkAppM `Continuous.uncurry_left #[c,← mkAppM `ContDiff.continuous #[← get `joint_phase_smooth]]
  let point := #[c,φ,continuous,← get `ρ]
  return #[(`hmphysical,mkAppN (← get `modulated_memLp) point),
    (`source,mkAppN (← get `realization) point),(`hsource,mkAppN (← get `realization_eq) point)]

/-- Apply an existing proposition-valued leaf with explicitly named actual
inputs; all omitted type and instance parameters are inferred by its own API. -/
private def familyNamedApp (name : Name) (values : Array (Name × Expr)) : MetaM Expr := do
  let inputs ← forallTelescope (← getConstInfo name).type fun args _ => do
    args.mapM fun arg => do
      let userName ← arg.fvarId!.getUserName
      return (values.find? (fun item => item.1 == userName)).map Prod.snd
  mkAppOptM name inputs

/-- Retain the original-data scalar/profile/support inputs of the observed
producer. Every field is fixed before histories, response orders and frequencies. -/
elab "retain_original_family_static_inputs" : command => liftTermElabM do
  let family := ns ++ `Family
  let output := family ++ `Static
  let observation := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
  let strong := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
  let masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
  let sourceNS := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
  forallBoundedTelescope (← getConstInfo (family ++ `S)).type (some 41) fun all _ => do
    unless all.size == 41 do throwError "original family statics: expected ONE fixed original41 threshold"
    let p := all[:39].toArray
    let fixed := p[:23].toArray
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let patch := mkAppN (mkConst (family ++ `patch)) p
    let cell := mkAppN (mkConst (family ++ `cell)) p
    let low := mkApp (mkConst `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder) p[0]!
    let beta := mkApp2 (mkConst ``Nat.add) low (mkApp2 (mkConst ``Nat.add) p[0]! (mkNatLit 2))
    let orders := mkAppN (mkConst (ns ++ `native_orders_of_inverse_reserve)) #[p[0]!,p[28]!,all[40]!]
    let reference := p[:24].toArray.push all[39]!
    let numeric := #[p[26]!,p[27]!,p[28]!,p[29]!,part orders 0,part orders 1,p[31]!]
    let currentBase := reference ++ numeric
    let regularBase := p[:24].toArray ++ #[mkAppN (mkConst (strong ++ `regular_scale)) reference] ++ numeric
    let phaseBase := currentBase.push patch
    let coeffBase := regularBase ++ #[beta,familyTail orders 2,← mkAppM `Nat.le_refl #[beta]]
    let obs (name : Name) := mkAppN (mkConst (observation ++ name)) phaseBase
    let geo (name : Name) := mkAppN (mkConst (ns ++ `Geometry ++ name)) phaseBase
    let coeff (name : Name) := mkAppN (mkConst (ns ++ `Coefficients ++ name)) coeffBase
    let cg (name : Name) := mkAppN (mkConst (ns ++ `Geometry.Cutoff ++ name)) fixed
    let χ₂ ← mkAppM `ContDiffBump.toFun #[stat `χ₂]
    let χ₃ ← mkAppM `ContDiffBump.toFun #[stat `χ₃]
    let center := (← inferType (stat `χ₃)).getAppArgs.back!
    let W := mkAppN (mkConst (ns ++ `Source.W)) fixed
    let hW := mkAppN (mkConst (ns ++ `Source.W_measurable)) fixed
    let X ← mkAppM `tsupport #[χ₂]
    let hXbase ← mkAppM `ContDiffBump.hasCompactSupport #[stat `χ₂]
    let .forallE _ finiteDimension _ .instImplicit ← inferType hXbase
      | throwError "original family statics: changed finite-dimensional compact-support API"
    let hX := mkApp hXbase (← synthInstance finiteDimension)
    let S ← mkAppM `tsupport #[χ₃]
    let hSU := mkAppN (mkConst (masks ++ `χ₃_support_chart)) fixed
    let hSW ← mkAppM `Set.Subset.trans #[hSU,stat `hUW]
    let hCgain := mkAppN (mkConst (ns ++ `Native.gain_cost_nonneg)) fixed
    let Cgain ← familyNonnegativeFunction hCgain
    let pairedD := mkAppN (mkConst (ns ++ `Paired.D)) fixed
    let pairedNN := mkAppN (mkConst (ns ++ `Paired.fact0)) fixed
    let Dnn ← forallBoundedTelescope (← inferType (coeff `Dcoeff_pos)) (some 1) fun j _ => do
      mkLambdaFVars j (← mkAppM `le_of_lt #[mkAppN (coeff `Dcoeff_pos) j])
    let Pphase ← withLocalDeclD `j (mkConst ``Nat) fun j => do
      mkLambdaFVars #[j] (mkApp (geo `Aphase) (mkApp (mkConst ``Nat.succ) j))
    let one ← mkNumeral (mkConst `Real) 1
    let two ← mkNumeral (mkConst `Real) 2
    let half ← mkAppM ``HDiv.hDiv #[one,two]
    let hHalf ← mkAppM (ns ++ `lt_one_of_half_bound) #[← mkAppM `le_refl #[half]]
    let V := mkAppN (mkConst (family ++ `V)) p
    let hV := mkAppN (mkConst (family ++ `V_open)) p
    let Vsubset := mkAppN (mkConst (masks ++ `V_subset_wholeWindow)) (fixed ++ #[patch,cell])
    let entries := #[
      (`W,W,true),(`hW,hW,false),(`X,X,true),(`hX,hX,false),(`S,S,true),(`hSW,hSW,false),
      (`χ,χ₃,true),(`χ₃,stat `χ₃,true),(`x,center,true),(`hχ₃,hSW,false),
      (`V,V,true),(`hV,hV,false),(`V_subset_wholeWindow,Vsubset,false),
      (`Cgain,Cgain,true),(`hCgain,hCgain,false),(`Dcoeff,coeff `Dcoeff,true),(`hDcoeff,Dnn,false),
      (`b,beta,true),(`θ,half,true),(`hθ,hHalf,false),
      (`Hphase,obs `H,true),(`hHphase,obs `H_nonneg,false),
      (`Pobs,obs `H,true),(`hPobs,obs `H_nonneg,false),
      (`Xφ,obs `X,true),(`hXφ,obs `X_compact,false),
      (`Csource,mkAppN (mkConst (sourceNS ++ `Csource)) p,true),
      (`gap,geo `lo,true),(`upper,geo `hi,true),(`Pphase,Pphase,true),(`Xcut,cg `X,true),
      (`Csolver,pairedD,true),(`hCsolver,pairedNN,false),
      (`Ccoefficient,coeff `Dhigh,true),(`hCcoefficient,coeff `Dhigh_nonneg,false)]
    for (name,value,asDef) in entries do
      discard <| store (output ++ name) all value asDef
    let I := mkAppN (mkConst (family ++ `RawIndex)) p
    unless (← inferType I).isSort do throwError "original family statics: RawIndex is not a fixed type"
  logInfo "original family static inputs ONLY: same W/chi3, chi2 support, full observation support, global/all-order phase and original source costs, native beta/gain/paired-solver and separate coefficient costs, all before histories and response orders"

/-- Weaken the SAME all-point phase bound from the native coefficient scale
to the admitted source scale, also on the physical-cutoff shoulders. -/
private def familyGlobalPhaseBound (static : Name → Expr) (ctx : Array (Name × Expr))
    (c x j : Expr) : MetaM Expr := do
  let get := familyGet ctx
  let nonnegativeOne ← familyNamedApp `zero_le_one #[(`α,mkConst `Real)]
  let nonnegativeL ← mkAppM `le_trans #[nonnegativeOne,← get `hL]
  let power ← mkAppM `pow_le_pow_left₀ #[nonnegativeL,← get `hLK,j]
  let multiply ← mkAppM `mul_le_mul_of_nonneg_left #[power,mkApp (static `hHphase) j]
  mkAppM `le_trans #[mkAppN (← get `global_phase_profiles) #[c,x,j],multiply]

private def originalFamilyStaticNames : Array Name := #[`W,`hW,`Cgain,`Dcoeff,`b,`θ,`hθ,`hCgain,`hDcoeff,
  `V,`X,`hV,`hX,`Hphase,`hHphase,`Csource,`S,`gap,`upper,`Pphase,`Xcut,`hSW,
  `x,`χ₃,`hχ₃,`Xφ,`hXφ,`Pobs,`Csolver,`Ccoefficient,`hPobs,`hCsolver,`hCcoefficient]

/-- Fill one concrete analytic field at an admitted raw member. The source39,
native38, observation39 and coefficient42 have already been specialized ONCE
at this member. This function does not select an object or assume a bound. -/
private def originalFamilyPointField (name body : Expr) (key : Name)
    (static : Name → Expr) (ctx : Array (Name × Expr)) : MetaM Expr := do
  let get := familyGet ctx
  let direct := #[`R,`hreal,`hR,`a,`hKloc,`ha,`ham,`hgain,`ρ,`A,`K,`L,`hρ,`hA,`hK,
    `φ,`f,`hcoeff,`hLK,`hwindow,`Op,`high,`hhigh,`hcoefficient,`hsolver]
  if direct.contains key then return ← get key
  if key == `χ then return static `χ
  if key == `hφ || key == `hf then do
    unless body.isAppOf `ContDiffOn do
      throwError "original observed family: changed smooth-on field {key}"
    return ← smoothOn (← get (if key == `hφ then `joint_phase_smooth else `joint_source_smooth))
      body.getAppArgs.back!
  if key == `hs || key == `hsφ then
    return ← forallBoundedTelescope body (some 2) fun point _ => do
      unless point.size == 2 do throwError "original observed family: changed support field"
      mkLambdaFVars point (mkApp (← get (if key == `hs then `source_support else `phase_support)) point[0]!)
  if key == `hm then
    return ← forallBoundedTelescope body (some 3) fun point _ => do
      unless point.size == 3 do throwError "original observed family: changed source membership field"
      mkLambdaFVars point (mkAppN (← get `source_jet_memLp) #[point[0]!,point[2]!])
  if key == `hmem then
    return ← forallBoundedTelescope body (some 4) fun point _ => do
      unless point.size == 4 do throwError "original observed family: changed source Fourier field"
      let hm := mkAppN (← get `source_jet_memLp) #[point[0]!,point[2]!]
      mkLambdaFVars point (mkAppN (← get `source_jet_fourier) #[point[0]!,point[2]!,point[3]!,hm])
  if key == `hprofile then
    return ← forallBoundedTelescope body (some 5) fun point _ => do
      unless point.size == 5 do throwError "original observed family: changed source profile field"
      let hm := mkAppN (← get `source_jet_memLp) #[point[0]!,point[2]!]
      mkLambdaFVars point (mkAppN (← get `source_jet_profile) #[point[0]!,point[2]!,point[3]!,point[4]!,hm])
  if key == `hphase || key == `hphaseObs then
    return ← forallBoundedTelescope body (some (if key == `hphase then 5 else 6)) fun point _ => do
      unless point.size == (if key == `hphase then 5 else 6) do
        throwError "original observed family: changed global phase profile field"
      mkLambdaFVars point (← familyGlobalPhaseBound static ctx point[0]! point[2]! point[4]!)
  if key == `g then
    return ← forallBoundedTelescope body (some 2) fun point _ => do
      unless point.size == 2 do throwError "original observed family: changed source geometry field"
      let whole := mkAppN (static `V_subset_wholeWindow) #[point[0]!,point[1]!]
      mkLambdaFVars point (mkAppN (← get `geometry) #[point[0]!,whole])
  if key == `source || key == `hmphysical || key == `hsource then
    return ← forallBoundedTelescope body (some (if key == `hsource then 2 else 1)) fun point _ => do
      unless point.size == (if key == `hsource then 2 else 1) do
        throwError "original observed family: changed exact forcing field"
      let forcing ← actualOriginalForcing ctx point[0]!
      mkLambdaFVars point (← familyGet forcing key)
  throwError "original observed family: unhandled analytic input {key} on {name}"

/-- Actual point fields precede the nonempty default. Apply the existing
observed producer on the fixed RAW index by precomposing these SAME fields
with the common admitted retraction. No residual/solver or source is replaced. -/
elab "apply_original_observed_remainder_to_nonempty_family" : command => liftTermElabM do
  let family := ns ++ `Family
  let history := `JanetCartan.PhysicalPrimary.OriginalHistoryFamily
  let producer := `JanetCartan.FixedDomainInverse.exists_observed_parameter_remainders_of_original_profiles
  let info ← getConstInfo producer
  forallBoundedTelescope (← getConstInfo (family ++ `S)).type (some 41) fun base _ => do
    unless base.size == 41 do throwError "original observed family: expected fixed original41 data"
    let fixed := base[:39].toArray
    let I := mkAppN (mkConst (family ++ `RawIndex)) fixed
    let scalarSpace := mkAppN (mkConst (family ++ `ScalarSpace)) fixed
    let payload := mkApp2 (mkConst ``Prod [Level.zero,Level.zero]) (mkConst `Real) scalarSpace
    let sourceAdmission := mkAppN (mkConst (family ++ `SourceAdmission)) fixed
    let S := mkAppN (mkConst (family ++ `S)) base
    let static (key : Name) := mkAppN (mkConst (family ++ `Static ++ key)) base
    withLocalDeclD `ν (mkConst `Real) fun ν => do
      let positive ← mkAppM ``LT.lt #[← mkNumeral (mkConst `Real) 0,ν]
      let belowOne ← mkAppM ``LT.lt #[ν,← mkNumeral (mkConst `Real) 1]
      withLocalDeclD `hν positive fun hν => do
        withLocalDeclD `hν1 belowOne fun hν1 => do
          let pointBase := base ++ #[ν,hν,hν1]
          let admitted := mkAppN (mkConst (history ++ `Admitted))
            #[fixed[0]!,payload,fixed[26]!,fixed[29]!,ν,S]
          let predicate ← withLocalDeclD `i I fun i => do
            mkLambdaFVars #[i] (mkApp2 (mkConst ``And) (mkApp admitted i) (mkApp sourceAdmission i))
          let admittedType := mkApp2 (mkConst ``Subtype [Level.one]) I predicate
          let fixedValue (key : Name) (index : Expr) : Option Expr :=
            if key == `d then some fixed[0]!
            else if key == `q then some (mkApp (mkConst ``Nat.succ) fixed[0]!)
            else if key == `ι then some index
            else if key == `ν then some ν
            else if key == `hν then some hν
            else if key == `hν1 then some hν1
            else if originalFamilyStaticNames.contains key then some (static key)
            else none
          withLocalDeclD `point admittedType fun y => do
            let proofs := Expr.proj ``Subtype 1 y
            let ctx ← actualRemainderContext fixed base[39]! base[40]! (.proj ``Subtype 0 y)
              (.proj ``And 0 proofs) (.proj ``And 1 proofs)
            let mut type := info.type.instantiateLevelParams info.levelParams (info.levelParams.map fun _ => Level.zero)
            let mut done := false
            while !done do
              let .forallE key domain rest _ := type
                | throwError "original observed family: point telescope ended early"
              let value ← match fixedValue key admittedType with
                | some v => pure v
                | none => do
                  let .forallE _ _ result _ := domain.headBeta
                    | throwError "original observed family: point field {key} not indexed"
                  let body := result.instantiate1 y
                  let val ← originalFamilyPointField y body key static ctx
                  discard <| storeExpectedSource (family ++ `Point ++ key) (pointBase.push y) val body (!(← isProp body))
                  pure (mkAppN (mkConst (family ++ `Point ++ key)) pointBase)
              type := rest.instantiate1 value
              if key == `hsolver then done := true
          let nonemptyType := mkApp (mkConst ``Nonempty [Level.one]) admittedType
          withLocalDeclD `hAdmittedNonempty nonemptyType fun hne => do
            let params := pointBase.push hne
            let nativeRetraction := mkAppN (mkConst (history ++ `admittedRetraction))
              #[fixed[0]!,payload,fixed[26]!,fixed[29]!,ν,S,sourceAdmission,hne]
            let retraction ← store (family ++ `retraction) params nativeRetraction true
            let mut application := mkConst producer (info.levelParams.map fun _ => Level.zero)
            let mut type ← inferType application
            let mut done := false
            let mut count := 0
            while !done do
              let .forallE key domain rest _ := type
                | throwError "original observed family: raw telescope ended early"
              let value ← match fixedValue key I with
                | some v => pure v
                | none => do
                  let point := mkAppN (mkConst (family ++ `Point ++ key)) pointBase
                  let val ← withLocalDeclD `i I fun i => do
                    mkLambdaFVars #[i] (mkApp point (mkApp retraction i))
                  storeExpectedSource (family ++ `Inputs ++ key) params val domain (!(← isProp domain))
              application := mkApp application value
              type := rest.instantiate1 value
              count := count + 1
              if key == `hsolver then done := true
            unless count > 60 do throwError "original observed family: unexpectedly short producer spine"
            discard <| storeExpectedSource (family ++ `nonempty_remainder) params application type
  logInfo "actual observed full-inverse producer applied on fixed RAW index: original Point44 fields, SAME admitted retraction, uncut residual/inverse/paired solver and original source; ONE S before all response orders and histories"

/-- Expand only the original producer application's indexed wrappers. Native
operators, source amplitudes, masks and phase constructors are NOT unfolded. -/
private def exposeActualFamilyInputs (input : Expr) : MetaM Expr := do
  let inputPrefix := (ns ++ `Family.Inputs).toString ++ "."
  let isInputAlias (e : Expr) := match e.getAppFn with
    | .const name _ => name.toString.startsWith inputPrefix
    | _ => false
  let env ← getEnv
  let mut value := input
  let mut rounds := 0
  while (value.find? isInputAlias).isSome do
    let next := value.replace fun e =>
      match e.getAppFn with
      | .const name levels =>
        if name.toString.startsWith inputPrefix then
          (env.find? name).bind fun info =>
            (info.value? (allowOpaque := true)).map fun body =>
              (body.instantiateLevelParams info.levelParams levels).beta e.getAppArgs
        else none
      | _ => none
    unless next != value do throwError "actual remainder transport: indexed alias cannot unfold"
    value := next
    rounds := rounds + 1
    if rounds > 8 then throwError "actual remainder transport: unexpectedly recursive indexed aliases"
  return value

private def actualRemainderExistenceType (base : Array Expr) (s k : Expr) : MetaM Expr := do
  withLocalDeclD `N (mkConst ``Nat) fun N => do
    withLocalDeclD `D (mkConst `Real) fun D => do
      let property := mkAppN (mkConst (ns ++ `Family.actual_remainder_bound)) (base ++ #[s,k,N,D])
      let all ← forallBoundedTelescope (← inferType property) (some 2) fun point _ => do
        unless point.size == 2 do throwError "actual remainder transport: expected raw datum and its primitive admission"
        mkForallFVars point (mkAppN property point)
      let nonnegative ← mkAppM ``LE.le #[← mkNumeral (mkConst `Real) 0,D]
      let conclusion := mkApp2 (mkConst ``And) nonnegative all
      let existsD ← mkAppM ``Exists #[← mkLambdaFVars #[D] conclusion]
      mkAppM ``Exists #[← mkLambdaFVars #[N] existsD]

/-- Apply the checked data-only admitted-retraction transport to the EXISTING
concrete nonempty observed FULL-INVERSE producer. The result has no analytic
or nonemptiness premise, no new default and no choice of a different inverse. -/
elab "transport_original_remainder_to_all_admitted_data" : command => liftTermElabM do
  let family := ns ++ `Family
  let original := family ++ `nonempty_remainder
  forallBoundedTelescope (← getConstInfo original).type (some 45) fun params result => do
    unless params.size == 45 do throwError "actual remainder transport: changed fixed nonempty45 spine"
    let base := params[:44].toArray
    let retraction := mkAppN (mkConst (family ++ `retraction)) params
    let nativeRetraction ← bodyAt (family ++ `retraction) params
    unless nativeRetraction.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalHistoryFamily.admittedRetraction 8 do
      throwError "actual remainder transport: changed shared data-only retraction"
    let hneType ← inferType params[44]!
    unless hneType.isAppOfArity ``Nonempty 1 do throwError "actual remainder transport: missing internal data subtype"
    let subtype := hneType.getAppArgs[0]!
    unless subtype.isAppOfArity ``Subtype 2 do throwError "actual remainder transport: changed original admission subtype"
    let I := subtype.getAppArgs[0]!
    let admission := subtype.getAppArgs[1]!
    -- Abstract the already-proved native point expression at symbolic N,D;
    -- never guess/rebuild the inverse observation or rescale the norm budget.
    forallBoundedTelescope result (some 2) fun sk exN => do
      unless sk.size == 2 && exN.isAppOfArity ``Exists 2 do
        throwError "actual remainder transport: changed all-order producer conclusion"
      withLocalDeclD `N (mkConst ``Nat) fun N => do
        let exD := exN.getAppArgs[1]!.beta #[N]
        unless exD.isAppOfArity ``Exists 2 do throwError "actual remainder transport: missing uniform cost"
        withLocalDeclD `D (mkConst `Real) fun D => do
          let pair := exD.getAppArgs[1]!.beta #[D]
          unless pair.isAppOfArity ``And 2 do throwError "actual remainder transport: changed cost/bound pair"
          forallBoundedTelescope pair.getAppArgs[1]! (some 1) fun raw bound => do
            unless raw.size == 1 do throwError "actual remainder transport: missing original raw index"
            let selected := mkApp retraction raw[0]!
            let expanded ← exposeActualFamilyInputs bound
            unless (expanded.find? (fun e => e == selected)).isSome do
              throwError "actual remainder transport: selected native datum did not occur"
            let pointBase := base ++ sk ++ #[N,D]
            withLocalDeclD `point subtype fun y => do
              let property := expanded.replace fun e => if e == selected then some y else none
              if (property.find? (fun e => e == params[44]! || e == raw[0]!)).isSome then
                throwError "actual remainder transport: default/ambient raw index leaked into native point property"
              discard <| storeExpectedSource (family ++ `point_remainder_bound) (pointBase.push y) property (mkSort .zero) true
            withLocalDeclD `i I fun i => withLocalDeclD `hi (mkApp admission i) fun hi => do
              let member := mkAppN (mkConst ``Subtype.mk [Level.one]) #[I,admission,i,hi]
              let property := mkAppN (mkConst (family ++ `point_remainder_bound)) (pointBase.push member)
              discard <| storeExpectedSource (family ++ `actual_remainder_bound) (pointBase ++ #[i,hi]) property (mkSort .zero) true
    let (finalProof,finalType) ← forallBoundedTelescope result (some 2) fun sk _ => do
      let allNonempty ← withLocalDeclD `hne hneType fun hne => do
        mkLambdaFVars #[hne] (mkAppN (mkConst original) (base ++ #[hne] ++ sk))
      let property := mkAppN (mkConst (family ++ `point_remainder_bound)) (base ++ sk)
      let inputs := nativeRetraction.getAppArgs[:7].toArray ++ #[property,allNonempty]
      let proof := mkAppN (mkConst (ns ++ `uniform_depth_cost_of_admitted_retraction)) inputs
      let target ← actualRemainderExistenceType base sk[0]! sk[1]!
      return ((← mkLambdaFVars sk proof),(← mkForallFVars sk target))
    if (finalProof.find? (fun e => e == params[44]!)).isSome then
      throwError "actual remainder transport: nonempty premise escaped into final theorem"
    discard <| storeExpectedSource (family ++ `admitted_remainder) base finalProof finalType
    for name in [`point_remainder_bound,`actual_remainder_bound,`admitted_remainder] do
      addDocStringCore (family ++ name) "Actual original-data observed FULL-INVERSE tail for the SAME residual, uncut inverse and paired solver, chi3 lift and original source. One prehistory S, then all orders, uniform N(s,k)/D(s,k), then every admitted history; empty case discharged and no analytic success premise (app:ch_regular:eq:inverse-remainder; app:ch_response:eq:response-graded-reduced)."
  logInfo "actual original admitted full-inverse remainder: original data, all orders, ONE prehistory S, uniform N/D, actual source/phase/residual/solver, exact admitted-retraction transport including the empty case"


end JanetCartan.PhysicalPrimary.OriginalParameterRemaindersTemplate
end
