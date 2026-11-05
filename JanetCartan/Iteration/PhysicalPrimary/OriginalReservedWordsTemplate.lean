module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Close the native finite-word constructor on the common original source family. -/
public meta section
namespace JanetCartan.PhysicalPrimary.OriginalReservedWordsTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalReservedWords
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def remn := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders
private def fam := remn ++ `Family
private def src := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
private def strong := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
private def obs := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
private def letters := `JanetCartan.PhysicalPrimary.OriginalLetterCurrent
private def steps := `JanetCartan.PhysicalPrimary.OriginalLetterProfiles
private def ord := `JanetCartan.PhysicalPrimary.OriginalWordOrdinary
private def hist := `JanetCartan.PhysicalPrimary.OriginalHistoryFamily
private def words := `JanetCartan.FixedDomainInverse.FiniteResidualWordProfiles
private def coords := `JanetCartan.ArbitraryAccuracy.SelectedLocalization.MeanCorrectedSource.ObservedCore.Coordinates
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private def tail (e : Expr) : Nat → Expr
  | 0 => e
  | k+1 => tail (.proj ``And 1 e) k
private def part (e : Expr) (i : Nat) := Expr.proj ``And 0 (tail e i)
private def real := mkConst `Real
private def atN (name : Name) (n : Expr) := mkApp (mkConst (ns ++ name)) n
private def reTrans (a b c hab hbc : Expr) : MetaM Expr := do
  let o ← synthInstance (mkApp (mkConst `Preorder [.zero]) real)
  return mkAppN (mkConst `le_trans [.zero]) #[real,o,a,b,c,hab,hbc]
private def defeq (name : Name) (a b : Expr) : MetaM Unit := do
  unless ← isDefEq a b do throwError "original reserved words: SAME {name} changed"
private def emit (name : Name) (xs : Array Expr) (value : Expr) (data := false)
    (ty : Option Expr := none) : MetaM Expr := do
  let result ← store (ns ++ name) xs value data ty
  addDocStringCore (ns ++ name) "Original finite residual powers: same native source, measured residual, phase and paired solver. The reserve and all family constants precede the queried histories (app:ch_regular:lem:finite-chain; app:ch_response:eq:response-graded-reduced)."
  return result
private def getBody (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some v := (← getConstInfo n).value? (allowOpaque := true) | throwError "missing {n}"
  return v.beta xs

private structure Static where
  p : Array Expr
  xs : Array Expr
  source : Array Expr
  base : Array Expr
  phase : Array Expr
  steps : Array Expr
  I : Expr
  payload : Expr

private def withStatic (go : Static → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (src ++ `S)).type (some 39) fun p _ => do
    unless p.size == 39 do throwError "original finite word: lost fixed source row/Ar/reserve"
    let d := p[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let dord := app (ns ++ `word_orders) #[d,p[37]!,p[28]!]
    let .forallE _ hScaleType _ _ ← whnf (← inferType (app (strong ++ `S) p[:24].toArray))
      | throwError "missing signed source interval"
    withLocalDeclD `hSignedSigma hScaleType fun hSigma => do
      forallBoundedTelescope (← inferType dord) (some 1) fun hs _ => do
        let h := mkAppN dord hs
        let reserve := p[37]!
        let source := p
        let F (f : Name) := app (fam ++ f) source
        let patch := F `patch
        let cell := F `cell
        let I := F `RawIndex
        let payload := mkApp2 (mkConst ``Prod [.zero,.zero]) real (F `ScalarSpace)
        defeq `shared_raw_index I (app (hist ++ `RawIndex) #[d,payload])
        let base := p[:24].toArray ++ #[hSigma,p[26]!,p[27]!,p[28]!,p[29]!,part h 1,part h 2,p[31]!]
        let basis := atN `wordBasis n
        let bt ← inferType basis
        unless bt.isAppOf `OrthonormalBasis do throwError "original word basis is not on the doubled real carrier"
        let ι := bt.getAppArgs[0]!
        let fin ← synthInstance (mkApp (mkConst `Fintype [.zero]) ι)
        let hCoeff := tail h 7
        let hOrder := app (ns ++ `word_history_order) #[n,reserve,p[28]!,p[29]!,hCoeff,p[31]!]
        let fixed := base ++ #[patch,cell,I,ι,fin,
          app (ns ++ `coefficientReserve) #[n,reserve],app (ns ++ `phaseReserve) #[n,reserve],reserve,
          part h 3,part h 4,part h 5,part h 6,hOrder,basis,mkConst (ns ++ `windowExponent),
          mkConst (ns ++ `windowExponent_pos),mkConst (ns ++ `windowExponent_lt_one),hCoeff]
        unless source.size == 39 && base.size == 32 && fixed.size == 50 do throwError "original prehistory ABI moved"
        go ⟨p,p ++ #[hSigma] ++ hs,source,base,base.push patch,fixed,I,payload⟩

elab "construct_original_reserved_word_threshold" : command => liftTermElabM do
  withStatic fun f => do
    let sl := app (letters ++ `S) f.steps
    let sp := app (obs ++ `S) f.phase
    let ss := app (src ++ `S) f.source
    let inner ← mkAppM ``Max.max #[sp,ss]
    discard <| emit `S f.xs (← mkAppM ``Max.max #[sl,inner]) true
    let hl ← emit `letter_threshold f.xs (← mkAppM `le_max_left #[sl,inner])
    let hi ← mkAppM `le_max_right #[sl,inner]
    discard <| emit `observation_threshold f.xs (← mkAppM `le_trans #[← mkAppM `le_max_left #[sp,ss],hi])
    discard <| emit `source_threshold f.xs (← mkAppM `le_trans #[← mkAppM `le_max_right #[sp,ss],hi])
    discard <| emit `hS f.xs (← mkAppM `le_trans #[app (letters ++ `hS) f.steps,hl])

private structure Common extends Static where
  T : Expr
  hT : Expr
  params : Array Expr
  retract : Expr
  sub : Expr

private def withCommon (go : Common → MetaM Unit) : MetaM Unit := do
  withStatic fun f => do
    withLocalDeclD `T real fun T => do
      withLocalDeclD `hT (← mkAppM ``LE.le #[app (ns ++ `S) f.xs,T]) fun hT => do
        let r := app (hist ++ `admittedRetraction) #[f.p[0]!,f.payload,f.p[26]!,f.p[29]!,
          mkConst (ns ++ `windowExponent),T,app (fam ++ `SourceAdmission) f.source]
        let ne := (← whnf (← inferType r)).bindingDomain!
        unless ne.isAppOfArity ``Nonempty 1 do throwError "original raw retraction admission moved"
        go {toStatic := f,T,hT,params := f.xs ++ #[T,hT],retract := r,sub := ne.appArg!}

private def onWindow (h V : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType h) (some 1) fun cs _ => do
    withLocalDeclD `hc (← mkAppM `Membership.mem #[V,cs[0]!]) fun hc => do
      mkLambdaFVars (cs.push hc) (mkAppN h cs)

private def fixedData (f : Common) (g : Name) := app (reg ++ g) f.p[:23].toArray
private def maskData (f : Common) (g : Name) := app (masks ++ g) f.p[:23].toArray
private def famData (f : Common) (g : Name) := app (fam ++ g) f.source
private def world (f : Common) (g : Name) := app (remn ++ `Source ++ g) f.p[:23].toArray
private def wholeWindowSpec (f : Common) := app (reg ++ `wholeWindow_spec)
  #[mkApp (mkConst ``Nat.succ) f.p[0]!,f.p[1]!,famData f `patch]

elab "construct_original_reserved_word_points" : command => liftTermElabM do
  withCommon fun f => do
    let n := mkApp (mkConst ``Nat.succ) f.p[0]!
    let W := world f `W
    let hW := world f `W_measurable
    let V := (← inferType (part (wholeWindowSpec f) 0)).appArg!
    let h₂ := maskData f `χ₂_compact
    let h₂c := maskData f `χ₂_smooth
    let h₃c := maskData f `χ₃_smooth
    let χ₂ := (← inferType h₂c).appArg!
    let χ₃ := (← inferType h₃c).appArg!
    let h₃W ← mkAppM `Set.Subset.trans #[maskData f `χ₃_support_chart,fixedData f `hUW]
    let Csrc := (← inferType (part (app `JanetCartan.PhysicalPrimary.OriginalLetterGeometry.original_parameter_source_spec
      #[n,f.p[1]!,famData f `patch,famData f `cell]) 0)).appArg!
    withLocalDeclD `y f.sub fun y => do
      let p := f.params.push y
      let keep (key : Name) (val : Expr) (d := false) := emit (`Point ++ key) p val d
      let i := Expr.proj ``Subtype 0 y
      let H := Expr.proj ``Subtype 1 y
      let ha := Expr.proj ``And 0 H
      let hs := Expr.proj ``And 1 H
      let fld (g : Name) := app (hist ++ `RawIndex ++ g) #[f.p[0]!,f.payload,i]
      let R := fld `R₀
      let stage := fld `length
      let history := #[stage,fld `u,fld `ell,part ha 1]
      let lam0 := fld `lam
      let K := fld `K
      let τ := Expr.proj ``Prod 0 (fld `datum)
      let scalar := mkAppN (mkConst ``Subtype.mk [.one])
        #[famData f `ScalarSpace,famData f `scalarPredicate,.proj ``Prod 1 (fld `datum),part hs 1]
      let S := app (ns ++ `S) f.xs
      let hS ← reTrans S f.T R f.hT (part ha 0)
      let reached (name : Name) (th : Expr) := reTrans th S R (app (ns ++ name) f.xs) hS
      let sL := app (letters ++ `S) f.steps
      let hL ← reached `letter_threshold sL
      let hC ← reTrans (app (strong ++ `S) f.base) sL R (app (letters ++ `current_threshold) f.steps) hL
      let hP ← reached `observation_threshold (app (obs ++ `S) f.phase)
      let hA ← reached `source_threshold (app (src ++ `S) f.source)
      let strong38 := f.base ++ #[R,hC] ++ history
      let weak := (← getBody (strong ++ `normalized_solver) strong38).headBeta
      unless weak.isAppOfArity (reg ++ `Current.normalized_solver) 38 do throwError "lost same original38 solver"
      let w := weak.getAppArgs
      let s := f.source ++ #[R,hA] ++ history ++ #[K,part ha 3,τ,part hs 0,scalar,fld `amplitude,tail ha 5,tail hs 2]
      let ph := f.phase ++ #[R,hP] ++ history
      unless s.size == 53 && ph.size == 39 do throwError "lost same source53/phase39"
      let source (g : Name) := app (remn ++ `Source ++ g) s
      let phase (g : Name) := app (obs ++ g) ph
      let native (g : Name) := app (remn ++ `Native ++ g) w
      let full := Expr.proj ``And 0 (source `original_profiles)
      let profileType ← inferType full
      unless profileType.isAppOfArity `JanetCartan.PhysicalPrimary.LeadingReducedSourceFourierBounds 7 do
        throwError "missing original reserved Fourier datum"
      let fa := profileType.getAppArgs
      let amp ← mkAppM ``HMul.hMul #[← mkAppM ``HPow.hPow #[τ,mkNatLit 3],fld `amplitude]
      for (key,a,b) in [(`a,fa[1]!,source `a),(`source_mask,fa[2]!,χ₂),(`Csource,fa[3]!,app (src ++ `Csource) f.source),
          (`tau_cubed_budget,fa[4]!,amp),(`source_scale,fa[5]!,K),(`natural_reserve,fa[6]!,f.p[37]!)] do defeq key a b
      let hsum := app (ord ++ `measured_sum) w
      let eq ← inferType hsum
      unless eq.isAppOfArity ``Eq 3 do throwError "missing literal measured sum"
      let P := eq.getAppArgs[1]!
      unless P.isAppOf `JanetCartan.RegularSector.FiniteAssembly.measuredOperator do throwError "lost measured residual head"
      let rawP := P.appArg!
      let paired := native `pairedSolver
      let rawJ := app (ord ++ `raw) w
      let ordinary ← forallBoundedTelescope (← inferType rawJ) (some 1) fun j _ => do
        mkLambdaFVars j (app (ord ++ `ordinary) (w ++ j ++ #[mkConst ``Bool.false]))
      let hparam ← forallBoundedTelescope (← inferType (phase `φ)) (some 2) fun cx _ => do
        let c := cx[0]!
        let x := cx[1]!
        let mem ← mkAppM `Membership.mem #[Csrc,c]
        withLocalDeclD `hout (mkNot mem) fun hout => do
          mkLambdaFVars #[c,hout,x] (mkAppN (source `parameter_zero) #[← mkAppM ``Prod.mk #[x,c],hout])
      let hsrc := source `joint_smooth
      let hsup := source `physical_zero
      let hφ := phase `joint_smooth
      let φ := phase `φ
      let hfourier ← onWindow (tail full 2) V
      let hφs ← onWindow (phase `support) V
      for (key,val,data) in [(`R₀,R,true),(`stage,stage,true),(`u,fld `u,true),(`ell,fld `ell,true),
          (`reached,hL,false),(`history,part ha 1,false),(`lam,lam0,true),(`K,K,true),(`Adata,amp,true),
          (`one_le_lam,part ha 2,false),(`scale_le,part ha 3,false),(`window,part ha 4,false),
          (`amplitude_nonneg,source `amplitude_nonneg,false),(`φ,φ,true),(`phase_smooth,hφ,false),
          (`phase_support,hφs,false),(`a,source `a,true),(`source_smooth,hsrc,false),(`source_zero,hsup,false),
          (`parameter_zero,hparam,false),(`reserved_fourier,hfourier,false),(`raw,rawJ,true),(`P,P,true),
          (`rawP,rawP,true),(`measured_sum,hsum,false),(`measured_full,← mkEqRefl P,false),
          (`ordinary,ordinary,false),(`Rcomplex,native `Rcomplex,true),(`solver,paired,true)] do
        discard <| keep key val data
      forallBoundedTelescope (← inferType φ) (some 1) fun cs _ => do
        let c := cs[0]!
        let ψ := mkApp φ c
        let hc ← mkAppM `Continuous.uncurry_left #[c,← mkAppM `ContDiff.continuous #[hφ]]
        let forcing := mkAppN (source `forcing_eq) #[c,ψ,lam0]
        let fp := #[c,ψ,hc,lam0]
        let sourceClass := mkAppN (source `realization) fp
        let hm := mkAppN (source `forcing_memLp) fp
        let he := app (ns ++ `original_forcing_class) #[f.p[0]!,W,hW,χ₂,χ₃,h₂,h₃W,source `a,hsrc,hsup,c,ψ,hc,lam0,forcing,hm]
        let et ← whnf (← inferType he)
        unless et.isAppOfArity ``Eq 3 do throwError "missing original local class equality"
        let rhs := et.getAppArgs[2]!
        unless rhs.isAppOf `DFunLike.coe do throwError "missing carrier multiplication on graph test"
        let datum := rhs.appArg!
        defeq `original_forcing_source et.getAppArgs[1]!.appArg! sourceClass
        discard <| keep `source (← mkLambdaFVars cs sourceClass) true
        discard <| keep `datum (← mkLambdaFVars cs datum) true
        discard <| keep `initial (← mkLambdaFVars cs he) false

private def mapped (name stop : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let ci ← getConstInfo name
  let levels := ci.levelParams.map (fun _ => Level.zero)
  let mut t := ci.type.instantiateLevelParams ci.levelParams levels
  let mut args : Array Expr := #[]
  repeat
    let .forallE k domain body bi := t | throwError "native {name}: lost argument {stop}"
    let value ← match (known.find? (fun kv => kv.1 == k)).map Prod.snd with
      | some v => pure v
      | none =>
        if bi.isInstImplicit then synthInstance domain
        else throwError "unfilled actual {name}/{k}"
    args := args.push value
    if k == stop then return mkAppN (mkConst name levels) args
    t := body.instantiate1 value
  throwError "missing {stop} in {name}"

private def putSmallWindow (globalProof target hsub : Expr) : MetaM Expr := do
  forallBoundedTelescope target (some 3) fun orders existsC => do
    let gt := mkAppN globalProof orders
    let C ← mkAppM ``Classical.choose #[gt]
    let hs ← mkAppM ``Classical.choose_spec #[gt]
    let et ← whnf existsC
    unless et.isAppOfArity ``Exists 2 do throwError "native local hglobal lost its uniform constant"
    let spec ← whnf (et.appArg!.beta #[C])
    let hb := tail hs 1
    let restricted ← forallBoundedTelescope spec.getAppArgs[1]! (some 3) fun y _ => do
      unless y.size == 3 do throwError "native local hglobal lost raw/c/hsmall"
      mkLambdaFVars y (mkAppN hb #[y[0]!,y[1]!,mkAppN hsub #[y[1]!,y[2]!]])
    let pair ← mkAppM ``And.intro #[.proj ``And 0 hs,restricted]
    mkLambdaFVars orders (← mkAppOptM ``Exists.intro #[some et.getAppArgs[0]!,some et.appArg!,some C,some pair])

private def constructFamilies (f : Common) : MetaM Unit := do
  let F (name : Name) := famData f name
  let M (name : Name) := maskData f name
  let n := mkApp (mkConst ``Nat.succ) f.p[0]!
  let mask := fun k => fixedData f k
  let fullV := part (wholeWindowSpec f) 0
  let V := (← inferType fullV).appArg!
  let csrcSpec := app `JanetCartan.PhysicalPrimary.OriginalLetterGeometry.original_parameter_source_spec #[n,f.p[1]!,F `patch,F `cell]
  let csrc := (← inferType (part csrcSpec 0)).appArg!
  let h₂ := M `χ₂_smooth
  let h₃ := M `χ₃_smooth
  let χ₂ := (← inferType h₂).appArg!
  let χ₃ := (← inferType h₃).appArg!
  let hW := world f `W_measurable
  let W := world f `W
  let hχ₂W ← mkAppM `Set.Subset.trans #[M `χ₂_support_chart,mask `hUW]
  let hSub := app (masks ++ `V_subset_wholeWindow) (f.p[:23].toArray ++ #[F `patch,F `cell])
  let hneType := (← whnf (← inferType f.retract)).bindingDomain!
  withLocalDeclD `hne hneType fun hne => do
    let params := f.params.push hne
    withLocalDeclD `i f.I fun i => do
      let y := mkAppN f.retract #[hne,i]
      let point (k : Name) := app (ns ++ `Point ++ k) (f.params.push y)
      let each (v : Expr) := mkLambdaFVars #[i] v
      let pf (k : Name) := each (point k)
      let dynamic := #[← pf `R₀,← pf `stage,← pf `u,← pf `ell,← pf `reached,← pf `history,
        ← pf `lam,← pf `K,← pf `Adata,← pf `one_le_lam,← pf `scale_le,← pf `window,← pf `amplitude_nonneg]
      let all := f.steps ++ dynamic
      unless all.size == 63 do throwError "expected original actual63 hstep"
      let residual := app (steps ++ `residual.source_admitted_step) all
      let solver := app (steps ++ `solver.source_admitted_step) all
      let J := (← whnf (← inferType (point `raw))).bindingDomain!
      let known : Array (Name × Expr) := #[(`d,f.p[0]!),(`r,n),(`I,f.I),(`J,J),
        (`e,app (coords ++ `Jcoord) #[f.p[0]!]),(`he,app (coords ++ `measurePreserving_Jcoord) #[f.p[0]!]),
        (`V,V),(`Csrc,csrc),(`hV,fullV),(`χout,χ₂),(`χin,χ₃),(`ho,← mkAppM `ContDiff.continuous #[h₂]),
        (`hi,← mkAppM `ContDiff.continuous #[h₃]),(`hob,← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[mask `χ₂]),
        (`hib,← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[mask `χ₃]),(`hS,M `χ₂_compact),
        (`raw,← pf `raw),(`P,← pf `P),(`hP,← pf `measured_sum),(`hordinary,← pf `ordinary),
        (`lam,dynamic[6]!),(`A,dynamic[8]!),(`K,dynamic[7]!),(`reserve,f.p[37]!),(`φ,← pf `φ),(`hφ,← pf `phase_smooth),
        (`X,app (obs ++ `X) f.phase),(`hX,app (obs ++ `X_compact) f.phase),(`hφs,← pf `phase_support),
        (`hstep,residual),(`S,← pf `solver),(`hsolverStep,solver),(`a₀,← pf `a),(`ha₀,← pf `source_smooth),
        (`has₀,← pf `source_zero),(`hap₀,← pf `parameter_zero),(`C₀,app (src ++ `Csource) f.source),
        (`hC₀,app (src ++ `Csource_nonneg) f.source),(`hfourier₀,← pf `reserved_fourier)]
      logInfo "word80: begin exact finite-word native application"
      let allWord ← mapped (words ++ `actual_finite_residual_word_reserved_bounds_of_one_step) `hfourier₀ known
      logInfo "word80: exact finite-word native application constructed"
      let gWords ← withLocalDeclD `N (mkConst ``Nat) fun N => mkLambdaFVars #[N] (tail (mkApp allWord N) 2)
      let gWords ← emit `Raw.global_reserved params gWords
      logInfo "word80: raw global bound kernel-checked"
      let R ← mkAppM `JanetCartan.FixedDomainInverse.complexLocalRetardedOperator #[hW,W,point `P]
      defeq `same_native_residual R (point `Rcomplex)
      let hi ← onWindow (point `initial) (F `V)
      let localKnown : Array (Name × Expr) := #[(`d,f.p[0]!),(`r,n),(`I,f.I),(`U,W),(`hU,hW),
        (`x,(← inferType (mask `χ₂)).appArg!),
        (`χ₂,mask `χ₂),(`χ₃,mask `χ₃),(`hχ₂,hχ₂W),(`raw,← pf `rawP),(`P,← pf `P),(`S,← pf `solver),
        (`hP,← pf `measured_full),(`source,← pf `source),(`datum,← pf `datum),(`V,F `V),(`hV,F `V_open),
        (`lam,dynamic[6]!),(`A,dynamic[8]!),(`K,dynamic[7]!),(`reserve,f.p[37]!),(`φ,← pf `φ),
        (`hφ,← pf `phase_smooth),(`hinitial,← each hi)]
      let convertWord ← mapped (words ++ `local_finite_word_reserved_bounds_of_global) `hinitial localKnown
      let small ← putSmallWindow gWords (← whnf (← inferType convertWord)).bindingDomain! hSub
      discard <| emit `Raw.local_reserved params (mkApp convertWord small)

private def uniformOrders (f : Common) (kind : Name) : MetaM Unit := do
  let rawN := ns ++ `Raw ++ kind
  let hneType := (← whnf (← inferType f.retract)).bindingDomain!
  withLocalDeclD `N (mkConst ``Nat) fun N => do
    withLocalDeclD `s (mkConst ``Nat) fun s => do
      withLocalDeclD `k (mkConst ``Nat) fun k => do
        let os := #[N,s,k]
        withLocalDeclD `hne hneType fun hne => do
          let atOrders := app rawN (f.params ++ #[hne] ++ os)
          let et ← whnf (← inferType atOrders)
          unless et.isAppOfArity ``Exists 2 do throwError "finite-word uniform constant missing"
          let P ← withLocalDeclD `y f.sub fun y => do
            withLocalDeclD `C real fun C => do
              let spec ← whnf (et.appArg!.beta #[C])
              unless spec.isAppOfArity ``And 2 do throwError "finite-word nonnegative constant missing"
              let ψ ← withLocalDeclD `i f.I fun i => do
                let .forallE _ _ body _ ← whnf spec.getAppArgs[1]! | throwError "finite-word history bound missing"
                let old ← Core.betaReduce (← zetaReduce (body.instantiate1 i))
                let ret ← Core.betaReduce (← zetaReduce (mkAppN f.retract #[hne,i]))
                unless (old.find? fun e => e == ret).isSome do
                  throwError "raw history not present in the native admitted retraction"
                let mut replaced := old.replace fun e => if e == ret then some y else none
                if (replaced.find? fun e => e == i || e == hne).isSome then
                  throwError "query contains another index/default outside the SAME admitted retraction"
                if kind == `local_reserved then
                  let some lo := replaced.find? (fun e => e.isAppOf `JanetCartan.FixedDomainInverse.complexLocalRetardedOperator)
                    | throwError "lost the literal local measured power"
                  let R := app (ns ++ `Point.Rcomplex) (f.params.push y)
                  defeq `named_native66_residual lo R
                  replaced := replaced.replace fun e => if e == lo then some R else none
                return replaced
              mkLambdaFVars #[y,C] ψ
          logInfo m!"word80: {kind} admitted predicate constructed"
          let h ← mkLambdaFVars #[hne] atOrders
          let proof := app (ns ++ `restrict_word_constant)
            #[f.p[0]!,f.payload,f.p[26]!,f.p[29]!,f.T,famData f `SourceAdmission,P,h]
          discard <| emit kind (f.params ++ os) proof

elab "construct_original_reserved_word_raw_bounds" : command => liftTermElabM do
  withCommon fun f => do
    logInfo "word80: common native threshold and admission prepared"
    constructFamilies f
    logInfo "word80: global and local raw families checked"

elab "construct_original_reserved_word_bounds" : command => liftTermElabM do
  withCommon fun f => do
    uniformOrders f `global_reserved
    logInfo "word80: global constants descended to every admitted index"
    uniformOrders f `local_reserved
  logInfo "same original full-strain source, reserved four-letter measured powers and full solver; uniform natural grade including low orders, independent τ/λ before the physical diagonal, no finite-word/remainder or hInitial premise"

elab "construct_original_reserved_colored_window" : command => liftTermElabM do
  let col := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
  forallBoundedTelescope (← getConstInfo (col ++ `radial_ge_one)).type (some 23) fun p conclusion => do
    unless p.size == 23 do throwError "original finite word: expected original22 + one actual colored group"
    let hrad := app (col ++ `radial_ge_one) p
    let radius := app (col ++ `Rcolor) p
    defeq `original_colored_multiplier conclusion.getAppArgs.back! radius
    withLocalDeclD `Rinit real fun R => do
      withLocalDeclD `hRinit (← mkAppM ``LE.le #[← mkNumeral real 1,R]) fun hR => do
        withLocalDeclD `stage (mkConst ``Nat) fun j => do
          discard <| emit `colored_window (p ++ #[R,hR,j]) (app (ns ++ `colored_window_of_radial) #[R,radius,hR,hrad,j])

end JanetCartan.PhysicalPrimary.OriginalReservedWordsTemplate
