module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! The two native threshold applications on exactly the original fixed
geometry. No threshold is selected and no dynamic continuation is changed. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalLetterGeometryTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalLetterGeometry
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def current := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
private def original := `JanetCartan.PhysicalSeed.OriginalBoundary
private def protectedNS := `JanetCartan.PhysicalInitialization.OriginalProtected
private def incidence := `JanetCartan.PhysicalPrimary.OriginalIncidence
private def whole := incidence ++ `Whole

private def normalizeStaticType (type : Expr) : MetaM Expr := do
  let type ← Core.betaReduce type
  transform type (post := fun expr => do
    let args := expr.getAppArgs
    let nativeNat := args.size > 0 && args[0]! == mkConst ``Nat
    if (nativeNat && (expr.isAppOf ``HAdd.hAdd || expr.isAppOf ``HSub.hSub ||
        expr.isAppOf ``OfNat.ofNat)) || expr.isAppOf ``Nat.add || expr.isAppOf ``Nat.sub then
      let reduced ← whnf expr
      if reduced != expr then return .visit reduced
    return .continue)

private def staticDefEq (value expected : Expr) : MetaM Bool := do
  let actual ← normalizeStaticType (← inferType value)
  let expected ← normalizeStaticType expected
  isDefEq actual expected

/-- Substitute known original geometry while retaining the exact native
numeric/basis/index binders. The seven final pre-threshold geometric clauses
are all actual original theorems, not hypotheses of the specialization. -/
private partial def specialize (label : Name) (fixed : Array Expr)
    (known : Array (Name × Expr)) (footprints : Array Expr) (proof type : Expr)
    (retained : Array Expr := #[]) (afterNumeric : Bool := false) (tailIndex : Nat := 0)
    (applied : Nat := 0) : MetaM Unit := do
  match type with
  | .mdata _ body => specialize label fixed known footprints proof body retained afterNumeric tailIndex applied
  | .letE _ _ value body _ =>
    specialize label fixed known footprints proof (body.instantiate1 value) retained afterNumeric tailIndex applied
  | .forallE name dom body bi =>
    if afterNumeric then
      unless tailIndex < footprints.size do throwError "original letter geometry: extra pre-threshold clause {name}"
      let value := footprints[tailIndex]!
      unless ← staticDefEq value dom do
        throwError "original letter geometry: actual footprint {tailIndex} does not match native clause {name}"
      specialize label fixed known footprints (mkApp proof value) (body.instantiate1 value)
        retained afterNumeric (tailIndex+1) (applied+1)
    else if let some (_,value) := known.find? (fun entry => entry.1 == name) then
      unless ← staticDefEq value dom do
        throwError "original letter geometry: actual static input {name} has the wrong native type"
      specialize label fixed known footprints (mkApp proof value) (body.instantiate1 value)
        retained (name == `hν1) tailIndex (applied+1)
    else
      let keepName := if name == `rStar then `rCoeff else name
      withLocalDecl keepName bi dom fun value => do
        specialize label fixed known footprints (mkApp proof value) (body.instantiate1 value)
          (retained.push value) (name == `hν1) tailIndex applied
  | _ =>
    unless type.isAppOfArity ``Exists 2 && afterNumeric && tailIndex == 7 do
      throwError "original letter geometry: lost the exact native threshold existential or one of seven static clauses"
    let names ← retained.mapM fun value => value.fvarId!.getUserName
    unless names.contains `I && names.contains `rCoeff && !names.contains `R₀ do
      throwError "original letter geometry: index/coefficient order no longer precede the threshold"
    discard <| store (ns ++ label) (fixed ++ retained) proof
    logInfo m!"{label}: closed {applied} exact static receiver inputs, retained BEFORE native threshold only {names.toList}; ALL native dynamic families/profiles unchanged"

/-- Apply both exact native hstep threshold producers. This does not assert
that the parent has instantiated their genuine dynamic continuation
(`app:ch_response:eq:fixed-factor-transfer`, `app:ch_regular:lem:finite-chain`). -/
elab "apply_original_fixed_letter_geometry" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `S)).type (some 32) fun original32 _ => do
    unless original32.size == 32 do throwError "original letter geometry: expected exact strong original32"
    let fixed := original32[:23].toArray
    let d := fixed[0]!
    let hn := fixed[1]!
    let n ← mkAppM ``HAdd.hAdd #[d,mkNatLit 1]
    let Tbase := mkAppN (mkConst (original ++ `T)) #[n,hn]
    forallBoundedTelescope (← inferType Tbase) (some 1) fun patch _ => do
      let a := patch[0]!
      let sourceSpecBase := mkAppN (mkConst (ns ++ `original_parameter_source_spec)) #[n,hn,a]
      forallBoundedTelescope (← inferType sourceSpecBase) (some 1) fun cells _ => do
        let cell := cells[0]!
        let params := original32 ++ #[a,cell]
        let get (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
        let T := mkApp Tbase a
        let ta := (← inferType T).getAppArgs
        let f := get `f
        let fa := (← inferType f).getAppArgs
        unless ta.size == 4 && fa.size == 7 do throwError "original letter geometry: actual T/f telescope changed"
        let patchArgs := #[d,hn,a]
        let originalPatch := #[n,hn,a]
        let sourceSpec := mkAppN (mkConst (ns ++ `original_parameter_source_spec)) (originalPatch.push cell)
        let hCsrc := Expr.proj ``And 0 sourceSpec
        let Csrc := (← inferType hCsrc).appArg!
        let windowSpec := mkAppN (mkConst (regular ++ `wholeWindow_spec)) originalPatch
        let hVwhole := Expr.proj ``And 0 windowSpec
        let Vwhole := (← inferType hVwhole).appArg!
        let source := #[n] ++ fixed[1:21].toArray
        let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,hn,source[20]!]
        let hμ := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure) (source.set! 20 cap)
        let hrCore := mkAppN (mkConst (protectedNS ++ `fact2)) source
        let screened ← mkAppM (regular ++ `screened_pos) #[hn,hrCore,hμ]
        let core ← mkAppM (regular ++ `core_spec) #[hn,screened]
        let coreAll := Expr.proj ``And 1 (.proj ``And 1 (.proj ``And 1 core))
        let hphysical := Expr.proj ``And 1 (mkApp coreAll a)
        let same := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) source[:18].toArray
        let orig (name : Name) := mkAppN (mkConst (original ++ name)) #[n,hn]
        let hR ← mkAppM (regular ++ `radius_lt_same_chart) #[same,orig `R_lt_chartRadius]
        let output := get `output
        let hob ← mkAppM (ns ++ `original_output_norm_bound) #[output,get `fact18]
        let hThreshold ← mkAppM `le_trans
          #[← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.radialThreshold_ge_one #[f],get `hL]
        let Gref := mkAppN (mkConst (current ++ `Gref)) original32[:25].toArray
        forallBoundedTelescope (← inferType (get `fact11)) (some 1) fun sector _ => do
          let p := sector[0]!
          let sp := fixed.push p
          let sec (name : Name) := mkAppN (mkConst (regular ++ `Sector ++ name)) sp
          let originalAt (name : Name) := mkApp (get name) p
          let chart := sec `chart
          let radius ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.maskRadius #[chart]
          let radiusPos ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.maskRadius_pos #[chart]
          let radii := originalAt `fact13
          let hbuffer := Expr.proj ``And 0 radii
          let hsource := Expr.proj ``And 1 radii
          let timePlateau := mkAppN (mkConst (ns ++ `original_endpoint_time_plateau))
            #[d,fa[1]!,fa[2]!,fa[3]!,fa[6]!,fa[4]!,fa[5]!,f,p,hbuffer,hsource,output,get `fact20]
          let hLrefl ← mkAppM `le_refl #[get `L]
          let angularPlateau := Expr.proj ``And 0 (mkAppN (originalAt `fact24) #[get `L,hLrefl])
          let hDamp ← forallBoundedTelescope (← inferType (originalAt `fact35)) (some 1) fun order _ => do
            mkLambdaFVars order (← mkAppM `le_of_lt #[mkAppN (originalAt `fact35) order])
          let swap (name : Name) : MetaM Expr := do
            forallBoundedTelescope (← inferType (get name)) (some 1) fun adj _ => do
              mkLambdaFVars #[p,adj[0]!] (mkAppN (get name) #[adj[0]!,p])
          let base ← swap `base
          let cost ← swap `cost
          let lambdaP (e : Expr) := mkLambdaFVars #[p] e
          withLocalDeclD `negative (mkConst ``Bool) fun negative => do
            let ip := sp ++ #[negative,a]
            let inc (name : Name) := mkAppN (mkConst (regular ++ `Incidence ++ name)) ip
            let cut (name : Name) := mkAppN (mkConst (incidence ++ name)) ip
            let both (e : Expr) := mkLambdaFVars #[p,negative] e
            let phaseCut (name : Name) := mkAppN (mkConst (regular ++ `Incidence ++ name)) (sp.push a)
            let sourceUpperPos ← mkAppM `lt_trans #[inc `fact6,inc `fact7]
            let invNonneg ← mkAppM `le_of_lt #[inc `fact19]
            let γ := mkAppN (mkConst (incidence ++ `Common.γ)) fixed
            let hγ := mkAppN (mkConst (incidence ++ `Common.fact0)) fixed
            let map : Array (Name × Expr) := #[
              (`d,d),(`P,ta[1]!),(`Uref,ta[2]!),(`hUref,ta[3]!),
              (`Ω,fa[1]!),(`x,fa[2]!),(`RQ,fa[3]!),(`Mcap,fa[6]!),(`K₀,fa[5]!),(`T,T),(`f,f),
              (`χp,← lambdaP (phaseCut `χp)),(`hcχp,← lambdaP (phaseCut `χp_compact)),
              (`evolutionTime,get `evolutionTime),(`speedGap,get `speedGap),(`rootSize,get `rootSize),(`rootCost,get `rootCost),
              (`hprotect,get `fact11),(`hbufferTarget,← lambdaP hbuffer),(`hsrcBuffer,← lambdaP hsource),
              (`ε,← lambdaP (sec `εcarrier)),(`aperture,← lambdaP (get `aperture)),(`timeRadius,← lambdaP radius),
              (`g,← both (inc `g)),(`Rad,← both (inc `Rad)),
              (`hε,← lambdaP (sec `fact2)),(`hεroot,← lambdaP (sec `fact3)),(`hεbuffer,← lambdaP (sec `fact5)),
              (`hAp,← lambdaP (get `fact1)),(`hg,← both (inc `fact17)),(`hRad,← both (inc `fact18)),
              (`htime,← lambdaP radiusPos),(`htimeε,← lambdaP (sec `fact6)),(`hsrctime,← lambdaP (← mkAppM `le_refl #[radius])),
              (`hphysical,hphysical),(`V,← both (inc `V)),(`hV,← both (inc `fact0)),(`hVc,← both (inc `fact1)),
              (`hVcov,← both (inc `fact2)),(`Vwhole,Vwhole),(`Csrc,Csrc),(`hVwhole,hVwhole),
              (`hVwholec,.proj ``And 0 (.proj ``And 1 windowSpec)),
              (`hVwholecov,mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalRetardedWhole.whole_window_covectors) patchArgs),
              (`hCsrc,hCsrc),(`hCsrcV,.proj ``And 1 sourceSpec),
              (`χinc,← both (cut `χ)),(`hχinc,← both (cut `fact0)),(`hcχinc,← both (cut `fact2)),(`hsχinc,← both (cut `fact3)),
              (`aWhole,← lambdaP (mkAppN (mkConst (whole ++ `wholeLo)) patchArgs)),
              (`BWhole,← lambdaP (mkAppN (mkConst (whole ++ `wholeHi)) patchArgs)),
              (`haWhole,← lambdaP (mkAppN (mkConst (whole ++ `fact0)) patchArgs)),
              (`gapInactive,← both γ),(`hgapInactive,← both hγ),
              (`a₀,← both (inc `sourceLower)),(`B₀,← both (inc `sourceUpper)),
              (`m,← lambdaP (sec `gradientLower)),(`Mfreq,← lambdaP (sec `gradientUpper)),
              (`ha₀,← both (inc `fact6)),(`hB₀,← both sourceUpperPos),
              (`hm,← lambdaP (sec `fact9)),(`hm1,← lambdaP (sec `fact10)),(`hMfreq,← lambdaP (sec `fact11)),
              (`InvBound,← both (inc `InvBound)),(`hInv,← both invNonneg),
              (`output,output),(`ho,get `fact17),(`hoc,get `fact19),(`hos,get `fact20),(`hob,hob),
              (`threshold,get `L),(`hthreshold,hThreshold),(`angular,get `angular),
              (`hang,← lambdaP (.proj ``And 0 (originalAt `fact36))),(`hangPlateau,← lambdaP angularPlateau),
              (`Damp,get `amplitudeCost),(`hDamp,← lambdaP hDamp),(`ra,get `ra),(`rb,get `rb),
              (`rectOut,get `χout),(`rectSource,get `χsource),(`hrectSource,get `hs),(`base,base),(`cost,cost),
              (`hlocalout,get `fact23),(`hlocalin,get `fact22),(`Gref,Gref),
              (`r,orig `b),(`R,orig `R),(`hr,orig `b_pos),(`hrR,orig `b_lt_R),(`hR,hR),
              (`ext,fixed[4]!),(`hextcenter,fixed[5]!),(`hextradius,fixed[6]!),
              (`Bband,original32[25]!),(`hBband,original32[26]!),(`kMin,original32[28]!)]
            let footprints := #[← lambdaP (sec `fact8),← lambdaP (sec `fact7),← both (inc `fact27),
              get `fact37,← lambdaP timePlateau,← both (inc `χp_germ),
              ← lambdaP (mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalRetardedWhole.whole_χp_germ) (sp.push a))]
            for (label,receiver) in [
                (`residual_initialized,`JanetCartan.PhysicalEllipticWords.exists_physical_history_measured_residual_hstep),
                (`solver_initialized,`JanetCartan.PhysicalPrimary.exists_physical_history_paired_solver_hstep)] do
              let info ← getConstInfo receiver
              unless info.levelParams.isEmpty do throwError "original letter geometry: native receiver universe telescope changed"
              specialize label params map footprints (mkConst receiver) info.type
  logInfo "SAME original static geometry closes both native53/50 threshold applications; small theta support and independent source/adjoint indices preserved; arbitrary I/basis/numeric data precede each threshold; genuine dynamic continuations stay untouched"

end JanetCartan.PhysicalPrimary.OriginalLetterGeometryTemplate
