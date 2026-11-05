module

public meta import Lean

/-!
# Choice order for the original physical moment charts

The earlier moment/trade and normalized-phase proofs both use the same
`exists_current_mixed_inverse T` before they estimate any primitive coefficient.
Their convenient uncurried statements put the numerical coefficient budgets
first. Recover the *actual* witnesses of these proofs, not a `choose` of that
uncurried statement (which would have an illicit dependence on the later
source dilation). The kernel checks the reconstructed introductions, and the
closed-declaration check also checks that no late budget appears in a margin.
-/

public meta section
namespace JanetCartan.PhysicalMean.OriginalSampledMomentGeometryTemplate
open Lean Meta Elab Command

private def ns := `JanetCartan.PhysicalMean.OriginalSampledMomentGeometry.Early

private def save (n : Name) (xs : Array Expr) (body : Expr) (base : Name := ns)
    (expected : Option Expr := none) : MetaM Expr := do
  let result ← match expected with
    | some t => pure t
    | none => inferType body
  let t ← mkForallFVars xs (← instantiateMVars result)
  let p ← mkLambdaFVars xs (← instantiateMVars body)
  if t.hasFVar || p.hasFVar || t.hasMVar || p.hasMVar || t.hasSorry || p.hasSorry then
    throwError "original moment chart: late/free or recovered operand in {n}"
  if ← isProp result then
    addDecl (.thmDecl {name := base ++ n, levelParams := [], type := t, value := p}) (forceExpose := true)
  else
    addDecl (.defnDecl {name := base ++ n, levelParams := [], type := t, value := p, hints := .abbrev, safety := .safe}) (forceExpose := true)
  return mkAppN (mkConst (base ++ n)) xs

private def pair (p : Expr) : MetaM (Expr × Expr) := do
  return (← mkAppM ``Classical.choose #[p], ← mkAppM ``Classical.choose_spec #[p])

/-- Close just the opening primitive existential/conjunction eliminators,
using their own witnesses and proof projections. Stop at an introduction. -/
private def introduction (p : Expr) (witness : Expr → MetaM (Expr × Expr)) : MetaM Expr := do
  let mut p ← Core.betaReduce (← zetaReduce p)
  for _ in [:24] do
    let n := p.getAppFn.constName?.getD .anonymous
    let args := p.getAppArgs
    if n == ``Exists.intro || n == ``And.intro then return p
    let ex := [``Exists.casesOn, ``Exists.rec, ``Exists.elim, `Exists.recOn].contains n
    let and := [``And.casesOn, ``And.rec, ``And.elim, `And.recOn].contains n
    unless ex || and do throwError "original moment chart: unexpected opening eliminator {n}"
    let head := if ex then ``Exists else ``And
    let mut scrutinee : Option Expr := none
    for a in args do
      if (← inferType a).isAppOf head then scrutinee := some a
    let some h := scrutinee | throwError "original moment chart: missing {head} scrutinee"
    let (v,hv) ← if ex then witness h else if h.isAppOf ``And.intro then
      pure (h.getAppArgs[h.getAppNumArgs-2]!,h.appArg!) else pure (.proj ``And 0 h, .proj ``And 1 h)
    let branch := if n == ``And.rec || n == ``Exists.rec then args[args.size-2]! else args.back!
    let closed := mkAppN branch #[v,hv]
    unless ← isDefEq (← inferType closed) (← inferType p) do
      throwError "original moment chart: existential replay changed the proved proposition"
    p ← Core.betaReduce (← zetaReduce closed)
  throwError "original moment chart: unsupported choice depth"

private def components (p : Expr) (expected : Name) : MetaM (Expr × Expr) := do
  unless p.isAppOf expected do throwError "original moment chart: expected {expected}, got {p.getAppFn}"
  return (p.getAppArgs[p.getAppNumArgs-2]!,p.appArg!)

private def primitive (p : Expr) : MetaM (Expr × Expr) := do
  if !p.isAppOf `JanetCartan.PhysicalAdjointGeometry.exists_primitive_trade_profiles then return ← pair p
  let ci ← getConstInfo p.getAppFn.constName?.get!
  let some body := ci.value? (allowOpaque := true) | throwError "original moment chart: primitive proof not exposed"
  components (← introduction (body.beta p.getAppArgs) pair) ``Exists.intro

/-- Expose the same analytic continuations, now with the genuine static
numerical chart margins named independently of all source-dependent budgets.
The consumers are the SAME current-map phase profile and source-only moment
trade in `app:ch_mean_pairs:eq:raw-adjoint-moments`. -/
elab "establish_original_moment_choice_order" : command => liftTermElabM <| withTransparency .reducible do
  for (label,name) in [(`trade,`JanetCartan.PhysicalMean.exists_original_moment_geometry_profiles),
      (`phase,`JanetCartan.PhysicalForwardMean.exists_original_normalizedPhase_profiles)] do
    let ci ← getConstInfo name
    let some body := ci.value? (allowOpaque := true) | throwError "original moment chart: import all {name}"
    forallTelescope ci.type fun xs _ => do
      let mut early := #[]
      for x in xs do
        let n := (← x.fvarId!.getUserName).eraseMacroScopes
        if [`n,`P,`U,`hU,`T,`c,`C,`ρ,`hP,`hρ].contains n then early := early.push x
      let mut p ← introduction (body.beta xs) primitive
      if label == `trade then
        let (ε,tail) ← components p ``Exists.intro
        let (hε,next) ← components tail ``And.intro
        discard <| save `width early ε
        discard <| save `width_pos early hε
        p := next
      let (δ,margin) ← components p ``Exists.intro
      let (hδ,packet) ← components margin ``And.intro
      discard <| save (label ++ `tolerance) early δ
      discard <| save (label ++ `tolerance_pos) early hδ
      let (D,profile) ← components packet ``Exists.intro
      let (hD,usage) ← components profile ``And.intro
      discard <| save (label ++ `C) xs D
      discard <| save (label ++ `C_pos) xs hD
      if label == `trade then
        let (compact,rest) ← components usage ``And.intro
        discard <| save `inside_joint_domain early compact
        discard <| save (label ++ `current) xs rest
        -- The actual proof chooses the localized joint pair from the same
        -- current frame alone, not anew at each moment reserve or frequency.
        lambdaTelescope rest fun dynamic kernel => do
          let output ← introduction kernel pair
          let (Y,directions) ← components output ``Exists.intro
          let (L,fields) ← components directions ``Exists.intro
          let mut current := xs
          let mut reserve := false
          for v in dynamic do
            if (← v.fvarId!.getUserName).eraseMacroScopes == `rStar then reserve := true
            if !reserve then current := current.push v
          unless reserve do throwError "original moment chart: current/reserve boundary missing"
          discard <| save `Y current Y
          discard <| save `L current L
          let (hy,fields) ← components fields ``And.intro
          let (hl,fields) ← components fields ``And.intro
          let (germ,fields) ← components fields ``And.intro
          let (duality,jet) ← components fields ``And.intro
          discard <| save `Y_smooth current hy
          discard <| save `L_smooth current hl
          discard <| save `Y_germ current germ
          discard <| save `trade_identity current duality
          discard <| save `L_profile (xs ++ dynamic) jet
      else
        discard <| save (label ++ `current) xs usage
  logInfo "shared original moment chart: SAME primitive trade/phase proofs, kernel-checked pre-source tolerances and displacement width"

private def original := `JanetCartan.PhysicalMean.OriginalSampledMomentGeometry
private def actual := original ++ `Native

private def native (n : Name) (params : Array Expr) (v : Expr) : MetaM Expr := save n params v actual
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs

/-- Name each complete selected continuation with its new witness in the
result type. Inlining repeated `choose_spec` on the full original graph would
replicate the complete dependent physical-history telescope exponentially. -/
private def familyNS := original ++ `Family
private def sealWitness (n : Name) (xs : Array Expr) (e : Expr) : MetaM (Expr × Expr) := do
  let existence ← save (n ++ `exists) xs e familyNS
  let t ← whnf (← inferType existence)
  unless t.isAppOfArity ``Exists 2 do throwError "original moment chart: {n} is not existential"
  let args := t.getAppArgs.push existence
  let levels := t.getAppFn.constLevels!
  let v ← save n xs (mkAppN (mkConst ``Classical.choose levels) args) familyNS
  let tail ← save (n ++ `spec) xs (mkAppN (mkConst ``Classical.choose_spec levels) args) familyNS
    (some (t.appArg!.beta #[v]))
  return (v,tail)

/-- Project the short original coefficient-reference telescope. Nothing is
reselected when these fields are used on the larger original graph. -/
elab "project_original_current_moment_family" : command => liftTermElabM <| withTransparency .reducible do
  let family := original ++ `exists_current_family
  forallBoundedTelescope (← getConstInfo family).type (some 10) fun ps _ => do
    let sel (n : Name) (xs : Array Expr) (b : Expr) := save n xs b familyNS
    let (_,s) ← sealWitness `S ps (app family ps)
    discard <| sel `hS ps (.proj ``And 0 s)
    let (_,l) ← sealWitness `DL ps (.proj ``And 1 s)
    let (_,p) ← sealWitness `DP ps l
    discard <| sel `DL_pos ps (.proj ``And 0 p)
    discard <| sel `DP_pos ps (.proj ``And 0 (.proj ``And 1 p))
    let ready ← sel `current ps (.proj ``And 1 (.proj ``And 1 p))
    forallBoundedTelescope (← inferType ready) (some 8) fun hist _ => do
      let xs := ps ++ hist
      let (_,q) ← sealWitness `Q xs (mkAppN ready hist)
      discard <| sel `Q_current xs (.proj ``And 0 q)
      let (_,y) ← sealWitness `Y xs (.proj ``And 1 q)
      let (_,l) ← sealWitness `L xs y
      discard <| sel `chart xs l

/-- Instantiate the one-chart construction on the same graph42 reference and
finite map. The only extra frame premise is the *numerical* pre-source
admission `γ ≤ tolerance hn`, not a current or phase success estimate. -/
elab "realize_original_history_moment_chart " ix:num : command => liftTermElabM <| withTransparency .reducible do
  let step := ix.getNat
  let raw := `JanetCartan.PhysicalSampling.OriginalPhaseMargins.raw_frame_margin_native
  let scalar := `JanetCartan.PhysicalSampling.OriginalScalarHistory
  forallBoundedTelescope (← getConstInfo raw).type (some 36) fun xs _ => do
    unless xs.size == 36 do throwError "original moment chart: native prehistory frame ABI changed"
    let dim := xs[0]!
    let hn := xs[1]!
    let ref := xs[:26].toArray ++ xs[27:29].toArray
    let G := app (scalar ++ `Gref) ref
    let hr := app (scalar ++ `radius_lt_chartRadius) ref
    let f := app (original ++ `exists_current_family) #[dim,hn,G,hr,xs[29]!,xs[30]!,xs[31]!,xs[32]!]
    withLocalDeclD `hγMoment (← mkAppM ``LE.le #[xs[24]!,app (original ++ `tolerance) #[dim,hn]]) fun hm => do
      forallBoundedTelescope (← inferType f) (some 1) fun res _ => do
        let pars := xs[:27].toArray ++ #[hm] ++ xs[27:].toArray ++ res
        let inputs := #[dim,hn,G,hr,xs[29]!,xs[30]!,xs[31]!,xs[32]!,res[0]!,xs[35]!]
        let staticField (n : Name) := app (familyNS ++ n) inputs
        let putAt (j : Nat) (n : Name) (b : Expr) := if step == j then native n pars b else pure (app (actual ++ n) pars)
        let Sgeo ← putAt 0 `Sgeometry (staticField `S)
        let DL ← putAt 0 `DL (staticField `DL)
        let DP ← putAt 0 `DP (staticField `DP)
        if step == 0 then return
        if step == 1 then
          discard <| native `DL_pos pars (staticField `DL_pos)
          discard <| native `DP_pos pars (staticField `DP_pos)
          return
        let graph := app (scalar ++ `Sgraph) (xs[:26].toArray ++ xs[27:].toArray)
        let shift := app (original ++ `shiftThreshold) #[dim,hn]
        let pre ← mkAppM ``Max.max #[graph,shift]
        let S ← putAt 2 `S (← mkAppM ``Max.max #[pre,Sgeo])
        if step == 2 then return
        if step == 3 then
          for (n,k) in [(`graph_le,`graph_le_joined),(`shift_le,`shift_le_joined),(`geometry_le,`geometry_le_joined)] do
            discard <| native n pars (app (original ++ k) #[graph,shift,Sgeo])
          discard <| native `hS pars (app (original ++ `two_le_joined)
            #[graph,shift,Sgeo,app (original ++ `shiftThreshold_ge) #[dim,hn]])
          return
        withLocalDeclD `R₀ (mkConst `Real) fun R => do
          withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S,R]) fun hR => do
            let hgr := app (original ++ `reached_graph) #[graph,shift,Sgeo,R,hR]
            let r := app raw (xs ++ #[R,hgr])
            forallBoundedTelescope (← inferType r) (some 4) fun hist _ => do
              let r := mkAppN r hist
              let dyn := pars ++ #[R,hR] ++ hist
              let live := inputs ++ #[R,app (original ++ `reached_geometry) #[graph,shift,Sgeo,R,hR]] ++ hist
              forallBoundedTelescope (← inferType r) (some 1) fun as _ => do
                let a := as[0]!
                let closing ← mkAppM `lt_of_lt_of_le #[mkApp r a,hm]
                let field (n : Name) := app (familyNS ++ n) (live ++ #[a,closing])
                let out := dyn.push a
                let val (j : Nat) (n : Name) := if step == j then native n out (field n) else pure (app (actual ++ n) out)
                let Q ← val 4 `Q
                if step == 4 then
                  discard <| native `Q_current out (field `Q_current)
                  return
                let Y ← val 5 `Y
                let L ← val 5 `L
                if step == 5 then return
                let sl := field `chart
                let h := app (original ++ `CurrentChart) #[dim,hn,a,Q,Y,L,mkApp DL a,mkApp DP a,xs[31]!,
                  app `JanetCartan.currentCoefficientScale #[R,hist[0]!]]
                unless ← withTransparency .default <| isDefEq (← inferType sl) h do
                  throwError "original moment chart: selected a different current/scale or primitive chart"
                discard <| save `chart out sl actual (some h)
  if step == 6 then logInfo "SAME graph42 raw projected stress, source-dilated reference and finite map: one global Y/L per original current patch, independent of sample and requested reserve"

/-- Specialize the native chart to the untouched outer bare row, including
its `userCap` *before* the once-only sampling and strong caps. This theorem is
universal in the physical carrier node; in particular the original common
event's very same random translation is admissible without a new choice. -/
elab "realize_original_sampled_moment_fields " ix:num : command => liftTermElabM <| withTransparency .reducible do
  let step := ix.getNat
  let nativeChart := actual ++ `chart
  let output := original ++ `AtPoint
  let proofName := original ++ `Bare.at_point
  if step ≥ 3 then
    forallBoundedTelescope (← getConstInfo (output ++ `fields)).type (some 47) fun params _ => do
      let mut facts := app (output ++ `fields) params
      if step ≤ 10 then
        let names := #[`continuous_phase,`phase_smooth,`direction_smooth,`native_phase_smooth,`active_high,`agree,`phase_trade]
        for _ in [:min (step-3) 7] do
          facts := .proj ``And 1 facts
        let fact := if step == 10 then facts else .proj ``And 0 facts
        let name := if step == 10 then `profiles else names[step-3]!
        discard <| save name params fact output
        return
      let i := params[44]!
      let config := params[:44].toArray
      let shiftT ← mkArrow (mkConst `JanetCartan.SeparatedSampling.Lattice) (mkConst `JanetCartan.SeparatedSampling.Point)
      withLocalDeclD `U (← mkArrow (← inferType i) shiftT) fun U => do
        withLocalDeclD `sample (mkConst `JanetCartan.SeparatedSampling.Sample) fun q => do
          let R := app `JanetCartan.historyScale #[params[38]!,mkConst `JanetCartan.growthExponent,params[40]!]
          let mesh ← mkAppM ``HPow.hPow #[R,← mkAppM ``Neg.neg #[mkConst `JanetCartan.separationExponent]]
          let color := app `JanetCartan.SeparatedSampling.color #[params[2]!,Expr.proj ``Prod 0 q]
          let z := app `JanetCartan.SeparatedSampling.node #[mesh,mkApp U i,q]
          discard <| save `fields (config ++ #[U,i,q]) (app (output ++ `fields) (config ++ #[i,color,z])) (original ++ `AtSample)
    if step == 11 then logInfo "actual unchanged finite-rate bare sampler: literal mask, whole four-mu tester, full phase, radial duality and both reserve profiles on the original color/mesh/node"
    return
  forallBoundedTelescope (← getConstInfo nativeChart).type (some 21) fun pre rem => do
    withLocalDeclD `other (← whnf rem).bindingDomain! fun other => do
      let bare := pre.push other
      let user := app `JanetCartan.PhysicalSampling.OriginalBare.userCap #[pre[0]!,pre[1]!,other]
      let scalar := pre.push user
      let chart := app nativeChart scalar
      forallBoundedTelescope (← inferType chart) (some 22) fun history suffix => do
        unless history.size == 22 do throwError "original moment nodes: expected original44 current prefix"
        let xs := scalar ++ history
        let s38 := xs[:38].toArray
        let graph := app `JanetCartan.PhysicalSampling.OriginalScalarHistory.Sgraph (xs[:26].toArray ++ xs[28:37].toArray)
        let shift := app (original ++ `shiftThreshold) #[xs[0]!,xs[1]!]
        let hshift := app (original ++ `reached_shift) #[graph,shift,app (actual ++ `Sgeometry) s38,xs[38]!,xs[39]!]
        let bound := app proofName (bare ++ #[xs[38]!,hshift,xs[40]!])
        forallBoundedTelescope (← inferType bound) (some 3) fun icz _ => do
          let i := icz[0]!
          let p := (← whnf (← whnf suffix).bindingDomain!)
          unless p.isAppOfArity ``Sigma 2 do throwError "original moment nodes: missing actual patch index"
          let prow ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.fst #[i]]
          let pcenter ← mkAppM ``Subtype.val #[prow]
          let a := mkAppN (mkConst ``Sigma.mk [.zero,.zero]) (p.getAppArgs ++ #[← mkAppM ``Prod.fst #[pcenter],← mkAppM ``Sigma.snd #[i]])
          let row := xs.push a
          let proof := mkAppN bound (icz ++ #[app (actual ++ `Q) row,app (actual ++ `Y) row,app (actual ++ `L) row,
            app (actual ++ `DL) (s38.push a), app (actual ++ `DP) (s38.push a),xs[32]!,
            app `JanetCartan.currentCoefficientScale #[xs[38]!,xs[40]!],app nativeChart row])
          let t ← Core.betaReduce (← zetaReduce (← inferType proof))
          unless t.isAppOfArity (original ++ `SampledChart) 11 do
            throwError "original moment nodes: expected actual sampled phase/mask/direction operands, obtained {t.getAppFn}"
          let mut operands := t.getAppArgs
          unless operands[2]!.isAppOf `JanetCartan.PhysicalForwardMean.singleRetainedForwardPhase do
            throwError "original moment nodes: literal phase from the original bare row was lost"
          let params := bare ++ history ++ icz
          for (j,n) in [(2,`φ),(3,`Φ),(4,`mask),(5,`direction)] do
            let f ← if step == (j-2)/2 then save n params operands[j]! output else pure (app (output ++ n) params)
            operands := operands.set! j f
          if step < 2 then return
          if step == 2 then
            discard <| save `fields params proof output (some (app (original ++ `SampledChart) operands))
            return

/-- The shared all-patch envelope is formed before histories, samples, or
orders of a downstream moment request. -/
elab "aggregate_original_moment_cost " which:num : command => liftTermElabM <| withTransparency .reducible do
  let label := if which.getNat == 0 then `DL else `DP
  forallBoundedTelescope (← getConstInfo (actual ++ label)).type (some 38) fun xs _ => do
    let D := app (actual ++ label) xs
    let hD := app (actual ++ (if which.getNat == 0 then `DL_pos else `DP_pos)) xs
    let args := #[xs[0]!,xs[1]!,D]
    discard <| native (label ++ `total) xs (app (original ++ `patchTotal) args)
    discard <| native (label ++ `le_total) xs (app (original ++ `le_patchTotal) (args.push hD))
    discard <| native (label ++ `total_nonneg) xs (app (original ++ `patchTotal_nonneg) (args.push hD))

end JanetCartan.PhysicalMean.OriginalSampledMomentGeometryTemplate
end
