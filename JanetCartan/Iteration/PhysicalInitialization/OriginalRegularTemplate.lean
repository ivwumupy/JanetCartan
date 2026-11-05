module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Specialization and compact proof-term retention for the normalized regular
solver on the exact original contracted reference and fixed protected mask family. -/

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalRegularTemplate
open Lean Meta Elab Command
open OriginalProtectedTemplate

def ns := `JanetCartan.PhysicalInitialization.OriginalRegular
private def protectedNS := `JanetCartan.PhysicalInitialization.OriginalProtected

/-- Compress the native long existential/conjunction telescope once. Actual
selectors then refer to small named tails, without traversing the complete
regular PDE/adjoint endpoint specification after each projection. -/
private partial def packPrefix (base : Name) (params : Array Expr) (raw : Expr) (i : Nat := 0) : MetaM Expr := do
  let t ← whnf raw
  let body ← if t.isAppOfArity ``Exists 2 then
    let .lam nm ty b _ := t.appArg! | throwError "regular source interval: expected named choice"
    withLocalDeclD nm ty fun x => do
      let tail ← packPrefix base (params.push x) (b.instantiate1 x) (i+1)
      mkAppM ``Exists #[← mkLambdaFVars #[x] tail]
  else if t.isAppOfArity ``And 2 then do
    let tail ← packPrefix base params t.appArg! (i+1)
    pure <| mkApp2 (mkConst ``And) t.getAppArgs[0]! tail
  else pure raw
  store (base ++ Name.mkSimple s!"Prefix_{i}") params body true

/-- Recover the native named `let` objects from the original telescope after
compact selection. Existential binders are instantiated by our *already*
chosen variables; no solver, field, mask, chart, or cutoff is chosen twice. -/
partial def keepNativeLets (base : Name) (params : Array Expr) (raw : Expr) : MetaM Unit := do
  if let .letE nm _ v b _ := raw then
    let name := base ++ nm
    let data ← if (← getEnv).contains name then do
      let data := mkAppN (mkConst name) params
      unless ← isDefEq data v do throwError "incompatible original selected let {name}"
      pure data
    else store name params v true
    keepNativeLets base params (b.instantiate1 data)
  else
    let t ← whnf raw
    if t.isAppOfArity ``Exists 2 then
      let .lam nm _ b _ := t.appArg! | throwError "expected original selected variable"
      let data := mkAppN (mkConst (base ++ nm)) params
      keepNativeLets base params (b.instantiate1 data)
    else if t.isAppOfArity ``And 2 then
      keepNativeLets base params t.appArg!

def selectCompact (base : Name) (params : Array Expr) (h : Expr) : MetaM Unit := do
  let t ← inferType h
  let packed ← packPrefix (base ++ `Types) params t
  let h ← store (base ++ `selected) params h false (some packed)
  select base params h
  keepNativeLets base params t

/-- The original source-frame callback `H` and selected incidence groups are
fixed, but the final source contraction has **not** been chosen. The reference
cap is allowed to be restricted further by the raw background and the
full-time momentum cap; no current inverse constant enters this construction. -/
elab "apply_regular_inverse_to_original_protected_sectors" : command => liftTermElabM do
  withLocalDeclD `d (mkConst ``Nat) fun d => do
    let n := mkApp (mkConst ``Nat.succ) d
    let p := mkApp (mkConst (protectedNS ++ `signed_protection)) n
    forallBoundedTelescope (← inferType p) (some 20) fun rest _ => do
      unless rest.size == 20 do throwError "original regular inverse: expected original21"
      let actual := #[n] ++ rest
      let fixed := #[d] ++ rest
      let hn := actual[1]!
      let protectedField (q : Name) := mkAppN (mkConst (protectedNS ++ q)) actual
      let H := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.H) actual[:18].toArray
      let same := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) actual[:18].toArray
      let hRorig := mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.R_lt_chartRadius) #[n, hn]
      let hR ← mkAppM (ns ++ `radius_lt_same_chart) #[same, hRorig]
      let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n, hn, actual[20]!]
      let source := actual.set! 20 capped
      let measureRadius := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure) source
      let hMeasure := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure) source
      let args := #[d, hn, protectedField `r, protectedField `fact2, measureRadius, hMeasure,
        protectedField `Γin, protectedField `Γout, protectedField `fact13, protectedField `fact14,
        protectedField `fact17, protectedField `fact21, protectedField `fact23,
        protectedField `a, protectedField `fact6, protectedField `δ, protectedField `fact5,
        actual[4]!, actual[5]!, actual[6]!, H, hR]
      let solver := mkAppN (mkConst (ns ++ `regular_on_fixed_sectors)) args
      forallBoundedTelescope (← inferType solver) (some 2) fun order _ => do
        let full := fixed ++ order
        let applied := mkAppN solver order
        discard <| store (ns ++ `on_source_interval) full applied
  logInfo "actual original21 protected sectors, source sets, extension and reference: constructed native complete regular inverse on a positive interval, no reference-margin or solver premise"

elab "retain_original_regular_source_interval" : command => liftTermElabM do
  let h ← getConstInfo (ns ++ `on_source_interval)
  forallBoundedTelescope h.type (some 23) fun x t => do
    let cached ← packPrefix (ns ++ `Types) x t
    let raw := mkAppN (mkConst (ns ++ `on_source_interval)) x
    let selected ← store (ns ++ `selected) x raw false (some cached)
    select ns x selected
  logInfo "fixed the original regular f, both terminal plateaus, characteristic and elliptic certificates, cutoff and solver budgets BEFORE the final contraction"

/-- Project the genuine stationary/elliptic/retarded charts, then choose the
single global full phase on their PHYSICAL union and original source cell. -/
elab "construct_original_regular_phase_and_incidence" : command => liftTermElabM do
  let sectorNS := ns ++ `Sector
  let incNS := ns ++ `Incidence
  let stationary := ns ++ `fact9
  forallBoundedTelescope (← getConstInfo stationary).type (some 24) fun x _ => do
    unless x.size == 24 do throwError "original regular phase: expected actual per-center stationary sector"
    selectCompact sectorNS x (mkAppN (mkConst stationary) x)
    let root := .proj ``And 0 (mkAppN (mkConst (ns ++ `fact15)) x)
    discard <| store (sectorNS ++ `rootBuffer) x root
  let all := sectorNS ++ `continuation
  forallBoundedTelescope (← getConstInfo all).type (some 26) fun x _ => do
    unless x.size == 26 do throwError "original regular phase: expected sector, independent SOURCE SIGN and original patch"
    selectCompact incNS x (mkAppN (mkConst all) x)
  let f := ns ++ `f
  forallBoundedTelescope (← getConstInfo f).type (some 23) fun fixed _ => do
    let n := mkApp (mkConst ``Nat.succ) fixed[0]!
    let hn := fixed[1]!
    let original := #[n] ++ fixed[1:21].toArray
    let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n, hn, original[20]!]
    let hμ := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure) (original.set! 20 cap)
    let hr := mkAppN (mkConst (protectedNS ++ `fact2)) original
    let screened ← mkAppM (ns ++ `screened_pos) #[hn, hr, hμ]
    let core ← mkAppM (ns ++ `core_spec) #[hn, screened]
    let coreAll := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 core))
    let src := mkAppN (mkConst (protectedNS ++ `Csrc)) #[n, hn]
    forallBoundedTelescope (← inferType src) (some 1) fun patch _ => do
      let a := patch[0]!
      let base := fixed.push a
      let cert := mkAppN (mkConst (ns ++ `fact11)) fixed
      forallBoundedTelescope (← inferType cert) (some 1) fun center _ => do
        let p := center[0]!
        let sp := fixed.push p
        withLocalDeclD `negative (mkConst ``Bool) fun negative => do
          let common := sp.push a
          let ap := sp ++ #[negative,a]
          let pair := center.push negative
          let get (q : Name) := mkAppN (mkConst (sectorNS ++ q)) sp
          let inc (q : Name) := mkAppN (mkConst (incNS ++ q)) ap
          let T := mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.T) #[n, hn, a]
          let chart := get `chart
          let idx ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.index #[chart]
          let K := mkAppN (mkConst (ns ++ `primarySet)) #[fixed[0]!, get `z, get `εcarrier, inc `V]
          let K ← store (incNS ++ `KP) ap K true
          let compact ← mkAppM (ns ++ `primarySet_compact) #[get `z, get `εcarrier, inc `fact1]
          let compact ← store (incNS ++ `KP_compact) ap compact
          let ta := (← inferType T).getAppArgs
          let ca := (← inferType chart).getAppArgs
          unless ta.size == 4 && ca.size == 7 do throwError "unexpected original chart telescope: patch {ta.size}, sector {ca.size}"
          let atP (q : Name) := mkAppN (mkConst (ns ++ q)) sp
          let window := (← inferType (inc `fact1)).appArg!
          let domain := mkAppN (mkConst `JanetCartan.ResponseTransfer.RetainedFactors.protected_incidence_full_source_domain)
            #[fixed[0]!, ta[1]!, ta[2]!, ta[3]!, T, ca[1]!, ca[2]!, ca[5]!, ca[3]!, ca[6]!, chart,
              atP `evolutionTime, atP `speedGap, atP `rootSize, atP `rootCost, mkApp cert p, get `εcarrier,
              get `fact3, .proj ``And 1 (mkApp coreAll a), window, inc `fact2]
          let domain ← store (incNS ++ `KP_domain) ap domain
          let I ← inferType p
          let fi ← synthInstance (← mkAppM `Finite #[I])
          let phase := mkAppN (mkConst (ns ++ `exists_shared_physical_phase) [.zero])
            #[fixed[0]!, hn, a, I, fi, ← mkLambdaFVars center idx, ← mkLambdaFVars pair K,
              ← mkLambdaFVars pair compact, ← mkLambdaFVars pair domain]
          let h ← store (ns ++ `phase_on_original_patch) base phase
          selectCompact (ns ++ `Phase) base h
          let χ := mkAppN (mkConst (ns ++ `Phase.χ)) base
          discard <| store (ns ++ `Phase.whole_germ) base (mkAppN (mkConst (ns ++ `wholeWindow_source_germ))
            #[n, hn, a, χ, mkAppN (mkConst (ns ++ `Phase.fact3)) base])
          let hp := mkApp (mkAppN (mkConst (ns ++ `Phase.continuation)) base) p
          let smooth := Expr.proj ``And 0 hp
          let raw := (← inferType smooth).appArg!
          discard <| store (incNS ++ `χp) common raw true
          let freeze (q : Name) (v : Expr) : MetaM Unit := do
            discard <| store (incNS ++ q) common v
          freeze `χp_smooth smooth
          freeze `χp_compact (mkAppN (mkConst (ns ++ `compact_sector_phase))
            #[fixed[0]!, idx, χ, mkAppN (mkConst (ns ++ `Phase.fact1)) base])
          freeze `χp_domain (.proj ``And 0 (.proj ``And 1 hp))
          discard <| store (incNS ++ `χp_germ) ap (mkApp (.proj ``And 0 (.proj ``And 1 (.proj ``And 1 hp))) negative)
          -- The complete pullback identity for every admissible frame stays in
          -- `Phase.continuation`. Its actual-Q application is named below.
  logInfo "actual protected original center/patch stationary carrier, full original source phase, ONE cutoff per patch pulled back along every sector and both quadratures"

private partial def nameLeadingLets (base : Name) (params : Array Expr) (h : Expr) : MetaM Expr := do
  let t ← inferType h
  if let .letE nm _ v body _ := t then
    let v ← store (base ++ nm) params v true
    let rest ← store (base ++ Name.mkSimple s!"afterLet_{nm}") params h false (some (body.instantiate1 v))
    nameLeadingLets base params rest
  else return h

/-- Apply the pre-contraction interval to `sourceDilationReference H σ`
itself. Join the rank/frame threshold and the normalized-solver threshold
before the scale or history, uniformly in every stage and every order. -/
elab "construct_original_regular_current_solver" : command => liftTermElabM do
  let top := ns ++ `continuation
  let historyNS := ns ++ `History
  let curNS := ns ++ `Current
  forallBoundedTelescope (← getConstInfo top).type (some 25) fun x _ => do
    unless x.size == 25 do throwError "actual regular inverse: expected original21, numeric protected order and source interval"
    let fixed := x[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) x[0]!
    let hn := x[1]!
    let original := #[n] ++ x[1:21].toArray
    let H := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.H) original[:18].toArray
    let capSpec := mkAppN (mkConst (ns ++ `afterChoice_contractionCap)) fixed
    let capOne ← store (ns ++ `contractionCap_le_one) fixed (.proj ``And 0 (.proj ``And 1 (.proj ``And 1 capSpec)))
    discard <| store (ns ++ `contractionCap_pos) fixed (.proj ``And 0 capSpec)
    let hσ := x[24]!
    let hσone ← mkAppM `le_trans #[.proj ``And 1 hσ, capOne]
    let ref ← mkAppM `JanetCartan.sourceDilationReference #[H, .proj ``And 0 hσ, hσone]
    let G ← store (ns ++ `Gref) x ref true
    let Gmap ← mkAppM `JanetCartan.FlatReference.map #[G]
    let atG := mkAppN (mkConst top) (x ++ #[G, ← mkEqRefl Gmap])
    let frame ← store (ns ++ `reference_frame_margin) x (.proj ``And 0 atG)
    let regular ← store (ns ++ `at_original_reference) x (.proj ``And 1 atG)
    let same := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) original[:18].toArray
    let hR ← mkAppM (ns ++ `radius_lt_same_chart) #[same,
      mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.R_lt_chartRadius) #[n, hn]]
    let protect (q : Name) := mkAppN (mkConst (protectedNS ++ q)) original
    forallBoundedTelescope (← inferType regular) (some 7) fun order _ => do
      unless order.size == 7 do throwError "actual regular inverse: expected seven numeric history-order inputs"
      let params := x ++ order
      let reg := mkAppN regular order
      let geo := mkAppN (mkConst (ns ++ `actual_history_frames))
        #[n, hn, G, hR, x[21]!, x[22]!, protect `δ, protect `fact5, frame,
          order[0]!, order[1]!, order[2]!, order[3]!, order[4]!, order[6]!]
      let sr ← store (historyNS ++ `Sregular) params (← mkAppM ``Classical.choose #[reg]) true
      let rr ← store (historyNS ++ `regularSpec) params (← mkAppM ``Classical.choose_spec #[reg]) false
        (some ((← whnf (← inferType reg)).appArg!.beta #[sr]))
      let sg ← store (historyNS ++ `Sgeometry) params (← mkAppM ``Classical.choose #[geo]) true
      let gg ← store (historyNS ++ `geometrySpec) params (← mkAppM ``Classical.choose_spec #[geo]) false
        (some ((← whnf (← inferType geo)).appArg!.beta #[sg]))
      let S ← store (historyNS ++ `S) params (← mkAppM ``max #[sr, sg]) true
      let lr ← mkAppM `le_max_left #[sr, sg]
      let lg ← mkAppM `le_max_right #[sr, sg]
      discard <| store (historyNS ++ `hS) params (← mkAppM `le_trans #[.proj ``And 0 rr, lr])
      withLocalDeclD `R₀ (mkConst `Real) fun R₀ => do
        withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S, R₀]) fun hR₀ => do
          let regAt := mkAppN (.proj ``And 1 rr) #[R₀, ← mkAppM `le_trans #[lr, hR₀]]
          let geoAt := mkAppN (.proj ``And 1 gg) #[R₀, ← mkAppM `le_trans #[lg, hR₀]]
          forallBoundedTelescope (← inferType regAt) (some 4) fun data _ => do
            let finalParams := params ++ #[R₀, hR₀] ++ data
            let hmap := mkAppN geoAt data
            let F ← mkAppM `JanetCartan.RevisedGlobal.finiteMap #[Gmap, data[1]!]
            let projected ← store (curNS ++ `projected) finalParams
              (← mkAppM (ns ++ `original_projected_map) #[hn, protect `δ, F, hmap]) true
            discard <| store (curNS ++ `signed_protection) finalParams (mkApp (protect `continuation) projected)
            let actual ← store (curNS ++ `normalized_solver) finalParams (mkAppN regAt data)
            let actual ← nameLeadingLets curNS finalParams actual
            selectCompact curNS finalParams actual
  logInfo "actual original H → sourceDilation H σ, common S BEFORE history; original current signed protection plus single normalized smooth physical inverse, both signed plateaus, exact regular operators and estimates"

/-- Native real source cutoff (index two), kept separate from the complex
retarded input mask. The original inverse bump localizes the true source. -/
elab "retain_original_small_source_product" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (ns ++ `f)).type (some 23) fun fixed _ => do
    let n := mkApp (mkConst ``Nat.succ) fixed[0]!
    let hn := fixed[1]!
    let original := #[n] ++ fixed[1:21].toArray
    let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n, hn, original[20]!]
    let native (q : Name) := mkAppN (mkConst (`JanetCartan.PhysicalSeed.SelectedBoundary ++ q)) (original.set! 20 cap)
    let χ := mkAppN (mkConst (ns ++ `measuredSourceCutoff)) #[n, native `rMeasure, native `hrMeasure]
    let name ← store (ns ++ `χsrc) fixed[:21].toArray χ true
    let orig (q : Name) := mkAppN (mkConst (ns ++ q)) fixed
    let h ← mkAppM (ns ++ `small_source_product) #[hn, mkAppN (mkConst (protectedNS ++ `fact2)) original,
      native `hrMeasure, orig `f, orig `χ₂, orig `r, .proj ``And 0 (orig `afterChoice_χ₃)]
    let t := (← inferType h).replace fun e => if e == χ then some name else none
    let all ← store (ns ++ `original_source_product) fixed h false (some t)
    discard <| store (ns ++ `χsrc_plateau) fixed (.proj ``And 0 all)
    discard <| store (ns ++ `χsrc_mul_χ₂) fixed (.proj ``And 0 (.proj ``And 1 all))
    discard <| store (ns ++ `source_input_plateau) fixed (.proj ``And 0 (.proj ``And 1 (.proj ``And 1 all)))
    discard <| store (ns ++ `source_cell_support) fixed (.proj ``And 1 (.proj ``And 1 (.proj ``And 1 all)))
  logInfo "the real source on the original label/covector cells is precisely the product of the ORIGINAL measured cutoff and inverse bump, with the entire small support protected"

/-- Apply the common physical phase to the actual normalized current Q,
retaining the independent label and covector of every original incidence. -/
elab "realize_original_regular_current_phase" : command => liftTermElabM do
  let curNS := ns ++ `Current
  let sel := curNS ++ `normalized_solver
  forallBoundedTelescope (← getConstInfo sel).type (some 38) fun x _ => do
    let fixed := x[:23].toArray
    let get (q : Name) := mkAppN (mkConst (curNS ++ q)) x
    let cert := mkAppN (mkConst (ns ++ `fact11)) fixed
    let hp := mkAppN (mkConst (ns ++ `phase_on_original_patch)) fixed
    forallBoundedTelescope (← inferType hp) (some 1) fun patch _ => do
      let a := patch[0]!
      forallBoundedTelescope (← inferType cert) (some 1) fun center _ => do
        let p := center[0]!
        let inc := fixed ++ #[p,mkConst ``Bool.false,a]
        let params := x ++ #[p,a]
        let Q := get `Q
        let small := mkAppN (mkConst (ns ++ `Incidence.fact3)) inc
        let frame := mkAppN (mkConst (ns ++ `frameInOriginalPatch))
          #[x[0]!, x[1]!, a, Q, get `hQ, mkAppN (mkConst (ns ++ `sourceMargin)) fixed, get `fact1, small]
        let frame ← store (curNS ++ `sourceFrame) params frame true
        discard <| store (curNS ++ `sourceFrame_val) params (← mkEqRefl Q) false
          (some (← mkEq (.proj ``Subtype 0 frame) Q))
        let phase := mkAppN (mkConst (ns ++ `Phase.continuation)) (fixed ++ #[a,p])
        discard <| store (curNS ++ `phase_pullback) params
          (mkApp (.proj ``And 1 (.proj ``And 1 (.proj ``And 1 phase))) frame)
        discard <| store (curNS ++ `physical_phase_smooth) params
          (mkApp (mkAppN (mkConst (ns ++ `Phase.fact4)) (fixed.push a)) frame)
        forallBoundedTelescope (← inferType cert) (some 1) fun center' _ => do
          let p' := center'[0]!
          let other := mkAppN (mkConst (curNS ++ `sourceFrame)) (x ++ #[p',a])
          discard <| store (curNS ++ `sourceFrame_independent_of_sector) (params.push p')
            (← mkEqRefl frame) false (some (← mkEq frame other))
  logInfo "actual extended Q gives one full physical source phase for all sectors, with literal equality of its coordinate pullbacks"

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | i+1 => part (.proj ``And 1 e) i

/-- Both orientations use the one actual inverse chart and the original
current full phase, on the SAME full label/covector incidence window. -/
elab "apply_original_signed_stationary_branches" : command => liftTermElabM do
  let cur := ns ++ `Current
  let fr := cur ++ `sourceFrame
  forallBoundedTelescope (← getConstInfo fr).type (some 40) fun pars _ => do
    let x := pars[:38].toArray
    let fixed := x[:23].toArray
    let p := pars[38]!
    let a := pars[39]!
    withLocalDeclD `negative (mkConst ``Bool) fun negative => do
      let signedArgs := x ++ #[p,negative,a]
      let inc (q : Name) := mkAppN (mkConst (ns ++ `Incidence ++ q)) (fixed ++ #[p,negative,a])
      let sec (q : Name) := mkAppN (mkConst (ns ++ `Sector ++ q)) (fixed.push p)
      let get (q : Name) := mkAppN (mkConst (cur ++ q)) x
      let static (q : Name) := mkAppN (mkConst (ns ++ q)) fixed
      let cp := mkApp (get `C) p
      let flow := mkApp (get `Φ) p
      let ode := mkApp (get `fact3) p
      let chartData := mkApp (get `fact4) p
      let c := sec `chart
      let ca := (← inferType c).getAppArgs
      let frame := mkAppN (mkConst fr) pars
      let grades := mkAppN (mkConst (ns ++ `stationary_current_grades))
        #[x[0]!, x[1]!, a, ca[3]!, get `Q, get `B, static `M, static `sourceMargin, get `fact2, get `fact1]
      let grades ← store (cur ++ `stationary_grades) (x ++ #[p,a]) grades
      let low := Expr.proj ``And 1 (.proj ``And 1 grades)
      discard <| store (cur ++ `active_incidence) signedArgs (mkAppN (inc `fact4) #[frame, low])
      discard <| store (cur ++ `active_dilated_incidence) signedArgs (mkAppN (inc `fact5) #[frame, low])
      discard <| store (cur ++ `source_gradient_range) signedArgs (mkAppN (inc `fact8) #[frame, low])
      let low3 := mkAppN (mkConst (ns ++ `stationary_regular_grade_three))
        #[x[0]!, ca[3]!, get `Q, get `B, static `M, get `fact2]
      let rt := (← inferType (part chartData 0)).appFn!.appArg!
      discard <| store (cur ++ `graph_gradient_range) (x.push p) (mkAppN (sec `fact12)
        #[get `Q, low3, rt, flow, cp, part chartData 7, part chartData 8, part chartData 9,
          part chartData 13, part chartData 14])
      let hp := mkApp (static `fact11) p
      let hs := part ode 1
      let fa := (← inferType hs).getAppArgs
      let ra ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.sourceRadius #[c]
      let pos ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.rootRadius_pos #[c]
      let clk := mkAppN (mkConst (ns ++ `stationary_initial_clock))
        #[x[0]!, fa[fa.size-5]!, fa[fa.size-4]!, ra, fa[fa.size-2]!, fa[fa.size-6]!, flow, pos, part hp 4, hs]
      let clk ← store (cur ++ `initial_clock) (x.push p) clk
      let native := mkAppN (inc `continuation) #[frame, part grades 0, part grades 1, low,
        flow, cp, ra, part chartData 4, part chartData 5, .proj ``And 1 clk, part chartData 7, part chartData 8,
        part chartData 14, part clk 0, part chartData 2, part chartData 1, part chartData 11, part chartData 9]
      let native ← store (cur ++ `signed_stationary) signedArgs native
      let κ ← store (cur ++ `κ) signedArgs (← mkAppM ``Classical.choose #[native]) true
      discard <| store (cur ++ `stationary) signedArgs (← mkAppM ``Classical.choose_spec #[native]) false
        (some ((← whnf (← inferType native)).appArg!.beta #[κ]))
  logInfo "actual full current source, original εcarrier/window and all four independent source-sign/adjoint critical graphs, phase zero, invertible averaged Hessians and all retained segments"

/-- The gap is the numerical angular accuracy requested by the original
incidence decomposition. It precedes σ. No smallness of the current frame,
flow estimate, successful chart, or inverse is assumed. -/
elab "apply_actual_graph_momentum_cap" : command => liftTermElabM do
  let graph := ns ++ `Graph
  let gsec := graph ++ `Sector
  forallBoundedTelescope (← getConstInfo (ns ++ `f)).type (some 23) fun fixed _ => do
    let n := mkApp (mkConst ``Nat.succ) fixed[0]!
    let hn := fixed[1]!
    let original := #[n] ++ fixed[1:21].toArray
    let H := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.H) original[:18].toArray
    let cert := mkAppN (mkConst (ns ++ `fact11)) fixed
    withLocalDeclD `γ (mkConst `Real) fun γ => do
      let zero := (← inferType (mkAppN (mkConst (protectedNS ++ `fact5)) original)).appFn!.appArg!
      withLocalDeclD `hγ (← mkAppM ``LT.lt #[zero, γ]) fun hγ => do
        let pars := fixed ++ #[γ, hγ]
        let nativeFrame := mkAppN (mkConst `JanetCartan.PhysicalInitialization.exists_reference_tolerance_for_physical_frame_admission)
          #[n, original[4]!, mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.b) #[n,hn],
            original[5]!, original[6]!, γ, γ, hγ, hγ]
        let ηframe ← store (graph ++ `ηframe) pars (← mkAppM ``Classical.choose #[nativeFrame]) true
        let frameSpec ← store (graph ++ `frameTolerance) pars (← mkAppM ``Classical.choose_spec #[nativeFrame]) false
          (some ((← whnf (← inferType nativeFrame)).appArg!.beta #[ηframe]))
        let framePos ← store (graph ++ `ηframe_pos) pars (part frameSpec 0)
        discard <| store (graph ++ `frame_admission) pars (.proj ``And 1 frameSpec)
        forallBoundedTelescope (← inferType cert) (some 1) fun center _ => do
          let p := center[0]!
          let sp := fixed.push p
          let gp := pars.push p
          let get (q : Name) := mkAppN (mkConst (ns ++ `Sector ++ q)) sp
          let chart := get `chart
          let ca := (← inferType chart).getAppArgs
          let atP (q : Name) := mkAppN (mkConst (ns ++ q)) sp
          let full := mkAppN (mkConst `JanetCartan.PhysicalPrimary.CharacteristicAdjointMomentum.exists_physical_history_graph_momentum_admission)
            #[fixed[0]!, ca[1]!, ca[2]!, ca[5]!, ca[3]!, ca[6]!, chart, get `rootBuffer,
              atP `evolutionTime, atP `speedGap, atP `rootSize, atP `rootCost, mkApp cert p, get `εcarrier,
              get `fact2, get `fact6, get `fact4, original[4]!,
              mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.b) #[n,hn], original[5]!, original[6]!, γ, hγ]
          let η ← store (gsec ++ `η) gp (← mkAppM ``Classical.choose #[full]) true
          let spec ← store (gsec ++ `ηSpec) gp (← mkAppM ``Classical.choose_spec #[full]) false
            (some ((← whnf (← inferType full)).appArg!.beta #[η]))
          let hη ← store (gsec ++ `η_pos) gp (part spec 0)
          discard <| store (gsec ++ `admission) gp (.proj ``And 1 spec)
          let I ← inferType p
          let fi ← synthInstance (← mkAppM `Finite #[I])
          let interval := mkAppN (mkConst (ns ++ `source_interval_for_graph_and_frame_margins) [.zero])
            #[n, hn, H, mkAppN (mkConst (ns ++ `contractionCap)) fixed,
              mkAppN (mkConst (ns ++ `contractionCap_pos)) fixed, I, fi,
              ← mkLambdaFVars center η, ← mkLambdaFVars center hη, ηframe, framePos]
          let raw ← store (graph ++ `source_interval) pars interval
          select graph pars raw
        let margin := mkAppN (mkConst (graph ++ `continuation)) pars
        forallBoundedTelescope (← inferType margin) (some 2) fun scale _ => do
          let q := pars ++ scale
          let hσreg ← store (graph ++ `regular_scale) q (← mkAppM (ns ++ `regular_scale_of_graph_scale)
            #[scale[1]!, mkAppN (mkConst (graph ++ `fact1)) pars])
          let refParams := fixed ++ #[scale[0]!, hσreg]
          let G := mkAppN (mkConst (ns ++ `Gref)) refParams
          let orig (a : Name) := mkAppN (mkConst (`JanetCartan.PhysicalSeed.OriginalBoundary ++ a)) #[n, hn]
          let hR ← mkAppM (ns ++ `radius_lt_same_chart) #[mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5)
            original[:18].toArray, orig `R_lt_chartRadius]
          let S := mkAppN (mkConst (ns ++ `History.S)) refParams
          forallBoundedTelescope (← inferType S) (some 7) fun order _ => do
            let before := q ++ order
            let regBefore := refParams ++ order
            let hframe := mkAppN (mkAppN (mkConst (graph ++ `frame_admission)) pars)
              #[G, orig `R, orig `b_pos, orig `b_lt_R, hR, .proj ``And 1 (mkAppN margin scale),
                order[0]!, order[1]!, order[2]!, order[3]!, order[4]!, order[6]!]
            let stFrame ← store (graph ++ `Sframe) before (← mkAppM ``Classical.choose #[hframe]) true
            let frameSpec ← store (graph ++ `frameHistorySpec) before (← mkAppM ``Classical.choose_spec #[hframe]) false
              (some ((← whnf (← inferType hframe)).appArg!.beta #[stFrame]))
            discard <| store (graph ++ `frame_current) before (.proj ``And 1 frameSpec)
            forallBoundedTelescope (← inferType cert) (some 1) fun center _ => do
              let p := center[0]!
              let now := before.push p
              let admit := mkAppN (mkConst (gsec ++ `admission)) (pars.push p)
              let hs := mkAppN admit #[G, orig `R, orig `b_pos, orig `b_lt_R, hR,
                mkApp (.proj ``And 0 (mkAppN margin scale)) p, order[0]!, order[1]!, order[2]!, order[3]!, order[4]!, order[6]!]
              let st ← store (gsec ++ `S) now (← mkAppM ``Classical.choose #[hs]) true
              let hs ← store (gsec ++ `currentSpec) now (← mkAppM ``Classical.choose_spec #[hs]) false
                (some ((← whnf (← inferType hs)).appArg!.beta #[st]))
              discard <| store (gsec ++ `current) now (.proj ``And 1 hs)
              let common ← mkAppM (ns ++ `common_graph_frame_threshold) #[mkAppN S order, stFrame, ← mkLambdaFVars center st]
              let s ← store (graph ++ `S) before (← mkAppM ``Classical.choose #[common]) true
              let bounds ← store (graph ++ `thresholds) before (← mkAppM ``Classical.choose_spec #[common]) false
                (some ((← whnf (← inferType common)).appArg!.beta #[s]))
              discard <| store (graph ++ `hS) before (← mkAppM `le_trans
                #[mkAppN (mkConst (ns ++ `History.hS)) regBefore, part bounds 0])
              withLocalDeclD `R₀ (mkConst `Real) fun R₀ => do
                withLocalDeclD `hR₀ (← mkAppM ``LE.le #[s, R₀]) fun hR₀ => do
                  let hSr ← store (graph ++ `regular_reached) (before ++ #[R₀,hR₀])
                    (← mkAppM `le_trans #[part bounds 0, hR₀])
                  let hSf ← store (graph ++ `frame_reached) (before ++ #[R₀,hR₀])
                    (← mkAppM `le_trans #[part bounds 1, hR₀])
                  let hSp ← mkAppM `le_trans #[mkApp (.proj ``And 1 (.proj ``And 1 bounds)) p, hR₀]
                  let rFix := regBefore ++ #[R₀, hSr]
                  let solver := mkAppN (mkConst (ns ++ `Current.normalized_solver)) rFix
                  forallBoundedTelescope (← inferType solver) (some 4) fun data _ => do
                    let cur (a : Name) := mkAppN (mkConst (ns ++ `Current ++ a)) (rFix ++ data)
                    let params := before ++ #[R₀, hR₀] ++ data
                    let cp := params.push p
                    let frame := mkAppN (mkConst (graph ++ `frame_current)) (before ++ #[R₀,hSf] ++ data)
                    let frame ← store (graph ++ `current_frame_bounds) params frame
                    discard <| store (graph ++ `current_frame_margin) params (.proj ``And 1 (.proj ``And 1 frame))
                    let full := mkAppN (mkConst (gsec ++ `current)) (now ++ #[R₀, hSp] ++ data)
                    let ode := mkApp (cur `fact3) p
                    let phase := mkApp (cur `fact4) p
                    let actual := mkAppN (.proj ``And 1 (.proj ``And 1 full))
                      #[mkApp (cur `Φ) p, mkApp (cur `C) p, part ode 1, part ode 2, part phase 4,
                        part ode 8, part phase 9, part phase 7]
                    let momentum ← store (graph ++ `momentum) cp actual
                    discard <| store (graph ++ `original_momentum) cp
                      (mkApp momentum (mkAppN (mkConst (ns ++ `aperture)) fixed))
                    discard <| store (graph ++ `regular_solver) params (mkAppN solver data)
                    discard <| store (graph ++ `signed_protection) params (cur `signed_protection)
  logInfo "one actual post-sector source cap and prehistory threshold: global current-frame C6 tolerance AND full-mask original momentum tolerance, on the SAME H/f/phase/normalized inverse"

end JanetCartan.PhysicalInitialization.OriginalRegularTemplate
end
