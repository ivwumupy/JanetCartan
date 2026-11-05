module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Concrete original-current applications for all native source ranges. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRetardedRangesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate
private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | i+1 => part (.proj ``And 1 e) i

elab "retain_original_native_source_ranges" : command => liftTermElabM do
  let cur := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
  let reg := `JanetCartan.PhysicalInitialization.OriginalRegular
  let geom := `JanetCartan.PhysicalPrimary.OriginalRetardedGeometry
  let gap := `JanetCartan.PhysicalPrimary.OriginalRetardedGap
  let inc := `JanetCartan.PhysicalPrimary.OriginalIncidence
  let whole := `JanetCartan.PhysicalPrimary.OriginalRetardedWhole
  let prim := `JanetCartan.PhysicalPrimary.OriginalRetardedPrimitives
  let ns := `JanetCartan.PhysicalPrimary.OriginalRetardedRanges
  let some body := (← getConstInfo (cur ++ `normalized_solver)).value? (allowOpaque := true)
    | throwError "native source ranges: exact original normalized-solver application is not exposed"
  forallBoundedTelescope (← getConstInfo (cur ++ `sourceFrame)).type (some 38) fun x _ => do
    let fixed := x[:23].toArray
    let weak := body.beta x
    unless weak.isAppOfArity (reg ++ `Current.normalized_solver) 38 do
      throwError "native source ranges: original current38 is not the SAME direct application"
    let wa := weak.getAppArgs
    let sectors := mkAppN (mkConst (cur ++ `fact3)) x
    forallBoundedTelescope (← inferType sectors) (some 1) fun sector _ => do
      let p := sector[0]!
      let sp := fixed.push p
      let chart := mkAppN (mkConst (reg ++ `Sector.chart)) sp
      let index ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.index #[chart]
      let z := mkAppN (mkConst (reg ++ `Sector.z)) sp
      let ε := mkAppN (mkConst (reg ++ `Sector.εcarrier)) sp
      let f := mkAppN (mkConst (reg ++ `f)) fixed
      let L := mkAppN (mkConst (reg ++ `L)) fixed
      let hL ← mkAppM `le_trans #[← mkAppM
        `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.radialThreshold_ge_one #[f],
          mkAppN (mkConst (reg ++ `hL)) fixed]
      let hLp ← mkAppM (ns ++ `original_threshold_pos) #[hL]
      let aperture := mkAppN (mkConst (reg ++ `aperture)) fixed
      let angular := mkAppN (mkConst (reg ++ `angular)) sp
      let cone := mkAppN (mkConst (reg ++ `Sector.fact7)) sp
      let endpoint := mkAppN (mkConst (reg ++ `fact24)) (sp ++ #[L,← mkAppM `le_refl #[L]])
      let hfreq ← mkAppM (prim ++ `selected_multiplier_in_native_frequency)
        #[f,p,hL,ε,aperture,angular,cone,part endpoint 0]
      discard <| store (ns ++ `frequency_support) (x.push p) hfreq
      discard <| store (ns ++ `radial_gradient_range) (x.push p)
        (mkAppN (mkConst (reg ++ `Current.graph_gradient_range)) (wa.push p))
      let momentum := mkAppN (mkConst (gap ++ `original_momentum)) (x.push p)
      let hmom ← forallBoundedTelescope (← inferType momentum) (some 6) fun point _ => do
        mkLambdaFVars point (part (mkAppN momentum point) 1)
      let frame := mkAppN (mkConst (cur ++ `sourceFrame)) x
      forallBoundedTelescope (← inferType frame) (some 1) fun patch _ => do
        let a := patch[0]!
        let cp := x ++ sector ++ patch
        let stat := sp.push a
        let Q := mkApp frame a
        let n ← mkAppM ``HAdd.hAdd #[x[0]!,mkNatLit 1]
        let T := mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.T)
          #[n,x[1]!,a]
        let φpos ← mkAppOptM `JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily.fullSourcePhaseInCoordinates
          #[some x[0]!,none,none,none,some T,some index,some Q]
        let wholeSpec := mkAppN (mkConst (reg ++ `wholeWindow_spec)) #[n,x[1]!,a]
        let foot := mkAppN (mkConst (geom ++ `box_in_source)) stat
        let hwhole := mkAppN (mkConst (cur ++ `whole_gradient_range)) (x.push a)
        let germ := mkAppN (mkConst (whole ++ `whole_χp_germ)) stat
        let band ← forallBoundedTelescope (← inferType germ) (some 2) fun point _ => do
          let y := Expr.proj ``Prod 0 point[0]!
          let c := Expr.proj ``Prod 1 point[0]!
          let hxy := mkAppN foot #[y,.proj ``And 0 point[1]!]
          let hc := mkAppN (part wholeSpec 2) #[c,.proj ``And 1 point[1]!]
          mkLambdaFVars point (mkAppN hwhole #[index,y,hxy,c,hc])
        discard <| store (ns ++ `whole_source_band) cp band
        withLocalDeclD `negative (mkConst ``Bool) fun negative => do
          let pars := x ++ #[p,negative,a]
          let signed := mkAppN (mkConst (reg ++ `Current.source_gradient_range)) (wa ++ #[p,negative,a])
          discard <| store (ns ++ `active_source_band) pars
            (← mkAppM (ns ++ `unsigned_source_band_of_function_choice) #[negative,φpos,signed])
          let rawGap := mkAppN (mkConst (gap ++ `source_gap)) (pars ++ #[L,hLp])
          let χ := mkAppN (mkConst (inc ++ `χ)) (fixed ++ #[p,negative,a])
          let β ← mkAppM `JanetCartan.RegularSector.FinitePdo.selectedEndpointMultiplier #[f,p,L]
          let sourceDomain ← forallBoundedTelescope (← inferType rawGap) (some 1) fun y rest => do
            let .forallE _ domain _ _ ← whnf rest
              | throwError "native inactive gap: missing original source-domain predicate"
            mkLambdaFVars y domain
          let C := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalProtected.Csrc) #[n,x[1]!,a]
          let gapValue := mkAppN (mkConst (inc ++ `gap)) (fixed ++ #[p,negative,a])
          let hgap := mkAppN (mkConst (ns ++ `source_gap_of_pointwise_signed_phase))
            #[x[0]!,negative,φpos,sourceDomain,C,χ,β,gapValue,rawGap]
          let hgap ← store (ns ++ `transported_source_gap) pars hgap
          logInfo "native inactive gap: pointwise signed source transported to whole-function choice"
          let e ← mkAppM `JanetCartan.CompatibleResponse.primaryCoordinateChange #[index]
          let φneg ← mkAppOptM `JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily.negativeFullSourcePhaseInCoordinates
            #[some x[0]!,none,none,none,some T,some index,some Q]
          let signedφ ← mkAppM ``ite #[← mkEq negative (mkConst ``Bool.true),φneg,φpos]
          let X := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalProtected.Xsrc) #[n,x[1]!,a]
          let V := mkAppN (mkConst (reg ++ `wholeWindow)) #[n,x[1]!,a]
          let source := mkAppN (mkConst (ns ++ `original_gap_on_native_box))
            #[x[0]!,e,z,signedφ,χ,β,X,C,V,ε,gapValue,mkAppN (mkConst (reg ++ `Sector.fact2)) sp,
              foot,part wholeSpec 2,hgap]
          let source ← store (ns ++ `inactive_source_gap) pars source
          let ψ ← mkAppM `JanetCartan.RegularSector.Characteristic.ConicPhase.curriedPhase
            #[← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.radialSection #[chart],
              mkApp (mkAppN (mkConst (cur ++ `C)) x) p]
          let hmask ← mkAppM `le_of_lt #[← mkAppM
            `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.maskRadius_pos #[chart]]
          let htwo := mkAppN (mkConst (gap ++ `twice_common_le_gap)) pars
          let common ← mkAppM (ns ++ `common_le_original_gap)
            #[mkAppN (mkConst (inc ++ `Common.fact0)) fixed,htwo]
          let forward ← forallBoundedTelescope (← inferType source) (some 7) fun point _ => do
            mkLambdaFVars point (← mkAppM `le_trans #[common,mkAppN source point])
          discard <| store (ns ++ `inactive_forward_gap) pars forward
          let F ← forallBoundedTelescope (← inferType hmom) (some 6) fun point _ => do
            let mem ← inferType point[5]!
            unless mem.isAppOfArity ``Membership.mem 5 do throwError "native momentum: expected retained frequency membership"
            return mem.getAppArgs[3]!
          let mask := (← inferType hmask).appArg!
          let commonMargin := (← inferType common).appFn!.appArg!
          let adj := mkAppN (mkConst (ns ++ `original_adjoint_gap_on_native_box))
            #[x[0]!,z,signedφ,χ,β,ψ,V,F,ε,mask,gapValue,commonMargin,hmask,htwo,hfreq,source,hmom]
          discard <| store (ns ++ `inactive_adjoint_gap) pars adj
  logInfo "SAME original current: positive phase bands on BOTH signed windows, full whole-box band, literal selected frequency carrier and actual forward/adjoint inactive gaps on the entire native box and elapsed interval"

end JanetCartan.PhysicalPrimary.OriginalRetardedRangesTemplate
