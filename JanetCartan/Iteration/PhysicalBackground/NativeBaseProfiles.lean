module

public import JanetCartan.Iteration.PhysicalBackground.NativeSourceProfiles
public import JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
public import JanetCartan.Iteration.PhysicalMean.CanonicalFieldProfiles
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# Actual uncut current base and full-strain profiles

Specialize the physical field producer to the *same* current zero-inverse
initializer, source cutoff, flat reference, limiting-mean field and admissible
history as `NativeMeasuredCancellation.Vbase`. Use the proved native raw grade
bound, not a hypothesis on the base or strain. Both constants and the joined
numerical threshold precede the histories. The profile holds on the original
closed `b`-ball, in particular throughout the measured six-buffer
(`app:ch_background:eq:bg-current-profile`, `main:prop:mean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
open JanetCartan JanetCartan.ContinuumRow JanetCartan.PositiveBackground

public meta section
namespace JanetCartan.PhysicalBackground.NativeBaseProfilesApplication
open Lean Meta Elab Term Command
private def localTerm (bindings : List (Name × Expr)) (code : String) (target? : Option Expr := none) : TermElabM Expr :=
  _root_.JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code target?

private def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq actual target do throwError "native base: wrong target for {name}"
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar || type.hasLevelMVar ||
      value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "native base: hidden dependence in {name}"
  let name := `JanetCartan.PhysicalBackground.NativeBaseProfiles ++ name
  if data then
    addDecl (.defnDecl {name, type, value, levelParams := [], hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, type, value, levelParams := []}) (forceExpose := true)
  return mkAppN (mkConst name) params

elab "realize_native_base_strain_profiles" : command => liftTermElabM do
  let sr := `JanetCartan.PhysicalBackground.NativeSourceProfiles
  let ad := `JanetCartan.PhysicalBackground.NativeAdmission
  let ref := `JanetCartan.PhysicalBackground.NativeReferenceSource
  let co := `JanetCartan.PhysicalBackground.NativeCoefficientProfiles
  let measured := `JanetCartan.PhysicalBackground.NativeMeasuredCancellation
  let oldRaw := `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original
  let producer := `JanetCartan.PhysicalMean.exists_history_fixedSourceBase_profile
  let info ← getConstInfo (sr ++ `raw_grade_profile)
  forallBoundedTelescope info.type (some 33) fun fixed _ => do
    let n := fixed[0]!
    let hn := fixed[1]!
    let original := fixed[:21].toArray
    let selected := original.set! 20 (mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[n,hn,original[20]!])
    let src (name : Name) := mkAppN (mkConst (ref ++ name)) selected
    let geom (name : Name) := mkAppN (mkConst (`JanetCartan.PhysicalSeed.OriginalBoundary ++ name)) #[n,hn]
    let Gref := mkAppN (mkConst (co ++ `Gref)) fixed[:23].toArray
    let H := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.H) fixed[:18].toArray
    let sameDomain := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) fixed[:18].toArray
    let hR ← localTerm [(`Gref,Gref),(`H,H),(`R,geom `R),(`sameDomain,sameDomain),(`original,geom `R_lt_chartRadius)]
      "(by change R < H.domain.chartRadius; rw [sameDomain]; exact original : R < Gref.domain.chartRadius)"
    let index ← inferType (mkAppN (mkConst `JanetCartan.PhysicalBackground.NativeDensity.geometryIndex) original)
    let fintype ← synthInstance (← mkAppM ``Fintype #[index])
    let chi ← localTerm [(`n,n),(`hr,src `hr),(`hcell,src `hcell)] "FixedCutoffs.periodic (n := n) hr hcell 2"
    let hchi ← localTerm [(`n,n),(`hr,src `hr),(`hcell,src `hcell)] "FixedCutoffs.periodic_smooth (n := n) hr hcell 2"
    let X0 := src `X0
    let hX ← localTerm [(`hx,src `X0_smooth),(`X0,X0),(`R,geom `R)] "(hx.contDiffOn : ContDiffOn ℝ ∞ X0 (ball 0 R))"
    withLocalDeclD `rBase (mkConst ``Nat) fun rb => do
      let rSource ← localTerm [(`rBase,rb),(`n,n)] "rBase + 1 + n"
      let partialRaw := mkAppN (mkConst (sr ++ `raw_grade_profile)) (fixed.push rSource)
      forallBoundedTelescope (← inferType partialRaw) (some 4) fun ord _ => do
        let fixedOrders := fixed ++ #[rb] ++ ord
        let sourceBefore := fixed ++ #[rSource] ++ ord
        let source (name : Name) := mkAppN (mkConst (sr ++ name)) sourceBefore
        let hStar ← localTerm [(`n,n),(`rStar,fixed[26]!),(`rb,rb),(`bound,ord[3]!)]
          "(by change (rb+1+n) + (2*(n+1)+14) ≤ rStar at bound; omega : 8 ≤ rStar)"
        let hreserve ← localTerm [(`n,n),(`rStar,fixed[26]!),(`rb,rb),(`bound,ord[3]!)]
          "(by change (rb+1+n) + (2*(n+1)+14) ≤ rStar at bound; omega : rb+3 ≤ rStar)"
        let packet := mkAppN (mkConst producer [.zero]) #[n,index,fintype,Gref,geom `b,geom `R,geom `b_pos,
          geom `b_lt_R,hR,chi,hchi,X0,hX,source `Craw,source `Craw_nonneg,fixed[24]!,fixed[25]!,fixed[26]!,
          rb,fixed[27]!,hStar,hreserve,fixed[29]!]
        let Sfield ← store `fieldS fixedOrders (← mkAppM ``Classical.choose #[packet]) true
        let hs ← mkAppM ``Classical.choose_spec #[packet]
        let hSfield ← store `fieldS_ge_two fixedOrders (.proj ``And 0 hs)
        let S ← store `S fixedOrders (← mkAppM ``Max.max #[source `S,Sfield]) true
        discard <| store `source_le_S fixedOrders (← localTerm [(`Ss,source `S),(`S,S)] "(le_max_left _ _ : Ss ≤ S)")
        discard <| store `field_le_S fixedOrders (← localTerm [(`Sf,Sfield),(`S,S)] "(le_max_right _ _ : Sf ≤ S)")
        discard <| store `hS fixedOrders (← localTerm [(`h,hSfield),(`S,S)] "(h.trans (le_max_right _ _) : 2 ≤ S)")
        let hasC := Expr.proj ``And 1 hs
        let C ← store `C fixedOrders (← mkAppM ``Classical.choose #[hasC]) true
        let hc ← mkAppM ``Classical.choose_spec #[hasC]
        discard <| store `C_nonneg fixedOrders (.proj ``And 0 hc)
        let cont := Expr.proj ``And 1 hc
        let rawAt := mkAppN partialRaw ord
        forallBoundedTelescope (← inferType rawAt) (some 7) fun rest _ => do
          let hist := rest[:6].toArray
          let inputs := fixedOrders ++ rest
          let all := fixed ++ hist
          let R0 := hist[0]!
          let scale := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[R0,hist[2]!]
          withLocalDeclD `hFieldThreshold (← mkAppM ``LE.le #[Sfield,R0]) fun hField => do
            let inputs := inputs.push hField
            let raw := mkAppN (mkConst (ad ++ `raw)) all
            let rawBody := (((← getConstInfo (ad ++ `raw)).value! (allowOpaque := true)).beta all).headBeta
            unless rawBody.isAppOfArity (oldRaw ++ `rawCurrent) 47 do throwError "native base: original raw row changed"
            let hraw := mkAppN (mkConst (oldRaw ++ `rawCurrent_mem)) rawBody.getAppArgs
            let full := mkAppN cont (#[R0,hField] ++ hist[2:].toArray ++
              #[raw,hraw,scale,← mkAppM ``le_refl #[scale],mkAppN rawAt rest])
            let V := mkAppN (mkConst (measured ++ `Vbase)) all
            let F ← localTerm [(`Gref,Gref),(`u,hist[3]!)] "RevisedGlobal.finiteMap Gref.map u"
            let fields := [(`F,F),(`V,V),(`b,geom `b),(`R,geom `R),(`C,C),(`T,scale),(`rb,rb)]
            let smooth ← localTerm fields "ContDiffOn ℝ ∞ V (ball 0 R)"
            discard <| store `smooth inputs (.proj ``And 0 full) false (some smooth)
            let high ← localTerm fields ("∀ s : ℕ, cNorm (closedBall 0 b) s V + " ++
              "cNorm (closedBall 0 b) s (linearizedMetric F V) ≤ C s * T ^ (s-rb)")
            discard <| store `base_strain_profile inputs (.proj ``And 1 full) false (some high)
  logInfo "native zero-raw initializer and FULL physical strain controlled on original closed b, constants before history; same measured Vbase"

end JanetCartan.PhysicalBackground.NativeBaseProfilesApplication
end

realize_native_base_strain_profiles
