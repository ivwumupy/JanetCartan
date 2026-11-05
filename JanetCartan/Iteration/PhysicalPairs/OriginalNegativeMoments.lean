module
public import JanetCartan.Iteration.PhysicalPairs.OriginalFirstMask
public import JanetCartan.Iteration.PhysicalPairs.OriginalNegativeRows

/-! # Original protected annulus and measured signed source negative norms

The fixed positive lower frequency is extracted from the original compact
`Ksource` and its proved exclusion of zero. Apply the quadrature estimate to
the same original full waves, raw frame, one physical measurement and original
external `λ*beat`. `app:ch_regular:eq:inverse-remainder` consumes these moments.
-/
public meta section
set_option maxHeartbeats 900000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalNegativeMoments
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalNegativeMoments
private def nr := `JanetCartan.PhysicalPairs.OriginalNegativeRows
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def geo := `JanetCartan.PhysicalPairs.OriginalMaskGeometry
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def rows := `JanetCartan.PhysicalPairs.OriginalMaskRows
private def col := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def down (e : Expr) : Nat → Expr | 0 => e | k+1 => down (.proj ``And 1 e) k
private def part (e : Expr) (k : Nat) := Expr.proj ``And 0 (down e k)
elab "price_original_negative_source " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (fm ++ `first_mask)).type (some 41) fun p _ => do
    let b := p[:37].toArray
    let fixed := p[:22].toArray
    let d := p[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let N := a `JanetCartan.embeddingDimension #[n]
    let K := a (col ++ `Ksource) fixed
    if piece.getNat == 0 then
      let hs := a (col ++ `source_normalized_interior) fixed
      let hn ← forallBoundedTelescope (← inferType hs) (some 2) fun arg _ => mkLambdaFVars arg (.proj ``And 0 (mkAppN hs arg))
      discard <| store (ns ++ `positive_lower) fixed (a (nr ++ `lower) #[d,K,a (col ++ `source_compact) fixed,hn])
      return
    let pre := a (ns ++ `positive_lower) fixed
    if piece.getNat == 1 then
      let price ← mkAppM ``Classical.choose #[pre]
      let named ← store (ns ++ `lower) fixed price true
      let spec ← mkAppM ``Classical.choose_spec #[pre]
      for (k,pf) in [(`lower_pos,Expr.proj ``And 0 spec),(`lower_on_original,Expr.proj ``And 1 spec)] do
        discard <| store (ns ++ k) fixed pf false (some ((← inferType pf).replace fun e => if e == price then some named else none))
      return
    let c := a (ns ++ `lower) fixed
    let z := p[:38].toArray
    let early := b ++ p[38:40].toArray
    let C := p[38]!
    let gf := (← inferType (a (hist ++ `historyMap) b)).bindingBody!
    let fix := gf.getAppArgs[:23].toArray
    let sa := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.GraphFamily).value! (allowOpaque := true)).beta gf.getAppArgs
    let coeff := sa.getAppArgs.back!.getAppArgs
    let AQ := a (op ++ `AQ) coeff
    let hAQ := a (op ++ `fact1) coeff
    let V := a (mask ++ `chart) fix
    let W := a (world ++ `W) fix
    let hχ := a (mask ++ `χ₂_smooth) fix
    let χ := (← inferType hχ).appArg!
    let hψ := a (mask ++ `χ₃_smooth) fix
    let ψ := (← inferType hψ).appArg!
    let hη := a (mask ++ `χsrc_smooth) fix
    let η := (← inferType hη).appArg!
    let D := a `JanetCartan.PhysicalPairs.OriginalSignedFrames.jointProfile p[:36].toArray
    let P := a (fm ++ `phaseCost) #[D]
    let G := mkApp P (mkNatLit 0)
    let high ← mkAppM ``HAdd.hAdd #[← mkAppM ``max #[c,G],← mkNumeral (mkConst ``Real) 1]
    if piece.getNat == 2 then
      let pf := a (nr ++ `exists_price) #[d,N,χ,ψ,hψ,a (mask ++ `χ₃_compact) fix,a (mask ++ `χ₃_on_χ₂) fix,c,high,a (ns ++ `lower_pos) fixed,
        P,a (rows ++ `sourceProfile) b,AQ,C,a (rows ++ `sourceProfile_nonneg) b,hAQ,p[39]!]
      discard <| store (ns ++ `price_before_waves) early pf
      return
    let low := a (ns ++ `price_before_waves) early
    let price ← mkAppM ``Classical.choose #[low]
    if piece.getNat == 3 then
      let name ← store (ns ++ `CN) early price true
      let h := part (← mkAppM ``Classical.choose_spec #[low]) 0
      discard <| store (ns ++ `CN_nonneg) early h false (some ((← inferType h).replace fun e => if e == price then some name else none))
      return
    let measured := ((← getConstInfo (fm ++ `measured)).value! (allowOpaque := true)).beta z
    lambdaBoundedTelescope measured 1 fun label row => do
      let t := label[0]!
      let v := row.getAppArgs
      let pt := v[:49].toArray
      let Kf := mkApp (a (fm ++ `fine) b) t
      let φ := mkApp (a (fm ++ `phase) b) t
      let ρ := mkApp (a (fm ++ `frequency) b) t
      let hi := a (hist ++ `measured_history) pt
      let hP := a (fm ++ `phaseCost_nonneg) #[D,a `JanetCartan.PhysicalPairs.OriginalSignedFrames.jointProfile_nonneg p[:36].toArray]
      if piece.getNat == 4 then
        let g := a (nr ++ `geometry) #[d,χ,φ,K,V,c,G,Kf,P,hχ,a (mask ++ `χ₂_compact) fix,a (mask ++ `χ₂_support_chart) fix,
          a (geo ++ `smooth) pt,a (ns ++ `lower_pos) fixed,a (ns ++ `lower_on_original) fixed,part hi 3,hP,
          a (geo ++ `gradient_in_source) pt,a (geo ++ `gradient_upper) pt]
        let jets ← forallBoundedTelescope (← inferType g).bindingDomain! (some 4) fun ys _ => do
          mkLambdaFVars ys (mkAppN (a (geo ++ `higher_jets) pt) ys[:3].toArray)
        discard <| store (ns ++ `source_geometry) b (← mkLambdaFVars label (mkApp g jets))
        return
      let window := part (a (hist ++ `native_window) pt) 0
      let β := a (hist ++ `Labels) b
      let A := a (fm ++ `left) z
      let B := a (fm ++ `right) z
      let M := a (fm ++ `fine) b
      let la := #[d,N,β,V,A,B,C,M,p[40]!]
      let h := down (← mkAppM ``Classical.choose_spec #[low]) 1
      let args := #[V,W,a (mask ++ `chart_open) fix,a (world ++ `W_measurable) fix,a (mask ++ `χ₃_support_chart) fix,η,φ,Kf,ρ,
        mkApp (a (ns ++ `source_geometry) b) t,a (fm ++ `one_of_two) #[ρ,part window 2],part window 3,
        mkApp (a (fm ++ `frame) b) t,mkApp A t,mkApp B t,a (fm ++ `on_chart) #[d,V,η,hη],a (rows ++ `row_smooth) pt,
        a (rows ++ `left_smooth) v,a (rows ++ `right_smooth) v,a (rows ++ `source_jets) pt,a (rows ++ `row_jets) pt,
        mkApp (a (fm ++ `left_bound) la) t,mkApp (a (fm ++ `right_bound) la) t,pt[45]!,mkApp (a (fm ++ `measured) z) t,a (rows ++ `represented_realization) v]
      let pf ← mkLambdaFVars label (mkAppN h args)
      let name := a (ns ++ `CN) early
      discard <| store (ns ++ `negative_moments) p pf false (some ((← inferType pf).replace fun e => if e == price then some name else none))
price_original_negative_source 0
price_original_negative_source 1
price_original_negative_source 2
price_original_negative_source 3
price_original_negative_source 4
price_original_negative_source 5
end JanetCartan.PhysicalPairs.OriginalNegativeMoments
end
