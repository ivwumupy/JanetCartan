module
public import JanetCartan.Iteration.PhysicalPairs.OriginalNegativeMoments
public import JanetCartan.Iteration.PhysicalPairs.OriginalShiftedCoefficients

/-! # The actual unobserved remainder of every complete original signed source

The SAME measured normalized residual and its SAME inverse act on the actual
once-measured source. Use its true negative Fourier moments, the original
forward/literal-adjoint gain, original coefficient classes, and the fixed true
frequency gap. No unobserved-tail or source localization conclusion is an
input. The only varying analytic input is the stage-13 full-wave derivative
profile. Consumed in `app:ch_regular:eq:finite-expansion`, `main:prop:pairs`.
-/
@[expose] public noncomputable section
namespace JanetCartan.PhysicalPairs.OriginalNeumannTail
theorem half_lt : (1/2 : ℝ) < 1 := by norm_num
theorem unit_price {X C T : ℝ} (h : X ≤ C*T) : X ≤ C*1*T := by simpa only [mul_one] using h
end JanetCartan.PhysicalPairs.OriginalNeumannTail
end
public meta section
set_option maxHeartbeats 900000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalNeumannTail
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalNeumannTail
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def nm := `JanetCartan.PhysicalPairs.OriginalNegativeMoments
private def sh := `JanetCartan.PhysicalPairs.OriginalShiftedCoefficients
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def native := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Native
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def atChoice (key : Name) (args : Array Expr) (h : Expr) : MetaM Expr := do
  let x ← mkAppM ``Classical.choose #[h]
  let named ← store (ns ++ key) args x true
  let proof ← mkAppM ``Classical.choose_spec #[h]
  let ty := (← inferType h).getAppArgs.back!.beta #[named]
  store (ns ++ key ++ `spec) args proof false (some ty)
private def existsAt (e h : Expr) : MetaM Expr := do
  let α ← inferType e
  let t ← inferType h
  let f ← withLocalDeclD `bound α fun x => mkLambdaFVars #[x] (t.replace fun s => if s == e then some x else none)
  mkAppOptM ``Exists.intro #[some α,some f,some e,some h]
elab "price_original_neumann_remainder " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (fm ++ `first_mask)).type (some 41) fun p _ => do
    let b := p[:37].toArray
    let z := p[:38].toArray
    let early := b ++ p[38:40].toArray
    let d := b[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let off := mkApp2 (mkConst ``Nat.add) d (mkNatLit 2)
    let beta := mkApp2 (mkConst ``Nat.add) (a `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[d]) off
    let gf := (← inferType (a (hist ++ `historyMap) b)).bindingBody!
    let fix := gf.getAppArgs[:23].toArray
    let nat := mkConst ``Nat
    withLocalDeclD `observationOrder nat fun s => withLocalDeclD `accuracy nat fun q => do
      let e := early ++ #[s,q]
      let input := p ++ #[s,q]
      if piece.getNat == 0 then
        let hG := a (native ++ `gain_cost_nonneg) fix
        let G ← forallBoundedTelescope (← inferType hG) (some 1) fun k body => mkLambdaFVars k body.appArg!
        let hθ := mkConst (ns ++ `half_lt)
        let ta := (← inferType hθ).getAppArgs
        let θ := ta[ta.size-2]!
        let pf := a `JanetCartan.PhysicalPairs.OriginalTailPrice.inverse_tail #[n,θ,hθ,G,a (sh ++ `D) b,a (nm ++ `CN) early,hG,a (sh ++ `D_nonneg) b,a (nm ++ `CN_nonneg) early,off,s,q]
        discard <| store (ns ++ `budget) e pf
        return
      if piece.getNat == 1 then
        discard <| atChoice `depth e (a (ns ++ `budget) e)
        return
      if piece.getNat == 4 then
        discard <| atChoice `cost e (a (ns ++ `depth.spec) e)
        return
      if piece.getNat == 5 then
        discard <| store (ns ++ `cost_nonneg) e (.proj ``And 0 (a (ns ++ `cost.spec) e))
        return
      let dep := a (ns ++ `depth) e
      let C := a (ns ++ `cost) e
      if piece.getNat == 3 then
        let h ← mkAppM ``And.intro #[a (ns ++ `cost_nonneg) e,a (ns ++ `actual_tail) input]
        discard <| store (ns ++ `unobserved_remainder) input (← existsAt dep (← existsAt C h))
        return
      let measured := ((← getConstInfo (fm ++ `measured)).value! (allowOpaque := true)).beta z
      lambdaBoundedTelescope measured 1 fun label row => do
        let t := label[0]!
        let pt := row.getAppArgs[:49].toArray
        let hi := a (hist ++ `measured_history) pt
        let now := pt[:36].toArray ++ #[pt[37]!,Expr.proj ``And 0 hi] ++ pt[39:43].toArray
        let current := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPairs.projected).value! (allowOpaque := true)).beta now
        unless current.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalRegular.Current.projected 38 do throwError "negative moment reached a different current"
        let weak := current.getAppArgs
        let dyn (k : Name) := a (native ++ k) weak
        let hK := dyn `real_half_bound
        let ka := (← inferType hK).getAppArgs
        let K := ka[ka.size-2]!.appArg!
        let hm := dyn `coefficient_monotone
        let A := (← inferType hm).appArg!
        let ρ := mkApp (a (fm ++ `frequency) b) t
        let L := a `JanetCartan.currentCoefficientScale #[pt[37]!,pt[39]!]
        let window := Expr.proj ``And 0 (a (hist ++ `native_window) pt)
        let two := Expr.proj ``And 0 (Expr.proj ``And 1 (Expr.proj ``And 1 window))
        let lc := a (sh ++ `current_window) pt
        let spec := Expr.proj ``And 1 (a (ns ++ `cost.spec) e)
        let pf := mkAppN spec #[a (world ++ `W) fix,a (world ++ `W_measurable) fix,K,hK,L,ρ,Expr.proj ``And 0 lc,a (fm ++ `one_of_two) #[ρ,two],Expr.proj ``And 1 lc,
          A,beta,dyn `coefficient_nonneg,hm,a (sh ++ `actual_bound) pt,dyn `gain,mkApp (a (fm ++ `measured) z) t,mkAppN (a (nm ++ `negative_moments) p) #[t,dep]]
        let priced ← mkAppM (ns ++ `unit_price) #[Expr.proj ``And 1 pf]
        let bound ← mkAppM ``And.intro #[Expr.proj ``And 0 pf,priced]
        discard <| store (ns ++ `actual_tail) input (← mkLambdaFVars label bound)
price_original_neumann_remainder 0
price_original_neumann_remainder 1
price_original_neumann_remainder 4
price_original_neumann_remainder 5
price_original_neumann_remainder 2
price_original_neumann_remainder 3
end JanetCartan.PhysicalPairs.OriginalNeumannTail
end
