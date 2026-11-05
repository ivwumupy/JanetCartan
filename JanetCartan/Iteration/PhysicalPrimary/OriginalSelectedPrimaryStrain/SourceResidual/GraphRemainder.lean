module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.GraphCoefficients

/-!
# The original inverse remainder on arbitrary primary source labels

The original full coefficient price and native forward/literal-adjoint gain
are instantiated on the same admitted graph. Only negative Fourier moments
of the original input remain explicit; their actual producer is
`OriginalNegativeRows.exists_price` on the same raw-wave factorization and
profiles used for the first mask. The chosen depth and price precede every
queried history, source and sample (`main:eq:primary-strain`,
`app:ch_regular:eq:inverse-remainder`). The input is not recut by `χ₂`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual

private theorem half_lt_one : (1/2 : ℝ) < 1 := by norm_num
private theorem unit_amplitude_bound {a b c : ℝ} (h : a ≤ b*c) : a ≤ b*1*c := by
  simpa only [mul_one] using h

/-- The negative moments of the original, already localized input. This
predicate fixes the real orthonormal components and the one zero extension
used by the native inverse-remainder estimate; no extra source cutoff is
inserted (`app:ch_regular:eq:inverse-remainder`). -/
public def inputMoments (d : ℕ) (β : Type) (W : Set (Euclidean (d+1)))
    (hW : MeasurableSet W) (ρ : β → ℝ)
    (u : β → LocalSobolev.LocalL2 W (Euclidean (d+1))) (CN : ℕ → ℝ) : Prop :=
  ∀ i (k : ℕ), ArbitraryAccuracy.componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ)
    (-(k : ℝ)) (SmallSupport.zeroExtend hW (u i)) ≤ CN k / (ρ i)^k

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.Template
open Lean Meta Elab Command

private def nonnegativeFunctionType (C : Expr) : MetaM Expr :=
  withLocalDeclD `k (mkConst ``Nat) fun k => do
    mkForallFVars #[k] (← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,mkApp C k])

private def chooseNamed (key : Name) (p : Array Expr) (h : Expr) (data : Bool) : MetaM Unit := do
  if data then
    discard <| save key p (← mkAppM ``Classical.choose #[h]) true
  else
    let named := app (root ++ key) p
    let spec ← mkAppM ``Classical.choose_spec #[h]
    let target := (← inferType h).getAppArgs[1]!.beta #[named]
    discard <| save (key ++ `spec) p spec false (some target)

elab "price_original_primary_inverse_remainder " mode:num : command => liftTermElabM do
  unless mode.getNat < 6 do throwError "primary inverse remainder: unknown price mode"
  withGraph fun x g _ _ _ => do
    let fixed := g[:23].toArray
    let d := x[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let offset := mkApp2 (mkConst ``Nat.add) d (mkNatLit 2)
    let cnType ← mkArrow (mkConst ``Nat) (mkConst ``Real)
    withLocalDeclD `CN cnType fun CN => do
      withLocalDeclD `hCN (← nonnegativeFunctionType CN) fun hCN =>
        withLocalDeclD `observationOrder (mkConst ``Nat) fun s =>
          withLocalDeclD `accuracy (mkConst ``Nat) fun q => do
            let p := x ++ #[CN,hCN,s,q]
            if mode.getNat == 0 then
              let hG := app (native ++ `gain_cost_nonneg) fixed
              let G ← forallBoundedTelescope (← inferType hG) (some 1) fun j bound =>
                mkLambdaFVars j bound.appArg!
              let hθ := mkConst ``half_lt_one
              let θ := (← inferType hθ).getAppArgs[2]!
              let proof := app `JanetCartan.PhysicalPairs.OriginalTailPrice.inverse_tail
                #[n,θ,hθ,G,app (root ++ `Dcoeff) x,CN,hG,app (root ++ `Dcoeff_nonneg) x,hCN,offset,s,q]
              discard <| save `inverse_budget p proof
            else if mode.getNat == 1 then
              chooseNamed `remainderDepth p (app (root ++ `inverse_budget) p) true
            else if mode.getNat == 2 then
              chooseNamed `remainderCost p (app (root ++ `remainderDepth.spec) p) true
            else if mode.getNat == 4 then
              chooseNamed `remainderDepth p (app (root ++ `inverse_budget) p) false
            else if mode.getNat == 5 then
              chooseNamed `remainderCost p (app (root ++ `remainderDepth.spec) p) false
            else
              discard <| save `remainderCost_nonneg p (part (app (root ++ `remainderCost.spec) p) 0)

price_original_primary_inverse_remainder 0
price_original_primary_inverse_remainder 1
price_original_primary_inverse_remainder 4
price_original_primary_inverse_remainder 2
price_original_primary_inverse_remainder 5
price_original_primary_inverse_remainder 3

/-- The exact original source-family telescope, before support, norm, first
mask or source moments are assumed. -/
def withSource
    (go : Array Expr → Array Expr → Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  withGraph fun x g weak coeff graph =>
    withLocalDeclD `β (mkSort .one) fun β => do
      withLocalDeclD `indices (← mkArrow β graph) fun indices => do
        let rest ← instantiateForall (← getConstInfo observed).type (x ++ #[β,indices])
        unless rest.isForall do throwError "primary inverse remainder: original source binder absent"
        withLocalDeclD `u rest.bindingDomain! fun u =>
          go (x ++ #[β,indices,u]) g weak coeff graph

private def existsAt (e h : Expr) : MetaM Expr := do
  let α ← inferType e
  let type ← inferType h
  let predicate ← withLocalDeclD `value α fun v =>
    mkLambdaFVars #[v] (type.replace fun t => if t == e then some v else none)
  mkAppOptM ``Exists.intro #[some α,some predicate,some e,some h]

elab "bound_original_primary_inverse_remainder" : command => liftTermElabM do
  withSource fun p g weak coeff _ => do
    let x := p[:36].toArray
    let fixed := g[:23].toArray
    let β := p[36]!
    let indices := p[37]!
    let u := p[38]!
    let d := x[0]!
    let W := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source.W fixed
    let hW := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source.W_measurable fixed
    let rho ← withLocalDeclD `i β fun i => do
      let (_,_,r,_,_) ← currentAt g weak coeff (mkApp indices i)
      mkLambdaFVars #[i] r
    withLocalDeclD `CN (← mkArrow (mkConst ``Nat) (mkConst ``Real)) fun CN => do
      withLocalDeclD `hCN (← nonnegativeFunctionType CN) fun hCN => do
        let ma := #[d,β,W,hW,rho,u,CN]
        let momentType := ((← getConstInfo ``inputMoments).value! (allowOpaque := true)).beta ma
        withLocalDeclD `hMoments momentType fun hMoments =>
          withLocalDeclD `observationOrder (mkConst ``Nat) fun s => do
            let proof ← withLocalDeclD `accuracy (mkConst ``Nat) fun q => do
              let early := x ++ #[CN,hCN,s,q]
              let depth := app (root ++ `remainderDepth) early
              let cost := app (root ++ `remainderCost) early
              let all ← withLocalDeclD `i β fun i => do
                let (w,L,r,_,window) ← currentAt g weak coeff (mkApp indices i)
                let dyn (key : Name) := app (native ++ key) w
                let hK := dyn `real_half_bound
                let K := (← inferType hK).getAppArgs[2]!.appArg!
                let hm := dyn `coefficient_monotone
                let A := (← inferType hm).appArg!
                let b := mkApp2 (mkConst ``Nat.add)
                  (app `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[d])
                  (mkApp2 (mkConst ``Nat.add) d (mkNatLit 2))
                let spec := down (app (root ++ `remainderCost.spec) early) 1
                let tail := mkAppN spec #[W,hW,K,hK,L,r,part window 0,part window 1,down window 2,
                  A,b,dyn `coefficient_nonneg,hm,app (root ++ `coefficient_bound) (x.push (mkApp indices i)),
                  dyn `gain,mkApp u i,mkAppN hMoments #[i,depth]]
                let bound ← mkAppM ``unit_amplitude_bound #[down tail 1]
                let pair ← mkAppM ``And.intro #[part tail 0,bound]
                mkLambdaFVars #[i] pair
              let complete ← mkAppM ``And.intro #[app (root ++ `remainderCost_nonneg) early,all]
              let result ← existsAt depth (← existsAt cost complete)
              mkLambdaFVars #[q] result
            discard <| save `unobserved_remainder (p ++ #[CN,hCN,hMoments,s]) proof

bound_original_primary_inverse_remainder

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.Template
end
