module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMask.Basic
public import JanetCartan.Iteration.PhysicalPairs.OriginalObservedPairs
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # Actual primary first-mask and low-source estimates

Apply the existing first-mask and once-measured low-norm theorems to the full
original-data family. All phase, Q/A/B, cutoff and realization inputs are
the actual producers. No localization-success premise is added.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate

open Lean Meta Elab Command

private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def costs := `JanetCartan.PhysicalPairs.MeasuredSourceCost

def scaleFacts (c : Context) : MetaM Expr := do
  let hR₀ ← mkAppM ``le_trans
    #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS c.data.native[:44].toArray,
      c.data.native[45]!]
  mkAppM ``JanetCartan.PhysicalMean.fixedPicard_history_scale_facts #[hR₀,c.data.native[46]!]

def commonProfile (c : Context) : MetaM Expr := do
  let fixed := c.data.native[:44].toArray
  let priceA := app (coeff ++ `CA) fixed
  let priceD := app (raw ++ `Craw) c.fixed
  let original := app (raw ++ `profile) c.data.profileArgs
  let facts ← scaleFacts c
  let hR ← mkAppM ``le_trans #[← mkAppOptM ``zero_le_one
    #[some (mkConst ``Real),none,none,none,none],part facts 0]
  let n := mkApp (mkConst ``Nat.succ) c.data.native[0]!
  pure <| app ``common_quadrature_profile
    #[n,app ``JanetCartan.embeddingDimension #[n],c.chart,
      app (masks ++ `chart_open) c.masksStatic,c.at `A,
      app (raw ++ `amplitude) c.data.args,priceA,priceD,c.R,hR,
      app (coeff ++ `CA_nonneg) fixed,app (raw ++ `Craw_nonneg) c.fixed,
      app (coeff ++ `A_jets) c.native,.proj ``And 0 original,.proj ``And 1 original,c.imaginary]

def sourceRows (c : Context) : MetaM (Array Expr) := do
  let fixed := c.data.native[:44].toArray
  let hχ := app (masks ++ `χ₂_smooth) c.masksStatic
  let hη := app (masks ++ `χsrc_smooth) c.masksStatic
  pure #[
    (← resultAt (masks ++ `χ₂_smooth) c.masksStatic).appArg!,
    (← resultAt (masks ++ `χsrc_smooth) c.masksStatic).appArg!,
    hχ,hη,app (masks ++ `χ₂_compact) c.masksStatic,
    app (masks ++ `χ₂_support_chart) c.masksStatic,
    app (masks ++ `chart_open) c.masksStatic,
    app (coeff ++ `X) fixed,app (coeff ++ `Y) fixed,app (coeff ++ `CQ) fixed,
    app (coeff ++ `X_nonneg) fixed,app (coeff ++ `Y_nonneg) fixed,app (coeff ++ `CQ_nonneg) fixed]

elab "prove_actual_primary_first_mask " mode:num : command => liftTermElabM do
  unless mode.getNat ≤ 9 do throwError "actual primary first mask: unknown mode"
  withFamily fun c => do
    let fixed := c.data.native[:44].toArray
    let CA := app (coeff ++ `CA) fixed
    let CD := app (raw ++ `Craw) c.fixed
    let C := c.field `Cmask
    if mode.getNat == 0 then
      let price ← mkAppM ``HAdd.hAdd #[CA,CD]
      save `Cmask c.fixed price (← inferType price) true
      return
    if mode.getNat == 1 then
      withLocalDeclD `q (mkConst ``Nat) fun q => do
        let proof ← mkAppM ``add_nonneg
          #[mkApp (app (coeff ++ `CA_nonneg) fixed) q,
            mkApp (app (raw ++ `Craw_nonneg) c.fixed) q]
        let target ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,mkApp C q]
        save `Cmask_nonneg c.fixed (← mkLambdaFVars #[q] proof) (← mkForallFVars #[q] target)
      return
    if mode.getNat == 2 then
      let proof ← c.family (.proj ``And 0 (← commonProfile c))
      save `B_smooth c.fixed proof (← inferType proof)
      return
    let d := c.data.native[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let N := app ``JanetCartan.embeddingDimension #[n]
    if mode.getNat == 3 then
      let proof ← c.family (.proj ``And 1 (← commonProfile c))
      let target := app (fm ++ `FullDerivativeProfile)
        #[d,N,c.labels,c.chart,c.field `A,c.field `B,C,c.field `fine]
      save `full_profile c.fixed proof target
      return
    let r ← sourceRows c
    let χ := r[0]!
    let η := r[1]!
    let X := r[7]!
    let Y := r[8]!
    let CQ := r[9]!
    let hC := c.field `Cmask_nonneg
    if mode.getNat == 5 then
      let S ← mkAppM ``tsupport #[χ]
      let proof := app (costs ++ `exists_cost)
        #[d,N,S,r[4]!,X,Y,CQ,C,r[10]!,r[11]!,r[12]!,hC]
      save `low_cost_exists c.fixed proof (← inferType proof)
      return
    if mode.getNat == 6 then
      let value ← mkAppM ``Classical.choose #[c.field `low_cost_exists]
      save `sourceNormCost c.fixed value (← inferType value) true
      return
    if mode.getNat == 7 then
      let spec ← mkAppM ``Classical.choose_spec #[c.field `low_cost_exists]
      let proof := Expr.proj ``And 0 spec
      let target ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,c.field `sourceNormCost]
      save `sourceNormCost_nonneg c.fixed proof target
      return
    if mode.getNat == 9 then
      let low ← c.family (.proj ``And 0 (c.at `sourceNorms))
      let proof ← mkAppM ``JanetCartan.PhysicalPairs.OriginalObservedPairs.flat_price
        #[c.field `input,c.field `frequency,c.field `sourceNormCost,c.field `sourceNormCost_nonneg,low]
      save `source_polynomial c.fixed proof (← inferType proof)
      return
    let facts ← scaleFacts c
    let window := app ``primary_frequency_window #[c.R,part facts 0]
    let P := app (phase ++ `P) fixed
    let hP := app (phase ++ `P_nonneg) fixed
    let K := app `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.Ksource
      c.graph[:22].toArray
    let onChart (f h : Expr) := app (fm ++ `on_chart) #[d,c.chart,f,h]
    let ledger := #[d,N,c.labels,c.chart,c.field `A,c.field `B,C,c.field `fine,c.field `full_profile]
    let left := app (fm ++ `left_bound) ledger
    let right := app (fm ++ `right_bound) ledger
    if mode.getNat == 4 then
      let ph ← phaseArgs c
      let hs := app (fm ++ `on_support)
        #[d,c.chart,K,χ,c.at `phase,r[5]!,app (phase ++ `representative_gradient_mem_source) ph]
      let hj := app (fm ++ `jets_on_support)
        #[d,c.chart,χ,c.at `phase,r[5]!,P,c.R,app (phase ++ `representative_jets_at_historyScale) ph]
      let minus ← c.family (mkConst ``Bool.false)
      let proof := app ``JanetCartan.PhysicalPairs.SampledMask.first_mask
        #[d,N,c.labels,c.chart,c.domain,r[6]!,c.domain_measurable,χ,η,r[4]!,r[5]!,
          onChart χ r[2]!,onChart η r[3]!,K,
          c.field `Q,c.field `A,c.field `B,minus,c.field `phase,c.field `frequency,c.field `fine,c.field `input,
          ← c.family (app (coeff ++ `Q_smooth) c.native),
          ← c.family (app (coeff ++ `A_smooth) c.native),c.field `B_smooth,
          ← c.family (onChart (c.at `phase) (app (phase ++ `representative_smooth) ph)),
          ← c.family (part facts 0),← c.family (.proj ``And 0 window),← c.family (.proj ``And 1 window),
          mkApp P (mkNatLit 0),P,X,Y,CQ,C,hP,r[10]!,r[11]!,r[12]!,hC,
          ← c.family (app (coeff ++ `χ₂_jets) c.native),← c.family (app (coeff ++ `χsrc_jets) c.native),
          ← c.family (app (coeff ++ `Q_jets) c.native),left,right,
          ← c.family hs,← c.family (app (phase ++ `representative_gradient_upper) ph),← c.family hj,
          c.field `realization]
      let target ← inferType proof
      save `first_mask c.fixed proof target
    else
      let spec ← mkAppM ``Classical.choose_spec #[c.field `low_cost_exists]
      let proof := mkAppN (.proj ``And 1 spec)
        #[c.chart,c.domain,r[6]!,c.domain_measurable,χ,η,c.at `Q,c.at `A,c.at `B,
          onChart χ r[2]!,onChart η r[3]!,app (coeff ++ `Q_smooth) c.native,
          app (coeff ++ `A_smooth) c.native,c.at `B_smooth,
          app (fm ++ `support_refl) #[d,χ],r[5]!,c.R,part facts 0,
          app (coeff ++ `χ₂_jets) c.native,app (coeff ++ `χsrc_jets) c.native,
          app (coeff ++ `Q_jets) c.native,mkApp left c.label,mkApp right c.label,
          mkConst ``Bool.false,c.at `phase,c.rho,c.at `input,c.at `realization]
      let unnamed ← mkAppM ``Classical.choose #[c.field `low_cost_exists]
      let type := (← inferType proof).replace fun e => if e == unnamed then some (c.field `sourceNormCost) else none
      save `sourceNorms c.fixed (← c.family proof) (← mkForallFVars #[c.label] type)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
end
