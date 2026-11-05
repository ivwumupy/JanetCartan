module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMaskTemplate
public import JanetCartan.Iteration.PhysicalPairs.OriginalNegativeMoments
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # Negative moments of the actual primary input

The original protected compact supplies a positive phase-gradient lower
bound. Together with the actual Q/A/B/cutoff profiles and exact once-cutoff
source realization, it proves the inverse-remainder moments uniformly over
the full selected33+N label family (`app:ch_regular:eq:inverse-remainder`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate

open Lean Meta Elab Command

private def negative := `JanetCartan.PhysicalPairs.OriginalNegativeRows
private def lower := `JanetCartan.PhysicalPairs.OriginalNegativeMoments
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask

/-- The existing geometry consumer has the ordinary `y, hy, q, hq` tail.
Opening these non-instance binders directly preserves that tail without
scanning a dependent source-support proof for a local typeclass. -/
private def phaseJets (type : Expr) (ph : Array Expr) : MetaM Expr :=
  loop 4 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Expr
    | 0, _, p =>
      mkLambdaFVars p (app (phase ++ `representative_jets_at_historyScale)
        (ph ++ p[:3].toArray))
    | k+1, type, p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual primary moments: original phase-jet tail changed"
      withLocalDeclNoLocalInstanceUpdate name bi (domain.instantiateRev p) fun x =>
        loop k body (p.push x)

elab "price_actual_primary_negative_source " mode:num : command => liftTermElabM do
  unless mode.getNat ≤ 4 do throwError "actual primary moments: unknown mode"
  withFamily fun c => do
    let d := c.data.native[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let N := app ``JanetCartan.embeddingDimension #[n]
    let rows ← sourceRows c
    let χ := rows[0]!
    let η := rows[1]!
    let fixed := c.data.native[:44].toArray
    let pre := c.graph[:22].toArray
    let P := app (phase ++ `P) fixed
    let hP := app (phase ++ `P_nonneg) fixed
    let c₀ := app (lower ++ `lower) pre
    let hc₀ := app (lower ++ `lower_pos) pre
    let G := mkApp P (mkNatLit 0)
    let high ← mkAppM ``HAdd.hAdd
      #[← mkAppM ``max #[c₀,G],← mkNumeral (mkConst ``Real) 1]
    let ψ := (← resultAt (masks ++ `χ₃_smooth) c.masksStatic).appArg!
    let hψ := app (masks ++ `χ₃_smooth) c.masksStatic
    if mode.getNat == 0 then
      let proof := app (negative ++ `exists_price)
        #[d,N,χ,ψ,hψ,app (masks ++ `χ₃_compact) c.masksStatic,
          app (masks ++ `χ₃_on_χ₂) c.masksStatic,c₀,high,hc₀,P,rows[8]!,rows[9]!,c.field `Cmask,
          rows[11]!,rows[12]!,c.field `Cmask_nonneg]
      save `negative_cost_exists c.fixed proof (← inferType proof)
      return
    if mode.getNat == 1 then
      let value ← mkAppM ``Classical.choose #[c.field `negative_cost_exists]
      save `CN c.fixed value (← inferType value) true
      return
    if mode.getNat == 2 then
      let spec ← mkAppM ``Classical.choose_spec #[c.field `negative_cost_exists]
      let value ← mkAppM ``Classical.choose #[c.field `negative_cost_exists]
      let proof := Expr.proj ``And 0 spec
      let target := (← inferType proof).replace fun e => if e == value then some (c.field `CN) else none
      save `CN_nonneg c.fixed proof target
      return
    let facts ← scaleFacts c
    let ph ← phaseArgs c
    if mode.getNat == 3 then
      let K := app `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.Ksource pre
      let proof := app (negative ++ `geometry)
        #[d,χ,c.at `phase,K,c.chart,c₀,G,c.R,P,rows[2]!,rows[4]!,rows[5]!,
          app (phase ++ `representative_smooth) ph,hc₀,app (lower ++ `lower_on_original) pre,
          part facts 0,hP,app (phase ++ `representative_gradient_mem_source) ph,
          app (phase ++ `representative_gradient_upper) ph]
      let requirement := (← inferType proof).bindingDomain!
      let jets ← phaseJets requirement ph
      let value ← c.family (mkApp proof jets)
      save `source_geometry c.fixed value (← inferType value)
      return
    let window := app ``primary_frequency_window #[c.R,part facts 0]
    let spec ← mkAppM ``Classical.choose_spec #[c.field `negative_cost_exists]
    let ledger := #[d,N,c.labels,c.chart,c.field `A,c.field `B,c.field `Cmask,c.field `fine,c.field `full_profile]
    let left := app (fm ++ `left_bound) ledger
    let right := app (fm ++ `right_bound) ledger
    let proof := mkAppN (.proj ``And 1 spec)
      #[c.chart,c.domain,rows[6]!,c.domain_measurable,app (masks ++ `χ₃_support_chart) c.masksStatic,
        η,c.at `phase,c.R,c.rho,c.at `source_geometry,.proj ``And 0 window,.proj ``And 1 window,
        c.at `Q,c.at `A,c.at `B,
        app (fm ++ `on_chart) #[d,c.chart,η,rows[3]!],app (coeff ++ `Q_smooth) c.native,
        app (coeff ++ `A_smooth) c.native,c.at `B_smooth,
        app (coeff ++ `χsrc_jets) c.native,app (coeff ++ `Q_jets) c.native,
        mkApp left c.label,mkApp right c.label,mkConst ``Bool.false,c.at `input,c.at `realization]
    let value ← mkAppM ``Classical.choose #[c.field `negative_cost_exists]
    let target := (← inferType proof).replace fun e => if e == value then some (c.field `CN) else none
    save `negative_moments c.fixed (← c.family proof) (← mkForallFVars #[c.label] target)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
end

