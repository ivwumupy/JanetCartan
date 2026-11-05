module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Realization.Basic
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # The actual complete primary source satisfies the first-mask identity

The derivative factorization is applied to the same complete-forcing raw
field and actual outer sample. No phase, source, or localization hypothesis
is left for the caller (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate

open Lean Meta Elab Command

private def sourcePointTelescope (type : Expr)
    (next : Array Expr → Expr → MetaM Expr) : MetaM Expr := loop 2 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Expr
    | 0, type, p => next p (type.instantiateRev p)
    | k+1, type, p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual primary realization: source support tail changed"
      withLocalDeclNoLocalInstanceUpdate name bi (domain.instantiateRev p) fun x =>
        loop k body (p.push x)

elab "prove_actual_primary_source_realization" : command => liftTermElabM do
  withFamily fun c => do
    let n := mkApp (mkConst ``Nat.succ) c.data.native[0]!
    let N := app ``JanetCartan.embeddingDimension #[n]
    let hp := app (masks ++ `χ₂_support_chart) c.masksStatic
    let χ := (← resultAt (masks ++ `χ₂_smooth) c.masksStatic).appArg!
    let η := (← resultAt (masks ++ `χsrc_smooth) c.masksStatic).appArg!
    let F := app `JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native.sourceF c.data.native
    let Z := app `JanetCartan.PhysicalPrimary.OriginalRawSourceField.raw c.data.sourceArgs
    let ph := ← phaseArgs c
    let φ := mkAppN (app (phase ++ `phase) c.native)
      #[ph[51]!,Expr.proj ``Subtype 0 ph[52]!]
    let φext := c.at `phase
    let D := app (raw ++ `amplitude) c.data.args
    let rawInfo ← getConstInfo c.data.source.getAppFn.constName!
    let rawBody := ((rawInfo.value! (allowOpaque := true)).beta c.data.source.getAppArgs).headBeta
    unless rawBody.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalRawSourceProfile.field 55 do
      throwError "actual primary realization: original raw full-forcing field55 changed"
    let p := rawBody.getAppArgs
    let reduced := app ``OriginalPrimaryStrainMaskData.cutoff_stress_quadrature_eq
      #[c.data.native[0]!,N,F,Z,χ,η,φ,c.at `Q,D,c.rho]
    let requirement := (← inferType reduced).bindingDomain!
    let hfactor ← sourcePointTelescope requirement fun x _ => do
      let hx := mkAppN hp x
      mkLambdaFVars x (app `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.raw_factor_on_source_chart
        (p ++ #[x[0]!,hx]))
    let proof := app ``quadrature_realization_on_chart
      #[c.data.native[0]!,N,c.chart,c.domain,c.domain_measurable,F,Z,χ,η,φ,φext,c.at `Q,D,c.rho,
        c.at `input,c.imaginary,hp,app (phase ++ `representative_germ) ph,hfactor,
        app (source ++ `input_zeroExtend) c.sourceArgs]
    let value ← c.family proof
    save `realization c.fixed value (← inferType value)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
end

