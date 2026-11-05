module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Profiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMask.Amplitude
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMask.Costs
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMaskTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Actual first-mask derivative profiles and fixed source prices

All derivative bounds follow from the original phase and coefficient
profiles. Their fixed costs precede every admitted history and source label;
the later first-mask theorem separately consumes the exact source identity
(`main:eq:primary-strain`, `app:ch_regular:eq:source-tail`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
open Lean Meta Elab Command
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate

run_cmd liftTermElabM do
  withFamily fun c => do
    let d := c.data.native[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let N := app ``JanetCartan.embeddingDimension #[n]
    let fine ← c.family c.R
    let proof ← c.family (.proj ``And 1 (← commonProfile c))
    let target := app `JanetCartan.PhysicalPairs.OriginalFirstMask.FullDerivativeProfile
      #[d,N,c.labels,c.chart,c.field `A,c.field `B,c.field `Cmask,fine]
    save `full_profile c.fixed proof target
end

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Cmask
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.full_profile
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.sourceNormCost_nonneg
