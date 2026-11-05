module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceForwardStatement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-!
# Literal original source endpoint values

Only the three endpoint values already occurring in the original prefix and
source predicates are named. Their original primitive53, source, sample and
point are retained verbatim. The source composition uses these compact names
for the SAME expressions; no new function, choice or mathematical hypothesis
is introduced (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Values.Template

open Lean Meta

private def publish (stage : Nat) : MetaM Unit :=
  SourceBridge.Template.withInputs fun c => do
    unless stage < 3 do
      throwError "source values: unknown original endpoint"
    let factor := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization
    let a := c.prefixEq.getAppArgs
    let (key, value) ← if stage == 0 then
      pure (`prefix_observation, a[1]!)
    else if stage == 1 then do
      let source ← SourceTemplate.bodyAt (SourceTemplate.app
        (factor ++ `observed_raw_angular_statement) (c.data.params ++ c.point))
      unless source.isAppOfArity ``Eq 3 do
        throwError "source values: exact original source predicate changed"
      pure (`source_observation, source.getAppArgs[1]!)
    else
      pure (`prefix_sum, a[2]!)
    let name := factor ++ `SourceBridge.Values ++ key
    SourceBridge.Template.save name (c.data.params.push c.point[0]!) value a[0]! true
    addDocStringCore name
      "Literal matrix endpoint copied from the original prefix/source predicate at SAME primitive53, source, sample and physical point56. No source membership, new choice, parameter, scale or hypothesis is added. Used only to keep the exact source58 composition compact (main:eq:primary-strain)."

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Values.Template
end
