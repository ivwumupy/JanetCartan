module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.ObservationStatement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.SumSource
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Values
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-!
# Composition of the exact source identities

This deduction is checked independently from the derivative-equality producer.
Its two inputs are the precise original prefix identity and exactly
`observed_field_statement56`; `observed_field_eq56` discharges the latter in
the public source58 bridge. The original grouped-source identity is already
supplied through `sum_eq_source56` (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- A private equality cut keeps each of the four original source endpoints
listed once in the final proof application. -/
private theorem original_source_transport {T : Type} {a b c d : T}
    (hObserved : a = b) (hPrefixed : a = c) (hSum : c = d) : b = d :=
  hObserved.symm.trans (hPrefixed.trans hSum)

meta section
open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization

run_meta do
  let factor := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization
  let root := factor ++ `SourceBridge
  let app := SourceTemplate.app
  SourceBridge.Template.withInputs fun c => do
    let p := c.data.params.push c.point[0]!
    let all := c.data.params ++ c.point
    let left ← SourceTemplate.bodyAt (app (root ++ `observed_field_statement) p)
    let right ← SourceTemplate.bodyAt (app (root ++ `sum_source_statement) p)
    unless left.isAppOfArity ``Eq 3 && right.isAppOfArity ``Eq 3 do
      throwError "source composition: exact original component equality changed"
    let l := left.getAppArgs
    let r := right.getAppArgs
    let prefixObservation := app (root ++ `Values.prefix_observation) p
    let sourceObservation := app (root ++ `Values.source_observation) p
    let prefixSum := app (root ++ `Values.prefix_sum) p
    withLocalDeclD `hPrefixed c.prefixed fun forward => do
      withLocalDeclD `hObserved (app (root ++ `observed_field_statement) p) fun observed => do
        let proof := mkAppN (mkConst ``original_source_transport)
          #[l[0]!, prefixObservation, sourceObservation, prefixSum, r[2]!,
            observed, forward, app (root ++ `sum_eq_source) p]
        SourceBridge.Template.save (root ++ `observed_from_prefix_and_field)
          (all ++ #[forward, observed]) proof
          (app (factor ++ `observed_raw_angular_statement) all)
        addDocStringCore (root ++ `observed_from_prefix_and_field)
          "Exact original source composition from the precise prefix identity and only observed_field_statement56. The independently proved observed_field_eq56 discharges that identity inside observed_raw_angular_of_prefixed58; Actual.prefixed_forward57 discharges the prefix premise in the parent Source application. No analytic or source-success input is added (main:eq:primary-strain)."

end

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.observed_from_prefix_and_field
