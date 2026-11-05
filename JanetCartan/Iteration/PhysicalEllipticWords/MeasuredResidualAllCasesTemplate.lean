module

public import JanetCartan.Iteration.PhysicalEllipticWords.MeasuredResidualAllCases
public meta import Lean

/-!
# Exact native finite-word one-step input

Preserve the complete primitive telescope and its prehistory threshold from
`exists_physical_history_measured_residual_alphabet_bounds`; expose the literal
`q : I × Vwhole` one-step conclusion consumed by the unchanged finite residual
power constructor. No analytic assumption or source reserve is added.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 32000

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalEllipticWords
open ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution.CompactTransfer
open Pseudodifferential FourierIntegral

private theorem reserved_bounds_native_step {d : ℕ} {I : Type}
    {V : Set (Euclidean 3 × Euclidean d)}
    {g : I → (Euclidean 3 × Euclidean d) →
      Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure (Euclidean (d+1)))}
    {A K : I → ℝ} {reserve : ℕ} (h : ReservedLetterBounds V g A K reserve) :
    ∀ ps : List (Euclidean 3 × Euclidean d), (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g q.1) q.2
        MemVectorFourierSobolev (s : ℝ) value ∧
          vectorFourierSobolevNorm (s : ℝ) value ≤ C * A q.1 * K q.1^(s+ps.length-reserve) := by
  intro ps hps s
  obtain ⟨C,hC,hbound⟩ := h.2 ps hps s
  exact ⟨C,hC,fun q ↦ hbound q.1 q.2 q.2.property⟩

end JanetCartan.PhysicalEllipticWords
end

public meta section
namespace JanetCartan.PhysicalEllipticWords.MeasuredResidualAllCasesTemplate
open Lean Meta Elab Command

private partial def nativeTelescope {α : Type} (type : Expr)
    (k : Array Expr → Expr → MetaM α) (xs : Array Expr := #[]) : MetaM α := do
  match type with
  | .mdata _ body => nativeTelescope body k xs
  | .letE _ _ value body _ => nativeTelescope (body.instantiate1 value) k xs
  | .forallE name dom body bi =>
    withLocalDecl name bi dom fun x ↦ nativeTelescope (body.instantiate1 x) k (xs.push x)
  | _ => k xs type

/-- The original threshold and all primitive inputs are retained verbatim;
only the checked reserved-profile projection changes to the native hstep. -/
elab "emit_actual_measured_residual_hstep" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalEllipticWords.exists_physical_history_measured_residual_alphabet_bounds
  let target := `JanetCartan.PhysicalEllipticWords.exists_physical_history_measured_residual_hstep
  let info ← getConstInfo source
  nativeTelescope info.type fun fixed outer => do
    unless outer.isAppOfArity ``Exists 2 do throwError "native threshold existential changed"
    let native := mkAppN (mkConst source (info.levelParams.map Level.param)) fixed
    let sourceArgs := outer.getAppArgs
    let callback ← withLocalDeclD `S₀ sourceArgs[0]! fun S₀ => do
      let specification := (mkApp sourceArgs[1]! S₀).headBeta
      withLocalDeclD `nativeSpec specification fun nativeSpec => do
        unless specification.isAppOfArity ``And 2 do throwError "native threshold conjunction changed"
        let continuation := .proj ``And 1 nativeSpec
        let mapped ← nativeTelescope specification.getAppArgs[1]! fun data result => do
          unless result.isAppOf `JanetCartan.PhysicalEllipticWords.ReservedLetterBounds do
            throwError "terminal alphabet profile changed"
          let original := mkAppN continuation data
          let step ← mkAppM ``JanetCartan.PhysicalEllipticWords.reserved_bounds_native_step #[original]
          mkLambdaFVars data step
        let pair ← mkAppM ``And.intro #[.proj ``And 0 nativeSpec,mapped]
        let predicate ← mkLambdaFVars #[S₀] (← inferType pair)
        let result ← mkAppOptM ``Exists.intro #[some sourceArgs[0]!,some predicate,some S₀,some pair]
        mkLambdaFVars #[S₀,nativeSpec] result
    let result ← mkAppM ``Exists.elim #[native,callback]
    let value ← instantiateMVars (← mkLambdaFVars fixed result)
    let type ← instantiateMVars (← inferType value)
    if value.hasSorry || type.hasSorry || value.hasMVar || type.hasMVar ||
        value.hasFVar || type.hasFVar then
      throwError "incomplete or dimension-polymorphic native all-case application"
    addDecl (.thmDecl {name := target, levelParams := info.levelParams, type, value}) (forceExpose := true)
  logInfo "kernel-checked actual four-case hstep, preserving every primitive input, native q:I×Vwhole indexing, source reserve and prehistory finite maximum"

end JanetCartan.PhysicalEllipticWords.MeasuredResidualAllCasesTemplate
end

open JanetCartan.PhysicalEllipticWords.MeasuredResidualAllCasesTemplate
emit_actual_measured_residual_hstep
