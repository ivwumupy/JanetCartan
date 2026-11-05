module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Apply the original39 sector-independent current to the literal full-word
phase germ and gradient ranges, without a new phase, margin or threshold. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalWordGradientTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalWordGradient
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def current := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
private def profiles := `JanetCartan.PhysicalPrimary.OriginalPhaseProfiles
private def whole := `JanetCartan.PhysicalPrimary.OriginalIncidence.Whole

/-- Close both native53 word-gradient inputs from the SAME original39 current,
whole source cutoff, unchanged word box and existing whole-source gradient
constants (`app:ch_response:eq:fixed-factor-transfer`). -/
elab "apply_original_whole_word_gradient_ranges" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `sourceFrame)).type (some 39) fun p _ => do
    unless p.size == 39 do throwError "original word gradients require the exact sector-independent original39 current"
    let a := p[38]!
    let patch := #[p[0]!,p[1]!,a]
    let fixed := p[:23].toArray.push a
    let χ := mkAppN (mkConst (regular ++ `Phase.χ)) fixed
    let hχ := mkAppN (mkConst (regular ++ `Phase.fact3)) fixed
    let Q := mkAppN (mkConst (current ++ `sourceFrame)) p
    let rawφ := mkAppN (mkConst (ns ++ `original_physical_phase)) #[p[0]!,p[1]!,a,χ,Q]
    let φ ← store (ns ++ `φ) p rawφ true
    let germ := mkAppN (mkConst (ns ++ `original_physical_phase_germ)) #[p[0]!,p[1]!,a,χ,Q,hχ]
    let germType := (← inferType germ).replace fun e => if e == rawφ then some φ else none
    let germ ← store (ns ++ `germ) p germ false (some germType)
    let subset := mkAppN (mkConst (profiles ++ `word_box_subset)) fixed
    let sets := (← inferType subset).getAppArgs
    let small := sets[sets.size-2]!
    let physicalBall := small.getAppArgs[small.getAppArgs.size-2]!
    let radius := physicalBall.appArg!
    let lo := mkAppN (mkConst (whole ++ `wholeLo)) patch
    let hi := mkAppN (mkConst (whole ++ `wholeHi)) patch
    let band := mkAppN (mkConst (current ++ `whole_gradient_range)) p
    let h := mkAppN (mkConst (ns ++ `full_word_gradient_ranges_of_germ))
      #[p[0]!,p[1]!,a,radius,Q,lo,hi,φ,subset,germ,band]
    let h ← store (ns ++ `gradient_ranges) p h
    discard <| store (ns ++ `physical_gradient_range) p (.proj ``And 0 h)
    discard <| store (ns ++ `coordinate_gradient_range) p (.proj ``And 1 h)
  logInfo "original39 full-word gradient ranges: SAME sector-independent current, prescribed positive phase/cutoff, original Whole.lo/hi, unchanged physical and coordinate 3f-radius boxes and entire wholeWindow; no reserve, new threshold or analytic premise"

end JanetCartan.PhysicalPrimary.OriginalWordGradientTemplate
