module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledPolynomial
public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledTerminalFlow
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.RetainedFamily
public meta import Lean

/-!
# Actual leakage between successive reflected masks

Use the original buffered cutoffs, both signed bands and the order-one
retarded and elliptic residual of the same physical history. The derivative,
loss and cost profiles are chosen before that history. This supplies the
individual signed-letter estimate of `app:ch_regular:lem:finite-chain`;
the final word power also needs the source first-mask input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInitialization.OriginalSampledFactors
open RegularSector.FiniteMasks.ActualFamily RegularSector.FinitePdo RegularSector.FiniteAlgebraic
/-- One auxiliary chart cutoff is one on the two original operator masks
    and on the full terminal physical box, uniformly before the history. -/
theorem exists_native_cutoff {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
    {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
    (f : ActualMaskFamily Ω x RQ A₀ K M) (output : Euclidean (d+1) → ℝ)
    (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (Rbase : ℝ) : ∃ ψ : f.centers → Euclidean (d+1) → ℝ,
    (∀ p, ContDiff ℝ ∞ (ψ p)) ∧ (∀ p, HasCompactSupport (ψ p)) ∧ (∀ p y, ‖ψ p y‖ ≤ 1) ∧
    (∀ p (b : Bool) y, y ∈ (if b then tsupport (chartInputMask f p) else tsupport (endpointOutputMask f p output)) → ψ p y = 1) ∧
    (∀ p y, y ∈ closedBall 0 Rbase → ψ p y = 1) := by
  classical
  have hcut (p : f.centers) : ∃ φ : Euclidean (d+1) → ℝ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ (∀ y, ‖φ y‖ ≤ 1) ∧
      (∀ (b : Bool) y, y ∈ (if b then tsupport (chartInputMask f p) else tsupport (endpointOutputMask f p output)) → φ y = 1) ∧
      (∀ y ∈ closedBall 0 Rbase, φ y = 1) := by
    have hc := (((chartPhysicalMasks_properties f p).2.2.2.1).union
      (endpointOutputMask_properties f p ho hoc hout).2.1).union (isCompact_closedBall 0 Rbase)
    obtain ⟨φ,hφ,hrange,hcomp,_,hplateau⟩ := CompatibleResponse.exists_compact_family_cutoff hc isOpen_univ (subset_univ _)
    refine ⟨φ,hφ,hcomp,fun y ↦ (Real.norm_of_nonneg (hrange y).1).trans_le (hrange y).2,?_,
      fun y hy ↦ (show y ∈ {z | φ z = 1} from interior_subset (hplateau (Or.inr hy)))⟩
    intro b y hy
    change y ∈ {z | φ z = 1}
    apply interior_subset (hplateau (Or.inl ?_))
    cases b
    · exact Or.inr hy
    · exact Or.inl hy
  choose ψ hs hc hb hp hR using hcut
  exact ⟨ψ,hs,hc,hb,hp,hR⟩
theorem support_of_buffer {X : Type} [PseudoMetricSpace X] {S A B : Set X} {e : ℝ}
    (h : cthickening e S ⊆ A ∩ B) : S ⊆ A := fun _ hz ↦ (h (self_subset_cthickening _ hz)).1
theorem diagonal_buffer {X : Type} [PseudoMetricSpace X] {S O : Set X} {e : ℝ} {R : X → X → Prop}
    (h : ∀ p ∈ cthickening e S, ∀ q, p = q ∨ R p q → closedBall q e ⊆ O) :
    ∀ p ∈ S, closedBall p e ⊆ O := fun p hp ↦ h p (self_subset_cthickening _ hp) p (Or.inl rfl)
theorem sector_ge_ten (d : ℕ) : 10 ≤ RegularSector.FiniteEvolution.sectorLowOrder d := by
  have h := (RegularSector.FiniteEvolution.sectorLowOrder_bounds d).2.2
  omega
end JanetCartan.PhysicalInitialization.OriginalSampledFactors
end
public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledFactors
open Lean Meta Elab Command OriginalProtectedTemplate
open scoped Matrix.Norms.Frobenius
private def base := `JanetCartan.PhysicalInitialization.OriginalSampledFactors
private def termNS := `JanetCartan.PhysicalInitialization.OriginalSampledTerminal
private def window := `JanetCartan.PhysicalInitialization.OriginalSampledLeakage.Window
private def coords := `JanetCartan.ArbitraryAccuracy.SelectedLocalization.MeanCorrectedSource.ObservedCore.Coordinates
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def app (k : Name) (x : Array Expr) := mkAppN (mkConst k) x
private def namedPacket (k label : Name) (arity : Nat) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo k).type (some arity) fun x _ => do
    unless x.size == arity do throwError "unexpected {label} binder count {x.size}"
    let h := app k x
    let P ← store (base ++ `Packet ++ label) x (← inferType h) true
    discard <| store (base ++ `Proven ++ label) x h false (some P)
run_cmd liftTermElabM do
  let k := ``exists_native_cutoff
  forallBoundedTelescope (← getConstInfo k).type (some 13) fun x _ => select (base ++ `Cutoffs) x (app k x)
  let k := window ++ `continuation
  forallBoundedTelescope (← getConstInfo k).type (some 74) fun x t => do
    unless (← whnf t).isAppOfArity ``Exists 2 do
      let keys ← x.mapM fun z => do pure (← z.fvarId!.getDecl).userName
      throwError "expected the native signed PDE loss/cost after 74 inputs, got {keys}"
    select (base ++ `Signed) x (app k x)
  let k := base ++ `Signed.continuation
  namedPacket k `before_current 74
  namedPacket k `at_current 95
  namedPacket k `resolved 126
-- The current geometric realization and its Fourier right/left operators are
-- selected from the same construction, not postulated for the numerical masks.
run_cmd liftTermElabM do
  let c := termNS ++ `Chain.continuation
  forallBoundedTelescope (← getConstInfo c).type (some 66) fun x _ => select (base ++ `Masks) x (app c x)
  let t := base ++ `Masks.fact17
  forallBoundedTelescope (← getConstInfo t).type (some 68) fun x _ => select (base ++ `Operators) x (app t x)

private def down (h : Expr) : Nat → Expr
  | 0 => h
  | k+1 => down (.proj ``And 1 h) k
private def field (h : Expr) (j : Nat) := Expr.proj ``And 0 (down h j)
private def named (key : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec opts : Expr → Array (Option Expr)
    | .forallE n _ body _ => #[(known.find? (·.1 == n)).map (·.2)] ++ opts body
    | .mdata _ e => opts e
    | _ => #[]
  let args := opts (← getConstInfo key).type
  unless (args.filter Option.isSome).size == known.size do throwError "missing input of {key}"
  mkAppOptM key args

/- Shorten the extended-phase gap to the exact primitive estimate, keeping
   both time orientations. All projections use literally the same masks. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  let masks := base ++ `Masks
  forallBoundedTelescope (← getConstInfo (masks ++ `Gext)).type (some 66) fun x _ => do
    let m (k : Name) := app (masks ++ k) x
    let first ← named `JanetCartan.InitialSourceLocalization.first_proofMask_source_plateau
      #[(`m,m `m),(`hplateau,m `fact6)]
    discard <| store (base ++ `MaskFacts.first_plateau) x first
    let h := m `fact2
    forallBoundedTelescope (← inferType h) (some 1) fun p _ => do
      discard <| store (base ++ `MaskFacts.phase_smooth) x (← mkLambdaFVars p (field (mkAppN h p) 1))
      discard <| store (base ++ `MaskFacts.phase_agrees) x (← mkLambdaFVars p (down (mkAppN h p) 3))
    forallBoundedTelescope (← inferType (m `fact7)) (some 1) fun k _ => do
      let shape := (← inferType (mkAppN (m `fact3) k)).getAppArgs
      discard <| store (base ++ `MaskFacts.inside) (x ++ k) shape[shape.size-2]! true
      discard <| store (base ++ `MaskFacts.outside) (x ++ k) shape[shape.size-1]! true
      discard <| store (base ++ `MaskFacts.support) (x ++ k) (← mkAppM ``support_of_buffer #[mkAppN (m `fact7) k])
    forallBoundedTelescope (← inferType (m `fact9)) (some 1) fun k _ => do
      let params := x ++ k
      discard <| store (base ++ `MaskFacts.diagonal) params (← mkAppM ``diagonal_buffer #[mkAppN (m `fact9) k])
      let gap := mkAppN (m `continuation) k
      forallBoundedTelescope (← inferType gap) (some 15) fun p _ => do
        let v := mkAppN gap p
        let inner ← mkAppM ``And.intro #[field v 1,field v 2]
        let result ← mkAppM ``And.intro #[field v 0,inner]
        discard <| store (base ++ `MaskFacts.short_gap) params (← mkLambdaFVars p result)
  let reps := base ++ `Operators.fact0
  forallBoundedTelescope (← getConstInfo reps).type (some 69) fun x _ => do
    discard <| store (base ++ `MaskFacts.right_realization) x (field (app reps x) 1)
    discard <| store (base ++ `MaskFacts.left_realization) x (field (app reps x) 2)
  namedPacket reps `realization 68
  namedPacket (base ++ `Operators.continuation) `quantization 71

/-- Recover the exact native arguments from the compact statement of the
prehistory chain. No proof body is inspected and no terminal or times are
chosen again. The kernel checks the resulting two oriented radii. -/
def factorsFor (x : Array Expr) : MetaM (Array Expr) := do
  let t ← inferType (app (termNS ++ `before_history) x)
  unless t.isAppOfArity (termNS ++ `Packet.beforeCurrent) 44 do throwError "missing fixed terminal packet"
  let chain := t.getAppArgs
  let original := chain[:40].toArray
  let hi := chain[41]!.appArg!
  let lo := chain[42]!.appArg!
  unless hi.isAppOfArity (window ++ `thi) 36 && lo.isAppOfArity (window ++ `tlo) 36 && hi.getAppArgs == lo.getAppArgs do
    throwError "the two proof bands must use thi and tlo of the same actual signed leakage theorem"
  let w := hi.getAppArgs
  let d := x[0]!
  let bases := #[`eT,`eI,`eu,`ez].map (fun k => app (coords ++ k) #[d])
  let keys ← bases.mapM fun b => do pure (← inferType b).getAppArgs[0]!
  let finites ← keys.mapM fun i => synthInstance (mkApp (mkConst ``Fintype [.zero]) i)
  let c (k : Name) := app (termNS ++ `Chain ++ k) chain
  let R := app (termNS ++ `Static.Rbase) original
  let f := original[26]!
  let fixed := f.getAppArgs
  let stat (k : Name) := app (reg ++ k) fixed
  let fa := (← inferType f).getAppArgs
  let cu := #[d,fa[1]!,fa[2]!,fa[3]!,fa[6]!,fa[4]!,fa[5]!,f,stat `output,stat `fact17,stat `fact19,stat `fact20,R]
  let cf (k : Name) := app (base ++ `Cutoffs ++ k) cu
  return w ++ keys ++ finites ++ bases ++ #[app (coords ++ `Jcoord) #[d],app (coords ++ `measurePreserving_Jcoord) #[d],
    c `θ,R,c `εcollar,c `δT,c `δI,c `H,c `Hcollar,c `fact0,c `fact2,c `fact10,c `fact3,c `fact4,c `fact1,
    c `χ,c `fact6,c `fact7,c `fact8,c `fact11,cf `ψ,cf `fact0,cf `fact1,cf `fact2,cf `fact3,cf `continuation]

run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (termNS ++ `before_history)).type (some 37) fun x _ => do
    let factors ← factorsFor x
    unless factors.size == 74 do throwError "incorrect fixed leakage packet"
    discard <| store (base ++ `loss) x (app (base ++ `Signed.bSigned) factors) true
    discard <| store (base ++ `cost) x (app (base ++ `Signed.Csigned) factors) true
    discard <| store (base ++ `fixed_before_current) x (app (base ++ `Proven.before_current) factors)


/- Cache the genuine current geometry before substituting a whole raw
   history. The same proofs are checked here on the weak38 native spine. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (reg ++ `Current.projected)).type (some 38) fun w _ => do
    let cur (k : Name) := app (reg ++ `Current ++ k) w
    let f := app (reg ++ `f) w[:23].toArray
    let Ω := (← inferType f).getAppArgs[1]!
    discard <| store (base ++ `NativeGeometry.Q_smooth) w
      (← named `ContDiff.contDiffOn #[(`s,Ω),(`h,cur `hQ)])
    discard <| store (base ++ `NativeGeometry.B_smooth) w
      (← named `ContDiff.contDiffOn #[(`s,Ω),(`h,cur `hB)])
    discard <| store (base ++ `NativeGeometry.range) w
      (← mkAppM `Set.MapsTo.mono_left #[cur `fact0,← mkAppM `Set.subset_univ #[Ω]])
end JanetCartan.PhysicalInitialization.OriginalSampledFactors
end
