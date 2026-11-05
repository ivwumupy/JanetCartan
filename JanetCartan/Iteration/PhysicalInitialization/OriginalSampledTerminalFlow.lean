module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledTerminal
public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledLeakage
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativePhaseMargins
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
public meta import Lean

/-!
# Reflected chains on the actual sampled physical history

Use the original finite inverse and all its own root/phase data. The positive
transport times are selected by the complete signed leakage theorem on the
actual terminal annulus; the two proof bands are `ra/thi` and `ra/tlo`, at
`2*power+1`. They are not the two source radii of a colored packet.
The costs precede each current. This supplies the geometry and localized
terminal elliptic error for the observed-chain step of `main:prop:pairs`;
the mask construction is not itself a statement of residual decay.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInitialization.OriginalSampledTerminal
open RegularSector.FiniteEvolution
theorem original_chart_in_physical (n : ℕ) (t R : ℝ) :
    ball (0 : Euclidean n) (min t R) ⊆ ball 0 R := ball_subset_ball (min_le_right _ _)
/-- Exact retarded radius of a selected transport time. -/
def radiusAtTime {I : Type} (ra : I → ℝ) (t : ℝ) := fun p ↦ ra p / t
/-- Positivity of the first oriented band. -/
theorem radiusAtTime_pos {I : Type} (ra : I → ℝ) (h : ∀ p, 0 < ra p)
    (t : ℝ) (ht : 0 < t) : ∀ p, 0 < radiusAtTime ra t p := fun p ↦ div_pos (h p) ht
/-- The ordinary word power requires this many reflected interfaces. -/
def reflectedDepth (power : ℕ) := 2*power+1
theorem native_sector_reserve (d rStar : ℕ) (h : sectorLowOrder d + 2 ≤ rStar) :
    2 + sectorLowOrder d ≤ rStar := by simpa only [Nat.add_comm 2] using h
theorem c3_on_protected_ball {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) (M r : ℝ)
    (h : ∀ D : Set (Euclidean n), IsCompact D → cNorm D 4 Q ≤ M) :
    cNorm (closedBall 0 (2*r)) 3 Q ≤ M :=
  (cNorm_mono_order (by decide : 3 ≤ 4)).trans (h _ (isCompact_closedBall _ _))
private def ellipticFrequency (_ρ : {r : ℝ // 1 ≤ r}) (_L : ℝ) (_hL : 1 ≤ _L)
    (_hρ : _L ≤ _ρ.1) : Unit := ()
end JanetCartan.PhysicalInitialization.OriginalSampledTerminal
end

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledTerminal
open Lean Meta Elab Command OriginalProtectedTemplate
private def root := `JanetCartan.PhysicalInitialization.OriginalSampledTerminal
private def orig := `JanetCartan.PhysicalInitialization.OriginalProtected
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def window := `JanetCartan.PhysicalInitialization.OriginalSampledLeakage.Window
private def margin := `JanetCartan.PhysicalSampling.OriginalPhaseMargins.raw_frame_margin_native
private def applied (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def down (h : Expr) : Nat → Expr
  | 0 => h
  | k+1 => down (.proj ``And 1 h) k
private def firstAt (h : Expr) (k : Nat) := Expr.proj ``And 0 (down h k)

/- Name the actual conclusion before substituting the entire finite history.
   These are definitionally the retained statements, not assumptions: each
   paired theorem is proved by its original producer. -/
private def packConclusion (key label : Name) (arity : Nat) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo key).type (some arity) fun params _ => do
    unless params.size == arity do throwError "changed {key} arity before {label}"
    let h := applied key params
    let P ← store (root ++ `Packet ++ label) params (← inferType h) true
    discard <| store (root ++ `FromProducer ++ label) params h false (some P)
run_cmd liftTermElabM do
  let key := root ++ `terminal_at_screened_radius
  forallBoundedTelescope (← getConstInfo key).type (some 40) fun x _ => do
    select (root ++ `Static) x (applied key x)
run_cmd liftTermElabM do
  let key := root ++ `Static.continuation
  forallBoundedTelescope (← getConstInfo key).type (some 44) fun x _ => do
    select (root ++ `Chain) x (applied key x)
  packConclusion (root ++ `Chain.continuation) `beforeCurrent 44
  packConclusion (root ++ `Chain.continuation) `onCurrent 66
run_cmd liftTermElabM do
  let key := root ++ `Static.fact13
  forallBoundedTelescope (← getConstInfo key).type (some 51) fun x _ => do
    select (root ++ `TerminalCosts) x (applied key x)
  packConclusion (root ++ `TerminalCosts.continuation) `sourceError 57

/-- Native original33 coefficient budget and the very same terminal annulus.
No `R₀`, varying current, sampled pair or depth occurs in this selection. -/
private def nativeWindow (x args : Array Expr) : Array Expr := Id.run do
  let g := args[26]!.getAppArgs ++ x[24:26].toArray ++ x[27:36].toArray
  let weak := g[:23].toArray ++ #[g[25]!,applied (reg ++ `Graph.regular_scale) g[:27].toArray] ++ g[27:34].toArray
  let reserve := applied `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[x[0]!]
  let hres := applied ``native_sector_reserve #[x[0]!,weak[27]!,weak[30]!]
  let coefficients := weak[:28].toArray ++ #[reserve,weak[28]!,weak[29]!,hres,weak[31]!]
  return coefficients ++ #[applied (root ++ `Static.a) args,applied (root ++ `Static.b) args,applied (root ++ `Static.fact6) args]
private def atReflectedDepth (x : Array Expr) (power : Expr) : MetaM (Array Expr) := do
  let args ← actualTerminalArguments x[:22].toArray x[22:24].toArray
  let fixed := args[26]!.getAppArgs
  let w := nativeWindow x args
  let lo := applied (window ++ `tlo) w
  let hi := applied (window ++ `thi) w
  let ra := applied (reg ++ `ra) fixed
  let I := (← inferType ra).bindingDomain!
  return args ++ #[applied ``reflectedDepth #[power],applied ``radiusAtTime #[I,ra,hi],
    applied ``radiusAtTime #[I,ra,lo],applied ``radiusAtTime_pos #[I,ra,applied (reg ++ `fact33) fixed,hi,applied (window ++ `fact1) w]]
run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo margin).type (some 36) fun x _ => do
    withLocalDeclD `power (mkConst ``Nat) fun power => do
      let args ← atReflectedDepth x power
      discard <| store (root ++ `before_history) (x.push power) (applied (root ++ `FromProducer.beforeCurrent) args)

/- Use each physical phase proof from the same weak38 evolution family. -/
elab "retain_terminal_phase_input " slot:num : command => liftTermElabM <| withTransparency .reducible do
  let cur := reg ++ `Current
  forallBoundedTelescope (← getConstInfo (cur ++ `projected)).type (some 38) fun w _ => do
    let native (name : Name) := applied (cur ++ name) w
    let n := mkApp (mkConst ``Nat.succ) w[0]!
    let ordinary := #[n] ++ w[1:21].toArray
    if slot.getNat == 0 then
      let low := native `fact2
      let four ← forallBoundedTelescope (← inferType low) (some 2) fun a _ => mkLambdaFVars a (down (mkAppN low a) 2)
      discard <| store (root ++ `current_C3) w (applied ``c3_on_protected_ball
        #[n,native `Q,applied (reg ++ `M) w[:23].toArray,applied (orig ++ `r) ordinary,four])
      return
    let chart := native `fact4
    let fields : Array (Name × Nat) := #[(`root_smooth,0),(`root_homogeneous,1),(`phase_projection,4),(`phase_source,5),(`phase_target,7),(`phase_smooth,8),(`phase_derivative,9),(`phase_diagonal,12)]
    let (name,k) := fields[slot.getNat-1]!
    let h ← forallBoundedTelescope (← inferType chart) (some 1) fun p _ => do
      let h := firstAt (mkAppN chart p) k
      if k == 12 then
        forallBoundedTelescope (← inferType h) (some 2) fun v _ => mkLambdaFVars (p ++ v) (down (mkAppN h v) 2)
      else mkLambdaFVars p h
    discard <| store (root ++ `Current ++ name) w h
retain_terminal_phase_input 0
retain_terminal_phase_input 1
retain_terminal_phase_input 2
retain_terminal_phase_input 3
retain_terminal_phase_input 4
retain_terminal_phase_input 5
retain_terminal_phase_input 6
retain_terminal_phase_input 7
retain_terminal_phase_input 8

/- On the actual elliptic core retain (pairedSource−Id) on the original χ₂
   with the unchanged χ₃ plateau, never an identity on arbitrary L². -/
run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (root ++ `fixed_terminal)).type (some 24) fun x _ => do
    let args ← actualTerminalArguments x[:22].toArray x[22:24].toArray
    let f := args[26]!
    let fixed := f.getAppArgs
    let get (name : Name) := applied (reg ++ name) fixed
    let bumps := get `afterChoice_χ₃
    let hχ₃ := firstAt bumps 1
    let U := (← inferType hχ₃).appArg!
    let n := mkApp (mkConst ``Nat.succ) x[0]!
    let phys ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.physicalRadius #[f]
    let Uin := applied ``original_chart_in_physical #[n,get `r,phys]
    let openU := applied `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open fixed
    let inU := firstAt bumps 7
    let houtput ← forallBoundedTelescope (← inferType inU) (some 2) fun y _ => mkLambdaFVars y (.proj ``And 0 (mkAppN inU y))
    let core := args ++ #[get `L,get `hL,get `fact17,get `fact19,get `fact18,get `χ₃,U,openU,hχ₃,Uin,houtput]
    forallBoundedTelescope (← getConstInfo ``ellipticFrequency).type (some 4) fun freq _ => do
      let h := applied (root ++ `FromProducer.sourceError) (core ++ freq ++ #[get `χ₂,firstAt bumps 2])
      discard <| store (root ++ `source_minus_identity) (x ++ freq) h

/- Close the full phase and protected-comparison fields on the original
   finite map, without a post-history choice of another comparison chart. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  let graph := reg ++ `Graph
  forallBoundedTelescope (← getConstInfo margin).type (some 42) fun x _ => do
    let S := (← inferType x[37]!).getAppArgs[2]!
    unless S.isAppOfArity (graph ++ `S) 34 do throwError "missing original graph threshold"
    let g := S.getAppArgs
    let s := g[:23].toArray
    let weak := s ++ #[g[25]!,applied (graph ++ `regular_scale) g[:27].toArray] ++ g[27:34].toArray ++
      #[x[36]!,applied (graph ++ `regular_reached) (g ++ x[36:38].toArray)] ++ x[38:42].toArray
    let cur (k : Name) := applied (reg ++ `Current ++ k) weak
    let co (k : Name) := applied (root ++ `Current ++ k) weak
    let ordinary := #[mkApp (mkConst ``Nat.succ) s[0]!] ++ s[1:21].toArray
    let fr := ordinary.push (cur `projected)
    let geom := applied (orig ++ `g) ordinary
    let I := (← inferType geom).bindingDomain!
    let chart (k : Name) := applied (root ++ k) fr
    withLocalDeclD `power (mkConst ``Nat) fun power => do
      let args ← atReflectedDepth x[:36].toArray power
      let h := applied (root ++ `FromProducer.onCurrent) (args ++ #[cur `Q,cur `hQ,applied (root ++ `current_C3) weak,
        cur `Φ,cur `C,cur `fact3,co `root_smooth,co `root_homogeneous,co `phase_projection,co `phase_source,
        co `phase_target,co `phase_smooth,co `phase_derivative,co `phase_diagonal,I,geom,chart `comparison_charts,
        applied (root ++ `graph_radii) ordinary,chart `graph_derivative,chart `graph_norm,chart `graph_covers,chart `graph_buffer])
      discard <| store (root ++ `on_actual_history) (x[:36].toArray ++ #[power] ++ x[36:].toArray) h
end JanetCartan.PhysicalInitialization.OriginalSampledTerminal
end
