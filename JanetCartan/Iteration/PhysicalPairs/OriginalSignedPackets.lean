module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedData
public import JanetCartan.Iteration.PhysicalPairs.DirectRealization

/-! # Actual original normal-completed signed Schwartz packet

The candidate is the genuine native `smoothSolver` on the UNCUT local tensor
class. Its algebraic normal term uses `χsrc` times the literal signed tensor of
both FULL derivatives, not an inner- or outer-measured substitute. Only the
actual geometric output cutoff `χenv` acts at the output. Native data and this
Schwartz member are unchanged for every later size or lag order.
`main:prop:pairs`, `app:ch_response:eq:response-full-map`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Metric Filter
open scoped SchwartzMap ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.OriginalSignedPackets
open AmbientResponse ResponseSourceExtension PhysicalInitialization PhysicalSeed

variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "V" => Euclidean N

def originalTensor {I : Type} (Z : I → SchwartzMap E (EuclideanSpace ℂ (Fin N))) (θ : I → E → ℝ)
    (minus : Bool) (i j : I) (η : E → ℝ) : MetricField n := fun y ↦ η y • SampledInput.tensor Z θ minus i j y

theorem originalTensor_smooth {I : Type} (Z : I → SchwartzMap E (EuclideanSpace ℂ (Fin N))) (θ : I → E → ℝ)
    (minus : Bool) (i j : I) (η : E → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ContDiff ℝ ∞ (originalTensor Z θ minus i j η) := (SampledInput.tensor_admitted Z θ minus i j hη hc).1

/-- Build the actual full ambient field rather than a merely smooth local row. -/
def realize {core chart : Set E} (Ξ : OutputCutoff core chart) (F : E → V) (g : E → E) (q : MetricField n)
    (ho : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart) (hi : IsImmersionOn F chart) (hr : HasFullNormalRankOn F chart)
    (hg : ContDiff ℝ ∞ g) (hq : ContDiff ℝ ∞ q) : SchwartzMap E V :=
  (Ξ.hasCompactSupport_zeroExtend (fun y : chart ↦ completedVariation F g q y)).toSchwartzMap
    (Ξ.contDiff_zeroExtend_restrict ho (contDiffOn_completedVariation ho hF hg.contDiffOn hq.contDiffOn hi hr))

theorem realize_formula {core chart : Set E} (Ξ : OutputCutoff core chart) (F : E → V) (g : E → E) (q : MetricField n)
    (ho : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart) (hi : IsImmersionOn F chart) (hr : HasFullNormalRankOn F chart)
    (hg : ContDiff ℝ ∞ g) (hq : ContDiff ℝ ∞ q) :
    ⇑(realize Ξ F g q ho hF hi hr hg hq) = (fun x ↦ Ξ.toFun x • completedVariation F g q x) := Ξ.zeroExtend_restrict _

theorem realize_germ {core chart : Set E} (Ξ : OutputCutoff core chart) (F : E → V) (g : E → E) (q : MetricField n)
    (ho : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart) (hi : IsImmersionOn F chart) (hr : HasFullNormalRankOn F chart)
    (hg : ContDiff ℝ ∞ g) (hq : ContDiff ℝ ∞ q) : ∀ x ∈ core,
    ⇑(realize Ξ F g q ho hF hi hr hg hq) =ᶠ[𝓝 x] completedVariation F g q := fun _ hx ↦ Ξ.zeroExtend_eventuallyEq _ hx

theorem retained_frame (hn : 5 ≤ n) {U : Set E} (hU : U ⊆ ball 0 (OriginalBoundary.b hn))
    (F : E → V) (hF : ContDiffOn ℝ ∞ F (ball 0 (OriginalBoundary.R hn)))
    (hi : IsImmersionOn F (ball 0 (OriginalBoundary.R hn))) (hr : HasFullNormalRankOn F (ball 0 (OriginalBoundary.R hn))) :
    ContDiffOn ℝ ∞ F U ∧ IsImmersionOn F U ∧ HasFullNormalRankOn F U := by
  have h := hU.trans (ball_subset_ball (OriginalBoundary.b_lt_R hn).le)
  exact ⟨hF.mono h,fun x hx ↦ hi x (h hx),fun x hx ↦ hr x (h hx)⟩
end JanetCartan.PhysicalPairs.OriginalSignedPackets
end

public meta section
set_option maxHeartbeats 750000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalSignedPackets
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSignedPackets
private def data := `JanetCartan.PhysicalPairs.OriginalSignedData
private def sampled := `JanetCartan.PhysicalInitialization.OriginalSampledPairs
private def inv := `JanetCartan.PhysicalPairs.OriginalInverse
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def down (v : Expr) : Nat → Expr
  | 0 => v
  | j+1 => down (.proj ``And 1 v) j
private def part (v : Expr) (j : Nat) := Expr.proj ``And 0 (down v j)

elab "realize_native_completed_packet " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun p gf => do
    let fixed := gf.getAppArgs[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let N := a `JanetCartan.embeddingDimension #[n]
    let now := p[:36].toArray ++ #[p[37]!,part (a (hist ++ `measured_history) p) 0] ++ p[39:43].toArray
    let current := a (sampled ++ `projected) now
    let F := Expr.proj ``Subtype 0 current
    let props := Expr.proj ``Subtype 1 current
    let ξ := a (mask ++ `χenv) fixed
    let xt := (← inferType ξ).getAppArgs
    let core := xt[xt.size-2]!
    let V := xt.back!
    if piece.getNat == 0 then
      let fr := a (ns ++ `retained_frame) #[n,N,p[1]!,V,a (mask ++ `chart_in_coefficient_ball) fixed,F,part props 0,part props 1,part props 2]
      discard <| store (ns ++ `on_frame) p fr
      return
    forallBoundedTelescope (← inferType (a (data ++ `uncut) p)) (some 1) fun Z _ => do
      let label := p ++ Z
      if piece.getNat == 1 then
        let ηs := a (mask ++ `χsrc_smooth) fixed
        let η := (← inferType ηs).appArg!
        let etaCompact := Expr.proj ``And 0 (a (data ++ `source_chart) p[:47].toArray)
        let I ← inferType p[46]!
        let args := #[n,N,I,Z[0]!,a (data ++ `angles) p,p[45]!,p[46]!,p[47]!,η]
        let orig := a (ns ++ `originalTensor) args
        let source ← store (ns ++ `tensor) label orig true
        let smooth := a (ns ++ `originalTensor_smooth) (args ++ #[ηs,etaCompact])
        discard <| store (ns ++ `tensor_smooth) label smooth false (some ((← inferType smooth).replace fun e => if e == orig then some source else none))
        return
      if piece.getNat == 2 then
        let ct ← inferType (a (data ++ `native_correction) label)
        let some corr := ct.find? fun e => e.isAppOfArity (inv ++ `Corr) 38 | throwError "native correction no longer carries the original38 actual solver"
        let smooth := mkApp (a (inv ++ `solver_smooth) corr.getAppArgs) (a (data ++ `uncut) label)
        let st ← inferType smooth
        let solved := st.appArg!
        let named ← store (ns ++ `solved) label solved true
        discard <| store (ns ++ `solved_smooth) label smooth false (some (st.replace fun e => if e == solved then some named else none))
        return
      let frame := a (ns ++ `on_frame) p
      let args := #[n,N,core,V,ξ,F,a (ns ++ `solved) label,a (ns ++ `tensor) label,a (mask ++ `chart_open) fixed,
        part frame 0,part frame 1,down frame 2,a (ns ++ `solved_smooth) label,a (ns ++ `tensor_smooth) label]
      let h := a (ns ++ `realize) args
      if piece.getNat == 3 then
        discard <| store (ns ++ `packet) label h true
        return
      let (name,pf) := if piece.getNat == 4 then (`formula,a (ns ++ `realize_formula) args) else (`core_germ,a (ns ++ `realize_germ) args)
      discard <| store (ns ++ name) label pf false (some ((← inferType pf).replace fun e => if e == h then some (a (ns ++ `packet) label) else none))
realize_native_completed_packet 0
realize_native_completed_packet 1
realize_native_completed_packet 2
realize_native_completed_packet 3
realize_native_completed_packet 4
realize_native_completed_packet 5
end JanetCartan.PhysicalPairs.OriginalSignedPackets
end
