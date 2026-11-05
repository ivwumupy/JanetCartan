module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedFrames
public import JanetCartan.Iteration.PhysicalPairs.SampledMask

/-! # Complete normalized geometry of the original external signed pair

The supplied original pair, including its genuine near-diagonal beat, is used
throughout. The scalar from the immutable 36-field jet budget agrees as a germ
with the original radial scalar on the entire actual first-mask chart. There is
no comparison between two independently chosen Hamilton charts.
`app:ch_pairs:setup:pairs-lag`, `app:ch_pairs:prop:pairs-lag-sum`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.PhysicalPairs.OriginalMaskGeometry
open PhysicalInitialization PhysicalSeed ActualCarriers FrozenMenu CurrentFullPhase ConstructedSignedGeometry SignedPairs

/-- The entire original first-mask chart lies inside the compact on which
all raw phase representatives have their genuine joint germs and jet costs. -/
theorem chart_buffer {d : ℕ} (hn : 5 ≤ d+1) (r μ : ℝ) {K : Set (Euclidean (d+1))} {M : ℝ}
    (f : RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily (ball 0 (OriginalBoundary.b hn)) 0
      (OriginalRegular.coreRadius hn (OriginalRegular.screenedRadius hn r μ)) (cubeStress (d+1)) K M) (t : ℝ) :
    ball (0 : Euclidean (d+1)) (min t f.physicalRadius) ⊆ closedBall 0 (OriginalRegular.coreRadius hn (OriginalRegular.screenedRadius hn r μ)) :=
  (ball_subset_closedBall.trans (closedBall_subset_closedBall ((min_le_right t f.physicalRadius).trans
    (by linarith [f.physicalRadius_pos] : f.physicalRadius ≤ 4*f.physicalRadius)))).trans f.physicalBall_coefficientDomain

/-- Retain smoothness, the true scalar germ, the ORIGINAL angular source hull
and graded normalized jets with the actual large fine scale. -/
theorem retain {d : ℕ} (D : CoverData (d+1)) {G : Type}
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (q : Pair G (Euclidean 3) (groupCube D assign))
    (Φ : G → Euclidean (d+1) × Euclidean 3 → ℝ) (hΦ : ∀ g, ContDiff ℝ ∞ (Φ g) ∧ HasCompactSupport (Φ g))
    (raw : G → Euclidean 3 → Euclidean (d+1) → ℝ) {U S K : Set (Euclidean (d+1))} (hUS : U ⊆ S)
    (hg : ∀ g v, v ∈ S ×ˢ groupCube D assign g → Φ g =ᶠ[𝓝 v] fun w ↦ raw g w.2 w.1)
    {L Lfine : ℝ} (hL : 1 ≤ L) (hle : L ≤ Lfine) (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m)
    (hj : ∀ g v, v ∈ S ×ˢ groupCube D assign g → ∀ m, ‖iteratedFDeriv ℝ m (Φ g) v‖ ≤ P m*L^(m-2))
    (hsource : ∀ x ∈ U, gradient (fun y ↦ q.vector (fun g z ↦ raw g z y)/q.beat) x ∈ K) :
    ContDiff ℝ ∞ (SampledMask.normalized q Φ) ∧
    ∀ x ∈ U, (SampledMask.normalized q Φ =ᶠ[𝓝 x] (fun y ↦ q.vector (fun g z ↦ raw g z y)/q.beat)) ∧
      gradient (SampledMask.normalized q Φ) x ∈ K ∧
      ‖fderiv ℝ (SampledMask.normalized q Φ) x‖ ≤ 2*(P 1+P 2) ∧
      ∀ j, ‖iteratedFDeriv ℝ (j+1) (SampledMask.normalized q Φ) x‖ ≤ 2*(P (j+1)+P (j+2))*Lfine^j := by
  obtain ⟨hs,hh⟩ := SampledMask.normalization (fun g ↦ convex_parameterCube _) q Φ (fun g ↦ (hΦ g).1)
    raw hg hL P hP hj
  refine ⟨hs,?_⟩
  intro x hx
  obtain ⟨he,hd,hj⟩ := hh x (hUS hx)
  refine ⟨he,he.gradient_eq.symm ▸ hsource x hx,hd,fun j ↦ (hj j).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hL) hle _)
    (mul_nonneg (by norm_num) (add_nonneg (hP _) (hP _)))
end JanetCartan.PhysicalPairs.OriginalMaskGeometry
end

public meta section
set_option maxHeartbeats 800000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalMaskGeometry
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalMaskGeometry
private def sn := `JanetCartan.PhysicalPairs.SampledMask
private def fs := `JanetCartan.PhysicalPairs.OriginalSignedFrames
private def quad := `JanetCartan.PhysicalPairs.SampledQuadrature
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def col := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def ob := `JanetCartan.PhysicalSeed.OriginalBoundary
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def part (pf : Expr) : Nat → Expr
  | 0 => .proj ``And 0 pf
  | i+1 => part (.proj ``And 1 pf) i

elab "publish_original_mask_geometry " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun p gf => do
    if piece.getNat ≥ 2 then
      let spec := a (ns ++ `spec) p
      if piece.getNat == 2 then
        discard <| store (ns ++ `smooth) p (part spec 0)
        return
      forallBoundedTelescope (← inferType (.proj ``And 1 spec)) (some 2) fun y _ => do
        let atPoint := mkAppN (.proj ``And 1 spec) y
        let (name,pf) := match piece.getNat with
          | 3 => (`germ,part atPoint 0)
          | 4 => (`gradient_in_source,part atPoint 1)
          | 5 => (`gradient_upper,part atPoint 2)
          | _ => (`higher_jets,Expr.proj ``And 1 (.proj ``And 1 (.proj ``And 1 atPoint)))
        discard <| store (ns ++ name) (p ++ y) pf
      return
    let fixed := gf.getAppArgs[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let orig := #[n] ++ fixed[1:21].toArray
    let cap := a `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,p[1]!,orig[20]!]
    let sel := orig.set! 20 cap
    let f := a (reg ++ `f) fixed
    let fa := (← inferType f).getAppArgs
    let hUS := a (ns ++ `chart_buffer) #[p[0]!,p[1]!,a `JanetCartan.PhysicalInitialization.OriginalProtected.r orig,
      a `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure sel,fa[fa.size-2]!,fa.back!,f,a (reg ++ `r) fixed]
    let ha := (← inferType hUS).getAppArgs
    let V := ha[ha.size-2]!
    let S := ha.back!
    let safe := p[:43].toArray
    let early := p[:36].toArray
    let now := early ++ #[p[37]!,part (a (hist ++ `measured_history) p) 0] ++ p[39:43].toArray
    let raw := a (quad ++ `group_phase) now
    let ca := (((← getConstInfo (quad ++ `group_phase)).value! (allowOpaque := true)).beta now).getAppArgs
    let hgrad := a (quad ++ `gradient_in_source) p
    let some q := (← inferType hgrad).find? (fun e => e.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalSampledPairs.pair 30)
      | throwError "actual source annulus lost original signed pair"
    let qa := (← inferType q).getAppArgs
    let window := part (a (hist ++ `native_window) p) 0
    let hL := part window 0
    let hle := part window 1
    let la := (← inferType hle).getAppArgs
    let rep := a (fs ++ `representative) safe
    let form := a (sn ++ `normalized) #[p[0]!,ca[5]!,qa.back!,q,rep]
    if piece.getNat == 0 then
      discard <| store (ns ++ `phase) p form true
      logInfo "normalized SUPPLIED native pair at its true beat"
      return
    let phi := a (ns ++ `phase) p
    let proof := a (ns ++ `retain) #[p[0]!,a (ob ++ `D) #[n,p[1]!],ca[5]!,ca[6]!,q,rep,a (fs ++ `smooth) safe,raw,V,S,
      a (col ++ `Ksource) p[:22].toArray,hUS,a (fs ++ `original_germ) safe,la[la.size-2]!,la.back!,hL,hle,
      a (fs ++ `jointProfile) early,a (fs ++ `jointProfile_nonneg) early,a (fs ++ `joint_jets) safe,hgrad]
    if piece.getNat == 1 then
      let ty := (← inferType proof).replace fun e => if e.isAppOfArity (sn ++ `normalized) 5 then some phi else none
      discard <| store (ns ++ `spec) p proof false (some ty)
      logInfo "actual static phase budget realized at native BOTH cutoffs, native row, true beat and fine scale"
      return
    throwError "unknown original phase step"
publish_original_mask_geometry 0
publish_original_mask_geometry 1
publish_original_mask_geometry 2
publish_original_mask_geometry 3
publish_original_mask_geometry 4
publish_original_mask_geometry 5
publish_original_mask_geometry 6
end JanetCartan.PhysicalPairs.OriginalMaskGeometry
end
