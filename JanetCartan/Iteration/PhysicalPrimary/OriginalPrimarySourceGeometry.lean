module
public import JanetCartan.Iteration.PhysicalInitialization.OriginalColoredProtectionApplication
/-! The individual colored primary covector lies in the SAME existing pair
source annulus; no new compact, inverse or mask is selected. The old doubled
plus diagonal supplies the stronger radial lower bound needed here. This is
only the ORIGINAL unshifted carrier, not an independently shifted covector.
Consumer: the raw whole-source first mask at the original phase
(main:eq:primary-strain; app:ch_regular:eq:source-tail). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] noncomputable section
open Set Metric
open scoped BigOperators
namespace JanetCartan.PhysicalPrimary.OriginalPrimarySourceGeometry
open SignedPairs PhysicalInitialization.ColoredRefinement
private theorem primary_mem_colored_source_annulus {n : ℕ} {I C X : Type*} [Fintype C]
    (S : I → Set (Euclidean 3)) (f : X → I → Euclidean 3 → Euclidean n)
    (a A : ℝ) (ha : 0 < a) (hA : 0 < A)
    (hpair : ∀ x (q : Pair I (Euclidean 3) S),
      a*q.beat ≤ ‖q.vector (f x)‖ ∧ ‖q.vector (f x)‖ ≤ A*q.beat)
    (k : C → ℝ) (hk : ∀ c, 1 ≤ k c) (x : X) (i : I) (c : C) (z : S i) :
    let family := fun x (ic : I × C) z ↦ k ic.2 • f x ic.1 z
    k c • f x i z ∈ (fun p : ℝ × Euclidean n ↦ p.1 • p.2) ''
      (Icc (a/4) ((2*A+a)*colorTotal k) ×ˢ
        (closure (directionSet family (fun ic ↦ S ic.1)) ∩ sphere 0 1)) := by
  intro family
  have hv := carrier_norm_bounds S f a A hpair x i z
  have hk0 : 0 ≤ k c := zero_le_one.trans (hk c)
  have hnorm : ‖k c • f x i z‖ = k c * ‖f x i z‖ := by
    rw [norm_smul, Real.norm_of_nonneg hk0]
  have hlo : a/4 ≤ ‖k c • f x i z‖ := by
    rw [hnorm]
    have hm := le_mul_of_one_le_left (norm_nonneg (f x i z)) (hk c)
    linarith [hv.1]
  have hhi : ‖k c • f x i z‖ ≤ (2*A+a)*colorTotal k := by
    rw [hnorm]
    calc
      k c * ‖f x i z‖ ≤ k c * (A/2) := mul_le_mul_of_nonneg_left hv.2 hk0
      _ ≤ k c * (2*A+a) := mul_le_mul_of_nonneg_left (by linarith) hk0
      _ = (2*A+a) * k c := mul_comm _ _
      _ ≤ (2*A+a)*colorTotal k := mul_le_mul_of_nonneg_left (color_le_total k hk c) (by positivity)
  have hn : k c • f x i z ≠ 0 := norm_pos_iff.mp ((by positivity : 0 < a/4).trans_le hlo)
  refine ⟨(‖k c • f x i z‖,NormedSpace.normalize (k c • f x i z)), ?_, ?_⟩
  · refine ⟨⟨hlo,hhi⟩, subset_closure (carrier_direction_mem
      (fun ic : I × C ↦ S ic.1) family x (i,c) z), ?_⟩
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hn
  · exact NormedSpace.norm_smul_normalize _
private theorem real_one_nonneg : (0 : ℝ) ≤ 1 := by norm_num
private theorem unscale_one {n : ℕ} {a A beat : ℝ} {v : Euclidean n}
    (h : a * (1 * beat) ≤ ‖(1 : ℝ) • v‖ ∧ ‖(1 : ℝ) • v‖ ≤ A * (1 * beat)) :
    a * beat ≤ ‖v‖ ∧ ‖v‖ ≤ A * beat := by
  simpa only [one_mul,one_smul] using h
#print axioms primary_mem_colored_source_annulus
end JanetCartan.PhysicalPrimary.OriginalPrimarySourceGeometry
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPrimarySourceGeometry
open Lean Meta Elab Command
private def applyName (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def pairTail (e : Expr) (k : Nat) : Expr := Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k
elab "check_actual_primary_source_annulus" : command => liftTermElabM do
  let old := `JanetCartan.PhysicalInitialization.OriginalProtected
  let col := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
  let info ← getConstInfo `JanetCartan.PhysicalSampling.OriginalWeights.Index
  forallTelescope info.type fun p _ => do
    unless p.size == 22 do throwError "primary source annulus: original22 changed"
    let n := applyName ``Nat.succ #[p[0]!]
    let extra := applyName `JanetCartan.PhysicalSampling.samplingCappedExtra #[p[0]!,p[1]!,p[2]!,p[21]!]
    let original := (#[n,p[1]!] ++ p[3:22].toArray).set! 20 extra
    let get (key : Name) := applyName (old ++ key) original
    let colored (key : Name) := applyName (col ++ key) p
    liftM <| IO.eprintln "primary annulus: original22 opened"
    let I := get `Groups
    let D := applyName `JanetCartan.PhysicalSeed.OriginalBoundary.D #[n,p[1]!]
    let S := mkAppN (mkConst `JanetCartan.ActualCarriers.ConstructedSignedGeometry.groupCube [.zero]) #[n,D,I,get `assign]
    let htrue := get `fact29
    liftM <| IO.eprintln "primary annulus: original geometry read"
    let hpair ← forallBoundedTelescope (← inferType htrue) (some 2) fun point _ => do
      let value := mkAppN htrue point
      let one ← mkNumeral (mkConst ``Real) 1
      let pair := mkAppN (pairTail value 2) #[one,mkConst ``real_one_nonneg]
      let first := (← inferType pair).getAppArgs[0]!
      let lhs := first.getAppArgs[2]!
      let beat := lhs.getAppArgs[5]!.getAppArgs[5]!
      let v := first.getAppArgs[3]!.getAppArgs.back!.getAppArgs.back!
      let proof := applyName ``unscale_one #[n,get `a,get `A,beat,v,pair]
      mkLambdaFVars point proof
    liftM <| IO.eprintln "primary annulus: uncolored bounds specialized"
    let C := applyName `JanetCartan.PhysicalInitialization.OriginalColoredProtection.Color #[p[2]!]
    let X := (← inferType (get `family)).bindingDomain!
    let finite ← synthInstance (mkApp (mkConst ``Fintype [.zero]) C)
    let info ← getConstInfo ``primary_mem_colored_source_annulus
    let proof := mkAppN (mkConst ``primary_mem_colored_source_annulus (info.levelParams.map fun _ => .zero))
      #[n,I,C,X,finite,S,get `family,get `a,get `A,get `fact6,get `fact7,hpair,colored `k,colored `scale_ge_one]
    liftM <| IO.eprintln "primary annulus: literal radial witness applied"
    forallBoundedTelescope (← inferType proof) (some 4) fun point _ => do
      unless point.size == 4 do throwError "primary source annulus: primary point boundary changed"
      let ic ← mkAppM ``Prod.mk #[point[1]!,point[2]!]
      let v := mkAppN (colored `family) #[point[0]!,ic,Expr.proj ``Subtype 0 point[3]!]
      let target ← mkAppM `Membership.mem #[colored `Ksource,v]
      let type ← instantiateMVars (← mkForallFVars (p ++ point) target)
      let value ← instantiateMVars (← mkLambdaFVars (p ++ point) (mkAppN proof point))
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
          throwError "primary source annulus: unresolved original geometry"
      let (type,value) := Lean.ShareCommon.shareCommon (type,value)
      let name := `JanetCartan.PhysicalPrimary.OriginalPrimarySourceGeometry.colored_carrier_mem_source
      addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
      addDocStringCore name "The SAME original22 unshifted colored primary carrier lies in the retained source compact; no shifted-gradient, new compact, inverse or mask is asserted (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
      logInfo "original22 primary covector lies in SAME retained colored Ksource, no compact/inverse/mask replacement"
check_actual_primary_source_annulus
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimarySourceGeometry.colored_carrier_mem_source
end JanetCartan.PhysicalPrimary.OriginalPrimarySourceGeometry
end
