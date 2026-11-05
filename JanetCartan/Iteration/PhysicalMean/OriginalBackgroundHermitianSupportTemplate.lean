module

public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitian
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
public meta import Lean

/-!
# Entire original exterior support and unscaled native-self identification

These downstream declarations do not participate in publication of the stable
native data. The same complete parent collar, rather than the inner annular
sampler plateau, contains every weighted point (app:ch_waves:eq:background-quadrature).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
open ContinuumRow CanonicalCarrier Sampling SeparatedSampling PhysicalSampling.OriginalOuterWeightsTemplate

private theorem outer_sampling_node (z : Point) :
    parameter (carrierSamplingEquiv.symm z) = WithLp.toLp 2 z := by
  obtain ⟨q,rfl⟩ := carrierSamplingEquiv.surjective z
  rw [carrierSamplingEquiv.symm_apply_apply, parameter_apply]
  ext c
  fin_cases c <;> rfl

private theorem outer_square_tsupport (χ : CarrierParameter → ℝ) :
    MapsTo carrierSamplingEquiv.symm (tsupport (outerSquare χ)) (tsupport χ) := by
  apply closure_minimal
  · intro z hz
    apply subset_tsupport χ
    intro hzero
    exact hz (by simp only [outerSquare,hzero,zero_pow (by decide : 2 ≠ 0)])
  · exact (isClosed_tsupport χ).preimage
      carrierSamplingLinearEquiv.symm.toContinuousLinearEquiv.continuous

private theorem outer_pair_support {n : ℕ} (χ : CarrierParameter → ℝ)
    (ζ : Euclidean 3 → Euclidean (n-1)) (K : Set (Euclidean 3 × Euclidean (n-1)))
    (hχ : ∀ z ∈ tsupport χ, (parameter z,ζ (parameter z)) ∈ K) :
    ∀ z ∈ tsupport (outerSquare χ), (WithLp.toLp 2 z,ζ (WithLp.toLp 2 z)) ∈ K := by
  intro z hz
  simpa only [outer_sampling_node] using hχ _ (outer_square_tsupport χ hz)

private theorem carrier_point_interior {n : ℕ} (hn : 5 ≤ n)
    (a : PhysicalInitialization.OriginalPatchIndex hn) (cell : PhysicalSeed.OriginalBoundary.centers hn a)
    (p : CarrierParameter)
    (hp : p ∈ ball (cell.1.1 0, FullPhaseCharts.ActualComparison.spectatorCenter cell.1.1)
      (PhysicalSeed.OriginalBoundary.εcarrier hn a cell)) :
    parameter p ∈ FrozenMenu.parameterInterior
      (2 * ((PhysicalSeed.OriginalBoundary.D hn).patches a.1 a.2).radius) := by
  have hcell := PhysicalSeed.OriginalBoundary.carrier_cells hn a cell
  have hpoint : ((0 : Euclidean n),p) ∈
      ball (0 : Euclidean n) (PhysicalSeed.OriginalBoundary.εcarrier hn a cell) ×ˢ
      ball (cell.1.1 0, FullPhaseCharts.ActualComparison.spectatorCenter cell.1.1)
        (PhysicalSeed.OriginalBoundary.εcarrier hn a cell) := ⟨mem_ball_self hcell.1,hp⟩
  exact (hcell.2.2.2.2.1 hpoint).2

private theorem actual_spatialPatch_smooth {n : ℕ} (hn : 5 ≤ n)
    (a : PhysicalInitialization.OriginalPatchIndex hn) :
    ContDiffOn ℝ ∞ (PhysicalSeed.OriginalBoundary.T hn a).reference.spatialPatch
      (FrozenMenu.parameterInterior
        (2 * ((PhysicalSeed.OriginalBoundary.D hn).patches a.1 a.2).radius)) := by
  exact (PhysicalSeed.OriginalBoundary.T hn a).reference.spatialPatch_smooth
    (((PhysicalSeed.OriginalBoundary.hD hn).2.2.2.2.1 a.1 a.2).1)

private theorem outer_parameter_support (χ : CarrierParameter → ℝ) (S : Set (Euclidean 3))
    (hχ : ∀ p ∈ tsupport χ, parameter p ∈ S) :
    ∀ z ∈ tsupport (outerSquare χ), WithLp.toLp 2 z ∈ S := by
  intro z hz
  simpa only [outer_sampling_node] using hχ _ (outer_square_tsupport χ hz)

/-- Apply the old root-to-parent buffer to the ENTIRE old physical coefficient
compact, not just the currently nonzero measurement or sampled points. -/
private theorem physical_set_parent {n : ℕ}
    {X : Set (Euclidean n)} {a ρ σ : ℝ}
    {zRoot zCell : Euclidean 3} {ηRoot ηCell : Euclidean (n-1)}
    (hX : X ⊆ closedBall (0 : Euclidean n) (a/8))
    (ha : 4*a ≤ ρ/2) (hρ : 0 < ρ)
    (hparent : closedBall ((0 : Euclidean n),(zRoot,ηRoot)) (2*ρ) ⊆
      ball ((0 : Euclidean n),(zCell,ηCell)) σ) :
    X ⊆ ball (0 : Euclidean n) σ := by
  intro x hx
  have hx' : x ∈ closedBall (0 : Euclidean n) (2*ρ) :=
    closedBall_subset_closedBall (by linarith : a/8 ≤ 2*ρ) (hX hx)
  have hp : (x,(zRoot,ηRoot)) ∈ closedBall ((0 : Euclidean n),(zRoot,ηRoot)) (2*ρ) := by
    rw [← closedBall_prod_same]
    exact ⟨hx',mem_closedBall_self (by positivity)⟩
  have hs := hparent hp
  rw [← ball_prod_same] at hs
  exact hs.1

private theorem graph_set_parent {n : ℕ}
    {X : Set (Euclidean n)} {ψ : Point → ℝ}
    {ζ : Euclidean 3 → Euclidean (n-1)}
    {zCell : Euclidean 3} {ηCell : Euclidean (n-1)} {σ : ℝ}
    (hX : X ⊆ ball (0 : Euclidean n) σ)
    (hψ : ∀ z ∈ tsupport ψ,
      (WithLp.toLp 2 z,ζ (WithLp.toLp 2 z)) ∈ closedBall (zCell,ηCell) σ) :
    ∀ x ∈ X, ∀ z ∈ tsupport ψ,
      (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z)) ∈
        closedBall ((0 : Euclidean n),(zCell,ηCell)) σ := by
  intro x hx z hz
  rw [← closedBall_prod_same]
  exact ⟨ball_subset_closedBall (hX hx),hψ z hz⟩

private theorem smaller_parent_in_current {E : Type} [PseudoMetricSpace E]
    {center : E} {σ : ℝ} {Ω : Set E}
    (h : closedBall center (2*σ) ⊆ Ω) : closedBall center σ ⊆ Ω := by
  intro x hx
  have hσ : 0 ≤ σ := dist_nonneg.trans (mem_closedBall.mp hx)
  exact h (closedBall_subset_closedBall (by linarith : σ ≤ 2*σ) hx)

private theorem parent_into_response_region {n : ℕ}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    {W : Set (Euclidean 3 × Euclidean (n-1))}
    {center : Euclidean 3 × Euclidean (n-1)} {σ : ℝ}
    (hraw : closedBall ((0 : Euclidean n),center) (2*σ) ⊆ Ω)
    (hW : closedBall center σ ⊆ W) :
    closedBall ((0 : Euclidean n),center) σ ⊆ Ω ∩ ((univ : Set (Euclidean n)) ×ˢ W) := by
  intro w hw
  refine ⟨smaller_parent_in_current hraw hw, mem_univ _, ?_⟩
  rw [← closedBall_prod_same] at hw
  exact hW hw.2

private theorem physical_ball_compact (n : ℕ) (r : ℝ) :
    IsCompact (closedBall (0 : Euclidean n) r) := isCompact_closedBall _ _

private theorem parent_ball_compact (n : ℕ)
    (c : Euclidean n × (Euclidean 3 × Euclidean (n-1))) (r : ℝ) :
    IsCompact (closedBall c r) := isCompact_closedBall _ _

end JanetCartan.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate
private def ps := `JanetCartan.PhysicalSampling
private def ns := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian

private def forallResult : Expr → Nat → MetaM Expr
  | type, 0 => pure type.consumeMData
  | type, k+1 => do
    let .forallE _ _ body _ := type.consumeMData
      | throwError "original positive Hermitian: changed support telescope"
    forallResult body k

private def membershipSet (type : Expr) : MetaM Expr := do
  unless type.isAppOfArity ``Membership.mem 5 do
    throwError "original positive Hermitian: changed support membership"
  let K := type.getAppArgs[3]!
  if K.hasLooseBVars then throwError "original positive Hermitian: parent depends on a later point"
  return K

private def checking (which : Nat) (work : MetaM Unit) : MetaM Unit := do
  liftM <| IO.eprintln s!"checking original background support field {which}"
  work
  liftM <| IO.eprintln s!"finished original background support field {which}"

elab "retain_original_positive_background_support " which:num : command => liftTermElabM <|
    checking which.getNat <| withTransparency .reducible <| withActualRow fun d => do
  let p := d.parameters
  let a := d.native64
  match which.getNat with
  | 7 =>
    let ca := d.mean70[37]!.getAppArgs
    let zero ← mkNumeral (← inferType d.mean70[37]!).bindingDomain! 0
    let radius ← mkAppM ``HMul.hMul #[← mkNumeral (mkConst ``Real) 4,ca[2]!]
    discard <| save `X p (← mkAppM ``Metric.closedBall #[zero,radius]) true
  | 8 =>
    let init := d.initial62
    let hsharp := mkAppN (mkConst (ps ++ `OriginalMeasuredSupport.coefficient_ball_in_original_sharp_ball))
      (a[:22].toArray.push d.row)
    let hA := mkAppN (mkConst (ps ++ `OriginalChoices.Band.ha_radius)) init[:7].toArray
    let radiusArgs := #[d.raw13[0]!,init[2]!,init[3]!,init[4]!,init[5]!]
    let radius := mkAppN (mkConst (ps ++ `originalSamplingRadius)) radiusArgs
    let parent := mkAppN (mkConst (ps ++ `originalSamplingRadius_spec)) (radiusArgs.push init[6]!)
    let proof ← mkAppM ``physical_set_parent #[hsharp,hA,.proj ``Subtype 1 radius,.proj ``And 0 parent]
    discard <| save `X_in_parent p proof
  | 9 =>
    let init := d.initial62
    let T := d.raw13[5]!
    unless T.isAppOfArity `JanetCartan.PhysicalSeed.OriginalBoundary.T 3 do
      throwError "original positive Hermitian: changed original patch family"
    let patch := T.getAppArgs[2]!
    let outer := mkAppN (mkConst (ps ++ `OriginalOuterWeights.χ_support_original)) (a[:22].toArray.push d.row)
    let χ := mkAppN (mkConst (ps ++ `OriginalOuterWeights.χ)) (a[:22].toArray.push d.row)
    let support ← mkAppM ``tsupport #[χ]
    let closed ← withLocalDeclNoLocalInstanceUpdate `q .default (mkConst `JanetCartan.ContinuumRow.CarrierParameter) fun q => do
      withLocalDeclNoLocalInstanceUpdate `hq .default (← mkAppM ``Membership.mem #[support,q]) fun hq => do
        let h := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.outer_carrier_in_closed_cell)
          #[d.raw13[0]!,init[2]!,patch,init[5]!,q,mkAppN outer #[q,hq]]
        mkLambdaFVars #[q,hq] h
    let K ← membershipSet (← forallResult (← inferType closed) 2)
    let point := mkAppN (mkConst ``outer_pair_support)
      #[d.raw13[0]!,χ,mkAppN (mkConst (ns ++ `ζ)) p,K,closed]
    discard <| save `outer_carrier_parent p point
  | 17 =>
    let X ← bodyAt (ns ++ `X) p
    discard <| save `X_compact p (mkAppN (mkConst ``physical_ball_compact) #[d.raw13[0]!,X.appArg!])
  | 18 =>
    let ca := d.mean70[37]!.getAppArgs
    unless ca.size == 4 do throwError "original positive Hermitian: changed common measurement"
    let one ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 3)) 1
    let hC := mkAppN (mkConst `JanetCartan.Sampling.tsupport_canonicalSamplingMeasurement) ca
    let hfour := mkAppN (mkConst `JanetCartan.ContinuumRow.FixedCutoffs.physical_tsupport_four) #[ca[0]!,ca[2]!,ca[3]!,one]
    discard <| save `C_support_X p (← mkAppM ``Set.Subset.trans #[hC,hfour])
  | 19 =>
    let n := d.raw13[0]!
    let merged := mkAppN (mkConst (ps ++ `samplingCappedExtra)) #[a[0]!,a[1]!,a[2]!,a[21]!]
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,a[1]!,merged]
    let seed := #[n,a[1]!] ++ a[3:21].toArray ++ #[capped]
    discard <| save `X_cell_gap p (mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hMeasureCell) seed)
  | 20 =>
    let hC := mkAppN (mkConst (ns ++ `C_support_X)) p
    let hX := mkAppN (mkConst (ns ++ `X_in_parent)) p
    discard <| save `measurement_support_parent p (← mkAppM ``Set.Subset.trans #[hC,hX])
  | 21 =>
    let hX := mkAppN (mkConst (ns ++ `X_in_parent)) p
    let point := mkAppN (mkConst (ns ++ `outer_carrier_parent)) p
    discard <| save `graph_in_parent p (← mkAppM ``graph_set_parent #[hX,point])
  | 22 =>
    let graph := mkAppN (mkConst (ns ++ `graph_in_parent)) p
    let parent ← membershipSet (← forallResult (← inferType graph) 4)
    discard <| save `parent p parent true
  | 23 =>
    let parent ← bodyAt (ns ++ `parent) p
    unless parent.isAppOf ``Metric.closedBall && parent.getAppNumArgs ≥ 2 do
      throwError "original positive Hermitian: actual parent is not the original closed ball"
    let pa := parent.getAppArgs
    discard <| save `parent_compact p (mkAppN (mkConst ``parent_ball_compact)
      #[d.raw13[0]!,pa[pa.size-2]!,pa[pa.size-1]!])
  | 24 =>
    let init := d.initial62
    let T := d.raw13[5]!
    unless T.isAppOfArity `JanetCartan.PhysicalSeed.OriginalBoundary.T 3 do
      throwError "original positive Hermitian: changed parent patch"
    let spec := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalUncutSource.parameterComparisonWindow_spec)
      #[d.raw13[0]!,init[2]!,T.getAppArgs[2]!,init[5]!]
    let subset := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 spec))
    let point := mkAppN (mkConst (ns ++ `outer_carrier_parent)) p
    let ψ := mkAppN (mkConst (ns ++ `ψ)) p
    let supp ← mkAppM ``tsupport #[ψ]
    let window ← withLocalDeclNoLocalInstanceUpdate `z .default (mkConst `JanetCartan.SeparatedSampling.Point) fun z => do
      withLocalDeclNoLocalInstanceUpdate `hz .default (← mkAppM ``Membership.mem #[supp,z]) fun hz => do
        let h := mkAppN point #[z,hz]
        let t ← inferType h
        unless t.isAppOfArity ``Membership.mem 5 do throwError "original positive Hermitian: changed carrier membership"
        mkLambdaFVars #[z,hz] (mkAppN subset #[t.getAppArgs[4]!,h])
    discard <| save `outer_carrier_comparison_window p window
  | 11 =>
    let colorType := (← inferType a[61]!).bindingDomain!
    withLocalDeclNoLocalInstanceUpdate `color .default colorType fun color => do
      let saved ← savedResponse d color
      let init := d.initial62
      let T := d.raw13[5]!
      unless T.isAppOfArity `JanetCartan.PhysicalSeed.OriginalBoundary.T 3 do
        throwError "original positive Hermitian: changed parent patch"
      let args := #[d.raw13[0]!,init[2]!,T.getAppArgs[2]!,init[5]!]
      let spec := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalUncutSource.parameterComparisonWindow_spec) args
      let W := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalUncutSource.parameterComparisonWindow) args
      let subset := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 spec))
      let raw := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.current_cell) saved.source53
      let hopen := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.current_open) saved.source53
      let rawΩ := (← inferType hopen).appArg!
      let parent ← bodyAt (ns ++ `parent) p
      let pa := parent.getAppArgs
      let proof := mkAppN (mkConst ``parent_into_response_region)
        #[d.raw13[0]!,rawΩ,W,.proj ``Prod 1 pa[pa.size-2]!,pa[pa.size-1]!,raw,subset]
      let Ω := mkAppN (mkConst (ns ++ `response_region)) (p.push color)
      let target ← mkAppM ``Set.Subset #[mkAppN (mkConst (ns ++ `parent)) p,Ω]
      discard <| save `parent_in_response_region (p.push color) proof false (some target)
  | 31 | 32 | 33 =>
    let colorType := (← inferType a[61]!).bindingDomain!
    withLocalDeclNoLocalInstanceUpdate `color .default colorType fun color => do
      let saved ← savedResponse d color
      let (short,field,data) := if which.getNat == 31 then (`response_region,`region,true)
        else if which.getNat == 32 then (`response_region_open,`region_open,false)
        else (`full_response_smooth,`response_smooth,false)
      let proof := mkAppN (mkConst (`JanetCartan.PhysicalPrimary.OriginalPhysicalResponse ++ field)) saved.full60
      discard <| save short (p.push color) proof data
  | 34 =>
    let outer := a[:22].toArray.push d.row
    let χ := mkAppN (mkConst (ps ++ `OriginalOuterWeights.χ)) outer
    let hχ := mkAppN (mkConst (ps ++ `OriginalOuterWeights.χ_support_original)) outer
    let supp ← mkAppM ``tsupport #[χ]
    let T := d.raw13[5]!
    unless T.isAppOfArity `JanetCartan.PhysicalSeed.OriginalBoundary.T 3 do
      throwError "original positive Hermitian: changed original patch"
    let ta := T.getAppArgs
    let interior ← withLocalDeclNoLocalInstanceUpdate `q .default (mkConst `JanetCartan.ContinuumRow.CarrierParameter) fun q => do
      withLocalDeclNoLocalInstanceUpdate `hq .default (← mkAppM ``Membership.mem #[supp,q]) fun hq => do
        let h := mkAppN (mkConst ``carrier_point_interior)
          #[ta[0]!,ta[1]!,ta[2]!,d.initial62[5]!,q,mkAppN hχ #[q,hq]]
        mkLambdaFVars #[q,hq] h
    let S ← membershipSet (← forallResult (← inferType interior) 2)
    let proof := mkAppN (mkConst ``outer_parameter_support) #[χ,S,interior]
    discard <| save `outer_parameter_interior p proof
  | 35 =>
    let T := d.raw13[5]!
    unless T.isAppOfArity `JanetCartan.PhysicalSeed.OriginalBoundary.T 3 do
      throwError "original positive Hermitian: changed original patch"
    discard <| save `ζ_smooth p (mkAppN (mkConst ``actual_spatialPatch_smooth) T.getAppArgs)
  | _ => throwError "original positive Hermitian: unknown actual support field"

end JanetCartan.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
end
