module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.GraphObservation
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceDiscrepancy
public import JanetCartan.Iteration.PhysicalPairs.OriginalResidualEmbedding

/-!
# Closed-core decay of the same original smooth source discrepancy

The angular estimate is transferred to the actual native discrepancy on the
same smooth source. Its smoothness and a.e. identity are already proved by
`OriginalSourceDiscrepancy`; neither is a new premise. The resulting constant
precedes every source label and history, and the bound holds on the original
closed half-core (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual

open Set MeasureTheory
open LocalSobolev SmallSupport ArbitraryAccuracy.ResidualLocalization
open RegularSector.NormalizedSolver RegularSector.FiniteMasks.ActualFamily

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)}
    {RQ M : ℝ} {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

private theorem discrepancy_angular_ae
    {f : ActualMaskFamily Ω center RQ A₀ K M} {hK : IsCompact K} {L₀ : ℝ}
    {output : Euclidean (d+1) → ℝ} {ho : Continuous output}
    {hob : ∀ y, ‖output y‖ ≤ 1} {W : Set (Euclidean (d+1))} {hW : MeasurableSet W}
    (V : Set (Euclidean (d+1))) {v : LocalL2 W (Euclidean (d+1))}
    {δ : Euclidean (d+1) → Euclidean (d+1)}
    (hδ : δ =ᵐ[volume] (realSource f hK L₀ output ho hob - 1) (zeroExtend hW v)) :
    δ =ᵐ[volume.restrict V]
      localRealCompression hW V (pairedSource f hK L₀ output ho hob - 1) v := by
  have h := localRealCompression_coeFn hW V
    (pairedSource f hK L₀ output ho hob - 1) v
  rw [← SignedProductEstimates.normalizedSource_real_defect_eq_compression] at h
  exact Filter.EventuallyEq.trans (ae_restrict_of_ae hδ) h.symm

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.Template

open Lean Meta Elab Command

private def discrepancy := `JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancy

elab "bound_original_primary_smooth_discrepancy" : command => liftTermElabM do
  withGraph fun x g weak coeff graph =>
    withLocalDeclD `β (mkSort .one) fun β => do
      withLocalDeclD `indices (← mkArrow β graph) fun indices => do
        let smoothType ← withLocalDeclD `originalHistory graph fun i => do
          let (w,_,_,_,_) ← currentAt g weak coeff i
          let D ← mkAppM ``DFunLike.coe #[app (discrepancy ++ `discrepancy) w]
          let type ← inferType D
          unless type.isForall && !type.bindingDomain!.containsFVar i.fvarId! do
            throwError "primary smooth observation: the source space depends on a queried history"
          pure type.bindingDomain!
        withLocalDeclD `v (← mkArrow β smoothType) fun v => do
          let u ← withLocalDeclD `i β fun i => do
            mkLambdaFVars #[i] (← mkAppM ``Subtype.val #[mkApp v i])
          let p := x ++ #[β,indices,u]
          let rapid := app (root ++ `uncut_corrected_rapid) p
          forallBoundedTelescope (← inferType rapid) (some 6) fun source _ => do
            unless source.size == 6 do
              throwError "primary smooth observation: the source support/profile/moment interface changed"
            withLocalDeclD `observationOrder (mkConst ``Nat) fun s =>
              withLocalDeclD `accuracy (mkConst ``Real) fun q => do
                let n := mkApp (mkConst ``Nat.succ) x[0]!
                let high := mkApp2 (mkConst ``Nat.add)
                  (mkApp2 (mkConst ``Nat.add) s n) (mkNatLit 1)
                let h := mkAppN rapid (source.push high)
                let ht ← inferType h
                unless ht.isAppOf ``JanetCartan.ArbitraryAccuracy.RapidDecayAt do
                  throwError "primary smooth observation: missing the proved uncut angular estimate"
                let ha := ht.getAppArgs
                let ρ := ha[ha.size-3]!
                let obs := ha.back!
                let fixed := g[:23].toArray
                let χ := app (regular ++ `χ₂) fixed
                let r ← mkAppM ``ContDiffBump.rIn #[χ]
                let hr ← mkAppM ``ContDiffBump.rIn_pos #[χ]
                let f := app (regular ++ `f) fixed
                let center := (← inferType f).getAppArgs[2]!
                let V ← mkAppM ``Metric.ball #[center,r]
                let (field,smooth,agree) ← withLocalDeclD `i β fun i => do
                  let (w,_,_,_,_) ← currentAt g weak coeff (mkApp indices i)
                  let datum := mkApp v i
                  let D ← mkAppM ``DFunLike.coe #[app (discrepancy ++ `discrepancy) w]
                  let value := mkApp D datum
                  let hs := app (discrepancy ++ `discrepancy_smooth) (w.push datum)
                  let he := app (discrepancy ++ `discrepancy_ae) (w.push datum)
                  let he ← mkAppM ``discrepancy_angular_ae #[V,he]
                  pure (← mkLambdaFVars #[i] value,← mkLambdaFVars #[i] hs,← mkLambdaFVars #[i] he)
                let proof ← mkAppM ``JanetCartan.PhysicalPairs.OriginalResidualEmbedding.on_inner_ball
                  #[center,r,hr,ρ,field,obs,smooth,agree,s,h,q]
                discard <| save `smooth_discrepancy_cNorm (x ++ #[β,indices,v] ++ source ++ #[s,q]) proof

bound_original_primary_smooth_discrepancy

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.Template
end
