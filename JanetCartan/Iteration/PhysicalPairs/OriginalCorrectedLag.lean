module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCorrectedPairs
public import JanetCartan.Iteration.PhysicalPairs.OriginalResidualEmbedding

/-! # Pointwise decay for the actual smooth-right minus original signed stress

Apply the proved full original corrected angular family, not a polynomial or
an individual tested letter, to the exact native discrepancy. The closed ball
is the stage ball, half the inner measurement radius. All constants precede
the actual history/common shift/sign/node. `app:ch_pairs:eq:pairs-lag-one-error`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Set Metric
open scoped ContDiff
namespace JanetCartan.PhysicalPairs.OriginalCorrectedLag

theorem point_of_cnorm {n : ℕ} {ι : Type*} (c : Euclidean n) (r : ℝ) (ρ : ι → ℝ)
    (f : ι → Euclidean n → Euclidean n) (hf : ∀ t, ContDiff ℝ ∞ (f t)) (q : ℝ)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, cNorm (closedBall c r) 0 (f t) ≤ C*(ρ t)^(-q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ∀ x ∈ closedBall c r, ‖f t x‖ ≤ C*(ρ t)^(-q) := by
  obtain ⟨C,hC,hh⟩ := h
  exact ⟨C,hC,fun t x hx ↦ (norm_le_cNorm (isCompact_closedBall _ _) ((hf t).of_le (by simp)) hx).trans (hh t)⟩
end JanetCartan.PhysicalPairs.OriginalCorrectedLag
end
public meta section
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalCorrectedLag
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalCorrectedLag
private def corr := `JanetCartan.PhysicalPairs.OriginalCorrectedPairs
private def err := `JanetCartan.PhysicalPairs.OriginalResidualEmbedding
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
elab "price_smooth_right_signed_discrepancy " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (fm ++ `first_mask)).type (some 41) fun p _ => do
    let b := p[:37].toArray
    let z := p[:38].toArray
    let β := a `JanetCartan.PhysicalPairs.SampledHistory.Labels b
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let ρ := a (fm ++ `frequency) b
    let measured := ((← getConstInfo (fm ++ `measured)).value! (allowOpaque := true)).beta z
    lambdaBoundedTelescope measured 1 fun label row => do
      let pt := row.getAppArgs
      let fam (v : Expr) := mkLambdaFVars label v
      let f ← fam (a (err ++ `error) pt)
      let hf ← fam (a (err ++ `error_smooth) pt)
      let ae := a (err ++ `actual_observation_ae) pt
      let rhs := (← inferType ae).appArg!
      unless rhs.isAppOfArity `MeasureTheory.AEEqFun.cast 6 && rhs.appArg!.isAppOfArity ``Subtype.val 3 do throwError "no original local angular observation class"
      let u ← fam rhs.appArg!.appArg!
      let some V := (← inferType ae).getAppArgs[2]!.find? (fun e => e.isAppOf `Metric.ball) | throwError "missing original inner measurement ball"
      let va := V.getAppArgs
      let c := va[va.size-2]!
      let r := va.back!
      let χ := r.appArg!
      let hr ← mkAppM `ContDiffBump.rIn_pos #[χ]
      withLocalDeclD `jetOrder (mkConst ``Nat) fun s => withLocalDeclD `accuracy (mkConst ``Real) fun q => do
        if piece.getNat == 0 then
          let level := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) s n) (mkNatLit 1)
          let h := a (corr ++ `corrected_rapid) (p.push level)
          let proof := mkAppN (mkConst (err ++ `on_inner_ball) [.zero]) #[n,β,c,r,hr,ρ,f,u,hf,← fam ae,s,h,q]
          discard <| store (ns ++ `smooth_right_cnorm) (p ++ #[s,q]) proof
          return
        let h := a (ns ++ `smooth_right_cnorm) (p ++ #[mkNatLit 0,q])
        let some D := (← inferType h).find? (fun e => e.isAppOf `Metric.closedBall) | throwError "no retained true closed stage ball"
        let rad := D.appArg!
        let pf := mkAppN (mkConst (ns ++ `point_of_cnorm) [.zero]) #[n,β,c,rad,ρ,f,hf,q,h]
        discard <| store (ns ++ `pointwise) (p.push q) pf
price_smooth_right_signed_discrepancy 0
price_smooth_right_signed_discrepancy 1
end JanetCartan.PhysicalPairs.OriginalCorrectedLag
end
