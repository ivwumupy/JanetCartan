module
public import JanetCartan.Iteration.PhysicalPairs.OriginalPacketSize
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageLagWidth
public import JanetCartan.Iteration.PhysicalPairs.Secondary

/-! # The original all-order and L² estimates for the SAME summed correction

Only the actual external quadrature coefficient mass multiplies the sharp
packet size. Positive and negative signs, including the doubled plus and
excluding only the identical minus, use a single family of full Schwartz
waves before all sign/node binders. The size threshold reaches the native
signed graph and the genuinely stronger size estimate simultaneously.
`app:ch_pairs:eq:pairs-lag-sum-size`, `main:eq:joint-physical-profile`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace JanetCartan.PhysicalPairs.OriginalStageSize
open Pseudodifferential PhysicalCutoff

def cost (D M : ℝ) := 2*D*max 0 M
theorem cost_nonneg {D : ℝ} (M : ℝ) (hD : 0 ≤ D) : 0 ≤ cost D M := mul_nonneg (mul_nonneg (by norm_num) hD) (le_max_left _ _)
theorem stage_one {S R₀ : ℝ} (hS : 2 ≤ S) (h₀ : S ≤ R₀) (j : ℕ) : 1 ≤ historyScale R₀ growthExponent j := by
  have h := (by norm_num : (1:ℝ) ≤ 2).trans (hS.trans h₀)
  exact h.trans (le_historyScale h j)

theorem packet_nonneg {D R : ℝ} (s : ℕ) (hD : 0 ≤ D) (hR : 1 ≤ R) : 0 ≤ D*(R^carrierExponent)^(s+1) :=
  mul_nonneg hD (pow_nonneg (Real.rpow_nonneg (zero_le_one.trans hR) _) _)

theorem total {D M A R δ x mass : ℝ} (s : ℕ) (hD : 0 ≤ D) (hR : 1 ≤ R) (hm : mass ≤ M*R^(1+samplingSlack))
    (hx : x ≤ 2*(D*(R^carrierExponent)^(s+1))*(δ*R^A)^2*mass) :
    x ≤ cost D M*δ^2*R^(2*A+1+samplingSlack)*(R^carrierExponent)^(s+1) := by
  have hm' := hm.trans (mul_le_mul_of_nonneg_right (le_max_right 0 M) (Real.rpow_nonneg (zero_le_one.trans hR) _))
  have h := OriginalLagAlgebra.total_price (δ := δ) (A := A) hR (packet_nonneg s hD hR) 0 hm'
  simp only [pow_zero,mul_one,Nat.cast_zero,mul_zero,neg_zero,Real.rpow_zero,sub_zero] at h
  exact (hx.trans h).trans_eq (by unfold cost; ring)

theorem order_zero {n N : ℕ} (S : 𝓢(Euclidean n,Euclidean N)) {C R δ : ℝ} (hR : 1 ≤ R)
    (h : (eLpNorm (fun ξ ↦ euclideanSobolevWeight ((0 : ℕ) : ℝ) ((2*Real.pi) • ξ) • 𝓕 (complexify S) ξ) 2 volume).toReal ≤
      C*δ^2*R^(2*RevisedScales.forcingExponent n+1+samplingSlack)*(R^carrierExponent)^(0+1 : ℕ)) :
    PhysicalBernstein.physicalL2Norm S ≤ C*δ^2*R^RevisedScales.displacementLoss n := by
  have hpos := zero_lt_one.trans_le hR
  simpa only [Nat.cast_zero, physicalWeightedNorm_zero_eq_L2, Nat.zero_add, pow_one, RevisedScales.displacementLoss, Real.rpow_add hpos, mul_assoc] using h
end JanetCartan.PhysicalPairs.OriginalStageSize
end
public meta section
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 18000
namespace JanetCartan.PhysicalPairs.OriginalStageSize
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalStageSize
private def sel := `JanetCartan.PhysicalPairs.OriginalSizeSelection
private def hs := `JanetCartan.PhysicalPairs.SampledHistory
private def sum := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def mass := `JanetCartan.PhysicalPairs.OriginalSampleMass
private def cw := `JanetCartan.PhysicalPairs.OriginalCommonWaves
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def a (k : Name) (v : Array Expr) := mkAppN (mkConst k) v
elab "price_the_original_physical_sum " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (sel ++ `D)).type (some 40) fun pre _ => do
    let b := pre[:37].toArray
    let hcap := pre[37]!
    let D := a (sel ++ `D) pre
    let M := a (mass ++ `constant) b[:22].toArray
    if piece.getNat ≤ 1 then
      withLocalDeclD `physicalOrder (mkConst ``Nat) fun s => do
        let term := a (ns ++ `cost) #[mkApp D s,M]
        if piece.getNat == 0 then discard <| store (ns ++ `constant) (pre.push s) term true
        else
          let pf := a (ns ++ `cost_nonneg) #[mkApp D s,M,mkApp (a (sel ++ `D_nonneg) pre) s]
          discard <| store (ns ++ `constant_nonneg) (pre.push s) pf false (some ((← inferType pf).replace fun e => if e == term then some (a (ns ++ `constant) (pre.push s)) else none))
      return
    withLocalDeclD `commonPrimary (a (cw ++ `Waves) b) fun W => do
      let w := a (cw ++ `onLabels) (b.push W)
      let first := a (fm ++ `first_mask) (b ++ #[w,pre[38]!,pre[39]!])
      withLocalDeclD `fullDerivativeJets (← inferType first).bindingDomain! fun hA => withLocalDeclD `physicalOrder (mkConst ``Nat) fun r => do
        let s := if piece.getNat == 2 then r else mkNatLit 0
        let p := b ++ #[hcap,W,pre[38]!,pre[39]!,hA]
        let cost := a (ns ++ `cost) #[mkApp D s,M]
        let named := a (ns ++ `constant) (pre.push s)
        let fixed := if piece.getNat == 2 then p.push s else p
        withLocalDeclD `R₀ (mkConst ``Real) fun R₀ => do withLocalDeclD `reachedSignedAndSize (← mkAppM ``LE.le #[a (sel ++ `S) pre,R₀]) fun h₀ => do
          let ho ← mkAppM ``le_trans #[a (sel ++ `reaches_signed) pre,h₀]
          let ht ← mkAppM ``le_trans #[a (sel ++ `reaches_size) pre,h₀]
          let head := b ++ #[R₀,ho]
          forallBoundedTelescope (← inferType (a (sum ++ `correction) head)) (some 6) fun row _ => do
            let stem := head ++ row
            let waves := mkAppN W (#[R₀,ho] ++ row)
            let hR ← mkAppM (ns ++ `stage_one) #[a (sel ++ `hS) pre,h₀,row[0]!]
            let R := (← inferType hR).appArg!
            let n := mkApp (mkConst ``Nat.succ) b[0]!
            let N := a `JanetCartan.embeddingDimension #[n]
            let A := a `JanetCartan.RevisedScales.forcingExponent #[n]
            withLocalDeclD `δ (mkConst ``Real) fun δ => do
              let native := stem ++ #[waves,δ]
              let all := fixed ++ #[R₀,h₀] ++ row ++ #[δ]
              if piece.getNat == 3 then
                let hs0 := a (ns ++ `size) (p ++ #[s,R₀,h₀] ++ row ++ #[δ])
                let result := a (ns ++ `order_zero) #[n,N,a (sum ++ `correction) native,named,R,δ,hR,hs0]
                discard <| store (ns ++ `physicalL2) all result
                return
              let hDn := mkApp (a (sel ++ `D_nonneg) pre) s
              let hSingle := a (ns ++ `packet_nonneg) #[mkApp D s,R,s,hDn,hR]
              let B := (← inferType hSingle).appArg!
              let sr ← mkAppOptM ``Nat.cast #[some (mkConst ``Real),none,s]
              let priced := mkAppN (a (sum ++ `exact_coefficient_mass_bound) native) #[sr,B,hSingle]
              let packets ← forallBoundedTelescope (← inferType priced).bindingDomain! (some 4) fun tail _ => do
                let hp := a `JanetCartan.PhysicalPairs.OriginalPacketSize.size (b ++ #[hcap,w,pre[38]!,pre[39]!,hA,R₀,ho,ht] ++ row ++ tail ++ #[s])
                mkLambdaFVars tail hp
              let each ← store (ns ++ `coefficient_mass_size) all (mkApp priced packets)
              let massBound := Expr.proj ``And 0 (.proj ``And 1 (a (mass ++ `coefficient_budgets) stem))
              let qty := (← inferType massBound).getAppArgs[2]!
              let lhs := (← inferType each).getAppArgs[2]!
              let total := a (ns ++ `total) #[mkApp D s,M,A,R,δ,lhs,qty,s,hDn,hR,massBound,each]
              discard <| store (ns ++ `size) all total false (some ((← inferType total).replace fun e => if e == cost then some named else none))
price_the_original_physical_sum 0
price_the_original_physical_sum 1
price_the_original_physical_sum 2
price_the_original_physical_sum 3
end JanetCartan.PhysicalPairs.OriginalStageSize
end
