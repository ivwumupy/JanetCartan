module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSizeSelection
public import JanetCartan.Iteration.PhysicalPairs.OriginalTensorLag

/-! # Sharp physical Hʳ bound for each actual signed Schwartz packet

Instantiate the merged reference size estimate with the exact true pair, the
same normalized inverse, the two slots of the complete derivative amplitude,
and the original global smooth solver. The auxiliary chart-supported source is
used only in the estimate: its once-measured L² class is identical and normal
reconstruction agrees on the output support. `app:ch_pairs:eq:pairs-lag-sum-size`.
-/
@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace JanetCartan.PhysicalPairs.OriginalPacketSize
def pairSlots {X : Type*} (l r : X) (j : Fin 2) : X := if j = 0 then l else r
def cacheSlots {X : Type*} (W : Fin 2 → X) (k : ℕ) : X := if k = 0 then W 0 else W 1
theorem different (sg : Bool) : sg = true → (0 : Fin 2) ≠ 1 := fun _ ↦ by decide
def unitFactor (n : ℕ) : Euclidean n → ℝ := fun _ ↦ 1
open scoped ContDiff in
theorem unit_smooth (n : ℕ) : ContDiff ℝ ∞ (unitFactor n) := contDiff_const
open scoped ContDiff in
theorem unit_on (n : ℕ) (U : Set (Euclidean n)) : ContDiffOn ℝ ∞ (unitFactor n) U := (unit_smooth n).contDiffOn
theorem strictly_positive {u : ℝ} (hu : 2 ≤ u) : 0 < u := (by norm_num : (0:ℝ) < 2).trans_le hu

open MeasureTheory Metric SmallSupport LocalSobolev AmbientResponse ProjectedStressFrame ProtectedFlow
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius NNReal ENNReal
local instance : Fact (1 ≤ ((2:ℝ≥0):ℝ≥0∞)) := ⟨by norm_num⟩
/-- Raw physical stress is used in the broad input. The normalized size operator
uses its genuine extension, which agrees only on the retained coefficient ball. -/
theorem measured_extended {n N : ℕ} {W : Set (Euclidean n)} {c : Euclidean n} (χ : ContDiffBump c)
    (ext : BallExtension.Parameters (Euclidean n)) (F : Euclidean n → Euclidean N) {b : ℝ}
    (hc : ext.center = 0) (hb : ext.radius = b) (hχb : tsupport (χ : Euclidean n → ℝ) ⊆ ball 0 b)
    (H : MetricField n) (η α : Euclidean n → ℝ) (hα : EqOn α η (tsupport (χ : Euclidean n → ℝ))) (v : LocalL2 W (Euclidean n))
    (hv : (v : Euclidean n → Euclidean n) =ᵐ[volume.restrict W] fun x ↦ (WithLp.toLp 2 (stressSource (projectedStress F) (fun y ↦ η y • H y) x) : Euclidean n)) :
    let f := fun x ↦ (WithLp.toLp 2 (cutoffSource (fun _ ↦ 1) (stressSource (extendedProjectedStress ext F) (fun y ↦ α y • H y)) x) : Euclidean n)
    ∀ hf : MemLp f 2 volume, bumpL2 (p := 2) le_rfl χ ((hf.restrict W).toLp f) = bumpL2 (p := 2) le_rfl χ v := by
  intro f hf
  apply Lp.ext
  filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ ((hf.restrict W).toLp f),bumpL2_coeFn (p := 2) le_rfl χ v,(hf.restrict W).coeFn_toLp,hv] with x he he' hnew hold
  rw [he,he',hnew,hold]
  by_cases hx : χ x = 0
  · simp only [hx,zero_smul]
  · have hs := subset_tsupport (χ : Euclidean n → ℝ) (show χ x ≠ 0 from hx)
    have hext : x ∈ closedBall ext.center ext.radius := by simpa only [hc,hb] using ball_subset_closedBall (hχb hs)
    have hQ : extendedProjectedStress ext F x = projectedStress F x := affineFrameExtension_eqOn ext (projectedStress F) hext
    simp only [f,cutoffSource,stressSource,LinearMap.coe_mk,AddHom.coe_mk,one_smul,hα hs,hQ]
end JanetCartan.PhysicalPairs.OriginalPacketSize
end
public meta section
set_option warningAsError true
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace JanetCartan.PhysicalPairs.OriginalPacketSize
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalPacketSize
private def sel := `JanetCartan.PhysicalPairs.OriginalSizeSelection
private def hp := `JanetCartan.PhysicalPairs.SampledHistory
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def rows := `JanetCartan.PhysicalPairs.OriginalMaskRows
private def sup := `JanetCartan.PhysicalPairs.OriginalSizeSupport
private def fq := `JanetCartan.PhysicalPairs.OriginalSizeFrequency
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def dataNS := `JanetCartan.PhysicalPairs.OriginalSignedData
private def pkt := `JanetCartan.PhysicalPairs.OriginalSignedPackets
private def a (k : Name) (v : Array Expr) := mkAppN (mkConst k) v
private def down (h : Expr) : Nat → Expr | 0 => h | k+1 => down (.proj ``And 1 h) k
private def part (h : Expr) (k : Nat) : Expr := .proj ``And 0 (down h k)
elab "prove_original_signed_packet_size " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hp ++ `index)).type (some 49) fun pt gf => do
    let b := pt[:37].toArray
    let fix := gf.getAppArgs[:23].toArray
    let d := b[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let N := a `JanetCartan.embeddingDimension #[n]
    let m (k : Name) := a (mask ++ k) fix
    let stat (k : Name) := a (reg ++ k) fix
    let t := a (hp ++ `label) pt
    let reached := part (a (hp ++ `measured_history) pt) 0
    let current := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPairs.projected).value! (allowOpaque := true)).beta (b[:36].toArray ++ #[pt[37]!,reached] ++ pt[39:43].toArray)
    let weak := current.getAppArgs
    let cur (k : Name) := a (reg ++ `Current ++ k) weak
    let F := Expr.proj ``Subtype 0 current
    let χ₂ := stat `χ₂
    let α := a (sup ++ `factor) fix
    let η := a (ns ++ `unitFactor) #[n]
    let hcapTy := (← inferType (a (sel ++ `native_budget) b)).bindingDomain!
    withLocalDeclD `historyCapForSize hcapTy fun hcap => do
      forallBoundedTelescope (← inferType (a (fm ++ `first_mask) b)) (some 4) fun pars _ => do
        let Z := mkApp pars[0]! t
        let ptZ := pt.push Z
        let selP := b ++ #[hcap,pars[1]!,pars[2]!]
        let named (k : Name) := a (sel ++ k) selP
        let θ := a (dataNS ++ `angles) pt
        let oldη := (← inferType (m `χsrc_smooth)).appArg!
        let H ← mkAppM `JanetCartan.PhysicalPairs.SampledInput.tensor #[Z,θ,pt[45]!,pt[46]!,pt[47]!]
        let htType ← mkAppM ``LE.le #[named `threshold,pt[37]!]
        withLocalDeclD `reachedPhysicalSize htType fun hr => do
          let all := b ++ #[hcap] ++ pars ++ pt[37:39].toArray ++ #[hr] ++ pt[39:].toArray
          if piece.getNat == 0 then
            let start := mkAppN (named `continuation) (#[pt[37]!,hr] ++ pt[39:43].toArray)
            let qsol ← mkAppM ``Classical.choose_spec #[start]
            let core ← mkAppM ``Classical.choose_spec #[qsol]
            let ret ← mkAppM (ns ++ `cacheSlots) #[cur `retarded]
            let norm := mkAppN core #[cur `W₁,ret,a `JanetCartan.PhysicalPairs.OriginalInverse.response_tame weak]
            let window := part (a (hp ++ `native_window) pt) 0
            let lc := part window 0
            let le := part window 1
            let fine := (← inferType le).appArg!
            let hlam := a (fq ++ `fine_le_lam) pt
            let lam := (← whnfR (← inferType hlam)).appArg!
            let rho := (← inferType (part window 2)).appArg!
            let specs := mkAppN norm #[fine,lam,rho,le,hlam,← mkAppM (ns ++ `strictly_positive) #[part window 2],a (fq ++ `rho_le_carrier) pt]
            let angles ← mkAppM (ns ++ `pairSlots) #[mkApp θ pt[46]!,mkApp θ pt[47]!]
            let amp ← mkAppM (ns ++ `pairSlots) #[a (rows ++ `leftAmplitude) ptZ,a (rows ++ `rightAmplitude) ptZ]
            let V := m `chart
            let hVB := m `chart_in_coefficient_ball
            let hV ← mkAppM (sel ++ `in_profile) #[stat `normRadius,hVB]
            let zero ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 0
            let one ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
            let fbase := mkAppN specs #[V,m `chart_open,hV,α,η,angles,amp,pt[45]!,zero,one,a (ns ++ `different) #[pt[45]!]]
            let hL ← mkAppM ``le_trans #[lc,le]
            let jets (f hf : Expr) := mkAppM (sup ++ `jet_bound) #[hVB,f,hf,hL]
            let left ← mkAppM (fm ++ `left_bound) #[pars[3]!]
            let right ← mkAppM (fm ++ `right_bound) #[pars[3]!]
            let proof := mkAppN fbase #[a (sup ++ `smooth) fix,a (fm ++ `support_refl) #[d,α],a (sup ++ `support_chart) fix,a (ns ++ `unit_on) #[n,V],
              a (fq ++ `angle_smooth) pt,a (rows ++ `left_smooth) ptZ,a (rows ++ `right_smooth) ptZ,a (fq ++ `angle_jets) pt,
              ← jets α (a (sup ++ `smooth) fix),← jets η (a (ns ++ `unit_smooth) #[n]),mkApp left t,mkApp right t]
            discard <| store (ns ++ `localized_response) all proof
            return
          let priced := a (ns ++ `localized_response) all
          let hf ← mkAppM ``Classical.choose #[priced]
          let start ← mkAppM ``Classical.choose_spec #[priced]
          let v ← mkAppM ``Subtype.val #[a (dataNS ++ `uncut) ptZ]
          let hχball ← mkAppM ``Set.Subset.trans #[m `χ₂_support_chart,m `chart_in_coefficient_ball]
          let exactInput ← mkAppM (ns ++ `measured_extended) #[χ₂,fix[4]!,F,fix[5]!,fix[6]!,hχball,H,oldη,α,a (sup ++ `same_input) fix,v,a (sup ++ `original_input_ae) ptZ]
          let same := mkApp exactInput hf
          if piece.getNat == 1 then
            discard <| store (ns ++ `same_measurement) all same
            return
          let same := a (ns ++ `same_measurement) all
          let ae := a (dataNS ++ `solver_representation) ptZ
          let old := a (dataNS ++ `measured) ptZ
          let pred ← withLocalDeclD `originalMeasured (← inferType old) fun u => do mkLambdaFVars #[u] ((← inferType ae).replace fun e => if e == old then some u else none)
          let trans ← mkAppM ``congrArg #[pred,← mkAppM ``Eq.symm #[same]]
          let hsol ← mkAppM ``Eq.mp #[trans,ae]
          let solver := a (pkt ++ `solved) ptZ
          let field := a (pkt ++ `packet) ptZ
          let form := a (pkt ++ `formula) ptZ
          let ψ := (← inferType (m `χ₃_smooth)).appArg!
          let eq ← withLocalDeclD `x (a `JanetCartan.Euclidean #[n]) fun x => do
            let atX ← mkAppM ``congrFun #[form,x]
            let some cv := (← inferType atX).find? (fun e => e.isAppOfArity `JanetCartan.AmbientResponse.completedVariation 6) | throwError "missing actual physical completion"
            let physicalF := cv.getAppArgs[2]!
            let more := a (sup ++ `same_field) #[n,N,ψ,oldη,α,a (sup ++ `same_output) fix,physicalF,solver,H,x]
            mkLambdaFVars #[x] (← mkAppM ``Eq.trans #[atX,more])
          let result := mkAppN start #[solver,a (pkt ++ `solved_smooth) ptZ,hsol,field,eq]
          discard <| store (ns ++ `size) all result
prove_original_signed_packet_size 0
prove_original_signed_packet_size 1
prove_original_signed_packet_size 2
end JanetCartan.PhysicalPairs.OriginalPacketSize
end
