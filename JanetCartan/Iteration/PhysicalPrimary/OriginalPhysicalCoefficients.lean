module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalReconstructionPhase
public import JanetCartan.Iteration.PhysicalPrimary.OriginalReconstructionProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalParameterRemainders
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate

/-! # All original uncut reconstruction coefficients on one history
Reserve an extra derivative for the physical phase gradient and join its
literal native current to the physical finite map's three reconstruction
multipliers. No coefficient bound or phase agreement is an input. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalCoefficients
open CurrentCoefficientProfiles

theorem reconstruction_floor {j h : ℕ} (hh : j+1+3 ≤ h) : 2+j ≤ h := by omega

/-- The original tensor-source mask has a fixed grade, independent of every
history and of the physical-scale window. -/
theorem cutoff_entry {n : ℕ} (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (b : ℝ)
    {K : ℝ} (hK : 1 ≤ K) (reserve : ℕ) :
    let f := fun q : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦ (χ q.1 : ℂ)
    ContDiffOn ℝ ∞ f (closedBall 0 b ×ˢ univ) ∧
      ∀ j q, q ∈ closedBall 0 b ×ˢ univ → ‖iteratedFDeriv ℝ j f q‖ ≤
        cNorm (closedBall 0 b) j (fun x ↦ (χ x : ℂ)) * K^(j-reserve) := by
  intro f
  exact OriginalReconstructionJoint.spatial_reconstruction_joint_profile_with_reserve
    (fun _ _ ↦ (Complex.ofRealCLM.contDiff.comp hχ).contDiffAt)
    (fun j ↦ le_mul_of_one_le_right (cNorm_nonneg _ _ _) (one_le_pow₀ hK))

def cutoffCost {n : ℕ} (χ : Euclidean n → ℝ) (b : ℝ) (j : ℕ) : ℝ :=
  cNorm (closedBall 0 b) j (fun x ↦ (χ x : ℂ))

theorem cutoffCost_nonneg {n : ℕ} (χ : Euclidean n → ℝ) (b : ℝ) (j : ℕ) :
    0 ≤ cutoffCost χ b j := cNorm_nonneg _ _ _

def combinedCost (χ H D : ℕ → ℝ) (j : ℕ) : ℝ := max (χ j) (max (H (j+1)) (D j))

theorem combinedCost_spec (χ H D : ℕ → ℝ) (hχ : ∀ j, 0 ≤ χ j) (j : ℕ) :
    0 ≤ combinedCost χ H D j ∧ χ j ≤ combinedCost χ H D j ∧
      H (j+1) ≤ combinedCost χ H D j ∧ D j ≤ combinedCost χ H D j :=
  ⟨(hχ j).trans (le_max_left _ _),le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _),(le_max_right _ _).trans (le_max_right _ _)⟩

theorem upgrade_coefficient_grade {A B L K x : ℝ} {j reserve : ℕ}
    (hL : 1 ≤ L) (hLK : L ≤ K) (hA : 0 ≤ A) (hAB : A ≤ B)
    (hx : x ≤ A * L^(j-reserve)) : x ≤ B * K^(j-reserve) := by
  apply hx.trans
  exact mul_le_mul hAB (pow_le_pow_left₀ (zero_le_one.trans hL) hLK _)
    (pow_nonneg (zero_le_one.trans hL) _) (hA.trans hAB)

end JanetCartan.PhysicalPrimary.OriginalPhysicalCoefficients
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalCoefficientsTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalCoefficients
private def ob := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
private def rec := `JanetCartan.PhysicalPrimary.OriginalReconstructionProfiles
private def ph := `JanetCartan.PhysicalPrimary.OriginalReconstructionPhase
private def cur := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def appl (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let r ← store (ns ++ k) xs v data t
  addDocStringCore (ns ++ k) "Actual reserved physical coefficient on the original finite map and retained phase; all constants and thresholds fixed before histories (app:ch_response:eq:response-reconstruction-grading)."
  return r
private def add (a b : Expr) := mkApp2 (mkConst ``Nat.add) a b
private def proofAt (name : Name) (xs : Array Expr) : MetaM Expr := do
  let some v := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "native coefficient: unavailable original producer {name}"
  Core.betaReduce (v.beta xs)

elab "initialize_native_reconstruction_coefficients" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (ob ++ `S)).type (some 33) fun obs _ => do
    let old := (← proofAt (ob ++ `Native.exists_profiles) obs).getAppArgs
    unless old.size == 24 do throwError "native coefficient: original retained-phase initialization shape {old.size}"
    let base := obs[:32].toArray
    withLocalDeclD `reserve (mkConst ``Nat) fun j => do
      let gradR := add j (mkNatLit 1)
      withLocalDeclD `hreserve (← mkAppM ``LE.le #[add gradR (mkNatLit 3),base[27]!]) fun hh => do
        let fixed := obs ++ #[j,hh]
        let full := appl (ph ++ `exists_physical_retained_phase_reserved_profiles)
          (old[:21].toArray ++ #[gradR,old[21]!,old[22]!,hh,old[23]!])
        let h ← emit `phase_initialization fixed full
        let s ← emit `phase_threshold fixed (← mkAppM ``Classical.choose #[h]) true
        let spec ← mkAppM ``Classical.choose_spec #[h]
        let phaseInfo := Expr.proj ``And 1 spec
        let H ← emit `phase_cost fixed (← mkAppM ``Classical.choose #[phaseInfo]) true
        let p ← mkAppM ``Classical.choose_spec #[phaseInfo]
        discard <| emit `phase_cost_nonneg fixed (.proj ``And 0 p)
        let rest ← emit `phase_continuation fixed (.proj ``And 1 (.proj ``And 1 p))
        let hr := appl (ns ++ `reconstruction_floor) #[j,base[27]!,hh]
        let rp := base ++ #[j,hr]
        let χ := (← inferType (appl (mask ++ `χ₂_smooth) base[:23].toArray)).appArg!
        let n := mkApp (mkConst ``Nat.succ) base[0]!
        let b := appl `JanetCartan.PhysicalSeed.OriginalBoundary.b #[n,base[1]!]
        let χC := appl (ns ++ `cutoffCost) #[n,χ,b]
        let D := appl (rec ++ `C) rp
        let C ← emit `C fixed (appl (ns ++ `combinedCost) #[χC,H,D]) true
        let bounds := appl (ns ++ `combinedCost_spec) #[χC,H,D,appl (ns ++ `cutoffCost_nonneg) #[n,χ,b]]
        for (k,which) in [(`C_nonneg,0),(`cutoff_cost_le,1),(`gradient_cost_le,2),(`reconstruction_cost_le,3)] do
          let h ← forallBoundedTelescope (← inferType bounds) (some 1) fun rr _ => do
            let mut v := mkAppN bounds rr
            for _ in List.range which do v := .proj ``And 1 v
            if which != 3 then v := .proj ``And 0 v
            mkLambdaFVars rr v
          let target := (← inferType h).replace fun e =>
            if e == appl (ns ++ `combinedCost) #[χC,H,D] then some C else none
          discard <| emit k fixed h false (some target)
        let recS := appl (rec ++ `S) rp
        let obsS := appl (ob ++ `S) obs
        let recObsS ← mkAppM ``Max.max #[recS,obsS]
        let th ← emit `S fixed (← mkAppM ``Max.max #[s,recObsS]) true
        let ps ← emit `phase_threshold_le fixed (← mkAppM `le_max_left #[s,recObsS])
        let ro ← mkAppM `le_max_right #[s,recObsS]
        let rs ← emit `reconstruction_threshold_le fixed (← mkAppM `le_trans #[← mkAppM `le_max_left #[recS,obsS],ro])
        let os ← emit `observation_threshold_le fixed (← mkAppM `le_trans #[← mkAppM `le_max_right #[recS,obsS],ro])
        discard <| emit `hS fixed (← mkAppM `le_trans #[.proj ``And 0 spec,ps])
        withLocalDeclD `R₀ (mkConst `Real) fun R₀ => do
          withLocalDeclD `hR₀ (← mkAppM ``LE.le #[th,R₀]) fun hR => do
            let hObs ← mkAppM `le_trans #[os,hR]
            let hRec ← mkAppM `le_trans #[rs,hR]
            let hPhase ← mkAppM `le_trans #[ps,hR]
            let pre := obs ++ #[R₀,hObs]
            forallBoundedTelescope (← inferType (appl (ob ++ `φ) pre)) (some 4) fun hs _ => do
              let dyn := pre ++ hs
              let xs := fixed ++ #[R₀,hR] ++ hs
              let φ := appl (ob ++ `φ) dyn
              let he := appl (ob ++ `φ_eq_retained) dyn
              let he0 ← proofAt (ob ++ `φ_eq_retained) dyn
              let Q := he0.getAppArgs.back!
              unless Q.isAppOfArity (cur ++ `sourceFrame) 39 do throwError "native coefficient: original permitted frame lost"
              let hQ := appl (cur ++ `sourceFrame_val) Q.getAppArgs
              let result := mkAppN rest (#[R₀,hPhase] ++ hs ++ #[Q,hQ])
              let hj := Expr.proj ``And 1 (.proj ``And 1 result)
              let joint := (← inferType (Expr.proj ``And 0 result)).appArg!
              unless joint.isAppOf `Function.uncurry do throwError "native coefficient: lost parameter-first phase"
              let rawφ := joint.appArg!
              let he ← emit `phase_eq_native xs he false (some (← mkEq φ rawφ))
              let rawT ← inferType hj
              let pred ← withLocalDeclD `ψ (← inferType φ) fun ψ => do
                let t := rawT.replace fun e => if e == rawφ then some ψ else none
                unless t != rawT do throwError "native coefficient: phase jet does not retain literal phase"
                mkLambdaFVars #[ψ] t
              let actual ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[pred,he],hj]
              let actual ← emit `phase_jets xs actual
              let L := appl `JanetCartan.currentCoefficientScale #[R₀,hs[0]!]
              let grad := appl (ph ++ `parameter_phase_reserved_gradient)
                #[base[0]!,φ,H,L,j,appl (ob ++ `joint_smooth) dyn,actual]
              discard <| emit `gradient_entries xs grad
              for (k,t) in [(`value_entries,`joint_value_entries),(`derivative_entries,`joint_derivative_entries),
                  (`source_entries,`joint_source_entries)] do
                discard <| emit k xs (appl (rec ++ t) (rp ++ #[R₀,hRec] ++ hs))
              let hχ := appl (mask ++ `χ₂_smooth) base[:23].toArray
              let χ := (← inferType hχ).appArg!
              let n := mkApp (mkConst ``Nat.succ) base[0]!
              let b := appl `JanetCartan.PhysicalSeed.OriginalBoundary.b #[n,base[1]!]
              let hL ← mkAppM `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
                #[← mkAppM `le_trans #[appl (ns ++ `hS) fixed,hR],hs[0]!]
              discard <| emit `cutoff_entries xs (appl (ns ++ `cutoff_entry) #[n,χ,hχ,b,L,hL,j])
  logInfo "same native reserved phase-gradient and all three finite-map reconstruction coefficients plus chi2 jets at one reached prehistory threshold"

end JanetCartan.PhysicalPrimary.OriginalPhysicalCoefficientsTemplate
end

set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
initialize_native_reconstruction_coefficients
