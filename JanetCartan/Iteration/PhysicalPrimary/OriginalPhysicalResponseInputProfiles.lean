module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalReducedProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullStrainProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalCoefficients
public import JanetCartan.Iteration.PhysicalPrimary.OriginalComparisonResponse

/-! # Same-history physical reconstruction inputs
The uniform complete-inverse profile, original uncontracted tensor and all
five reconstruction coefficients are combined before histories. The only
new dynamic inequality reaches their fixed numerical maximum. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfiles
open CanonicalAtomRealization OriginalPhysicalCoefficients

theorem coefficient_order {r n rs h : ℕ} (hr : r+n+1 = rs) (hs : 16+rs ≤ h) : r+1+3 ≤ h := by omega

theorem reserve_le_source {r n rs : ℕ} (hr : r+n+1 = rs) : r ≤ rs := by omega

theorem region_geometry {n d : ℕ} {O : Set (Euclidean n × (Euclidean 3 × Euclidean d))}
    {X : Set (Euclidean n)} {V : Set (Euclidean 3 × Euclidean d)} {b : ℝ}
    (hO : IsOpen O) (hV : IsOpen V) (hX : X ⊆ closedBall 0 b) :
    let Ω := O ∩ (interior X ×ˢ V)
    IsOpen Ω ∧ Ω ⊆ X ×ˢ V ∧ Ω ⊆ O ∧ Ω ⊆ univ ×ˢ V ∧ Ω ⊆ closedBall 0 b ×ˢ univ := by
  exact ⟨hO.inter (isOpen_interior.prod hV),fun _ h ↦ ⟨interior_subset h.2.1,h.2.2⟩,
    inter_subset_left,fun _ h ↦ ⟨mem_univ _,h.2.2⟩,fun _ h ↦ ⟨hX (interior_subset h.2.1),mem_univ _⟩⟩

theorem protected_source_in_coefficient_ball {n : ℕ} (hn : 5 ≤ n)
    (a : PhysicalInitialization.OriginalPatchIndex hn) :
    PhysicalInitialization.OriginalProtected.Xsrc hn a ⊆ closedBall 0 (PhysicalSeed.OriginalBoundary.b hn) :=
  closedBall_subset_closedBall (PhysicalInitialization.OriginalProtected.sourceRadius_lt_b hn).le

/-- Lift the actual common coefficient profile to the admitted physical scale;
only the existing L≤K scale inequality is used. -/
theorem coefficient_on_region {n d : ℕ} {Ω J : Set (Euclidean n × (Euclidean 3 × Euclidean d))}
    (hΩJ : Ω ⊆ J) {f : Euclidean n × (Euclidean 3 × Euclidean d) → ℂ}
    {A C : ℕ → ℝ} {L K : ℝ} {reserve : ℕ}
    (h : ContDiffOn ℝ ∞ f J ∧ ∀ j q, q ∈ J → ‖iteratedFDeriv ℝ j f q‖ ≤ A j*L^(j-reserve))
    (hL : 1 ≤ L) (hLK : L ≤ K) (hA : ∀ j, 0 ≤ A j) (hAC : ∀ j, A j ≤ C j) :
    ContDiffOn ℝ ∞ f Ω ∧ ∀ j q, q ∈ Ω → ‖iteratedFDeriv ℝ j f q‖ ≤ C j*K^(j-reserve) :=
  ⟨h.1.mono hΩJ,fun j q hq ↦ upgrade_coefficient_grade hL hLK (hA j) (hAC j) (h.2 j q (hΩJ hq))⟩

theorem global_coefficient_on_region {n d : ℕ} (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d)))
    {f : Euclidean n × (Euclidean 3 × Euclidean d) → ℂ} {A C : ℕ → ℝ} {L K : ℝ} {reserve : ℕ}
    (hs : ContDiff ℝ ∞ f) (hb : ∀ j q, ‖iteratedFDeriv ℝ j f q‖ ≤ A j*L^(j-reserve))
    (hL : 1 ≤ L) (hLK : L ≤ K) (hA : ∀ j, 0 ≤ A j) (hAC : ∀ j, A j ≤ C j) :
    ContDiffOn ℝ ∞ f Ω ∧ ∀ j q, q ∈ Ω → ‖iteratedFDeriv ℝ j f q‖ ≤ C j*K^(j-reserve) :=
  ⟨hs.contDiffOn,fun j q _ ↦ upgrade_coefficient_grade hL hLK (hA j) (hAC j) (hb j q)⟩

theorem enlarge_amplitude_grade {A B τ size K z : ℝ} {j reserve rSource : ℕ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hτ : 0 < τ) (hs : 0 ≤ size) (hK : 1 ≤ K)
    (hr : reserve ≤ rSource) (hz : z ≤ A*(τ^3*size)*K^(j-rSource)) :
    z ≤ B*(τ^3*size)*K^(j-reserve) := by
  apply hz.trans
  have hbudget : 0 ≤ τ^3*size := mul_nonneg (pow_nonneg hτ.le _) hs
  exact mul_le_mul (mul_le_mul_of_nonneg_right hAB hbudget)
    (pow_le_pow_right₀ hK (Nat.sub_le_sub_left hr j)) (pow_nonneg (zero_le_one.trans hK) _)
    (mul_nonneg (hA.trans hAB) hbudget)

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfiles
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfilesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate
open OriginalPhysicalReducedProfilesTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfiles
private def red := `JanetCartan.PhysicalPrimary.OriginalPhysicalReducedProfiles
private def inv := `JanetCartan.PhysicalPrimary.OriginalInverseEnvelopes
private def cf := `JanetCartan.PhysicalPrimary.OriginalPhysicalCoefficients
private def strain := `JanetCartan.PhysicalPrimary.OriginalFullStrainProfiles
private def phase := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
private def ind := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def family := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def cmp := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def app (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ k) xs v data t
  logInfo m!"actual reconstruction input: checked {k}"
  addDocStringCore (ns ++ k) "Actual same-history uncontracted strain, full reduced solution and reconstruction coefficient profiles; costs fixed before histories and the sole extra premise reaches their numerical maximum (app:ch_response:eq:response-reconstruction-grading)."
  return h
private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | k+1 => part (.proj ``And 1 e) k
private def unary (T : Expr) (f : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `j T fun j => do mkLambdaFVars #[j] (← f j)

elab "join_actual_reconstruction_inputs" : command => liftTermElabM do
  withNativePhysicalInputs fun xs p old s _pt => do
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let nNat := mkConst ``Nat
    let oldBase := old[:44].toArray
    let member := app (ind ++ `point) old
    let nativePhase ← bodyAt (family ++ `Point.φ) (oldBase.push member)
    unless nativePhase.isAppOfArity (phase ++ `φ) 39 do throwError "native response inputs: phase39 lost"
    let ph := nativePhase.getAppArgs[:33].toArray
    let va := (← bodyAt (geo ++ `parameter_window) s).getAppArgs
    let cn := #[n,s[1]!,va[23]!,va[24]!]
    let ws := app (cmp ++ `parameterComparisonWindow_spec) cn
    let V := app (cmp ++ `parameterComparisonWindow) cn
    let X := app `JanetCartan.PhysicalInitialization.OriginalProtected.Xsrc #[n,s[1]!,ph[32]!]
    let hO := app (geo ++ `current_open) s
    let hX := app (ns ++ `protected_source_in_coefficient_ball) #[n,s[1]!,ph[32]!]
    let region ← mkAppM (ns ++ `region_geometry) #[hO,.proj ``And 0 ws,hX]
    let Ω := (← inferType (.proj ``And 0 region)).appArg!
    let Ω ← emit `region xs Ω true
    let region ← emit `region_geometry_actual xs region
    withLocalDeclD `reserve nNat fun res => do
      let rs := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) res n) (mkNatLit 1)
      withLocalDeclD `hSourceReserve (← mkEq rs s[37]!) fun hr => do
        let hrC := app (ns ++ `coefficient_order) #[res,n,s[37]!,s[28]!,hr,s[38]!]
        let cp := ph ++ #[res,hrC]
        let fixed := p ++ #[res,hr]
        let a := app (inv ++ `S) p
        let b := app (strain ++ `S) s[:39].toArray
        let c := app (cf ++ `S) cp
        let bc ← mkAppM ``Max.max #[b,c]
        let S ← emit `S fixed (← mkAppM ``Max.max #[a,bc]) true
        let ha ← emit `inverse_threshold fixed (← mkAppM `le_max_left #[a,bc])
        let habc ← mkAppM `le_max_right #[a,bc]
        let hb ← emit `strain_threshold fixed (← mkAppM `le_trans #[← mkAppM `le_max_left #[b,c],habc])
        let hc ← emit `coefficient_threshold fixed (← mkAppM `le_trans #[← mkAppM `le_max_right #[b,c],habc])
        discard <| emit `S_ge_two fixed (← mkAppM `le_trans #[app (inv ++ `hS) p,ha])
        let C ← emit `C fixed (app (cf ++ `C) cp) true
        let hC ← emit `C_nonneg fixed (app (cf ++ `C_nonneg) cp)
        let G := app (red ++ `C) p
        let A := app (strain ++ `C) s[:39].toArray
        let Bval ← unary nNat fun r => mkAppM ``Max.max #[mkApp G r,mkApp A r]
        let B ← emit `B fixed Bval true
        let hG := app `JanetCartan.CanonicalAtomRealization.reducedProfileClassicalBudget_nonneg
          #[n,s[0]!,n,app (red ++ `FourierCost) p,app (red ++ `FourierCost_nonneg) p]
        let hBG ← emit `reduced_cost_le fixed (← unary nNat fun r => mkAppM `le_max_left #[mkApp G r,mkApp A r])
        let hBA ← emit `strain_cost_le fixed (← unary nNat fun r => mkAppM `le_max_right #[mkApp G r,mkApp A r])
        discard <| emit `B_nonneg fixed (← unary nNat fun r => mkAppM `le_trans #[mkApp hG r,mkApp hBG r])
        withLocalDeclD `hResponseReached (← mkAppM ``LE.le #[S,s[39]!]) fun hR => do
          let all := xs ++ #[res,hr,hR]
          let hCoeff ← mkAppM `le_trans #[hc,hR]
          let hStrain ← mkAppM `le_trans #[hb,hR]
          let cargs := cp ++ #[s[39]!,hCoeff] ++ s[41:45].toArray
          let L := app `JanetCartan.currentCoefficientScale #[s[39]!,s[41]!]
          let hL ← mkAppM `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
            #[← mkAppM `le_trans #[app (cf ++ `hS) cp,hCoeff],s[41]!]
          let hK := app (family ++ `Point.hK) (oldBase.push member)
          let hAK := app (strain ++ `C_nonneg) s[:39].toArray
          let rawStrain := app (strain ++ `envelope) s
          let st := app (strain ++ `profiles) (s.push hStrain)
          let biggerV := app (geo ++ `parameter_window) s
          let hVbig := app (geo ++ `parameter_window_open) s
          let entries := app `JanetCartan.PhysicalPrimary.OriginalReducedReserve.strain_coordinate_entries
            #[n,s[0]!,biggerV,hVbig,rawStrain,.proj ``And 0 st,A,s[47]!,s[50]!,s[45]!,s[37]!,.proj ``And 1 st]
          discard <| emit `strain_entries all entries
          discard <| emit `reduced_jets all (app (red ++ `joint_jets) (xs ++ #[res,hr]))
          let hJ : Expr := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 (.proj ``And 1 region)))
          let hχ := app (mask ++ `χ₂_smooth) s[:23].toArray
          let χ := (← inferType hχ).appArg!
          let bb := app `JanetCartan.PhysicalSeed.OriginalBoundary.b #[n,s[1]!]
          let hcχ := app (cf ++ `cutoffCost_nonneg) #[n,χ,bb]
          let cut ← mkAppM (ns ++ `coefficient_on_region)
            #[hJ,app (cf ++ `cutoff_entries) cargs,hL,s[46]!,hcχ,app (cf ++ `cutoff_cost_le) cp]
          discard <| emit `cutoff_profile all cut
          let gradient := app (cf ++ `gradient_entries) cargs
          let H := app (cf ++ `phase_cost) cp
          let hH := app (cf ++ `phase_cost_nonneg) cp
          let hHA ← unary nNat fun r => pure <| mkApp hH (mkApp2 (mkConst ``Nat.add) r (mkNatLit 1))
          let grad ← forallBoundedTelescope (← inferType (.proj ``And 0 gradient)) (some 1) fun ii _ => do
            let h ← mkAppM (ns ++ `global_coefficient_on_region)
              #[Ω,mkAppN (.proj ``And 0 gradient) ii,mkAppN (.proj ``And 1 gradient) ii,hL,s[46]!,hHA,
                app (cf ++ `gradient_cost_le) cp]
            mkLambdaFVars ii h
          discard <| emit `gradient_profiles all grad
          for k in [`value_entries,`derivative_entries,`source_entries] do
            let h := app (cf ++ k) cargs
            let result ← forallBoundedTelescope (← inferType h) (some 2) fun ii _ => do
              let hrRec := app (cf ++ `reconstruction_floor) #[res,ph[27]!,hrC]
              let nn := app `JanetCartan.PhysicalPrimary.OriginalReconstructionProfiles.C_nonneg (ph[:32].toArray ++ #[res,hrRec])
              let h ← mkAppM (ns ++ `coefficient_on_region)
                #[hJ,mkAppN h ii,hL,s[46]!,nn,app (cf ++ `reconstruction_cost_le) cp]
              mkLambdaFVars ii h
            discard <| emit k all result
          let _ := C
          let _ := hC
          let _ := B
          let _ := hBA
          let _ := hK
          let _ := hAK
          let _ := L
          let _ := V
          let _ := X
          let _ := H
  logInfo "actual common physical reconstruction threshold and coefficient profiles; full matrix strain and same complete-inverse classical jets retained with the original scalar size"

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfilesTemplate
end
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
join_actual_reconstruction_inputs
