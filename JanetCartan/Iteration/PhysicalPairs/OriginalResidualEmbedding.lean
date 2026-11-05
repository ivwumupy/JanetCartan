module
public import JanetCartan.Iteration.PhysicalPairs.OriginalPacketPDE
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.ResidualSobolevTransfer
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CoefficientNorms

/-! # Identification of the corrected observation with the true signed smooth error

Use compact support only in the original coefficient chart, never in the
smaller measurement ball. The local angular representative and the two global
smooth fields then agree almost everywhere on that inner ball. The Sobolev
embedding cost precedes all samples. `app:ch_pairs:eq:pairs-lag-one-error`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory Filter
open scoped ContDiff NNReal ENNReal Matrix.Norms.Frobenius JanetCartan.TensorFrobenius SchwartzMap
namespace JanetCartan.PhysicalPairs.OriginalResidualEmbedding
open AmbientResponse CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension LocalSobolev SmallSupport ArbitraryAccuracy
variable {n N : ℕ} {I : Type}
local notation "E" => Euclidean n

theorem actual_forcing_smooth (Z : I → SchwartzMap E (EuclideanSpace ℂ (Fin N)))
    (θ : I → E → ℝ) (minus : Bool) (i j : I) {U : Set E} {η : E → ℝ} (hU : IsOpen U)
    (Q : E → Fin n → MetricTensor n) (hQ : ∀ k, ContDiffOn ℝ ∞ (fun x ↦ Q x k) U)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ContDiff ℝ ∞ (fun y ↦ (WithLp.toLp 2 (stressSource Q (OriginalSignedPackets.originalTensor Z θ minus i j η) y) : E)) := by
  unfold OriginalSignedPackets.originalTensor
  have hg := contDiff_euclideanCutoffStressSource Q (fun _ ↦ 1) hU hQ contDiff_const hηU
    ⟨_,SampledInput.tensor_admitted Z θ minus i j hη hc⟩
  simpa only [euclideanCutoffStressSource,cutoffSource,LinearMap.coe_mk,AddHom.coe_mk,one_smul] using hg

theorem smooth_difference_observation (V : Set E) (f : E → E) (a z : Lp E 2 (volume : Measure E))
    (u : LocalL2 V E) (hf : f =ᵐ[volume.restrict V] (a : E → E) - (z : E → E))
    (hu : ((Lp.memLp (a-z)).restrict V).toLp (a-z) = u) : f =ᵐ[volume.restrict V] u := by
  rw [← hu]
  have hsub : (fun x ↦ (a-z) x) =ᵐ[volume.restrict V] (a : E → E) - (z : E → E) := ae_restrict_of_ae (Lp.coeFn_sub a z)
  exact hf.trans (hsub.symm.trans (MemLp.coeFn_toLp _).symm)

theorem on_inner_ball {ι : Type*} (c : E) (r : ℝ) (hr : 0 < r) (ρ : ι → ℝ) (f : ι → E → E)
    (u : ι → LocalL2 (ball c r) E) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (he : ∀ t, f t =ᵐ[volume.restrict (ball c r)] u t) (s : ℕ)
    (h : RapidDecayAt (restrictionSobolevScale (ball c r) E isOpen_ball.measurableSet) (s+n+1) ρ (fun _ ↦ 1) u)
    (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, cNorm (closedBall c (r/2)) s (f t) ≤ C*(ρ t)^(-q) := by
  obtain ⟨D,hD,embed⟩ := RegularSector.FiniteAssembly.CoefficientNorms.exists_cNorm_le_restrictionSobolevNorm (F := E) n s
  obtain ⟨B,hB,est⟩ := h q
  refine ⟨D*B,mul_nonneg (zero_le_one.trans hD) hB,?_⟩
  intro t
  have hmem : MemRestrictionSobolev (ball c r) (s+n+1) (u t) := (est t).1
  have hnorm := (est t).2
  rw [restrictionSobolevScale_gradeNorm isOpen_ball.measurableSet hmem,mul_one] at hnorm
  exact (embed c (r/2) r (half_pos hr) (half_lt_self hr) (f t) (hf t).contDiffOn (u t) (he t) hmem).trans
    ((mul_le_mul_of_nonneg_left hnorm (zero_le_one.trans hD)).trans_eq (mul_assoc _ _ _).symm)
end JanetCartan.PhysicalPairs.OriginalResidualEmbedding
end
public meta section
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalResidualEmbedding
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalResidualEmbedding
private def sd := `JanetCartan.PhysicalPairs.OriginalSignedData
private def pkt := `JanetCartan.PhysicalPairs.OriginalSignedPackets
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def lp (e : Expr) : MetaM Expr := do
  unless e.isAppOfArity `MeasureTheory.AEEqFun.cast 6 && e.appArg!.isAppOfArity ``Subtype.val 3 do throwError "no original Lp class in discrepancy"
  return e.appArg!.appArg!
elab "identify_original_signed_angular_error " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (sd ++ `measured)).type (some 50) fun p _ => do
    let actual := a (sd ++ `uncut) p
    let raw := ((← getConstInfo (sd ++ `uncut)).value! (allowOpaque := true)).beta p
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let info := a `JanetCartan.PhysicalPairs.OriginalPacketEquation.right_discrepancy p
    let ty := (← inferType info).getAppArgs
    let err := ty[3]!
    if piece.getNat == 0 then
      discard <| store (ns ++ `error) p err true
      return
    let named := a (ns ++ `error) p
    if piece.getNat == 1 then
      let xs := raw.getAppArgs
      let args := xs[:9].toArray ++ xs[10:].toArray
      let sm := a (ns ++ `actual_forcing_smooth) args
      let some solver := (← inferType (a (sd ++ `solver_representation) p)).find? (fun e => e.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalRegular.Current.smoothSolver 38)
        | throwError "missing original solver"
      let sr := Expr.proj ``And 0 (mkApp (a `JanetCartan.PhysicalInitialization.OriginalRegular.Current.fact21 solver.getAppArgs) actual)
      let pf ← mkAppM `ContDiff.sub #[sr,sm]
      let t := ← inferType pf
      discard <| store (ns ++ `error_smooth) p pf false (some (mkApp t.appFn! named))
      return
    let ab := ty.back!.getAppArgs
    let source ← lp ab[ab.size-2]!
    let z ← lp ab.back!
    let some ext := z.find? (fun e => e.isAppOf `JanetCartan.SmallSupport.zeroExtend) | throwError "angular defect lost original global corrected class: {z.getAppFn}"
    let some A := source.find? (fun e => e.isAppOf `JanetCartan.RegularSector.NormalizedSolver.realSource || e.getAppFn.constName?.any (·.getString! == "realSource"))
      | throwError "not a normalized actual paired source"
    let some V := ty[2]!.find? (fun e => e.isAppOf `Metric.ball) | throwError "missing original observation ball"
    let sa := A.getAppArgs
    let rel ← mkAppM `JanetCartan.UniformStep.normalizedSourceDiscrepancy_restriction_eq (sa[(sa.size-6):].toArray ++ #[ext.appArg!,V,z.appArg!])
    let et ← whnfR (← inferType rel)
    unless et.isAppOfArity ``Eq 3 do throwError "native restriction is not a proved Lp equality"
    let obs := et.appArg!
    let pf := a (ns ++ `smooth_difference_observation) #[n,V,named,source,z,obs,info,rel]
    discard <| store (ns ++ `actual_observation_ae) p pf
identify_original_signed_angular_error 0
identify_original_signed_angular_error 1
identify_original_signed_angular_error 2
end JanetCartan.PhysicalPairs.OriginalResidualEmbedding
end
