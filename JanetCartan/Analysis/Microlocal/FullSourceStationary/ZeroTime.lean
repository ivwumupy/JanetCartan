module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.StationaryBranch.ZeroTime

/-!
# Initial stationary geometry for the original full source

The zero-time identities concern integration-variable derivatives with the
full source parameter fixed. They therefore follow from the existing exact
conic identities applied to that literal slice, without identifying any
independent source parameters. The inverse bound uses the full joint second
phase jet. Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.FullSourceStationary
open CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic ConicPhase EvolutionIntegral
open ResponseTransfer.DirectEvolution ResponseTransfer.RetainedFactors
open EvolutionIntegral.KernelIdentification

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)

/-- Joint full-source gradient smoothness, preserving the independent
covector parameter (`app:ch_response:eq:response-exact-phase`). -/
theorem contDiffOn_full_source_gradient
    {φ : E → Param → ℝ} {Ω : Set (E × Param)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω) :
    ContDiffOn ℝ ∞ (fun q : E × Param ↦ gradient (fun y ↦ φ y q.2) q.1) Ω := by
  intro q hq
  have hf : ContDiffAt ℝ ∞ (fun v : (E × Param) × E ↦ φ v.2 v.1.2) (q, q.1) :=
    (hφ.contDiffAt (hΩ.mem_nhds hq)).comp (q, q.1)
      (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  have hd : ContDiffAt ℝ ∞
      (fun p : E × Param ↦ fderiv ℝ (fun y ↦ φ y p.2) p.1) q :=
    hf.fderiv contDiffAt_fst (by simp)
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
    q hd).contDiffWithinAt

/-- Both literal full-source orientations are stationary at the original
source diagonal at zero elapsed time. Only the retained chart's actual initial
condition is used (`app:ch_response:eq:response-exact-phase`). -/
theorem full_source_conic_zeroTime_stationary
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph TC TC}
    (hC : (C : TC → TC) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    (φ : E → Param → ℝ) (q : E × Param)
    (hφ : DifferentiableAt ℝ (fun y ↦ φ y q.2) q.1)
    (hgraph : elapsedChartPoint 0 q.1 (gradient (fun y ↦ φ y q.2) q.1) ∈
      domain ℓ C.target) :
    gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase ℓ C) φ ((0, q), w))
      (WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)) = 0 := by
  exact retained_conic_zeroTime_stationary adj ℓ hC hsource hi
    (fun y _ ↦ φ y q.2) (q.1, 0) hφ hgraph

/-- The full-source zero-time Hessian is the same explicit invertible block
on the original normalized conic domain. The slice retains the given full
source parameter exactly (`app:ch_response:eq:direct-envelope-profile`). -/
theorem full_source_conic_zeroTime_hessian
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph TC TC}
    (hC : (C : TC → TC) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    {φ : E → Param → ℝ} {Ω : Set (E × Param)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    (q : E × Param) {w : W} (hw : (w.fst, q.2) ∈ Ω)
    (hout : fullSourceGraphPoint false ((0, q), w) ∈ domain ℓ C.target)
    (hsrc : fullSourceGraphPoint true ((0, q), w) ∈ domain ℓ C.target) :
    fderiv ℝ (gradient (fun v ↦
      fullSourceJointPhase adj (curriedPhase ℓ C) φ ((0, q), v))) w =
      (retainedDiagonalHessianEquiv
        (fderiv ℝ (gradient (fun y ↦ φ y q.2)) w.fst)).toContinuousLinearMap := by
  let F : E × Euclidean 3 → E × Param := fun p ↦ (p.1, q.2)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk contDiff_const
  exact retained_conic_zeroTime_hessian_orientation adj ℓ hC hsource hi
    (φ := fun y _ ↦ φ y q.2) (hΩ.preimage hF.continuous)
    (hφ.comp hF.contDiffOn (fun _ hp ↦ hp)) (q.1, 0) hw hout hsrc

/-- The physical Hessian costs only the second joint full-source jet, with
constant one and the original norms (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_full_source_spatialHessian_le_joint
    {φ : E → Param → ℝ} {Ω : Set (E × Param)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {q : E × Param} (hq : q ∈ Ω) :
    ‖fderiv ℝ (gradient (fun y ↦ φ y q.2)) q.1‖ ≤
      ‖iteratedFDeriv ℝ 2 (Function.uncurry φ) q‖ := by
  have hn := (InnerProductSpace.toDual ℝ E).symm.norm_iteratedFDeriv_comp_left
    (fderiv ℝ (fun y ↦ φ y q.2)) q.1 1
  have he : ‖fderiv ℝ (gradient (fun y ↦ φ y q.2)) q.1‖ =
      ‖iteratedFDeriv ℝ 2 (fun y ↦ φ y q.2) q.1‖ := by
    calc
      _ = ‖iteratedFDeriv ℝ 1 ((InnerProductSpace.toDual ℝ E).symm ∘
          fderiv ℝ (fun y ↦ φ y q.2)) q.1‖ := by rw [norm_iteratedFDeriv_one]; rfl
      _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fun y ↦ φ y q.2)) q.1‖ := hn
      _ = _ := norm_iteratedFDeriv_fderiv
  rw [he]
  let L : E →L[ℝ] E × Param := (ContinuousLinearMap.id ℝ E).prod 0
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun y ↦ by simp [L, Prod.norm_def])
  have hb := SymbolBudgets.norm_iteratedFDeriv_preAffine_le L (0, q.2) hΩ hφ
    (x := q.1) (by simpa [L] using hq) 2
  have hp := pow_le_one₀ (norm_nonneg L) hL (n := 2)
  exact (by simpa [L, Function.uncurry] using
    hb.trans (mul_le_of_le_one_right (norm_nonneg _) hp))

/-- An explicit inverse bound for either literal full-source zero-time
Hessian from the primitive joint second-jet bound. The actual history phase
profiles produce this budget (`app:ch_response:eq:direct-envelope-profile`). -/
theorem full_source_conic_zeroTime_stationary_inverse_bound
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph TC TC}
    (hC : (C : TC → TC) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    {φ : E → Param → ℝ} {Ω : Set (E × Param)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) Ω)
    {q : E × Param} (hq : q ∈ Ω) {B : ℝ}
    (hB : ‖iteratedFDeriv ℝ 2 (Function.uncurry φ) q‖ ≤ B)
    (hgraph : elapsedChartPoint 0 q.1 (gradient (fun y ↦ φ y q.2) q.1) ∈
      domain ℓ C.target) :
    let w : W := WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)
    let H := fderiv ℝ (gradient (fun v ↦
      fullSourceJointPhase adj (curriedPhase ℓ C) φ ((0, q), v))) w
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    IsUnit H ∧ ‖Ring.inverse H‖ ≤
      ‖e.symm.toContinuousLinearMap‖ * (1 + B) * ‖e.toContinuousLinearMap‖ := by
  dsimp only
  rw [full_source_conic_zeroTime_hessian adj ℓ hC hsource hi hΩ hφ q
    (w := WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)) hq hgraph
    (by simpa [fullSourceGraphPoint, elapsedChartPoint] using hgraph)]
  refine ⟨(retainedDiagonalHessianEquiv _).toUnit.isUnit,
    (norm_inverse_retainedDiagonalHessian_le _).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ((norm_full_source_spatialHessian_le_joint hΩ hφ hq).trans hB))
        (norm_nonneg _)) (norm_nonneg _)

end JanetCartan.FullSourceStationary
