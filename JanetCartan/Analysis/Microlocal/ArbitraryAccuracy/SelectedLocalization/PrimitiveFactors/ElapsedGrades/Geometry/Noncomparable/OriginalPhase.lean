module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.Domains
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.ChartControls.Homogeneity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.PhaseBudgets

/-!
# Covector geometry from the original retained phase

These lemmas supply the derivative-field estimates, covector comparison, and
supported germ transfer used by `exists_selected_elapsed_covector_comparison`.
The temporal estimate differentiates both original times. No elapsed bound or
localization estimate is assumed (`app:ch_regular:eq:high-phase` and
`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open RegularSector.Characteristic.UniformEvolution EvolutionLocalization FourierIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "P" => ℝ × ℝ × Euclidean d

/-- Convert the original spatial mixed matrix bound into the operator norm
needed by `phaseCovectorMap_comparison_of_original_phase`. The Euclidean
operator norm is bounded by the Frobenius norm without a dimensional loss
(`app:ch_regular:eq:high-phase`). -/
theorem selected_phaseMomentum_mixed_norm_le (Ψ : TwoTimePhase d) (r : ℝ)
    (x : E) (η : Euclidean d)
    (hd : DifferentiableAt ℝ (fun ζ ↦ phaseMomentum Ψ r ((x 0, spatialPart x), ζ)) η) :
    ‖fderiv ℝ (fun ζ ↦ phaseMomentum Ψ r ((x 0, spatialPart x), ζ)) η -
      ContinuousLinearMap.id ℝ (Euclidean d)‖ ≤
        ‖mixedPhaseMatrix (Ψ (x 0) (x 0-r)) (spatialPart x) η - 1‖ := by
  let F := fun ζ ↦ phaseMomentum Ψ r ((x 0, spatialPart x), ζ)
  let B := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let L := fderiv ℝ F η - ContinuousLinearMap.id ℝ (Euclidean d)
  let A := LinearMap.toMatrix B B L.toLinearMap
  have he : A = mixedPhaseMatrix (Ψ (x 0) (x 0-r)) (spatialPart x) η - 1 := by
    have hg (f : Euclidean d → ℝ) (v : Euclidean d) (i : Fin d) :
        gradient f v i = partialDeriv f v i := by
      rw [partialDeriv, ← inner_gradient_left, EuclideanSpace.inner_single_right]
      simp
    ext i j
    have hi : (fun ζ ↦ partialDeriv (fun y ↦ Ψ (x 0) (x 0-r) y ζ) (spatialPart x) i) =
        fun ζ ↦ F ζ i := funext fun ζ ↦ (hg _ _ _).symm
    have hproj := ((EuclideanSpace.proj i).hasFDerivAt.comp η hd.hasFDerivAt).fderiv
    simp only [EuclideanSpace.coe_proj, Function.comp_def] at hproj
    have hA : A i j = L (EuclideanSpace.single j 1) i := by
      simp [A, B, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
        OrthonormalBasis.coe_toBasis_repr_apply]
    rw [hA]
    change (fderiv ℝ F η) (EuclideanSpace.single j 1) i - _ =
      (fderiv ℝ _ η) (EuclideanSpace.single j 1) - _
    rw [hi, hproj]
    congr 1
    simp only [EuclideanSpace.single, Matrix.one_apply]
    split_ifs <;> simp_all
  rw [← he]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) ?_
  intro v
  have ha : A.toEuclideanLin = L.toLinearMap := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.toLin_toMatrix _ _ _
  have hv := congrArg (fun f : Euclidean d →ₗ[ℝ] Euclidean d ↦ f v) ha
  rw [Matrix.toLpLin_apply] at hv
  calc
    ‖L v‖ = ‖Matrix.replicateCol Unit (A.mulVec v.ofLp)‖ := by
      rw [Matrix.frobenius_norm_replicateCol, hv]
      rfl
    _ ≤ ‖A‖ * ‖Matrix.replicateCol Unit v.ofLp‖ := by
      rw [Matrix.replicateCol_mulVec]
      exact Matrix.frobenius_norm_mul _ _
    _ = ‖A‖ * ‖v‖ := by rw [Matrix.frobenius_norm_replicateCol]

/-- Bound the simultaneous-time derivative field by the original joint
mixed derivative. The direction is `(1,1,0)`, retaining both original times.
Consumer: `selected_original_phaseCovectorMap_comparison`
(`app:ch_regular:eq:high-phase`). -/
theorem selected_phaseShear_mixed_norm_le (Ψ : TwoTimePhase d) (r : ℝ) (x : E)
    {D : Set (Euclidean d)} (hD : IsOpen D) {η : Euclidean d} (hη : η ∈ D)
    (hΨ : ∀ ζ ∈ D, ContDiffAt ℝ ∞ (jointPhase Ψ)
      ((x 0, x 0-r, spatialPart x), ζ)) :
    ‖fderiv ℝ (fun ζ ↦ phaseShear Ψ r ((x 0, spatialPart x), ζ)) η‖ ≤
      ‖fderiv ℝ (fun ζ ↦ fderiv ℝ
        (fun p : P ↦ Ψ p.1 p.2.1 p.2.2 ζ) (x 0, x 0-r, spatialPart x)) η‖ := by
  let p : P := (x 0, x 0-r, spatialPart x)
  let v : P := (1, 1, 0)
  let G : Euclidean d → P →L[ℝ] ℝ := fun ζ ↦
    fderiv ℝ (fun p : P ↦ Ψ p.1 p.2.1 p.2.2 ζ) p
  have hG : DifferentiableAt ℝ G η := by
    have h := (hΨ η hη).comp (η, p)
      (f := fun v : Euclidean d × P ↦ (v.2, v.1))
      (contDiffAt_snd.prodMk contDiffAt_fst)
    exact (h.fderiv (m := ∞) contDiffAt_const (by simp)).differentiableAt (by simp)
  have he : (fun ζ ↦ phaseShear Ψ r ((x 0, spatialPart x), ζ)) =ᶠ[𝓝 η]
      (fun ζ ↦ G ζ v) := by
    filter_upwards [hD.mem_nhds hη] with ζ hζ
    have hs := ((hΨ ζ hζ).comp p (f := fun w : P ↦ (w, ζ))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    let L : (ℝ × Euclidean d) →L[ℝ] P :=
      (ContinuousLinearMap.fst ℝ ℝ (Euclidean d)).prod
        ((ContinuousLinearMap.fst ℝ ℝ (Euclidean d)).prod
          (ContinuousLinearMap.snd ℝ ℝ (Euclidean d)))
    have hp : HasFDerivAt (fun w : ℝ × Euclidean d ↦ (w.1, w.1-r, w.2))
        L (x 0, spatialPart x) :=
      hasFDerivAt_fst.prodMk ((hasFDerivAt_fst.sub_const r).prodMk hasFDerivAt_snd)
    have hh := (hs.hasFDerivAt.comp (x 0, spatialPart x) hp).fderiv
    change (fderiv ℝ (fun w : ℝ × Euclidean d ↦ Ψ w.1 (w.1-r) w.2 ζ)
      (x 0, spatialPart x)) (1, 0) = G ζ v
    simp only [Function.comp_def, jointPhase] at hh
    rw [hh]
    rfl
  have hd := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp η hG.hasFDerivAt
  change HasFDerivAt (fun ζ ↦ G ζ v) _ η at hd
  rw [he.fderiv_eq, hd.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (fderiv ℝ G η)) ?_
  intro ζ
  change ‖((fderiv ℝ G η) ζ) v‖ ≤ ‖fderiv ℝ G η‖ * ‖ζ‖
  calc
    _ ≤ ‖(fderiv ℝ G η) ζ‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖(fderiv ℝ G η) ζ‖ := by simp [v]
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

/-- Identify the output derivative with the literal full covector field.
Consumer: `hg` of `exists_completePhysicalResidual_restriction_bound`, after
supported germ transfer (`app:ch_regular:eq:chain-tail`). -/
theorem selected_fderiv_elapsedPhase_output (Ψ : TwoTimePhase d) (r : ℝ) (x ξ : E)
    (hs : DifferentiableAt ℝ (fun p ↦ elapsedSpatialPhase Ψ r p (spatialPart ξ))
      (x 0, spatialPart x)) :
    fderiv ℝ (fun u ↦ elapsedPhase Ψ r u ξ) x = innerSL ℝ (phaseCovectorMap Ψ r x ξ) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin (d+1)) ℝ).toBasis.ext
  intro i
  simp only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply]
  change partialDeriv (fun u ↦ elapsedPhase Ψ r u ξ) x i = _
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [elapsedPhase_output_zero Ψ r x ξ hs]
    simp [phaseCovectorMap, phaseFieldPoint, phaseShear,
      EuclideanSpace.inner_single_right]
  · rw [elapsedPhase_output_succ Ψ r x ξ j hs]
    simp only [innerSL_apply_apply, EuclideanSpace.inner_single_right,
      starRingEnd_apply, star_trivial, one_mul]
    change partialDeriv _ _ j = (gradient (fun y ↦ Ψ (x 0) (x 0-r) y (spatialPart ξ))
      (spatialPart x)) j
    rw [partialDeriv, ← inner_gradient_left, EuclideanSpace.inner_single_right]
    simp

/-- Uniform covector comparison on the full retained cone, from the same
chart's original smoothness, differential, mixed half-gap and phase cost.
The doubled retained radius supplies the angular margin required by the
mixed-jet budget. Only coefficient order three occurs. Consumer:
`exists_selected_elapsed_covector_comparison` (`app:ch_regular:eq:high-phase`). -/
theorem selected_original_phaseCovectorMap_comparison
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : RootState (Euclidean d)} {ε b : ℝ}
    (hε : 0 < ε) (hεb : 4 * ε ≤ b)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (Characteristic.TwoTimePoint (Euclidean d))
      (Characteristic.TwoTimePoint (Euclidean d))}
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hnear : ∀ q ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C q - 1‖ ≤ 1/2)
    (KQ : Set E) (Q : E → Fin (d+1) → MetricTensor (d+1))
    (phaseCost : ℕ → ℝ) (hcost : 0 ≤ phaseCost 2)
    (hphase : ∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
      phaseCost m * (1 + cNorm KQ (m+1) Q))
    {M : ℝ} (hM : 0 ≤ M) (hQ : cNorm KQ 3 Q ≤ M)
    {r : ℝ} (hr : r ∈ Icc 0 ε) {x ξ : E}
    (hx : x ∈ elapsedPhysicalBox z ε)
    (hξ : spatialPart ξ ∈ angularCone ℓ z.2.2 ε) :
    let B := retainedPhaseCost ℓ z (2*ε) (1/2) 2 phaseCost 2 * (1+M)
    (3+2*B)⁻¹ * ‖ξ‖ ≤ ‖phaseCovectorMap (curriedPhase ℓ C) r x ξ‖ ∧
      ‖phaseCovectorMap (curriedPhase ℓ C) r x ξ‖ ≤ (3+2*B) * ‖ξ‖ := by
  intro B
  have hεb' : 2 * ε ≤ b := by linarith
  have hcost' : 0 ≤ retainedPhaseCost ℓ z (2*ε) (1/2) 2 phaseCost 2 :=
    mul_nonneg (jetBoundConstant_pos _ _ _).le hcost
  have hB : 0 ≤ B := mul_nonneg hcost' (by positivity)
  have hprod := contDiffOn_retained_product ℓ hε hεb' hbuffer hs
  have hbase := elapsed_mem_bufferedBase hε hr hx
  have hjoint (η : Euclidean d) (hη : η ∈ angularCone ℓ z.2.2 ε) :
      ContDiffAt ℝ ∞ (jointPhase (curriedPhase ℓ C))
        ((x 0, x 0-r, spatialPart x), η) :=
    hprod.contDiffAt ((isOpen_ball.prod (isOpen_angularCone _ _ _)).mem_nhds ⟨hbase, hη⟩)
  have helapsed : ContDiffAt ℝ ∞ (Function.uncurry (elapsedSpatialPhase (curriedPhase ℓ C) r))
      (phaseFieldPoint x ξ) :=
    (hjoint _ hξ).comp (phaseFieldPoint x ξ)
      (f := fun a : (ℝ × Euclidean d) × Euclidean d ↦
        ((a.1.1, a.1.1-r, a.1.2), a.2))
      ((contDiffAt_fst.fst.prodMk ((contDiffAt_fst.fst.sub contDiffAt_const).prodMk
        contDiffAt_fst.snd)).prodMk contDiffAt_snd)
  have hmomentum := (contDiffAt_phaseFields (curriedPhase ℓ C) r helapsed).2.1
  have hdm : DifferentiableAt ℝ
      (fun η ↦ phaseMomentum (curriedPhase ℓ C) r ((x 0, spatialPart x), η)) (spatialPart ξ) :=
    (hmomentum.comp (spatialPart ξ) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  apply phaseCovectorMap_comparison_of_original_phase (curriedPhase ℓ C) r x ξ hB helapsed
  · filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
    exact Filter.Eventually.of_forall fun p ↦ extend_smul ℓ (twoTimePhase C)
      (p.1, (p.1-r, (p.2, spatialPart ξ))) ha
  · apply (selected_phaseMomentum_mixed_norm_le (curriedPhase ℓ C) r x (spatialPart ξ) hdm).trans
    exact norm_mixedPhaseMatrix_phase_sub_one_le ℓ hε
      ((closedBall_subset_closedBall hεb').trans hbuffer) hs hdiff
      (fun q hq ↦ hnear q (closedBall_subset_closedBall hεb' hq)) hr hx hξ
  · apply (selected_phaseShear_mixed_norm_le (curriedPhase ℓ C) r x
      (isOpen_angularCone _ _ _) hξ hjoint).trans
    have hb' := retained_mixed_coefficient_bound ℓ (show 0 < 2*ε by positivity)
      (show 2*(2*ε) ≤ b by linarith) hbuffer hs KQ Q phaseCost hphase
      (show r ∈ Icc 0 (2*ε) from ⟨hr.1, by linarith [hr.2]⟩)
      (show x ∈ elapsedPhysicalBox z (2*ε) from
        ⟨ball_subset_ball (by linarith) hx.1, ball_subset_ball (by linarith) hx.2⟩)
      (show spatialPart ξ ∈ angularCone ℓ z.2.2 ((2*ε)/2) by
        rw [show (2*ε)/2 = ε by ring]; exact hξ)
    exact hb'.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hQ) hcost')

/-- Transfer smoothness and the exact output derivative to the supported
auxiliary on the SAME `Vphase` and `Ua` from
`exists_selected_elapsed_physical_carriers`. The germ agreement is produced
by `jc-selected-elapsed-quantitative-phase`; its instantiation remains with
the parent construction. This supplies `hSphase` and `hg` of
`exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:eq:chain-tail`). -/
theorem selected_supported_elapsed_phase_regular
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : RootState (Euclidean d)} {ε b Δ : ℝ}
    (hε : 0 < ε) (hεb : 2*ε ≤ b)
    {C : OpenPartialHomeomorph (Characteristic.TwoTimePoint (Euclidean d))
      (Characteristic.TwoTimePoint (Euclidean d))}
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (Ψ : TwoTimePhase d) (Vphase : Set (E × E)) (Ua : Set (SymbolBudgets.TwoTimePoint d))
    (hUa : Ua ⊆ bufferedBase z ε ×ˢ angularCone ℓ z.2.2 ε)
    (hmap : ∀ r ∈ Icc 0 Δ, ∀ w ∈ Vphase, elapsedPhasePoint r w ∈ Ua)
    (heq : ∀ w ∈ Ua, jointPhase Ψ =ᶠ[𝓝 w] jointPhase (curriedPhase ℓ C)) :
    ∀ r ∈ Icc 0 Δ,
      ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase Ψ r)) Vphase ∧
      ∀ u ξ, (u, ξ) ∈ Vphase →
        fderiv ℝ (fun v ↦ elapsedPhase Ψ r v ξ) u =
          innerSL ℝ (phaseCovectorMap (curriedPhase ℓ C) r u ξ) := by
  have hprod := contDiffOn_retained_product ℓ hε hεb hbuffer hs
  have horig (w : SymbolBudgets.TwoTimePoint d) (hw : w ∈ Ua) :
      ContDiffAt ℝ ∞ (jointPhase (curriedPhase ℓ C)) w :=
    hprod.contDiffAt ((isOpen_ball.prod (isOpen_angularCone _ _ _)).mem_nhds (hUa hw))
  intro r hr
  have hc : ContDiff ℝ ∞ (elapsedPhasePoint (d := d) r) :=
    contDiff_elapsedPhasePoint.comp (contDiff_id.prodMk contDiff_const)
  have ht : ContDiff ℝ ∞ (fun w : E × E ↦ (w.1 0-r)*w.2 0) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d+1))).contDiff.comp contDiff_fst).sub
      contDiff_const).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d+1))).contDiff.comp contDiff_snd)
  constructor
  · intro w hw
    have ha := (horig _ (hmap r hr w hw)).congr_of_eventuallyEq (heq _ (hmap r hr w hw))
    exact (ht.contDiffAt.add (ha.comp w hc.contDiffAt)).contDiffWithinAt
  · intro u ξ hu
    have hpoint := hmap r hr (u, ξ) hu
    have hp : ContinuousAt (fun v : E ↦ elapsedPhasePoint r (v, ξ)) u :=
      hc.continuous.continuousAt.comp
        (show ContinuousAt (fun v : E ↦ (v, ξ)) u from continuousAt_id.prodMk continuousAt_const)
    have heg := (heq _ hpoint).comp_tendsto
      hp
    have he : (fun v ↦ elapsedPhase Ψ r v ξ) =ᶠ[𝓝 u]
        (fun v ↦ elapsedPhase (curriedPhase ℓ C) r v ξ) := by
      filter_upwards [heg] with v hv
      exact congrArg (fun a ↦ (v 0-r)*ξ 0+a) hv
    rw [he.fderiv_eq]
    apply selected_fderiv_elapsedPhase_output
    exact ((horig _ hpoint).comp (u 0, spatialPart u)
      (f := fun p : ℝ × Euclidean d ↦ ((p.1, p.1-r, p.2), spatialPart ξ))
      ((contDiffAt_fst.prodMk ((contDiffAt_fst.sub contDiffAt_const).prodMk contDiffAt_snd)).prodMk
        contDiffAt_const)).differentiableAt (by simp)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
