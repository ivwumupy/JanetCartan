module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

/-!
# The primitive mixed second jet of the elapsed phase

The full graph constructor needs an operator norm of the mixed second
derivative. The original joint `(t,s,y)` versus `η` derivative supplies it:
the elapsed substitution and spatial projection are contractions, and the
temporal Fourier term contributes at most one. Consumer:
`exists_fullGraphFamily_of_wholeImage_phase`, for
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open SymbolBudgets
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => ℝ × ℝ × Euclidean d

private def elapsedPositionLinear : E →L[ℝ] P :=
  (EuclideanSpace.proj 0).prod ((EuclideanSpace.proj 0).prod spatialProjection)

private theorem norm_elapsedPositionLinear_le :
    ‖elapsedPositionLinear (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul, elapsedPositionLinear, ContinuousLinearMap.prod_apply, Prod.norm_def]
  exact max_le (PiLp.norm_apply_le x 0)
    (max_le (PiLp.norm_apply_le x 0) (norm_spatialPart_le x))

/-- The actual spacetime mixed second jet is bounded by one plus the
original joint mixed second jet. This closes the mixed-jet input of the
whole-image graph producer without assuming an elapsed-phase bound.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_elapsedPhase_mixed_fderiv_le
    (Ψ : TwoTimePhase d) (r : ℝ) (x ξ : E)
    {D : Set (Euclidean d)} (hD : IsOpen D) (hξ : spatialPart ξ ∈ D)
    (hΨ : ∀ η ∈ D, ContDiffAt ℝ ∞ (jointPhase Ψ)
      ((x 0, x 0 - r, spatialPart x), η)) :
    ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun w ↦ elapsedPhase Ψ r w v) x) ξ‖ ≤
      1 + ‖fderiv ℝ (fun η ↦ fderiv ℝ
        (fun p : P ↦ Ψ p.1 p.2.1 p.2.2 η)
        (x 0, x 0 - r, spatialPart x)) (spatialPart ξ)‖ := by
  let L : E →L[ℝ] P := elapsedPositionLinear
  let e : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let Q : E →L[ℝ] Euclidean d := spatialProjection
  let p : P := (x 0, x 0 - r, spatialPart x)
  let G : Euclidean d → P →L[ℝ] ℝ := fun η ↦
    fderiv ℝ (fun v : P ↦ Ψ v.1 v.2.1 v.2.2 η) p
  let J : (P →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E P ℝ).flip L
  have hL : ‖L‖ ≤ 1 := norm_elapsedPositionLinear_le
  have he : ‖e‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [one_mul, e, EuclideanSpace.coe_proj] using PiLp.norm_apply_le v 0
  have hQ : ‖Q‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    exact (norm_spatialPart_le v).trans_eq (one_mul _).symm
  have hJ : ‖J‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    exact (f.opNorm_comp_le L).trans (by simpa using mul_le_mul_of_nonneg_left hL (norm_nonneg f))
  have hG : DifferentiableAt ℝ G (spatialPart ξ) := by
    have h := (hΨ _ hξ).comp (spatialPart ξ, p)
      (f := fun v : Euclidean d × P ↦ (v.2, v.1))
      (contDiffAt_snd.prodMk contDiffAt_fst)
    exact (h.fderiv (m := ∞) contDiffAt_const (by simp)).differentiableAt (by simp)
  have heq : (fun v ↦ fderiv ℝ (fun w ↦ elapsedPhase Ψ r w v) x) =ᶠ[𝓝 ξ]
      (fun v ↦ (e v) • e + J (G (Q v))) := by
    filter_upwards [Q.continuous.continuousAt.eventually (hD.mem_nhds hξ)] with v hv
    have hs := ((hΨ _ hv).comp p
      (f := fun z : P ↦ (z, spatialPart v))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have hp : HasFDerivAt (fun w : E ↦ (w 0, w 0 - r, spatialPart w)) L x :=
      e.hasFDerivAt.prodMk ((e.hasFDerivAt.sub_const r).prodMk Q.hasFDerivAt)
    have ht := ((e.hasFDerivAt (x := x)).sub_const r).mul_const (v 0)
    have hh := ht.fun_add (hs.hasFDerivAt.comp x hp)
    change _ = (v 0) • e + (G (spatialPart v)).comp L
    simpa only [elapsedPhase, jointPhase, L, e, p, G, J, Q,
      EuclideanSpace.coe_proj, Function.comp_def, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul, mul_comm] using hh.fderiv
  have hd := (e.hasFDerivAt.smul_const e).add
    (J.hasFDerivAt.comp ξ (hG.hasFDerivAt.comp ξ Q.hasFDerivAt))
  change HasFDerivAt (fun v ↦ e v • e + J (G (Q v))) _ ξ at hd
  rw [heq.fderiv_eq, hd.fderiv]
  have ht : ‖e.smulRight e‖ ≤ 1 :=
    by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      change ‖e v • e‖ ≤ 1 * ‖v‖
      rw [norm_smul, one_mul]
      exact (mul_le_mul_of_nonneg_left he (norm_nonneg (e v))).trans
        (by simpa using e.le_of_opNorm_le he v)
  have hs : ‖J.comp ((fderiv ℝ G (Q ξ)).comp Q)‖ ≤ ‖fderiv ℝ G (Q ξ)‖ := by
    calc
      _ ≤ ‖J‖ * (‖fderiv ℝ G (Q ξ)‖ * ‖Q‖) :=
        (J.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg J))
      _ ≤ 1 * (‖fderiv ℝ G (Q ξ)‖ * 1) :=
        mul_le_mul hJ (mul_le_mul_of_nonneg_left hQ (norm_nonneg (fderiv ℝ G (Q ξ))))
          (mul_nonneg (norm_nonneg (fderiv ℝ G (Q ξ))) (norm_nonneg Q)) zero_le_one
      _ = _ := by ring
  exact (norm_add_le (e.smulRight e) (J.comp ((fderiv ℝ G (Q ξ)).comp Q))).trans
    (add_le_add ht hs)

/-- The temporal row of the triangular mixed matrix is controlled by the
original joint mixed derivative. Consumer: `exists_elapsedPhase_mixed_bounds`,
which supplies the inverse bound in the supported integer theorem for
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_elapsedTimeDerivative_row_le (Ψ : TwoTimePhase d) (r : ℝ) (x : Euclidean (d + 1)) (η : Euclidean d)
    {D : Set (Euclidean d)} (hD : IsOpen D) (hη : η ∈ D)
    (hΨ : ∀ ζ ∈ D, ContDiffAt ℝ ∞ (jointPhase Ψ)
      ((x 0, x 0-r, spatialPart x), ζ)) :
    ‖fun j : Fin d ↦ partialDeriv (elapsedTimeDerivative Ψ r (x 0, spatialPart x)) η j‖ ≤
      ‖fderiv ℝ (fun ζ ↦ fderiv ℝ
        (fun p : ℝ × ℝ × Euclidean d ↦ Ψ p.1 p.2.1 p.2.2 ζ)
        (x 0, x 0-r, spatialPart x)) η‖ := by
  let p : P := (x 0, x 0-r, spatialPart x)
  let v : P := (1, 1, 0)
  let G : Euclidean d → P →L[ℝ] ℝ := fun ζ ↦
    fderiv ℝ (fun p : P ↦ Ψ p.1 p.2.1 p.2.2 ζ) p
  have hG : DifferentiableAt ℝ G η := by
    have h := (hΨ η hη).comp (η, p)
      (f := fun v : Euclidean d × P ↦ (v.2, v.1))
      (contDiffAt_snd.prodMk contDiffAt_fst)
    exact (h.fderiv (m := ∞) contDiffAt_const (by simp)).differentiableAt (by simp)
  have he : elapsedTimeDerivative Ψ r (x 0, spatialPart x) =ᶠ[𝓝 η]
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
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fderiv ℝ G η))).mpr
  intro j
  change ‖(fderiv ℝ _ η) (EuclideanSpace.single j 1)‖ ≤ ‖fderiv ℝ G η‖
  rw [he.fderiv_eq, hd.fderiv]
  change ‖((fderiv ℝ G η) (EuclideanSpace.single j 1)) v‖ ≤ ‖fderiv ℝ G η‖
  calc
    _ ≤ ‖(fderiv ℝ G η) (EuclideanSpace.single j 1)‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ G η‖ * ‖EuclideanSpace.single j 1‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right ((fderiv ℝ G η).le_opNorm _) (norm_nonneg v)
    _ = _ := by simp [v]

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
