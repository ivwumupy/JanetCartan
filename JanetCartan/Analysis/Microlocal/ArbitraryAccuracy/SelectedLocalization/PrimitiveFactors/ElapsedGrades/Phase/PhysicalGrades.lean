module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.Profiles

/-!
# Physical base jets of the selected conic phase

With frequency fixed, radial normalization is an affine contraction in both
times and the physical position. Its scalar factor costs only `‖ℓ‖ * ‖η‖`.
This supplies the physical phase grades in `CompleteFactor`, directly from
the retained local phase estimate (`app:ch_regular:eq:high-phase`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ}

private def phaseBaseInclusion : (ℝ × ℝ × Euclidean d) →L[ℝ] TwoTimePoint (Euclidean d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ (v.1, (v.2.1, (v.2.2, 0)))
      map_add' := by intro v w; simp
      map_smul' := by intro a v; simp }

private theorem norm_phaseBaseInclusion_le : ‖phaseBaseInclusion (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖(v.1, (v.2.1, (v.2.2, (0 : Euclidean d))))‖ ≤ 1 * ‖v‖
  simp only [one_mul, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg v.2.2), le_refl]

/-- Fixed-frequency base jets of the original continued phase cost zero
derivatives and one frequency factor. This is the radial-rescaling step
used for `CompleteFactor.hauxPhaseGrades` in
`app:ch_regular:eq:high-phase`. -/
theorem norm_iteratedFDeriv_curriedExtend_base_le
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {J U : Set (TwoTimePoint (Euclidean d))} (hJ : IsCompact J)
    (hU : IsOpen U) (hJU : J ⊆ U)
    {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    (η : Euclidean d) (v : ℝ × ℝ × Euclidean d)
    (hv : normalize ℓ (budgetCoordinates (v, η)) ∈ J) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun w : ℝ × ℝ × Euclidean d ↦
      curriedExtend ℓ F w.1 w.2.1 w.2.2 η) v‖ ≤
        ‖η‖ * ‖ℓ‖ * cNorm J n F := by
  let b : TwoTimePoint (Euclidean d) := (0, (0, (0, (ℓ η)⁻¹ • η)))
  let f : (ℝ × ℝ × Euclidean d) → ℝ := fun w ↦ F (phaseBaseInclusion w + b)
  have hpoint : phaseBaseInclusion v + b = normalize ℓ (budgetCoordinates (v, η)) := by
    simp [phaseBaseInclusion, b, ConicPhase.normalize, budgetCoordinates]
  have hf : ContDiffAt ℝ ∞ f v :=
    (hF.contDiffAt (hU.mem_nhds (hJU (hpoint ▸ hv)))).comp v
      (phaseBaseInclusion.contDiff.contDiffAt.add contDiffAt_const)
  have hb : ‖iteratedFDeriv ℝ n f v‖ ≤ cNorm J n F := by
    apply (SymbolBudgets.norm_iteratedFDeriv_preAffine_le phaseBaseInclusion b hU hF
      (hJU (hpoint ▸ hv)) n).trans
    apply (mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg _) norm_phaseBaseInclusion_le) (norm_nonneg _)).trans
    rw [mul_one]
    exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ
      (fun w hw ↦ (hF.contDiffAt (hU.mem_nhds (hJU hw))).of_le (by simp))
      (hpoint ▸ hv) le_rfl
  have he : (fun w : ℝ × ℝ × Euclidean d ↦ curriedExtend ℓ F w.1 w.2.1 w.2.2 η) =
      fun w ↦ (ℓ η) • f w := by
    funext w
    simp [curriedExtend, extend, ConicPhase.normalize, f, phaseBaseInclusion, b]
  rw [he]
  change ‖iteratedFDeriv ℝ n ((ℓ η) • f) v‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (hf.of_le (by simp)), norm_smul]
  calc
    ‖ℓ η‖ * ‖iteratedFDeriv ℝ n f v‖ ≤ (‖ℓ‖ * ‖η‖) * cNorm J n F :=
      mul_le_mul (ℓ.le_opNorm η) hb (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)
local notation "Mat" => MetricTensor (d+1)

/-- The retained local phase estimate produces uniform physical base grades
before choosing the coefficients, slow scale, source frequency or accuracy.
The only analytic inputs are the local smoothness, buffer and `phaseCost`
outputs of `exists_finite_direct_operator_bounds`. The parent supplies the
normalized carrier inclusion geometrically. Consumer:
`CompleteFactor.hauxPhaseGrades` (`app:ch_regular:eq:initial-coefficient-profile`,
`app:ch_regular:eq:high-phase`). -/
theorem exists_selected_physicalPhase_base_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M) (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ P : ℕ → ℝ, (∀ k, 0 ≤ P k) ∧
      ∀ (Rstar : ℕ), 3 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Fin (d+1) → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j - Rstar)) →
      ∀ C : f.centers → OpenPartialHomeomorph T T,
      (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (C p)) (C p).target) →
      (∀ p,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        closedBall (z.1, z) (f.chart p).targetRadius ⊆ (C p).target) →
      (∀ p m,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        cNorm (closedBall (z.1, z) (f.chart p).targetRadius) m (twoTimePhase (C p)) ≤
          (f.chart p).phaseCost m * (1 + cNorm (closedBall x RQ) (m+1) Q)) →
      ∀ p η v,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        normalize (f.chart p).radialSection (budgetCoordinates (v, η)) ∈
          closedBall (z.1, z) (f.chart p).targetRadius →
        ∀ k, ‖iteratedFDeriv ℝ (k+1) (fun w : ℝ × ℝ × Euclidean d ↦
          curriedExtend (f.chart p).radialSection (twoTimePhase (C p)) w.1 w.2.1 w.2.2 η) v‖ ≤
            ‖η‖ * P k * L ^ k := by
  classical
  let D := fun p k ↦ ‖(f.chart p).radialSection‖ *
    ((f.chart p).phaseCost (k+1) * (1 + A (k+2)))
  have hD p k : 0 ≤ D p k := mul_nonneg (norm_nonneg _)
    (mul_nonneg ((f.chart p).phaseCost_pos _).le (by linarith [hA (k+2)]))
  refine ⟨fun k ↦ ∑ p, D p k, fun k ↦ Finset.sum_nonneg (fun p _ ↦ hD p k), ?_⟩
  intro Rstar hRstar L hL Q hQ C hC hbuffer hphase p η v e z hv k
  have hb := norm_iteratedFDeriv_curriedExtend_base_le (f.chart p).radialSection
    (isCompact_closedBall _ _) (C p).open_target (hbuffer p) (hC p) η v hv (k+1)
  have hl : cNorm (closedBall (z.1, z) (f.chart p).targetRadius) (k+1)
      (twoTimePhase (C p)) ≤ ((f.chart p).phaseCost (k+1) * (1 + A (k+2))) * L ^ k := by
    have ht := JointBudget.fixed_profile_transfer_bound (r := k+1) (c := 1) (ν := 1)
      hL (hA (k+2)) ((f.chart p).phaseCost_pos (k+1)).le (by omega : 1+1 ≤ Rstar)
      (hQ (k+2)) (hphase p (k+1))
    simpa only [Nat.add_sub_cancel] using ht
  apply hb.trans
  calc
    _ ≤ ‖η‖ * D p k * L ^ k :=
      (mul_le_mul_of_nonneg_left hl (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
        (by dsimp [D]; ring)
    _ ≤ ‖η‖ * (∑ p, D p k) * L ^ k := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun p _ ↦ hD p k) (Finset.mem_univ p)) (norm_nonneg _))
      (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
