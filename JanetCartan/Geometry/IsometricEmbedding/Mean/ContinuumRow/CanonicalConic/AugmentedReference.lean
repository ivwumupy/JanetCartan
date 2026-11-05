module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SymbolGeometry
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# The fixed reference for the augmented transport differential

Incidence transversality makes the data block invertible. The spectator
derivative is retained as the off-diagonal block; it is not discarded when
passing from slice inverses to joint inverse jets (`bg-Psi`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Reorder the original variables without changing their values. The
incidence coordinate belongs to the data block (`bg-Psi`). -/
def augmentedInputCoordinates : InputVariables n ≃L[ℝ]
    (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p ↦ ((p.2.1.2, p.1.1, p.1.2), (p.2.1.1, p.2.2))
      invFun := fun q ↦ ((q.1.2.1, q.1.2.2), (q.2.1, q.1.1), q.2.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The output reordering uses the SAME orthogonal physical coordinates as
the conic inverse (`app:ch_background:eq:bg-full-complex-amplitude`). -/
def augmentedOutputCoordinates : (Variables n × Euclidean 2) ≃L[ℝ]
    (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := symbolOutputCoordinates T
      invFun := fun q ↦ ((q.1.2.1, q.1.2.2, (adaptedSliceCoordinates T).equiv.symm q.2), q.1.1)
      left_inv := fun p ↦ by
        change ((p.1.1, p.1.2.1, (adaptedSliceCoordinates T).equiv.symm
          ((adaptedSliceCoordinates T).equiv p.1.2.2)), p.2) = p
        rw [ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun p ↦ by simp [symbolOutputCoordinates]
      map_add' := fun _ _ ↦ by simp [symbolOutputCoordinates]
      map_smul' := fun _ _ ↦ by simp [symbolOutputCoordinates] }

/-- The frozen frequency map with all spectator derivatives retained
(`app:ch_background:eq:bg-Psi`). -/
def frozenJointFrequency
    (q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))) :
    ℝ × Euclidean (n - 1) :=
  frozenChart (fun s ↦ gradient (dispersion T) (spatialCarrier T (q.1.1, s))) q.2

/-- The actual frozen augmented map in original physical coordinates. This
is fixed before the current immersion (`bg-Psi`). -/
def frozenAugmentedChart (p : InputVariables n) : Variables n × Euclidean 2 :=
  (augmentedOutputCoordinates T).symm
    ((augmentedInputCoordinates (n := n) p).1,
      frozenJointFrequency T (augmentedInputCoordinates (n := n) p))

/-- Joint frozen smoothness follows from the retained dispersion and patch
on their actual carrier interior (`bg-mixed-input`). -/
theorem frozenJointFrequency_contDiffAt {c C : ℝ} (hP : P.IsValid c C)
    {q : (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1))}
    (hq : carrierParameters (q.1.1, q.2.1) ∈ parameterInterior (2 * P.radius)) :
    ContDiffAt ℝ ∞ (frozenJointFrequency T) q :=
  (ActualInverses.frozenChart_contDiffAt T hP (q := (q.1.1, q.2)) hq).comp q
    (contDiffAt_fst.fst.prodMk contDiffAt_snd)

/-- The original-variable frozen augmented map is smooth on its actual
carrier interior (`app:ch_background:eq:bg-Psi`). -/
theorem frozenAugmentedChart_contDiffAt {c C : ℝ} (hP : P.IsValid c C)
    {p : InputVariables n}
    (hp : carrierParameters (p.2.1.2, p.2.1.1) ∈ parameterInterior (2 * P.radius)) :
    ContDiffAt ℝ ∞ (frozenAugmentedChart T) p :=
  (augmentedOutputCoordinates T).symm.contDiff.contDiffAt.comp p
    (((augmentedInputCoordinates (n := n)).contDiff.contDiffAt.fst).prodMk
      ((frozenJointFrequency_contDiffAt T hP hp).comp p
        (augmentedInputCoordinates (n := n)).contDiff.contDiffAt))

variable {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)

/-- Frozen augmented input center; physical positions are zero and the
transverse covector is the selected incidence direction (`bg-Psi`). -/
def augmentedInputCenter : InputVariables n :=
  ((0, 0), (z₀ 0, spectatorCenter z₀), T.data.adapted.embedding.toContinuousLinearMap.adjoint k)

/-- The fixed reference derivative, including the spectator off-diagonal
block. Invertibility follows from the primitive frozen incidence derivative
via `referenceEquiv`, rather than an assumed chart (`bg-Psi`). -/
def augmentedReferenceEquiv : InputVariables n ≃L[ℝ] (Variables n × Euclidean 2) :=
  let q := augmentedInputCoordinates (augmentedInputCenter T (z₀ := z₀) (k := k))
  let B := (fderiv ℝ (frozenJointFrequency T) q).comp
    (ContinuousLinearMap.inl ℝ (Euclidean 2 × Euclidean n × Euclidean n)
      (ℝ × Euclidean (n - 1)))
  (augmentedInputCoordinates (n := n)).trans
    (((ContinuousLinearEquiv.refl ℝ (Euclidean 2 × Euclidean n × Euclidean n)).skewProd
      (FrozenIncidence.referenceEquiv T hP hz₀ hinc hd) B).trans
        (augmentedOutputCoordinates T).symm)

/-- The explicit block equivalence is precisely the derivative of the
original-variable frozen augmented map (`app:ch_background:eq:bg-Psi`). -/
theorem fderiv_frozenAugmentedChart_center :
    fderiv ℝ (frozenAugmentedChart T) (augmentedInputCenter T (z₀ := z₀) (k := k)) =
      (augmentedReferenceEquiv T hP hz₀ hinc hd : InputVariables n →L[ℝ] _) := by
  let p := augmentedInputCenter T (z₀ := z₀) (k := k)
  let q := augmentedInputCoordinates p
  let D := fderiv ℝ (frozenJointFrequency T) q
  let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
  have hq : carrierParameters (q.1.1, q.2.1) ∈ parameterInterior (2 * P.radius) := by
    change carrierParameters (spectatorCenter z₀, z₀ 0) ∈ _
    rw [carrierParameters_spectatorCenter]
    exact parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz₀ i).le)
  have hf := (frozenJointFrequency_contDiffAt T hP hq).differentiableAt (by simp)
  have hdata : D.comp (ContinuousLinearMap.inr ℝ
      (Euclidean 2 × Euclidean n × Euclidean n) (ℝ × Euclidean (n - 1))) = G := by
    have hc := hf.hasFDerivAt.comp q.2
      ((hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2))
    have he := hc.fderiv
    change fderiv ℝ (frozenChart (fun s ↦ gradient (dispersion T)
      (spatialCarrier T (spectatorCenter z₀, s))))
      (z₀ 0, T.data.adapted.embedding.toContinuousLinearMap.adjoint k) = _ at he
    exact he.symm.trans (FrozenIncidence.fderiv_eq_referenceEquiv T hP hz₀ hinc hd)
  have haug := (hasFDerivAt_fst (p := q)).prodMk hf.hasFDerivAt
  have hcomp := (augmentedOutputCoordinates T).symm.hasFDerivAt.comp p
    (haug.comp p (augmentedInputCoordinates (n := n)).hasFDerivAt)
  change HasFDerivAt (frozenAugmentedChart T) _ p at hcomp
  rw [hcomp.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  apply (augmentedOutputCoordinates T).injective
  change (augmentedOutputCoordinates T) ((augmentedOutputCoordinates T).symm
      ((augmentedInputCoordinates v).1, D (augmentedInputCoordinates v))) =
    (augmentedOutputCoordinates T) ((augmentedOutputCoordinates T).symm
      ((augmentedInputCoordinates v).1, G (augmentedInputCoordinates v).2 +
        D ((augmentedInputCoordinates v).1, 0)))
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  have he := congrArg (fun L : (ℝ × Euclidean (n - 1)) →L[ℝ]
    (ℝ × Euclidean (n - 1)) ↦ L (augmentedInputCoordinates v).2) hdata
  change D (0, (augmentedInputCoordinates v).2) = G (augmentedInputCoordinates v).2 at he
  rw [← he, ← map_add]
  simp only [Prod.mk_add_mk, zero_add, add_zero, Prod.mk.eta]

/-- A common positive ball has a quarter derivative gap for the fixed
augmented reference. Both the equivalence and radius precede the immersion;
the actual perturbation consumes the remaining quarter (`bg-Psi`). -/
theorem exists_frozen_augmented_gap {cap : ℝ} (hcap : 0 < cap) :
    ∃ ρ > (0 : ℝ), ρ < cap ∧
      ∀ p ∈ closedBall (augmentedInputCenter T (z₀ := z₀) (k := k)) ρ,
        ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
          (fderiv ℝ (frozenAugmentedChart T) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 4 := by
  let p := augmentedInputCenter T (z₀ := z₀) (k := k)
  let A := augmentedReferenceEquiv T hP hz₀ hinc hd
  have hp : carrierParameters (p.2.1.2, p.2.1.1) ∈ parameterInterior (2 * P.radius) := by
    change carrierParameters (spectatorCenter z₀, z₀ 0) ∈ _
    rw [carrierParameters_spectatorCenter]
    exact parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz₀ i).le)
  have hc := (frozenAugmentedChart_contDiffAt T hP hp).continuousAt_fderiv (by simp)
  have hn : ContinuousAt (fun x ↦ ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (frozenAugmentedChart T) x) - ContinuousLinearMap.id ℝ (InputVariables n)‖) p :=
    ((continuousAt_const.clm_comp hc).sub continuousAt_const).norm
  have hz : A.symm.toContinuousLinearMap.comp (fderiv ℝ (frozenAugmentedChart T) p) -
      ContinuousLinearMap.id ℝ (InputVariables n) = 0 := by
    rw [fderiv_frozenAugmentedChart_center T hP hz₀ hinc hd]
    apply ContinuousLinearMap.ext
    intro x
    change A.symm (A x) - x = 0
    rw [ContinuousLinearEquiv.symm_apply_apply, sub_self]
  have he := hn.eventually (gt_mem_nhds (show ‖A.symm.toContinuousLinearMap.comp
    (fderiv ℝ (frozenAugmentedChart T) p) - ContinuousLinearMap.id ℝ (InputVariables n)‖ <
      (1 / 4 : ℝ) by rw [hz, norm_zero]; norm_num))
  obtain ⟨d, hdpos, hdball⟩ := Metric.eventually_nhds_iff_ball.mp he
  refine ⟨min d cap / 2, by positivity, by linarith [min_le_right d cap], ?_⟩
  intro x hx
  exact (hdball x (closedBall_subset_ball (by linarith [min_le_left d cap]) hx)).le

end JanetCartan.ContinuumRow.CanonicalConic
