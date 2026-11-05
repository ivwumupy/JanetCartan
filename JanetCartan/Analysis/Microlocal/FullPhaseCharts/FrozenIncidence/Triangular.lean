module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.FrozenIncidence.Transversality
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Frozen

/-!
# The actual triangular frozen differential

The last two coordinates of the primitive incidence point are the spectator
center. The shared `carrierParameters` identifies its scalar derivative with
the proved first-coordinate incidence derivative, supplying `triangularEquiv`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.FullPhaseCharts.FrozenIncidence
open HamiltonPhase ActualCarriers ActualCarriers.FrozenPhaseReference
open ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase

/-- The literal last two coordinates of a frozen incidence point
(`app:ch_seed:prop:seed-phase-charts`). -/
def spectatorCenter (z : Euclidean 3) : Euclidean 2 :=
  WithLp.toLp 2 ![z 1, z 2]

/-- Reassembling the incidence point uses the shared carrier coordinates
(`app:ch_seed:prop:seed-phase-charts`). -/
@[simp] theorem carrierParameters_spectatorCenter (z : Euclidean 3) :
    carrierParameters (spectatorCenter z, z 0) = z := by
  ext i
  fin_cases i <;> simp [carrierParameters_apply, spectatorCenter]

/-- The scalar carrier coordinate differentiates to the first coordinate
vector of the original patch (`app:ch_seed:prop:seed-phase-charts`). -/
theorem hasDerivAt_carrierParameters (p : Euclidean 2) (t : ℝ) :
    HasDerivAt (fun s ↦ carrierParameters (p, s)) (EuclideanSpace.single 0 1) t := by
  have h := carrierParameters.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t p).prodMk (hasDerivAt_id t))
  apply h.congr_deriv
  ext i
  fin_cases i <;> simp [carrierParameters_apply]

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Joint smoothness of the actual frozen velocity in both spectator
coordinates and the first coordinate (`app:ch_seed:prop:seed-phase-charts`). -/
theorem carrier_gradient_smooth {c C : ℝ} (hP : P.IsValid c C) :
    ContDiffOn ℝ ∞ (fun q ↦ gradient (dispersion T) (spatialCarrier T q))
      (carrierParameters ⁻¹' parameterInterior (2 * P.radius)) := by
  exact (patch_gradient_smooth T hP).comp carrierParameters.contDiff.contDiffOn
    (fun _ h ↦ h)

/-- The primitive nonzero incidence derivative is precisely the nonzero
scalar in the triangular differential, at the literal spectator center
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem scalar_incidence_transverse {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z) = 0)
    (hd : fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z
      (EuclideanSpace.single 0 1) ≠ 0) :
    ⟪deriv (fun t ↦ gradient (dispersion T) (spatialCarrier T (spectatorCenter z, t)))
        (z 0), T.data.adapted.embedding.toContinuousLinearMap.adjoint k⟫_ℝ ≠ 0 := by
  have hzD := parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz i).le)
  have hV := ((patch_gradient_smooth T hP).contDiffAt
    ((isOpen_parameterInterior _).mem_nhds hzD)).differentiableAt (by simp)
  have hline := hasDerivAt_carrierParameters (spectatorCenter z) (z 0)
  have hvel := hV.hasFDerivAt.comp_hasDerivAt_of_eq (z 0) hline
    (carrierParameters_spectatorCenter z).symm
  have hpair := (hV.hasFDerivAt.inner ℝ
    (hasFDerivAt_const (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) z))
  have hp := hpair.comp_hasDerivAt_of_eq (z 0) hline
    (carrierParameters_spectatorCenter z).symm
  have hp' := hvel.inner ℝ
    (hasDerivAt_const (z 0) (T.data.adapted.embedding.toContinuousLinearMap.adjoint k))
  have hEq := hp.unique hp'
  have hderiv : deriv (fun t ↦ gradient (dispersion T)
      (spatialCarrier T (spectatorCenter z, t))) (z 0) =
      fderiv ℝ (fun w ↦ gradient (dispersion T) (T.reference.spatialPatch w)) z
        (EuclideanSpace.single 0 1) := hvel.deriv
  rw [hderiv]
  have hnonzero := dispersion_incidence_transverse T hP hz hinc hd
  rw [hpair.fderiv] at hnonzero
  simp only [inner_zero_right, zero_add] at hEq
  exact fun hzero ↦ hnonzero (hEq.trans hzero)

/-- The actual frozen chart has the triangular derivative equivalence at
incidence; all its invertibility input is proved from primitive incidence
(`app:ch_seed:prop:seed-phase-charts`). -/
def referenceEquiv {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z) = 0)
    (hd : fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z
      (EuclideanSpace.single 0 1) ≠ 0) :
    (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)) :=
  triangularEquiv
    ⟪deriv (fun t ↦ gradient (dispersion T) (spatialCarrier T (spectatorCenter z, t)))
      (z 0), T.data.adapted.embedding.toContinuousLinearMap.adjoint k⟫_ℝ
    (gradient (dispersion T) (spatialCarrier T (spectatorCenter z, z 0)))
    (scalar_incidence_transverse T hP hz hinc hd)

/-- Identification of the central equivalence with the differential of the
literal frozen chart (`app:ch_seed:prop:seed-phase-charts`). -/
theorem fderiv_eq_referenceEquiv {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z) = 0)
    (hd : fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z
      (EuclideanSpace.single 0 1) ≠ 0) :
    fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
        (spatialCarrier T (spectatorCenter z, t))))
      (z 0, T.data.adapted.embedding.toContinuousLinearMap.adjoint k) =
      (referenceEquiv T hP hz hinc hd :
        (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))) := by
  have hzD := parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz i).le)
  have hV : ContDiffAt ℝ ∞ (fun q ↦ gradient (dispersion T) (spatialCarrier T q))
      (spectatorCenter z, z 0) :=
    (carrier_gradient_smooth T hP).contDiffAt
      (((isOpen_parameterInterior _).preimage carrierParameters.continuous).mem_nhds
        (by
          change carrierParameters (spectatorCenter z, z 0) ∈ parameterInterior (2 * P.radius)
          rwa [carrierParameters_spectatorCenter]))
  have hv := (hV.comp (z 0) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  exact (hasFDerivAt_frozenChart hv.hasDerivAt).fderiv

end JanetCartan.FullPhaseCharts.FrozenIncidence
