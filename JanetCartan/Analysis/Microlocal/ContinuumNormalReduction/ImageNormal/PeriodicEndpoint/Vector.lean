module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicEndpoint.Scalar
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector
public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.L2

/-!
# Real vector local H¹ transfer

Finite-coordinate synthesis of the scalar chart transfer supplies the endpoint
needed for the literal adjoint in `app:ch_background:prop:bg-frame`, Step 1.
The input norm is that of the actual complex inclusion over Lebesgue measure.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.PeriodicLocalL2 JanetCartan.Pseudodifferential
open JanetCartan.Pseudodifferential.DifferentialChart JanetCartan.AmplitudeBound

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicEndpoint

variable {n m : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin m)

private theorem weakDerivative_map (L : ℂ →L[ℝ] V) {i : Fin n}
    {u v : PeriodicL2 n ℂ} (hd : HasPeriodicWeakDerivative i u v) :
    HasPeriodicWeakDerivative i (L.compLpL 2 volume u) (L.compLpL 2 volume v) := by
  intro φ hφ
  have h := hd (fun z ↦ L.adjoint (φ z)) (hφ.comp_clm L.adjoint)
  rw [periodicCoordinateDeriv_comp_clm hφ L.adjoint] at h
  calc
    _ = ∫ z, inner ℝ (v z) (L.adjoint (φ z)) := by
      apply integral_congr_ae
      filter_upwards [L.coeFn_compLpL v] with z hz
      rw [hz, L.adjoint_inner_right]
    _ = _ := h
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [L.coeFn_compLpL u] with z hz
      rw [hz, L.adjoint_inner_right]

private theorem weakDerivative_sum {i : Fin n} (s : Finset (Fin m))
    (u v : Fin m → PeriodicL2 n V)
    (hd : ∀ a ∈ s, HasPeriodicWeakDerivative i (u a) (v a)) :
    HasPeriodicWeakDerivative i (∑ a ∈ s, u a) (∑ a ∈ s, v a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasPeriodicWeakDerivative.zero (F := V) i
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hd a (Finset.mem_insert_self _ _)).add
      (ih (fun b hb ↦ hd b (Finset.mem_insert_of_mem hb)))

private def realCoordinateSynthesis (a : Fin m) : ℂ →L[ℝ] V :=
  Complex.reCLM.smulRight (EuclideanSpace.single a 1)

private theorem norm_realCoordinateSynthesis_le (a : Fin m) (z : ℂ) :
    ‖realCoordinateSynthesis a z‖ ≤ ‖z‖ := by
  change ‖z.re • (EuclideanSpace.single a 1 : V)‖ ≤ ‖z‖
  rw [norm_smul, show ‖(EuclideanSpace.single a 1 : V)‖ = 1 by
    simpa only [EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin m) ℝ).norm_eq_one a, mul_one]
  exact Complex.abs_re_le_norm z

private theorem norm_realCoordinateSynthesis_l2_le (a : Fin m) (u : PeriodicL2 n ℂ) :
    ‖(realCoordinateSynthesis a).compLpL 2 volume u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(realCoordinateSynthesis a).coeFn_compLpL u] with z hz
  rw [hz]
  exact norm_realCoordinateSynthesis_le a (u z)

/-- The local real-vector endpoint: support in a fixed strict subcube and
Fourier H¹ membership of the literal complex inclusion produce membership in
the actual normalized-torus H¹ space, with an explicit finite-dimensional
constant. This is the chart step for the negative-Sobolev error estimate in
`app:ch_background:prop:bg-frame`, Step 1. The `2π` factor converts unit-frequency
Euclidean derivatives to the physical convention of the periodic scale. -/
theorem exists_real_vector_periodic_h1 {r : ℝ} (hr : r < 1 / 2)
    (u : EuclideanL2 n V)
    (hs : ∀ᵐ x ∂volume, x ∉ chartBox r → u x = 0)
    (hu : MemVectorFourierSobolev 1 (l2ComplexInclusion volume u)) :
    ∃ U : PeriodicSobolevSpace n V 1,
      PeriodicSobolevSpace.toL2 1 U = toTorus (𝕜 := ℝ) u ∧
      ‖U‖ ≤ ((m : ℝ) * (1 + 2 * Real.pi * n)) *
        vectorFourierSobolevNorm 1 (l2ComplexInclusion volume u) := by
  classical
  let c := finiteL2CoordinateIsometry volume (l2ComplexInclusion volume u)
  have hc (a : Fin m) : c a =ᵐ[volume] fun x ↦ (u x a : ℂ) := by
    filter_upwards [finiteL2Coordinates_apply_ae volume (l2ComplexInclusion volume u) a,
      euclideanComplexInclusion.coeFn_compLpL u] with x hx hy
    exact hx.trans (by rw [show (l2ComplexInclusion volume u) x =
      euclideanComplexInclusion (u x) from hy]; rfl)
  have hcs (a : Fin m) : ∀ᵐ x ∂volume, x ∉ chartBox r → c a x = 0 := by
    filter_upwards [hc a, hs] with x hx hy hbox
    rw [hx, hy hbox]
    simp
  choose w hd hn using fun a ↦ exists_scalar_periodic_derivatives hr (c a) (hcs a) (hu a)
  let p (a : Fin m) := toTorus (𝕜 := ℂ) (c a)
  let R (a : Fin m) := (realCoordinateSynthesis a).compLpL 2 (volume : Measure (Torus n))
  have hp (a : Fin m) : p a =ᵐ[volume]
      fun z ↦ (u (centeredTorusRepresentative z) a : ℂ) :=
    (toTorus_coe (𝕜 := ℂ) (c a)).trans
      (measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp (hc a).restrict)
  have he : toTorus (𝕜 := ℝ) u = ∑ a, R a (p a) := by
    apply Lp.ext
    filter_upwards [toTorus_coe (𝕜 := ℝ) u,
      Lp.coeFn_finsetSum Finset.univ (fun a ↦ R a (p a)),
      ae_all_iff.mpr hp,
      ae_all_iff.mpr (fun a ↦ (realCoordinateSynthesis a).coeFn_compLpL (p a))]
      with z hz hsum hpz hRz
    rw [hz, hsum]
    simp only [Finset.sum_apply, Function.comp_apply]
    change u (centeredTorusRepresentative z) = ∑ a, R a (p a) z
    simp_rw [show ∀ a, R a (p a) z = realCoordinateSynthesis a (p a z) from hRz, hpz]
    ext b
    simp [realCoordinateSynthesis, EuclideanSpace.single, Pi.single_apply]
  let v (i : Fin n) : PeriodicL2 n V := ∑ a, R a (w a i)
  have hv (i : Fin n) : HasPeriodicWeakDerivative i (toTorus (𝕜 := ℝ) u) (v i) := by
    rw [he]
    exact weakDerivative_sum Finset.univ _ _ (fun a _ ↦
      weakDerivative_map (realCoordinateSynthesis a) (hd a i))
  obtain ⟨U, hU, hbound⟩ := exists_h1_of_weakDerivatives _ v hv
  refine ⟨U, hU, hbound.trans ?_⟩
  have hval : ‖toTorus (𝕜 := ℝ) u‖ ≤ ∑ a, ‖p a‖ := by
    rw [he]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ ↦
      norm_realCoordinateSynthesis_l2_le a (p a)))
  have hder (i : Fin n) : ‖v i‖ ≤ ∑ a, ‖w a i‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ ↦
      norm_realCoordinateSynthesis_l2_le a (w a i)))
  calc
    _ ≤ (∑ a, ‖p a‖) + ∑ i, ∑ a, ‖w a i‖ :=
      add_le_add hval (Finset.sum_le_sum (fun i _ ↦ hder i))
    _ = ∑ a, (‖p a‖ + ∑ i, ‖w a i‖) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ∑ a : Fin m, (1 + 2 * Real.pi * n) * fourierSobolevNorm 1 (c a) :=
      Finset.sum_le_sum (fun a _ ↦ hn a)
    _ ≤ ∑ _a : Fin m, (1 + 2 * Real.pi * n) *
        vectorFourierSobolevNorm 1 (l2ComplexInclusion volume u) := by
      exact Finset.sum_le_sum (fun a _ ↦ mul_le_mul_of_nonneg_left
        (fourierSobolevNorm_coordinate_le 1 c a) (by positivity))
    _ = _ := by simp [mul_assoc]

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicEndpoint
