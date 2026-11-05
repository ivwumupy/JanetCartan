module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.NegativeBounds.IntegerBounds
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality

/-!
# Local pairing for the negative retarded estimates

The existing scalar local pairing is applied to the exact finite vector
coordinates. Its positive norm is the infimum over genuine weak extensions.
The retarded application retains the source zero extension and requires the
literal identification of the local output's zero extension. The sector owner
supplies this identification on its source/output mask domains (exchanged for
the adjoint), after forming its actual localized operator. No negative estimate
or extension theorem is assumed here. Sources:
`app:ch_regular_base:eq:negative-duality`, `app:ch_regular:eq:inverse-remainder`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open Pseudodifferential LocalSobolev ArbitraryAccuracy
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin q)
local notation "L²" => Lp V 2 (volume : Measure E)

private theorem coordinate_zeroExtend {U : Set E} (hU : MeasurableSet U)
    (h : LocalL2 U V) (i : Fin q) :
    SmallSupport.zeroExtend hU (finiteL2CoordinateIsometry (volume.restrict U) h i) =
      finiteL2CoordinateIsometry volume (SmallSupport.zeroExtend hU h) i := by
  apply Lp.ext
  have hc := (ae_restrict_iff' hU).mp
    (finiteL2Coordinates_apply_ae (volume.restrict U) h i)
  filter_upwards [SmallSupport.zeroExtend_coeFn hU
    (finiteL2CoordinateIsometry (volume.restrict U) h i),
    finiteL2Coordinates_apply_ae volume (SmallSupport.zeroExtend hU h) i,
    SmallSupport.zeroExtend_coeFn hU h, hc] with x hx hy hz hc
  change (finiteL2CoordinateIsometry volume (SmallSupport.zeroExtend hU h) i) x =
    (SmallSupport.zeroExtend hU h x) i at hy
  change x ∈ U → (finiteL2CoordinateIsometry (volume.restrict U) h i) x = h x i at hc
  rw [hx, hy, hz]
  by_cases hxU : x ∈ U
  · simp only [indicator_of_mem hxU, hc hxU]
  · simp [hxU]

/-- The supported/restriction pairing in the complex vector Fourier norm used
by the retarded constructor. This is the existing scalar weak-extension pairing
summed over isometric coordinates, with explicit fixed factor `q`.
Source: `app:ch_regular_base:eq:negative-duality`.
-/
theorem norm_inner_le_vectorNegativeNorm_mul_restrictionSobolevNorm
    {U : Set E} (hU : MeasurableSet U) (k : ℕ) (h v : LocalL2 U V)
    (hv : MemRestrictionSobolev U k v) :
    ‖inner ℂ h v‖ ≤ ((q : ℝ) * scalarLocalDualityConstant n k) *
      vectorFourierSobolevNorm (-(k : ℝ)) (SmallSupport.zeroExtend hU h) *
        restrictionSobolevNorm U k v := by
  have hC := (scalarLocalDualityConstant_pos n k).le
  have hn : 0 ≤ vectorFourierSobolevNorm (-(k : ℝ)) (SmallSupport.zeroExtend hU h) :=
    norm_nonneg _
  apply le_mul_restrictionSobolevNorm_of_extensions hv (by positivity)
  intro e
  let P : Fin q → V →L[ℝ] ℂ := fun i ↦
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i).restrictScalars ℝ
  have hP (i : Fin q) : ‖P i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x i‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using PiLp.norm_apply_le x i
  have hproj {μ : Measure E} (i : Fin q) (u : Lp V 2 μ) :
      (P i).compLp u = finiteL2CoordinateIsometry μ u i := by rfl
  have hlocal (i : Fin q) :
      restrictionSobolevNorm U k (finiteL2CoordinateIsometry (volume.restrict U) v i) ≤
        e.jetNorm := by
    rw [← hproj]
    exact (restrictionSobolevNorm_le (e.mapCLM (P i))).trans
      ((e.jetNorm_mapCLM_le (P i)).trans
        (mul_le_of_le_one_left e.jetNorm_nonneg (hP i)))
  have hpair (i : Fin q) := norm_inner_le_negativeNorm_mul_restrictionSobolevNorm hU k
    (finiteL2CoordinateIsometry (volume.restrict U) h i)
    (finiteL2CoordinateIsometry (volume.restrict U) v i)
    (show MemRestrictionSobolev U k (finiteL2CoordinateIsometry (volume.restrict U) v i) by
      rw [← hproj]
      exact ⟨e.mapCLM (P i)⟩)
  simp_rw [coordinate_zeroExtend] at hpair
  rw [← finiteL2Coordinates_inner, PiLp.inner_apply]
  calc
    _ ≤ ∑ i, ‖inner ℂ (finiteL2CoordinateIsometry (volume.restrict U) h i)
        (finiteL2CoordinateIsometry (volume.restrict U) v i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin q, (scalarLocalDualityConstant n k *
        vectorFourierSobolevNorm (-(k : ℝ)) (SmallSupport.zeroExtend hU h)) * e.jetNorm := by
      apply Finset.sum_le_sum
      intro i _
      exact (hpair i).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (fourierSobolevNorm_coordinate_le _ _ i) hC)
        (hlocal i) restrictionSobolevNorm_nonneg (mul_nonneg hC hn))
    _ = _ := by simp [mul_assoc]

/-- Apply the retarded negative estimate to the original supported source and
pair its local output with the actual restriction space. The equality `hout`
records the required mask/support identification; it must be proved for the
sector's local realization, using the output mask for `Q` and the source mask
for `Q.adjoint`. The positive estimates are supplied by the primitive signed
constructor. Source: `app:ch_regular_base:eq:negative-duality`.
-/
theorem retarded_local_negative_pairing_of_positive
    (Q : L² →L[ℂ] L²) (o μ : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (C H : ℕ → ℝ) (hC : ∀ s, 0 ≤ C s) (hH : ∀ s, 0 ≤ H s)
    (hpos : ∀ s : ℕ, ∀ T : L² →L[ℂ] L², (T = Q ∨ T = Q.adjoint) →
      ∀ u, MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (T u) ∧
          vectorFourierSobolevNorm (s : ℝ) (T u) ≤ (Δ * C s) *
            (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u + H (s+μ) * ‖u‖))
    (k : ℕ) (T : L² →L[ℂ] L²) (hT : T = Q ∨ T = Q.adjoint)
    {U W : Set E} (hU : MeasurableSet U) (hW : MeasurableSet W)
    (f : LocalL2 U V) (h v : LocalL2 W V)
    (hout : SmallSupport.zeroExtend hW h = T (SmallSupport.zeroExtend hU f))
    (hv : MemRestrictionSobolev W k v) :
    ‖inner ℂ h v‖ ≤
      (((q : ℝ) * scalarLocalDualityConstant n k) *
        (((q : ℝ) * q * (Δ * C (k+o))) * (1 + H (k+o+μ)))) *
      vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) (SmallSupport.zeroExtend hU f) *
        restrictionSobolevNorm W k v := by
  have hb := (retarded_negative_integer_bounds_of_positive Q o μ hΔ C H hC hH
    hpos k T hT (SmallSupport.zeroExtend hU f)).2
  have hp := norm_inner_le_vectorNegativeNorm_mul_restrictionSobolevNorm hW k h v hv
  rw [hout] at hp
  apply hp.trans
  have hc : 0 ≤ (q : ℝ) * scalarLocalDualityConstant n k :=
    mul_nonneg (Nat.cast_nonneg q) (scalarLocalDualityConstant_pos n k).le
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb hc) restrictionSobolevNorm_nonneg

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
