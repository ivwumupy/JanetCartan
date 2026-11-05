module

public import JanetCartan.Analysis.PhysicalCutoff.Tail
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.QuadratureNorm
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Physical radian Fourier norms of the same reconstructed response

The graded reconstruction estimates give the actual whole-space coordinate
Fourier norm. Paper-v2 `main:prop:pairs` consumes the radian Bessel norm of the
same real Schwartz field, not a periodic norm. The comparison below retains
the field and its Lebesgue measure and costs only an order-dependent constant.
No response norm or derivative estimate is a hypothesis of this conversion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.PhysicalPairs

open Pseudodifferential ArbitraryAccuracy

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "C" => EuclideanSpace ℂ (Fin N)
local notation "V" => EuclideanSpace ℝ (Fin N)

private def coordinate (f : 𝓢(E, C)) (i : Fin N) : 𝓢(E, ℂ) :=
  SchwartzMap.postcompCLM (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin N ↦ ℂ) i) f

private theorem coordinate_apply (f : 𝓢(E, C)) (i : Fin N) (x : E) :
    coordinate f i x = f x i := rfl

private theorem coordinates_toLp (f : 𝓢(E, C)) :
    finiteL2CoordinateIsometry volume (f.toLp 2 volume) =
      WithLp.toLp 2 (fun i ↦ (coordinate f i).toLp 2 volume) := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [finiteL2Coordinates_apply_ae volume (f.toLp 2 volume) i,
    f.coeFn_toLp 2 volume, (coordinate f i).coeFn_toLp 2 volume] with x hx hf hc
  exact hx.trans ((congrArg (fun v : C ↦ v i) hf).trans hc.symm)

private theorem fourier_coordinate (f : 𝓢(E, C)) (i : Fin N) :
    𝓕 (coordinate f i) = coordinate (𝓕 f) i := by
  apply SchwartzMap.ext
  intro ξ
  change 𝓕 (coordinate f i) ξ = 𝓕 f ξ i
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq,
    eval_integral_piLp ((Real.fourierIntegral_convergent_iff ξ).2 f.integrable).eval_piLp]
  rfl

private def weighted (s : ℝ) (f : 𝓢(E, C)) : 𝓢(E, C) :=
  SchwartzMap.smulLeftCLM C (euclideanSobolevWeight s) (𝓕 f)

private theorem coordinate_weighted_norm (s : ℝ) (f : 𝓢(E, C)) (i : Fin N) :
    ‖(coordinate (weighted s f) i).toLp 2 volume‖ =
      fourierSobolevNorm s ((coordinate f i).toLp 2 volume) := by
  rw [SchwartzMap.norm_toLp, fourierSobolevNorm]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [(𝓕 (coordinate f i)).coeFn_toLp 2 volume] with ξ hξ
  rw [fourier_coordinate] at hξ
  simp only [weightedL2Fourier, SchwartzMap.toLp_fourier_eq, fourier_coordinate, hξ,
    coordinate_apply, weighted,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_euclideanSobolevWeight s),
    PiLp.smul_apply]

/-- The vector Fourier norm from the actual inverse calculus is exactly the
weighted Lebesgue L² norm of the SAME Schwartz transform. There is no periodic
identification or dimension loss (`main:prop:pairs`). -/
theorem vectorFourierSobolevNorm_schwartz_eq (s : ℝ) (f : 𝓢(E, C)) :
    vectorFourierSobolevNorm s (f.toLp 2 volume) =
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ξ • 𝓕 f ξ) 2 volume).toReal := by
  have hnorm : ‖(weighted s f).toLp 2 volume‖ =
      vectorFourierSobolevNorm s (f.toLp 2 volume) := by
    rw [← (finiteL2CoordinateIsometry volume).norm_map ((weighted s f).toLp 2 volume),
      coordinates_toLp, vectorFourierSobolevNorm, coordinates_toLp, matrixFourierSobolevNorm,
      PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [coordinate_weighted_norm, Real.norm_eq_abs, sq_abs]
  rw [← hnorm, SchwartzMap.norm_toLp]
  congr 2
  exact SchwartzMap.smulLeftCLM_apply (hasTemperateGrowth_euclideanSobolevWeight s) _

private theorem physicalWeight_le (r : ℕ) (ξ : E) :
    euclideanSobolevWeight r ((2 * Real.pi) • ξ) ≤
      (2 * Real.pi) ^ r * euclideanSobolevWeight r ξ := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hpone : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hscale : ((2 * Real.pi) ^ 2) ^ ((r : ℝ) / 2) = (2 * Real.pi) ^ r := by
    rw [← Real.rpow_natCast (2 * Real.pi) 2, ← Real.rpow_mul hp.le]
    simp only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * ((r : ℝ) / 2) = r by ring, Real.rpow_natCast]
  unfold euclideanSobolevWeight
  rw [norm_smul, Real.norm_of_nonneg hp.le]
  calc
    _ ≤ ((2 * Real.pi)^2 * (1 + ‖ξ‖^2)) ^ ((r : ℝ)/2) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      nlinarith [sq_nonneg (2 * Real.pi - 1)]
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity), hscale]

/-- The physical radian norm of the SAME Schwartz field is controlled by the
actual inverse's Fourier norm at the SAME order. Only `(2π)^r` is lost; no
carrier, separation, history or accuracy factor appears (`main:prop:pairs`). -/
theorem physicalWeightedNorm_le_vectorFourierSobolevNorm (r : ℕ) (f : 𝓢(E, C)) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) • 𝓕 f ξ)
      2 volume).toReal ≤
      (2 * Real.pi) ^ r * vectorFourierSobolevNorm r (f.toLp 2 volume) := by
  let g := weighted (r : ℝ) f
  let p : 𝓢(E, C) := SchwartzMap.smulLeftCLM C
    (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ)) (𝓕 f)
  have hg : (g : E → C) = fun ξ ↦ euclideanSobolevWeight r ξ • 𝓕 f ξ :=
    SchwartzMap.smulLeftCLM_apply (hasTemperateGrowth_euclideanSobolevWeight r) _
  have hp : (p : E → C) = fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) • 𝓕 f ξ :=
    SchwartzMap.smulLeftCLM_apply (PhysicalCutoff.hasTemperateGrowth_physicalWeight r) _
  have hpNorm : ‖p.toLp 2 volume‖ =
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) • 𝓕 f ξ)
        2 volume).toReal := by rw [SchwartzMap.norm_toLp, hp]
  rw [← hpNorm]
  calc
    ‖p.toLp 2 volume‖ ≤ ‖(((2 * Real.pi)^r) • g).toLp 2 volume‖ := by
      rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
      apply ENNReal.toReal_mono ((((2 * Real.pi)^r) • g).memLp 2 volume).eLpNorm_ne_top
      apply eLpNorm_mono p.continuous.aestronglyMeasurable
      intro ξ
      rw [hp, smul_apply, hg, norm_smul, norm_smul, norm_smul,
        Real.norm_of_nonneg (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) r),
        Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le,
        Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (physicalWeight_le r ξ) (norm_nonneg (𝓕 f ξ))
    _ = _ := by
      change ‖SchwartzMap.toLpCLM ℝ C 2 volume (((2 * Real.pi)^r) • g)‖ = _
      rw [map_smul, norm_smul,
        Real.norm_of_nonneg (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) r)]
      congr 1
      change ‖g.toLp 2 volume‖ = _
      rw [SchwartzMap.norm_toLp, hg, vectorFourierSobolevNorm_schwartz_eq]

/-- Complex inclusion of the real Schwartz output has exactly the real
component norm used by the original inverse. The original representatives and
measure are unchanged (`main:prop:pairs`). -/
theorem vectorFourierSobolevNorm_complexify_eq (s : ℝ) (u : 𝓢(E, V)) :
    vectorFourierSobolevNorm s ((PhysicalCutoff.complexify u).toLp 2 volume) =
      componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin N) ℝ) s
        (u.toLp 2 volume) := by
  have he (i : Fin N) :
      finiteL2CoordinateIsometry volume ((PhysicalCutoff.complexify u).toLp 2 volume) i =
        realComponentL2 (EuclideanSpace.basisFun (Fin N) ℝ) i (u.toLp 2 volume) := by
    apply Lp.ext
    filter_upwards [finiteL2Coordinates_apply_ae volume
        ((PhysicalCutoff.complexify u).toLp 2 volume) i,
      (PhysicalCutoff.complexify u).coeFn_toLp 2 volume,
      realComponentL2_coeFn (EuclideanSpace.basisFun (Fin N) ℝ) i (u.toLp 2 volume),
      u.coeFn_toLp 2 volume] with x hx hc hr hu
    change (finiteL2CoordinateIsometry volume
      ((PhysicalCutoff.complexify u).toLp 2 volume) i) x = _ at hx
    rw [hx, hc, hr, hu, EuclideanSpace.basisFun_inner]
    rfl
  simp only [vectorFourierSobolevNorm, matrixFourierSobolevNorm,
    PiLp.norm_eq_of_L2, Real.norm_eq_abs, sq_abs,
    componentFourierSobolevNorm, he]

/-- Direct transfer of the actual reconstructed complex-coordinate profile to
the physical real field (`main:prop:pairs`). The premises specify only the
same representatives and Sobolev membership, not an output size estimate. -/
theorem physicalWeightedNorm_le_matrix_representative (r : ℕ) (u : 𝓢(E, V))
    (v : E → C) (out : PiLp 2 (fun _ : Fin N ↦ Lp ℂ 2 (volume : Measure E)))
    (hrep : ∀ i, out i =ᵐ[volume] fun x ↦ v x i)
    (hreal : ∀ x, u x = euclideanRealPart (v x))
    (hmem : MemMatrixFourierSobolev r out) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
      𝓕 (PhysicalCutoff.complexify u) ξ) 2 volume).toReal ≤
      (2 * Real.pi) ^ r * matrixFourierSobolevNorm r out := by
  let z := (finiteL2CoordinateIsometry volume).symm out
  have hz : finiteL2CoordinateIsometry volume z = out :=
    (finiteL2CoordinateIsometry volume).apply_symm_apply out
  have hzrep : z =ᵐ[volume] v :=
    (finiteL2CoordinateIsometry_ae_iff volume z v).mpr (by simpa only [hz] using hrep)
  have huz : u.toLp 2 volume = l2RealPart volume z := by
    apply Lp.ext
    filter_upwards [u.coeFn_toLp 2 volume, euclideanRealPart.coeFn_compLpL z, hzrep]
      with x hu hr hv
    exact hu.trans ((hreal x).trans ((congrArg euclideanRealPart hv).symm.trans hr.symm))
  have hzm : MemVectorFourierSobolev r z := by
    simpa only [MemVectorFourierSobolev, hz] using hmem
  calc
    _ ≤ (2 * Real.pi)^r *
        vectorFourierSobolevNorm r ((PhysicalCutoff.complexify u).toLp 2 volume) :=
      physicalWeightedNorm_le_vectorFourierSobolevNorm r _
    _ = (2 * Real.pi)^r *
        componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin N) ℝ) r
          (l2RealPart volume z) := by rw [vectorFourierSobolevNorm_complexify_eq, huz]
    _ ≤ (2 * Real.pi)^r * vectorFourierSobolevNorm r z :=
      mul_le_mul_of_nonneg_left
        (ResponseTransfer.SourceNegative.componentFourierSobolevNorm_l2RealPart_le hzm)
        (by positivity)
    _ = _ := by rw [vectorFourierSobolevNorm, hz]

end JanetCartan.PhysicalPairs
