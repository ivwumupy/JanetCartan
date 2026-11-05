module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Density

/-!
# Simultaneous approximation of first L² coordinate derivatives

The extension step for `app:ch_response:eq:direct-envelope-profile` uses compact
smooth source tests converging together with every first coordinate derivative.
The existence of these approximants is proved from the given L² derivatives,
using the established Fourier Sobolev density theorem. No approximation or
output-regularity hypothesis is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Filter LineDeriv
open scoped ContDiff SchwartzMap Topology
namespace JanetCartan.ResponseTransfer.SpatialRealization
open Pseudodifferential AmplitudeBound
variable {n : ℕ}

/-- Coordinate derivatives respect differences in the actual Euclidean L²
classes, for the source approximation in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem coordinateDerivative_sub {i : Fin n}
    {u v du dv : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))}
    (hu : HasEuclideanL2CoordinateDerivative i u du)
    (hv : HasEuclideanL2CoordinateDerivative i v dv) :
    HasEuclideanL2CoordinateDerivative i (u - v) (du - dv) := by
  let J := Lp.toTemperedDistributionCLM ℂ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2
  let D := lineDerivOpCLM ℂ (𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (EuclideanSpace.basisFun (Fin n) ℝ i)
  change D (J (u - v)) = J (du - dv)
  rw [map_sub, map_sub, map_sub]
  exact congrArg₂ (· - ·) hu hv

/-- The coordinate derivative graph is closed under simultaneous L² limits.
This passes actual compact-test identities to all data in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem coordinateDerivative_of_tendsto {i : Fin n}
    {u v : ℕ → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))}
    {U V : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))}
    (h : ∀ k, HasEuclideanL2CoordinateDerivative i (u k) (v k))
    (hu : Tendsto u atTop (𝓝 U)) (hv : Tendsto v atTop (𝓝 V)) :
    HasEuclideanL2CoordinateDerivative i U V := by
  let J := Lp.toTemperedDistributionCLM ℂ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2
  let D := (lineDerivOpCLM ℂ (𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (EuclideanSpace.basisFun (Fin n) ℝ i)).comp J
  exact tendsto_nhds_unique ((D.continuous.tendsto U).comp hu)
    (((J.continuous.tendsto V).comp hv).congr fun k ↦ (h k).symm)

/-- Compact smooth approximation converges simultaneously in L² and in every
first L² coordinate derivative. This is the actual source-density obligation
in `app:ch_response:eq:direct-envelope-profile`, including dimension zero.
The derivative classes in the sequence are the classical derivatives of the
same compact smooth functions. -/
theorem exists_compactSmooth_coordinateDerivatives_tendsto
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (du : Fin n → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdu : ∀ i, HasEuclideanL2CoordinateDerivative i u (du i)) :
    ∃ (g : ℕ → EuclideanSpace ℝ (Fin n) → ℂ) (hg : ∀ k, ContDiff ℝ ∞ (g k))
      (hc : ∀ k, HasCompactSupport (g k)),
      let v : ℕ → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := fun k ↦
        ((hg k).continuous.memLp_of_hasCompactSupport (hc k)).toLp (g k)
      let dv : ℕ → Fin n → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := fun k i ↦
        (((contDiff_euclideanCoordinateDerivList (hg k) [i]).continuous.memLp_of_hasCompactSupport (hasCompactSupport_euclideanCoordinateDerivList (hc k) [i])).toLp
            (euclideanCoordinateDerivList [i] (g k)))
      Tendsto v atTop (𝓝 u) ∧ ∀ i, Tendsto (fun k ↦ dv k i) atTop (𝓝 (du i)) := by
  have hu : MemFourierSobolev (1 : ℝ) u := by
    simpa using (memFourierSobolev_zero u).of_coordinateDerivatives (by norm_num)
      (fun i ↦ memFourierSobolev_zero (du i)) hdu
  obtain ⟨g, hg, hc, hm, hnorm, hlim⟩ := exists_compactSmooth_fourierSobolev_nat_tendsto 1 u (by simpa using hu)
  simp only [Nat.cast_one] at hm hnorm
  refine ⟨g, hg, hc, hlim, ?_⟩
  intro i
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ ↦ dist_nonneg) _
    (show Tendsto (fun k ↦ (2 * Real.pi) * fourierSobolevNorm 1
      (((hg k).continuous.memLp_of_hasCompactSupport (hc k)).toLp (g k) - u)) atTop (𝓝 0) by
        simpa using hnorm.const_mul (2 * Real.pi))
  intro k
  have hd := coordinateDerivative_sub (hasEuclideanL2CoordinateDerivative_toLp
    (g k) (hg k) (hc k) i) (hdu i)
  simpa only [dist_eq_norm, zero_add, fourierSobolevNorm_zero] using
    hd.fourierSobolevNorm_le (s := 0) (by norm_num) (by simpa using (hm k).sub hu)

end JanetCartan.ResponseTransfer.SpatialRealization
