module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Limits
public import Mathlib.Analysis.Convex.Integral

/-!
# Closed Fourier Sobolev balls and elapsed-time integration

For `app:ch_regular_base:lem:retarded-kernel`, the datum-wise integral is taken
in L². The Sobolev ball is closed and convex in that ambient space, so Jensen's
closed-convex-set theorem supplies membership and the exact interval-length
bound. No Sobolev-valued measurability premise is needed. Closedness is proved
from the actual weighted Fourier norms, using the scalar Fourier/Fatou limit
lemma and a convergent subsequence of the finite vector of coordinate norms.

Consumer: the forward and literal-adjoint estimates in `SobolevIntegration`.
-/

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal Topology
open JanetCartan.Pseudodifferential
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SobolevIntegration
@[expose] public noncomputable section
variable {n q : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "V" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)

private theorem weighted_smul_ae (s a : ℝ) (u : L²) :
    weightedL2Fourier s (a • u) =ᵐ[volume] a • weightedL2Fourier s u := by
  have h : 𝓕 (a • u) = a • 𝓕 u :=
    (fourierCLM ℂ L²).map_smul_of_tower a u
  filter_upwards [Lp.coeFn_smul a (𝓕 u)] with ξ hξ
  simp only [weightedL2Fourier, h, hξ, Pi.smul_apply]
  exact smul_comm _ _ _

private theorem scalar_smul (s a : ℝ) (u : L²) (hu : MemFourierSobolev s u) :
    MemFourierSobolev s (a • u) ∧
      fourierSobolevNorm s (a • u) = |a| * fourierSobolevNorm s u := by
  refine ⟨(hu.const_smul a).ae_eq (weighted_smul_ae s a u).symm, ?_⟩
  simp only [fourierSobolevNorm, eLpNorm_congr_ae (weighted_smul_ae s a u),
    eLpNorm_const_smul, ENNReal.toReal_mul, enorm, ENNReal.coe_toReal, coe_nnnorm,
    Real.norm_eq_abs]

private theorem euclidean_norm_mono (a b : EuclideanSpace ℝ (Fin q))
    (h : ∀ i, |a i| ≤ |b i|) : ‖a‖ ≤ ‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (h i) 2)

private theorem vector_add (s : ℝ) (u v : V)
    (hu : MemVectorFourierSobolev s u) (hv : MemVectorFourierSobolev s v) :
    MemVectorFourierSobolev s (u + v) ∧
      vectorFourierSobolevNorm s (u + v) ≤
        vectorFourierSobolevNorm s u + vectorFourierSobolevNorm s v := by
  constructor
  · intro i
    simpa only [map_add, PiLp.add_apply] using (hu i).add (hv i)
  · let a : EuclideanSpace ℝ (Fin q) := WithLp.toLp 2
      (fun i ↦ fourierSobolevNorm s (finiteL2CoordinateIsometry volume u i))
    let b : EuclideanSpace ℝ (Fin q) := WithLp.toLp 2
      (fun i ↦ fourierSobolevNorm s (finiteL2CoordinateIsometry volume v i))
    change ‖_‖ ≤ ‖a‖ + ‖b‖
    apply le_trans (euclidean_norm_mono _ (a + b) ?_) (norm_add_le a b)
    intro i
    simp only [PiLp.add_apply, map_add,
      abs_of_nonneg (fourierSobolevNorm_nonneg _ _)]
    rw [abs_of_nonneg (add_nonneg (fourierSobolevNorm_nonneg _ _)
      (fourierSobolevNorm_nonneg _ _))]
    exact fourierSobolevNorm_add_le (hu i) (hv i)

private theorem vector_smul (s a : ℝ) (u : V) (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev s (a • u) ∧
      vectorFourierSobolevNorm s (a • u) = |a| * vectorFourierSobolevNorm s u := by
  have he : finiteL2CoordinateIsometry volume (a • u) =
      a • finiteL2CoordinateIsometry volume u :=
        (finiteL2CoordinateIsometry volume).toContinuousLinearEquiv.toContinuousLinearMap.map_smul_of_tower a u
  constructor
  · intro i
    simpa only [he, PiLp.smul_apply] using (scalar_smul s a _ (hu i)).1
  · have hn : (WithLp.toLp 2 (fun i ↦
        fourierSobolevNorm s (finiteL2CoordinateIsometry volume (a • u) i)) :
        EuclideanSpace ℝ (Fin q)) =
        |a| • WithLp.toLp 2 (fun i ↦
          fourierSobolevNorm s (finiteL2CoordinateIsometry volume u i)) := by
      ext i
      simpa only [he, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul] using
        (scalar_smul s a _ (hu i)).2
    change ‖_‖ = _
    rw [hn, norm_smul, Real.norm_eq_abs, abs_abs]
    rfl

private theorem vector_zero (s : ℝ) :
    MemVectorFourierSobolev s (0 : V) ∧ vectorFourierSobolevNorm s (0 : V) = 0 := by
  have hf : 𝓕 (0 : L²) = (0 : L²) := (fourierCLM ℂ L²).map_zero
  have hw : weightedL2Fourier (d := n) s 0 =ᵐ[volume] 0 := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure E)] with ξ hξ
    simp only [weightedL2Fourier, hf, hξ, smul_zero, Pi.zero_apply]
  have hm : MemFourierSobolev (d := n) s 0 := (MemLp.zero).ae_eq hw.symm
  have hn : fourierSobolevNorm (d := n) s 0 = 0 := by
    simp [fourierSobolevNorm, eLpNorm_congr_ae hw]
  constructor
  · intro i
    simpa only [map_zero, PiLp.zero_apply] using hm
  · simp [vectorFourierSobolevNorm, matrixFourierSobolevNorm, hn]
    rfl

/-- The actual vector Fourier Sobolev ball is closed in L², retaining both
membership and the Hilbert norm bound. Consumer: elapsed-time integration in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem isClosed_vectorSobolevBall (s B : ℝ) :
    IsClosed {u : V | MemVectorFourierSobolev s u ∧ vectorFourierSobolevNorm s u ≤ B} := by
  apply IsSeqClosed.isClosed
  intro u v hbound hlim
  let b : ℕ → EuclideanSpace ℝ (Fin q) := fun k ↦ WithLp.toLp 2
    (fun i ↦ fourierSobolevNorm s (finiteL2CoordinateIsometry volume (u k) i))
  have hb : ∀ k, b k ∈ Metric.closedBall 0 B := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hbound k).2
  obtain ⟨c, hc, φ, hφ, hbc⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin q)) B).tendsto_subseq hb
  have hcoord (i : Fin q) :
      MemFourierSobolev s (finiteL2CoordinateIsometry volume v i) ∧
        fourierSobolevNorm s (finiteL2CoordinateIsometry volume v i) ≤ c i := by
    apply memFourierSobolev_and_norm_le_of_tendsto s
      (((PiLp.continuous_apply 2 _ i).comp (finiteL2CoordinateIsometry volume).continuous).continuousAt.tendsto.comp
        (hlim.comp hφ.tendsto_atTop))
      (fun k ↦ (hbound (φ k)).1 i)
      ((PiLp.continuous_apply 2 _ i).continuousAt.tendsto.comp hbc)
    intro k
    exact le_rfl
  refine ⟨fun i ↦ (hcoord i).1, ?_⟩
  apply le_trans (euclidean_norm_mono _ c ?_)
    (show ‖c‖ ≤ B by simpa only [Metric.mem_closedBall, dist_zero_right] using hc)
  intro i
  simpa only [PiLp.toLp_apply, abs_of_nonneg (fourierSobolevNorm_nonneg _ _),
    abs_of_nonneg ((fourierSobolevNorm_nonneg _ _).trans (hcoord i).2)] using (hcoord i).2

/-- Convexity of the actual vector Sobolev ball, with no change of norm or
channel-count factor. Consumer: the closed-convex integral argument for
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem convex_vectorSobolevBall (s B : ℝ) :
    Convex ℝ {u : V | MemVectorFourierSobolev s u ∧ vectorFourierSobolevNorm s u ≤ B} := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hua, hna⟩ := vector_smul s a u hu.1
  obtain ⟨hvb, hnb⟩ := vector_smul s b v hv.1
  obtain ⟨hm, hn⟩ := vector_add s _ _ hua hvb
  refine ⟨hm, hn.trans ?_⟩
  rw [hna, hnb, abs_of_nonneg ha, abs_of_nonneg hb]
  calc
    a * vectorFourierSobolevNorm s u + b * vectorFourierSobolevNorm s v ≤
        a * B + b * B := add_le_add (mul_le_mul_of_nonneg_left hu.2 ha)
          (mul_le_mul_of_nonneg_left hv.2 hb)
    _ = B := by rw [← add_mul, hab, one_mul]

/-- An L² Bochner integral of uniformly Sobolev-bounded data belongs to the
same Sobolev space, with exactly the interval-length cost. Only ambient L²
integrability is required: Fourier closedness and convexity supply the result
without an additional Sobolev-valued measurability assumption.
Source: the integration step of `app:ch_regular_base:lem:retarded-kernel`. -/
theorem integral_vectorSobolev_bound {Δ : ℝ} (hΔ : 0 ≤ Δ) (s B : ℝ)
    (f : ℝ → V) (hf : IntegrableOn f (Icc 0 Δ))
    (hbound : ∀ᵐ r ∂volume.restrict (Icc 0 Δ),
      MemVectorFourierSobolev s (f r) ∧ vectorFourierSobolevNorm s (f r) ≤ B) :
    MemVectorFourierSobolev s (∫ r in Icc 0 Δ, f r) ∧
      vectorFourierSobolevNorm s (∫ r in Icc 0 Δ, f r) ≤ Δ * B := by
  rcases hΔ.eq_or_lt with hΔ | hΔ
  · subst Δ
    simpa using (vector_zero (n := n) (q := q) s).imp_right le_of_eq
  · have hvol : volume.real (Icc 0 Δ) = Δ := by
      simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hΔ.le]
    have hpos : volume (Icc 0 Δ) ≠ 0 := by
      simpa only [Real.volume_Icc, sub_zero, ne_eq, ENNReal.ofReal_eq_zero] using not_le.mpr hΔ
    obtain ⟨hm, hn⟩ := (convex_vectorSobolevBall (n := n) (q := q) s B).set_average_mem
      (isClosed_vectorSobolevBall s B) hpos measure_Icc_lt_top.ne hbound hf
    obtain ⟨hsm, hsn⟩ := vector_smul s Δ _ hm
    have he : Δ • (⨍ r in Icc 0 Δ, f r) = ∫ r in Icc 0 Δ, f r := by
      simpa only [hvol] using measure_smul_setAverage (μ := volume) f
        (s := Icc 0 Δ) measure_Icc_lt_top.ne
    rw [he] at hsm hsn
    refine ⟨hsm, ?_⟩
    rw [hsn, abs_of_pos hΔ]
    exact mul_le_mul_of_nonneg_left hn hΔ.le

end
end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SobolevIntegration
