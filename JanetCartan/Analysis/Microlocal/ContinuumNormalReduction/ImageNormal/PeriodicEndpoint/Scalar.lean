module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.WeakTransfer
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.FirstDerivatives

/-!
# Local scalar H¹ transfer

The local endpoint in Step 1 of `app:ch_background:prop:bg-frame` uses the
actual quotient-measure maps. Compactly extending tests transfers the weak
derivatives; the physical periodic symbols reconstruct the H¹ norm.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.PeriodicLocalL2 JanetCartan.Pseudodifferential
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicEndpoint

variable {n : ℕ}

/-- The actual periodic H¹ norm is bounded by the sum of the L² norms of
the field and its coordinate weak derivatives. This reconstructs the endpoint
norm in `app:ch_background:prop:bg-frame`, Step 1, with physical `2π` symbols. -/
theorem exists_h1_of_weakDerivatives {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (u : PeriodicL2 n F) (v : Fin n → PeriodicL2 n F)
    (hd : ∀ i, HasPeriodicWeakDerivative i u (v i)) :
    ∃ U : PeriodicSobolevSpace n F 1,
      PeriodicSobolevSpace.toL2 1 U = u ∧ ‖U‖ ≤ ‖u‖ + ∑ i, ‖v i‖ := by
  have hu := (mem_periodicSobolevLevel_one_iff_weakDerivatives u).mpr
    (fun i ↦ ⟨v i, hd i⟩)
  refine ⟨PeriodicSobolevSpace.ofL2 1 u hu, rfl, ?_⟩
  rw [PeriodicSobolevSpace.norm_eq, PeriodicSobolevSpace.toL2_ofL2]
  simp only [Nat.cast_one]
  have he : periodicSobolevNorm 1 u ^ 2 = ‖u‖ ^ 2 + ∑ i, ‖v i‖ ^ 2 := by
    rw [periodicSobolevNorm, Real.sq_sqrt (tsum_nonneg (fun k ↦ by positivity))]
    apply HasSum.tsum_eq
    apply ((hasSum_sq_periodicL2FourierCoeff u).add
      (hasSum_sum (s := Finset.univ) (fun i _ ↦
        hasSum_sq_periodicL2FourierCoeff (v i)))).congr_fun
    intro k
    simp only [periodicL2FourierCoeff_apply, WithLp.prod_norm_sq_eq_of_L2,
      Real.rpow_one]
    change (1 + frequencyNorm k ^ 2) *
      (‖(periodicFourierCoeff u k).1‖ ^ 2 + ‖(periodicFourierCoeff u k).2‖ ^ 2) =
      (‖(periodicFourierCoeff u k).1‖ ^ 2 + ‖(periodicFourierCoeff u k).2‖ ^ 2) +
      ∑ i, (‖(periodicFourierCoeff (v i) k).1‖ ^ 2 +
        ‖(periodicFourierCoeff (v i) k).2‖ ^ 2)
    simp_rw [(hd _).sq_periodicFourierCoeff]
    rw [← Finset.sum_mul, ← frequencyNorm_sq_eq_sum]
    ring
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ ↦ norm_nonneg (v i))
  have hn : 0 ≤ periodicSobolevNorm 1 u := Real.sqrt_nonneg _
  have hv : 0 ≤ ∑ i, ‖v i‖ := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  nlinarith [norm_nonneg u, mul_nonneg (norm_nonneg u) hv]

/-- Supported Euclidean Fourier H¹ data give actual periodic weak derivatives
with a controlled total L² norm. The unit-frequency Euclidean norm incurs the
explicit `1 + 2πn` factor when compared to physical derivatives
(`app:not:fourier`; `app:ch_background:prop:bg-frame`, Step 1). -/
theorem exists_scalar_periodic_derivatives {r : ℝ} (hr : r < 1 / 2)
    (u : EuclideanL2 n ℂ)
    (hs : ∀ᵐ x ∂volume, x ∉ chartBox r → u x = 0)
    (hu : MemFourierSobolev 1 u) :
    ∃ v : Fin n → PeriodicL2 n ℂ,
      (∀ i, HasPeriodicWeakDerivative i (toTorus (𝕜 := ℂ) u) (v i)) ∧
      ‖toTorus (𝕜 := ℂ) u‖ + ∑ i, ‖v i‖ ≤
        (1 + 2 * Real.pi * n) * fourierSobolevNorm 1 u := by
  obtain ⟨χ⟩ := nonempty_sourceCutoff (d := n) hr
  have hu' : MemFourierSobolev ((0 : ℝ) + 1) u := by simpa using hu
  obtain ⟨_, w, hw, _, hn⟩ := hu'.exists_coordinateDerivatives_norm_bounds (by norm_num)
  refine ⟨fun i ↦ toTorus (𝕜 := ℂ) (χ.localize (w i)), ?_, ?_⟩
  · intro i
    apply (hasPeriodicWeakDerivativeList_singleton i _ _).mp
    apply hasPeriodicWeakDerivativeList_of_chart hr χ [i] u (w i) hs
    simpa only [HasEuclideanL2CoordinateDerivative, euclideanCoordinateDerivative,
      EuclideanSpace.basisFun_apply, orderedTransferAction] using (hw i).1
  · exact (add_le_add (norm_toTorusFun_le u)
      (Finset.sum_le_sum (fun i _ ↦ (norm_toTorusFun_le _).trans
        (χ.norm_localize_le (w i))))).trans (by
          simpa only [zero_add, fourierSobolevNorm_zero] using hn)

/-- Scalar local H¹ transfer through the literal normalized-torus map,
for the negative-Sobolev error in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_scalar_periodic_h1 {r : ℝ} (hr : r < 1 / 2)
    (u : EuclideanL2 n ℂ)
    (hs : ∀ᵐ x ∂volume, x ∉ chartBox r → u x = 0)
    (hu : MemFourierSobolev 1 u) :
    ∃ U : PeriodicSobolevSpace n ℂ 1,
      PeriodicSobolevSpace.toL2 1 U = toTorus (𝕜 := ℂ) u ∧
      ‖U‖ ≤ (1 + 2 * Real.pi * n) * fourierSobolevNorm 1 u := by
  obtain ⟨v, hd, hn⟩ := exists_scalar_periodic_derivatives hr u hs hu
  obtain ⟨U, hU, hb⟩ := exists_h1_of_weakDerivatives _ v hd
  exact ⟨U, hU, hb.trans hn⟩

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicEndpoint
