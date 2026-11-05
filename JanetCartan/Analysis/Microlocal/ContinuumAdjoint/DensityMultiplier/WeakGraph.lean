module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.WeakGraph.IntegrationByParts
/-!
# Weak closure of weighted carrier jets

The strong limits produced by `DensityMultiplier.MixedJetClosure` satisfy
weighted integration by parts against every compact smooth complex test.
This identifies the limits as actual carrier derivatives for
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint` on the literal measure `dz dη`.

Only carrier directions are differentiated. Transverse weights move onto
compactly supported tests for the L² limit passage. The parent construction
retains graph-density instantiation, partial Fourier transfer, and norm assembly.
-/

open MeasureTheory Filter
open scoped ContDiff Topology

@[expose] public noncomputable section

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow
variable {n k : ℕ}

private theorem continuous_integral_carrierL2_evaluation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℂ) {ψ : CarrierVariable n → ℂ}
    (hψ : MemLp ψ 2 (carrierMeasure n)) :
    Continuous (fun v : Lp V 2 (carrierMeasure n) ↦
      ∫ x, ψ x * L (v x) ∂carrierMeasure n) := by
  let B : ℂ →L[ℝ] V →L[ℝ] ℂ :=
    (ContinuousLinearMap.mul ℝ ℂ).bilinearComp (ContinuousLinearMap.id ℝ ℂ) L
  have he (v : Lp V 2 (carrierMeasure n)) :
      B.lpPairing (carrierMeasure n) 2 2 (hψ.toLp ψ) v =
        ∫ x, ψ x * L (v x) ∂carrierMeasure n := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with x hx
    change (hψ.toLp ψ) x * L (v x) = _
    rw [hx]
  exact (B.lpPairing (carrierMeasure n) 2 2 (hψ.toLp ψ)).continuous.congr he

/-- The compact-test pairing is continuous on actual jet L² classes, for the
weak-graph limit in `app:ch_background:eq:bg-density-adjoint`. -/
theorem tendsto_integral_test_mul_carrierJet
    {v : ℕ → Lp (CarrierParameter [×k]→L[ℝ] ℂ) 2 (carrierMeasure n)}
    {J : Lp (CarrierParameter [×k]→L[ℝ] ℂ) 2 (carrierMeasure n)}
    (hv : Tendsto v atTop (𝓝 J)) {φ : CarrierVariable n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (w : Fin k → CarrierParameter) :
    Tendsto (fun j ↦ ∫ x, φ x * v j x w ∂carrierMeasure n) atTop
      (𝓝 (∫ x, φ x * J x w ∂carrierMeasure n)) := by
  have : IsFiniteMeasureOnCompacts (carrierMeasure n) := by
    unfold carrierMeasure; infer_instance
  exact ((continuous_integral_carrierL2_evaluation
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ CarrierParameter) ℂ w)
    (hφ.continuous.memLp_of_hasCompactSupport hcφ (p := 2))).tendsto J).comp hv

/-- The unbounded transverse weight moves onto the compactly supported test,
so strong L² convergence suffices for the transposed pairing in
`app:ch_background:eq:bg-density-adjoint`. -/
theorem tendsto_integral_weighted_test_derivative (t : ℕ)
    {v : ℕ → CarrierL2 n} {g : CarrierL2 n} (hv : Tendsto v atTop (𝓝 g))
    {φ : CarrierVariable n → ℂ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (w : Fin k → CarrierParameter) :
    Tendsto (fun j ↦ ∫ x, (etaBesselWeight t x : ℂ) * v j x *
      iteratedFDeriv ℝ k (fun z ↦ φ (z, x.2)) x.1 w ∂carrierMeasure n) atTop
      (𝓝 (∫ x, (etaBesselWeight t x : ℂ) * g x *
        iteratedFDeriv ℝ k (fun z ↦ φ (z, x.2)) x.1 w ∂carrierMeasure n)) := by
  have he (v : CarrierL2 n) : (∫ x, weightedCarrierJet k t φ x w * v x ∂carrierMeasure n) =
      ∫ x, (etaBesselWeight t x : ℂ) * v x *
        iteratedFDeriv ℝ k (fun z ↦ φ (z, x.2)) x.1 w ∂carrierMeasure n := by
    congr 1
    ext x
    simp only [weightedCarrierJet, smul_apply, Complex.real_smul]
    ring
  simpa only [ContinuousLinearMap.id_apply, he, Function.comp_def] using
    ((continuous_integral_carrierL2_evaluation (ContinuousLinearMap.id ℝ ℂ)
      (memLp_weightedCarrierJet_apply k t hφ hcφ w)).tendsto g).comp hv

/-- Strong limits of the actual weighted jets are weak carrier derivatives
on literal product Lebesgue measure (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-density-adjoint`). The only approximation premises
are strong convergence of the tests and of their actual weighted jets.
`exists_densitySymbolTestJet_limit` and `exists_densitySymbolTestL2_limit`
supply these premises for the density symbol; their instantiation belongs to
the parent density-multiplier assembly. All derivatives here are in `z`. -/
theorem weightedCarrierJet_weak_identity_of_tendsto (k t : ℕ)
    (u : ℕ → carrierInitialTestSpace n) (g : CarrierL2 n)
    (J : Lp (CarrierParameter [×k]→L[ℝ] ℂ) 2 (carrierMeasure n))
    (hu : Tendsto (fun j ↦ carrierInitialTestToLp (u j)) atTop (𝓝 g))
    (hJ : Tendsto (fun j ↦ testWeightedCarrierJet k t (u j)) atTop (𝓝 J))
    {φ : CarrierVariable n → ℂ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (w : Fin k → CarrierParameter) :
    (∫ x, φ x * J x w ∂carrierMeasure n) = (-1 : ℂ)^k *
      ∫ x, (etaBesselWeight t x : ℂ) * g x *
        iteratedFDeriv ℝ k (fun z ↦ φ (z, x.2)) x.1 w ∂carrierMeasure n := by
  have he (j : ℕ) :
      (∫ x, φ x * testWeightedCarrierJet k t (u j) x w ∂carrierMeasure n) =
        (-1 : ℂ)^k * ∫ x, (etaBesselWeight t x : ℂ) * carrierInitialTestToLp (u j) x *
          iteratedFDeriv ℝ k (fun z ↦ φ (z, x.2)) x.1 w ∂carrierMeasure n := by
    calc
      _ = ∫ x, φ x * weightedCarrierJet k t (u j).val x w ∂carrierMeasure n := by
        apply integral_congr_ae
        filter_upwards [(memLp_weightedCarrierJet_of_compactSupport k t
          (u j).property.1 (u j).property.2).coeFn_toLp] with x hx
        change testWeightedCarrierJet k t (u j) x = _ at hx
        rw [hx]
      _ = (-1 : ℂ)^k * ∫ x, (etaBesselWeight t x : ℂ) * (u j).val x *
          iteratedFDeriv ℝ k (fun z ↦ φ (z, x.2)) x.1 w ∂carrierMeasure n :=
        integral_test_mul_weightedCarrierJet k t (u j).property.1 (u j).property.2 hφ hcφ w
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [(carrierInitialTest_memLp (u j)).coeFn_toLp] with x hx
        change carrierInitialTestToLp (u j) x = (u j).val x at hx
        rw [hx]
  exact tendsto_nhds_unique (tendsto_integral_test_mul_carrierJet hJ hφ hcφ w)
    (((tendsto_integral_weighted_test_derivative t hu hφ hcφ w).const_mul
      ((-1 : ℂ)^k)).congr' (Eventually.of_forall (fun j ↦ (he j).symm)))

end JanetCartan.ContinuumAdjoint.DensityMultiplier
