module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ReserveInterpolation.Profiles

/-!
# Fixed-reserve estimate from the full transport primitives

This discharges the original-amplitude premise of the fixed-reserve bound,
retaining rho, r(z,Y), and flow in `app:ch_background:prop:bg-adjoint`.
The parent geometric construction supplies the displayed scalar/geometry
profiles on its buffered frequency charts.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow
variable {n : ℕ}

/-- The generated coefficients of the actual normalized transported amplitude
have high-norm exponent (s-k)/s, with a fixed reserve q ≤ Q. All profile
hypotheses concern the primitive geometry and scalar factors before composition.
This is the primitive producer for the raw adjoint Sobolev assembly after
`app:ch_background:eq:bg-derivative-trade`. -/
theorem exists_transportExpansion_fixedReserve_symbol_bound (L V c ρ r Y flow)
    (hc : ContDiff ℝ ∞ (c : AdjointJetPoint n → ℂ))
    (hρ : ContDiff ℝ ∞ (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2))
    (hr : ContDiff ℝ ∞ r)
    (hY : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ (p.1, Y p)))
    (hf : ContDiff ℝ ∞ flow)
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ)
        (normalizedTransportAmplitude c ρ r Y flow)))
    (hs : 0 < ds.length) (Q : ℕ) (C P N A B F D W : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hP : ∀ i, 0 ≤ P i) (hNpos : ∀ i, 0 ≤ N i)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (hF : ∀ i, 0 ≤ F i)
    (hD : ∀ i, 0 ≤ D i) (hW : ∀ i, 0 ≤ W i) :
    ∃ K ≥ 0, ∀ (H R : ℝ), 1 ≤ H →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U →
      (∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞ (adjointAngularGraph R) (p,η)) →
      ∀ (p : AdjointSymbolPoint n), p.2 ∈ U →
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ halfOrderRadialFactor χ (R • p.2)) p →
      (∀ i ≤ Q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i c p.1‖ ≤
          C i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2)
          (adjointAngularGraph R p)‖ ≤ P i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ i, 1 ≤ i → i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (adjointAngularGraph R) p‖ ≤
          N i * H ^ (((i-1-Q : ℕ) : ℝ) / ds.length)) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i r (adjointScalarGraph Y p)‖ ≤ A i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ i, 1 ≤ i → i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (fun v : AdjointJetPoint n ↦ (v.1, Y v)) p.1‖ ≤
          B i * H ^ (((i-1-Q : ℕ) : ℝ) / ds.length)) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i flow p.1‖ ≤
          F i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (branchField L V d j) p.1‖ ≤
          D i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      ∀ q ≤ Q, ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ ≤
        K * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / ds.length) * Real.sqrt R := by
  let J := transportSymbolJetBudget C P N A B F
  have hJ : ∀ i, 0 ≤ J i := transportSymbolJetBudget_nonneg C P N A B F
    hC hP hNpos hA hB hF
  have hsm := contDiff_normalizedTransportAmplitude c ρ r Y flow hc
    (fun θ ↦ hρ.comp (contDiff_fst.prodMk contDiff_const)) hr hY hf
  obtain ⟨K, hK, hbound⟩ := exists_expansion_fixedReserve_symbol_bound L V _ hsm hfield
    ds χ t ht hs Q W (fun i ↦ J i + D i) hW (fun i ↦ add_nonneg (hJ i) (hD i))
  refine ⟨K, hK, ?_⟩
  intro H R hH U hU hN p hp hrad hradBound hcC hρP hNN hrA hYB hfF hcoeff
  have hc' : ContDiff ℝ ∞ (fun p : AdjointSymbolPoint n ↦ c p.1) := hc.comp contDiff_fst
  have hf' : ContDiff ℝ ∞ (fun p : AdjointSymbolPoint n ↦ flow p.1) := hf.comp contDiff_fst
  have hY' : ContDiff ℝ ∞ (adjointScalarGraph Y) := hY.comp contDiff_fst
  apply hbound H R hH U hU
    (fun η hη v ↦ contDiffAt_normalizedTransportAmplitude_symbol c ρ r Y flow R (v,η)
      hc'.contDiffAt hρ.contDiffAt (hN η hη v) hr.contDiffAt hY'.contDiffAt hf'.contDiffAt)
    p hp hrad hradBound
  · intro i hi
    have hb := normalizedTransportAmplitude_symbol_reserve_profile c ρ r Y flow R p Q i
      hc'.contDiffAt hρ.contDiffAt (hN p.2 hp p.1) hr.contDiffAt hY'.contDiffAt hf'.contDiffAt
      C P N A B F hC hP hNpos hA hB hF hH (by exact_mod_cast hs)
      (fun j hj ↦ (adjoint_spatial_jet_lift_bound c hc j p).trans (hcC j (hj.trans hi)))
      (fun j hj ↦ hρP j (hj.trans hi))
      (fun j hj hj' ↦ hNN j hj (hj'.trans hi)) (fun j hj ↦ hrA j (hj.trans hi))
      (fun j hj hj' ↦ (adjoint_spatial_jet_lift_bound _ hY j p).trans
        (hYB j hj (hj'.trans hi))) (fun j hj ↦
        (adjoint_spatial_jet_lift_bound flow hf j p).trans (hfF j (hj.trans hi)))
    exact hb.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hD i))
      (Real.rpow_nonneg (le_trans zero_le_one hH) _))
  · intro d hd j i hi
    exact ((adjoint_spatial_jet_lift_bound _ (hfield d j) i p).trans (hcoeff d hd j i hi)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hJ i))
        (Real.rpow_nonneg (le_trans zero_le_one hH) _))

end JanetCartan.ContinuumAdjoint.DerivativeKernels
