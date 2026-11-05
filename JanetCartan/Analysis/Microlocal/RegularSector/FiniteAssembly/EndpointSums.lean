module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.DirectOperators
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SumBounds

/-!
# Gain of the same finite upper-endpoint PDO sum

The exact endpoint certificates below are produced on the same phase and W₁
by `exists_finite_common_retarded_sums`. Sum them with one additive original
coefficient profile and the common sector shift; no endpoint is discarded.
This deduction is consumed by the final three-term residual assembly
(`energy-complete-residual`, `sector-theorem-residual`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.EvolutionIntegral FiniteEvolution FiniteAlgebraic FinitePdo
open FiniteMasks FiniteMasks.ActualFamily Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- Sum the actual endpoint constructor's certificates. In the sector
construction, `Rbox`, `D`, `Dgain` and `Gain` are fixed BEFORE Q and B; the
constant here uses only these data. The premise is the existing per-chart
producer conclusion, never a bound assumed for the assembled endpoint.
Both signs and the literal adjoint are retained (`measured-adjoint`). -/
theorem selectedFiniteEndpointPDO_signed_gain
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (output : E → ℝ)
    (Rbox : f.centers → ℝ) (D Dgain Gain : f.centers → ℕ → ℝ)
    (hDgain : ∀ p n, 1 ≤ Dgain p n) (hGain : ∀ p n, 0 ≤ Gain p n)
    (hendpoint : ∀ p, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) Q B
      (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p L Q (W₁ p)) (Rbox p) M (D p) (Dgain p) (Gain p))
    (n : ℕ) :
    let T := selectedFiniteEndpointPDO f L Q W₁ output
    let cost := ∑ p, ((d+1 : ℝ)*(d+1)*Gain p n)*Dgain p (2*(d+2)+(n+1))
    let high := 1+cNorm (closedBall x RQ) (n+sectorLowOrder d) Q+
      cNorm (closedBall x RQ) (n+sectorLowOrder d) B
    (∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
      MemVectorFourierSobolev (n : ℝ) u →
      MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
      vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
        cost * (vectorFourierSobolevNorm (n : ℝ) u+high*‖u‖)) ∧
    (∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
      MemVectorFourierSobolev (-(n : ℝ)) (V u) ∧
      vectorFourierSobolevNorm (-(n : ℝ)) (V u) ≤
        ((d+1 : ℝ)*(d+1)*cost)*(1+high)*vectorFourierSobolevNorm (-((n : ℝ)+1)) u) := by
  classical
  intro T cost high
  have hcost : 0 ≤ cost := Finset.sum_nonneg fun p _ ↦
    mul_nonneg (mul_nonneg (by positivity) (hGain p n)) (zero_le_one.trans (hDgain p _))
  have hhigh : 0 ≤ high := by
    dsimp [high]
    linarith [cNorm_nonneg (closedBall x RQ) (n+sectorLowOrder d) Q,
      cNorm_nonneg (closedBall x RQ) (n+sectorLowOrder d) B]
  have hp (V : H →L[ℂ] H) (hV : V = T ∨ V = T.adjoint) (u : H)
      (hu : MemVectorFourierSobolev (n : ℝ) u) :
      MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
      vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
        cost * (vectorFourierSobolevNorm (n : ℝ) u+high*‖u‖) := by
    apply finitePhysicalOperator_bound_from_physical
      (fun p ↦ (f.chart p).index)
      (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p L Q (W₁ p))) (n : ℝ) ((n : ℝ)+1) high
      (fun p ↦ ((d+1 : ℝ)*(d+1)*Gain p n)*Dgain p (2*(d+2)+(n+1))) _ V hV u hu
    intro p V hV u hu
    have hb := ((hendpoint p).2.2.2 n).1 u hu
    have hv : MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
        vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
          ((d+1 : ℝ)*(d+1)*Gain p n) * (vectorFourierSobolevNorm (n : ℝ) u+
            (Dgain p (2*(d+2)+(n+1)) *
              (1+cNorm (closedBall x RQ) (n+(2*(d+2)+11)) Q+
                cNorm (closedBall x RQ) (n+(2*(d+2)+11)) B))*‖u‖) := by
      rcases hV with rfl | rfl
      · exact hb.1
      · exact hb.2
    refine ⟨hv.1, hv.2.trans ?_⟩
    have horder : n+(2*(d+2)+11) ≤ n+sectorLowOrder d :=
      Nat.add_le_add_left (sectorLowOrder_bounds d).2.2 n
    have hsmall : 1+cNorm (closedBall x RQ) (n+(2*(d+2)+11)) Q+
        cNorm (closedBall x RQ) (n+(2*(d+2)+11)) B ≤ high :=
      add_le_add (add_le_add le_rfl (cNorm_mono_order horder)) (cNorm_mono_order horder)
    have hdim : 0 ≤ (d+1 : ℝ)*(d+1)*Gain p n := mul_nonneg (by positivity) (hGain p n)
    have hnorm : vectorFourierSobolevNorm (n : ℝ) u ≤
        Dgain p (2*(d+2)+(n+1))*vectorFourierSobolevNorm (n : ℝ) u :=
      le_mul_of_one_le_left (norm_nonneg _) (hDgain p _)
    calc
      _ ≤ ((d+1 : ℝ)*(d+1)*Gain p n)*
          (Dgain p (2*(d+2)+(n+1))*vectorFourierSobolevNorm (n : ℝ) u+
            (Dgain p (2*(d+2)+(n+1))*high)*‖u‖) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hnorm
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall
              (zero_le_one.trans (hDgain p _))) (norm_nonneg u))) hdim
      _ = _ := by ring
  refine ⟨hp, ?_⟩
  intro V hV u
  rcases hV with rfl | rfl
  · simpa only [Nat.cast_add, Nat.cast_one] using negativeVectorFourierSobolev_tame_bound_of_adjoint
      (Nat.cast_nonneg n) (by positivity) hcost hhigh T
      (fun v hv ↦ hp _ (Or.inr rfl) v hv) u
  · simpa only [Nat.cast_add, Nat.cast_one] using negativeVectorFourierSobolev_tame_bound_of_adjoint
      (Nat.cast_nonneg n) (by positivity) hcost hhigh T.adjoint
      (fun v hv ↦ by simpa only [ContinuousLinearMap.adjoint_adjoint] using
        (hp T (Or.inl rfl) v hv)) u

end JanetCartan.RegularSector.FiniteAssembly
