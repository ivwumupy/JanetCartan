module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.SourceIdentity
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.FrequencySobolev
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.NegativeBounds

/-!
# Signed Sobolev bounds for the normalized complete source

The exact scalar Fourier identity gives order-zero estimates with the original
physical mask order. Its literal adjoint reverses that order. These estimates
provide the single smooth source representative in the complete construction
and retain the angular discrepancy separately from the gain-one residual.
Sources: `resolved-angular-tail`, `sector-theorem-identity`, `measured-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.NormalizedSolver
open FiniteMasks.ActualFamily FourierIntegral LowBounds Pseudodifferential
open Characteristic.EvolutionIntegral
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The actual normalized source and its literal adjoint preserve every
positive and negative integer Sobolev order. All constants precede the final
collar, the varying coefficients, and the input; no source PDE or estimate
is assumed (`resolved-angular-tail`, `measured-adjoint`). -/
theorem exists_pairedSource_order_zero_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (L : ℝ), f.radialThreshold ≤ L → ∀ n : ℕ, ∀ V : H →L[ℂ] H,
      (V = pairedSource f hK L output ho.continuous hob ∨
        V = (pairedSource f hK L output ho.continuous hob).adjoint) →
      (∀ u : H, MemVectorFourierSobolev (n : ℝ) u →
        MemVectorFourierSobolev (n : ℝ) (V u) ∧
        vectorFourierSobolevNorm (n : ℝ) (V u) ≤ C n * vectorFourierSobolevNorm (n : ℝ) u) ∧
      ∀ u : H, MemVectorFourierSobolev (-(n : ℝ)) (V u) ∧
        vectorFourierSobolevNorm (-(n : ℝ)) (V u) ≤
          ((d+1 : ℝ)*(d+1)*C n)*vectorFourierSobolevNorm (-(n : ℝ)) u := by
  let hfo := fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2
  let hfi := fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2
  choose Co hCo hO using fun n ↦ exists_sourceCutMultiplier_fourierSobolev_bound (n := d+1) (r := d+1)
    output ho hoc hob n
  choose Cf hCf hF using fun n ↦ exists_sourceCutMultiplier_fourierSobolev_bound (n := d+1) (r := d+1)
    f.outputMask f.outputMask_smooth f.outputMask_compact hfo n
  choose Ci hCi hI using fun n ↦ exists_sourceCutMultiplier_fourierSobolev_bound (n := d+1) (r := d+1)
    f.inputMask f.inputMask_smooth f.inputMask_compact hfi n
  let C n := Co n * Cf n * Ci n
  have hC n : 0 ≤ C n := mul_nonneg (mul_nonneg (hCo n) (hCf n)) (hCi n)
  refine ⟨C, hC, ?_⟩
  intro L hL n
  have hfreq (u : H) (hu : MemVectorFourierSobolev (n : ℝ) u) :
      MemVectorFourierSobolev (n : ℝ) (sourceFourierOperator f hK L u) ∧
      vectorFourierSobolevNorm (n : ℝ) (sourceFourierOperator f hK L u) ≤
        vectorFourierSobolevNorm (n : ℝ) u :=
    scalarPhysicalFrequencyOperator_fourierSobolev_bound (normalizedSourceMask f hK L)
      (normalizedSourceMask_properties f hK L).1.continuous
      (fun ξ ↦ (Real.norm_of_nonneg ((normalizedSourceMask_properties f hK L).2 ξ).1).trans_le
        ((normalizedSourceMask_properties f hK L).2 ξ).2) (n : ℝ) u hu
  have hpos (V : H →L[ℂ] H)
      (hV : V = pairedSource f hK L output ho.continuous hob ∨
        V = (pairedSource f hK L output ho.continuous hob).adjoint)
      (u : H) (hu : MemVectorFourierSobolev (n : ℝ) u) :
      MemVectorFourierSobolev (n : ℝ) (V u) ∧
      vectorFourierSobolevNorm (n : ℝ) (V u) ≤ C n * vectorFourierSobolevNorm (n : ℝ) u := by
    rcases hV with rfl | rfl
    · rw [pairedSource_eq_fourier_composition f hK hL output ho.continuous hob]
      obtain ⟨him, hin⟩ := hI n u hu
      obtain ⟨hbm, hbn⟩ := hfreq _ him
      obtain ⟨hfm, hfn⟩ := hF n _ hbm
      obtain ⟨hom, hon⟩ := hO n _ hfm
      refine ⟨hom, (hon.trans (mul_le_mul_of_nonneg_left
        (hfn.trans (mul_le_mul_of_nonneg_left (hbn.trans hin) (hCf n))) (hCo n))).trans_eq ?_⟩
      dsimp only [C]
      ring
    · rw [pairedSource_adjoint_eq_fourier_composition f hK hL output ho.continuous hob]
      obtain ⟨hom, hon⟩ := hO n u hu
      obtain ⟨hfm, hfn⟩ := hF n _ hom
      obtain ⟨hbm, hbn⟩ := hfreq _ hfm
      obtain ⟨him, hin⟩ := hI n _ hbm
      refine ⟨him, (hin.trans (mul_le_mul_of_nonneg_left
        (hbn.trans (hfn.trans (mul_le_mul_of_nonneg_left hon (hCf n)))) (hCi n))).trans_eq ?_⟩
      dsimp only [C]
      ring
  intro V hV
  have hadj : V.adjoint = pairedSource f hK L output ho.continuous hob ∨
      V.adjoint = (pairedSource f hK L output ho.continuous hob).adjoint := by
    rcases hV with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (ContinuousLinearMap.adjoint_adjoint _)
  refine ⟨hpos V hV, fun u ↦ ?_⟩
  simpa only [zero_mul, add_zero, mul_one, Nat.cast_add, Nat.cast_one] using
    negativeVectorFourierSobolev_tame_bound_of_adjoint (Nat.cast_nonneg n) (Nat.cast_nonneg n)
      (hC n) (le_refl (0 : ℝ)) V
      (fun v hv ↦ by simpa only [zero_mul, add_zero] using hpos V.adjoint hadj v hv) u

end JanetCartan.RegularSector.NormalizedSolver
