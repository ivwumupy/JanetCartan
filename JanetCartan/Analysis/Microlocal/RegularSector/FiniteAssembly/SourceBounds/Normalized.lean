module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.SourceIdentity
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Multiplier

/-!
# Uniform bounds for the actual normalized complete source

The characteristic and elliptic source sum, externally halved and literally
paired, has its published scalar Fourier representative between the original
physical masks. Its scalar range gives constants independent of the final
radial threshold. These are the terminal order-zero estimates for
`app:ch_regular:eq:chain-tail`; the analytic residual remains separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open FiniteMasks.ActualFamily NormalizedSolver Characteristic.EvolutionIntegral
open FourierIntegral LowBounds Pseudodifferential LocalSobolev
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- The same normalized characteristic/elliptic source and its literal
adjoint have order-zero Fourier bounds. All constants precede the radial
threshold, coefficients and history; the original low shoulder and all three
physical masks are retained (`sector-theorem-identity`, `measured-adjoint`). -/
theorem exists_normalizedSource_uniform_sobolev_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ L : ℝ, f.radialThreshold ≤ L → ∀ s : ℕ,
      ∀ T : H →L[ℂ] H,
        (T = pairedSource f hK L output ho.continuous hob ∨
          T = (pairedSource f hK L output ho.continuous hob).adjoint) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (T u) ∧
        vectorFourierSobolevNorm (s : ℝ) (T u) ≤
          C s * vectorFourierSobolevNorm (s : ℝ) u := by
  let hib := fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2
  let hfb := fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2
  choose Ci hCi hi using fun s ↦ exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) f.inputMask f.inputMask_smooth f.inputMask_compact hib s
  choose Co hCo hf using fun s ↦ exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) f.outputMask f.outputMask_smooth f.outputMask_compact hfb s
  choose Cc hCc hc using fun s ↦ exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) output ho hoc hob s
  refine ⟨fun s ↦ Cc s * Co s * Ci s,
    fun s ↦ mul_nonneg (mul_nonneg (hCc s) (hCo s)) (hCi s), ?_⟩
  intro L hL s T hT u hu
  have hfreq (v : H) (hv : MemVectorFourierSobolev (s : ℝ) v) :
      MemVectorFourierSobolev (s : ℝ) (sourceFourierOperator f hK L v) ∧
      vectorFourierSobolevNorm (s : ℝ) (sourceFourierOperator f hK L v) ≤
        vectorFourierSobolevNorm (s : ℝ) v :=
    scalarPhysicalFrequencyOperator_fourierSobolev_bound _ _ _ _ v hv
  rcases hT with rfl | rfl
  · rw [pairedSource_eq_fourier_composition f hK hL]
    obtain ⟨hmi, hni⟩ := hi s u hu
    obtain ⟨hmf, hnf⟩ := hfreq _ hmi
    obtain ⟨hmo, hno⟩ := hf s _ hmf
    obtain ⟨hmc, hnc⟩ := hc s _ hmo
    refine ⟨hmc, hnc.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left (hno.trans
      (mul_le_mul_of_nonneg_left (hnf.trans hni) (hCo s))) (hCc s)).trans_eq (by ring)
  · rw [pairedSource_adjoint_eq_fourier_composition f hK hL]
    obtain ⟨hmc, hnc⟩ := hc s u hu
    obtain ⟨hmo, hno⟩ := hf s _ hmc
    obtain ⟨hmf, hnf⟩ := hfreq _ hmo
    obtain ⟨hmi, hni⟩ := hi s _ hmf
    refine ⟨hmi, hni.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left (hnf.trans
      (hno.trans (mul_le_mul_of_nonneg_left hnc (hCo s)))) (hCi s)).trans_eq (by ring)

/-- Subtracting ONE identity from the actual normalized source preserves
uniform order-zero control in both literal orientations, including the full
angular and bounded-frequency discrepancy. Consumer:
`finiteChain_observation_rapidDecayAt.hBcost` (`resolved-angular-tail`). -/
theorem exists_normalizedSource_discrepancy_uniform_sobolev_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ L : ℝ, f.radialThreshold ≤ L → ∀ s : ℕ,
      let D := pairedSource f hK L output ho.continuous hob - 1
      ∀ T : H →L[ℂ] H, (T = D ∨ T = D.adjoint) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (T u) ∧
        vectorFourierSobolevNorm (s : ℝ) (T u) ≤
          C s * vectorFourierSobolevNorm (s : ℝ) u := by
  obtain ⟨C, hC, hbound⟩ := exists_normalizedSource_uniform_sobolev_constants f hK output ho hoc hob
  refine ⟨fun s ↦ C s + 1, fun s ↦ add_nonneg (hC s) zero_le_one, ?_⟩
  intro L hL s D T hT u hu
  have hsub (S : H →L[ℂ] H)
      (hS : S = pairedSource f hK L output ho.continuous hob ∨
        S = (pairedSource f hK L output ho.continuous hob).adjoint) :
      MemVectorFourierSobolev (s : ℝ) ((S-1) u) ∧
        vectorFourierSobolevNorm (s : ℝ) ((S-1) u) ≤
          (C s+1)*vectorFourierSobolevNorm (s : ℝ) u := by
    obtain ⟨hm, hn⟩ := hbound L hL s S hS u hu
    obtain ⟨hnm, hnn⟩ := TerminalBounds.neg_bound hu
    obtain ⟨hsm, hsn⟩ := TerminalBounds.add_bound hm hnm
    have he : (S-1) u = S u + -u := by simp [sub_eq_add_neg]
    rw [he]
    refine ⟨hsm, hsn.trans ((add_le_add hn hnn.le).trans_eq (by ring))⟩
  rcases hT with rfl | rfl
  · exact hsub _ (Or.inl rfl)
  · simpa only [D, map_sub, ContinuousLinearMap.adjoint_one] using
      hsub _ (Or.inr rfl)

end JanetCartan.RegularSector.FiniteAssembly
