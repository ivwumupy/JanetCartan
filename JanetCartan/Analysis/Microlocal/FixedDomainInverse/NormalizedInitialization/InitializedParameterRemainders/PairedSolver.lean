module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.Conjugation
public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.Operators

/-!
# The original half solver gives the complete paired Fourier estimate

The supplied initializer records its positive Fourier bounds on `Tplus 0`,
the half of the unpaired characteristic and elliptic sum. The complete
`pairedSolver` additionally contains its physical conjugate. Conjugation has
the same Sobolev order with a fixed dimension/order constant; combining both
terms preserves the original additive coefficient profile.

Consumer: `exists_initialized_observed_parameter_remainders` and the same
solver's qualitative joint realization,
`app:ch_response:eq:response-actual-solver-formula`,
`app:ch_regular:eq:parametrix-tame` and `real-sector-normalization`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open Pseudodifferential ResponseTransfer.Complement
open RegularSector NormalizedSolver FiniteMasks.ActualFamily FiniteAssembly
open Characteristic.EvolutionIntegral
open FourierIntegral.LowBounds
open JanetCartan.CharacteristicTransport.CompleteResidual

variable {d : ℕ} {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d (d + 1)

/-- The initializer's literal half-solver positive estimate gives the full
paired solver's positive estimate. The conjugation cost is chosen before the
coefficient field, retarded operator and history, with no derivative or scale
loss and no change in the additive high coefficient factor
(`app:ch_regular:eq:parametrix-tame`,
`app:ch_response:eq:response-actual-solver-formula`). -/
theorem exists_initialized_pairedSolver_fourier_tame_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (C : ℕ → ℝ) (hC : ∀ s, 0 ≤ C s) (Kcoeff : Set E) (shift : ℕ) :
    ∃ D : ℕ → ℝ, (∀ s, 0 ≤ D s) ∧
      ∀ (Q : E → Fin (d + 1) → MetricTensor (d + 1)) (B : E → MetricTensor (d + 1))
        (retarded : H →L[ℂ] H),
      let Tplus := (1 / 2 : ℂ) • (selectedFiniteDirectSolver f L₀ Q B output ho hob retarded +
        (sourceCutMultiplier output ho hob).comp (EllipticComplement.ellipticSolver f hK L₀ Q))
      (∀ (s : ℕ) u, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (Tplus u) ∧
          vectorFourierSobolevNorm (s : ℝ) (Tplus u) ≤
            C s * (vectorFourierSobolevNorm (s : ℝ) u +
              (1 + cNorm Kcoeff (s + shift) Q + cNorm Kcoeff (s + shift) B) * ‖u‖)) →
      ∀ (s : ℕ) u, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (pairedSolver f hK L₀ Q B output ho hob retarded u) ∧
          vectorFourierSobolevNorm (s : ℝ) (pairedSolver f hK L₀ Q B output ho hob retarded u) ≤
            D s * (vectorFourierSobolevNorm (s : ℝ) u +
              (1 + cNorm Kcoeff (s + shift) Q + cNorm Kcoeff (s + shift) B) * ‖u‖) := by
  choose Cstar hCstar hstar using fun s ↦
    FiniteResidualEnvelopes.exists_star_fourierSobolev_constant (d + 1) (d + 1) s
  let D := fun s ↦ C s * (1 + Cstar s + Cstar s ^ 2)
  have hD s : 0 ≤ D s := mul_nonneg (hC s)
    (add_nonneg (add_nonneg zero_le_one (hCstar s).le) (sq_nonneg _))
  refine ⟨D, hD, ?_⟩
  intro Q B retarded Tplus hhalf s u hu
  let high := 1 + cNorm Kcoeff (s + shift) Q + cNorm Kcoeff (s + shift) B
  have hhigh : 0 ≤ high :=
    add_nonneg (add_nonneg zero_le_one (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)
  obtain ⟨hm, hb⟩ := hhalf s u hu
  obtain ⟨hus, hubs⟩ := hstar s u hu
  obtain ⟨hms, hbs⟩ := hhalf s (star u) hus
  obtain ⟨hmss, hbss⟩ := hstar s (Tplus (star u)) hms
  have he : pairedSolver f hK L₀ Q B output ho hob retarded u =
      Tplus u + star (Tplus (star u)) := by
    simp only [pairedSolver, normalizedPair, physicalPairedSectorSum, Finset.sum_singleton]
    rfl
  let a : vectorFourierSobolevLevel (s : ℝ) := ⟨Tplus u, hm⟩
  let b : vectorFourierSobolevLevel (s : ℝ) := ⟨star (Tplus (star u)), hmss⟩
  have hsum : MemVectorFourierSobolev (s : ℝ) (Tplus u + star (Tplus (star u))) :=
    (a + b).property
  have hsumBound : vectorFourierSobolevNorm (s : ℝ) (Tplus u + star (Tplus (star u))) ≤
      vectorFourierSobolevNorm (s : ℝ) (Tplus u) +
        vectorFourierSobolevNorm (s : ℝ) (star (Tplus (star u))) := by
    change vectorFourierSobolevNorm (s : ℝ) (a + b).val ≤
      vectorFourierSobolevNorm (s : ℝ) a.val + vectorFourierSobolevNorm (s : ℝ) b.val
    rw [← norm_vectorWeightedFourier, ← norm_vectorWeightedFourier, ← norm_vectorWeightedFourier, map_add]
    exact norm_add_le _ _
  rw [he]
  refine ⟨hsum, hsumBound.trans ?_⟩
  have hconj : vectorFourierSobolevNorm (s : ℝ) (star (Tplus (star u))) ≤
      Cstar s * (C s * (Cstar s * vectorFourierSobolevNorm (s : ℝ) u + high * ‖u‖)) := by
    apply hbss.trans
    apply mul_le_mul_of_nonneg_left _ (hCstar s).le
    apply hbs.trans
    rw [norm_star]
    exact mul_le_mul_of_nonneg_left (add_le_add hubs le_rfl) (hC s)
  calc
    _ ≤ C s * (vectorFourierSobolevNorm (s : ℝ) u + high * ‖u‖) +
        Cstar s * (C s * (Cstar s * vectorFourierSobolevNorm (s : ℝ) u + high * ‖u‖)) :=
      add_le_add hb hconj
    _ ≤ D s * (vectorFourierSobolevNorm (s : ℝ) u + high * ‖u‖) := by
      have hnorm : 0 ≤ vectorFourierSobolevNorm (s : ℝ) u :=
        (norm_nonneg (vectorWeightedFourier (s : ℝ) ⟨u, hu⟩)).trans_eq
          (norm_vectorWeightedFourier (s : ℝ) ⟨u, hu⟩)
      have h₁ := mul_nonneg (mul_nonneg (hC s) (hCstar s).le)
        hnorm
      have h₂ := mul_nonneg (mul_nonneg (hC s) (sq_nonneg (Cstar s)))
        (mul_nonneg hhigh (norm_nonneg u))
      dsimp only [D]
      nlinarith only [h₁, h₂]

end JanetCartan.FixedDomainInverse
