module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Chains.Decay

/-!
# Polynomial costs of the literal physical PDOs

The consumer is `finiteChain_observation_rapidDecayAt`'s `hcost` (and,
for an order-zero source/angular multiplier, `hBcost`), in
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
The natural-order estimates are instantiated for `maskedPhysicalPDO`, including
its literal Hilbert adjoint. The first estimate retains the additive high
symbol budget; only the subsequent estimate absorbs its original `L` profile.
The cycle symbol contains the original physical `2π` conversion and both masks.

The primitive inputs are joint smoothness, fixed paired-position support, a
uniform low Frobenius derivative budget and the original high symbol profile.
Their producers are `PdoRealization`'s `GraphNormalAmplitudeBounds` interface,
`AlgebraicSymbols.SupportedSymbols`, `AlgebraicSymbols.MaskedJets`,
`AlgebraicSymbols.SupportedBudgets` and the endpoint transport budgets in
`RegularSector.Characteristic.EndpointPdoBounds`. Actual current-history
substitution remains the regular-sector/finite-family parent's obligation.
No operator estimate or polynomial-cost predicate is an input.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization

open Pseudodifferential FourierIntegral AmplitudeBound
open RegularSector.Characteristic RegularSector.Characteristic.PdoRealization
open CharacteristicTransport.CompleteResidual ResponseTransfer ResponseTransfer.Complement

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)

/-- The SAME masked physical PDO and its literal adjoint have one natural-order
constant, chosen before either mask or symbol, with the additive high budget
unchanged. This is the PDO input to the polynomial absorption in
`app:ch_regular:eq:chain-tail`. -/
theorem exists_maskedPhysicalPDO_integer_tame_constant (R M : ℝ) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χout χsource : E → ℂ) (c : E → E → Mat),
      GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R M →
      ∀ Hhi : ℝ,
        (∀ ξ is, is.length ≤ 2 * (d + 1 + 1) + s → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is
            (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤ Hhi) →
      ∀ W : H →L[ℂ] H,
        (W = maskedPhysicalPDO χout χsource c ∨
          W = (maskedPhysicalPDO χout χsource c).adjoint) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
        vectorFourierSobolevNorm (s : ℝ) (W u) ≤
          C * (vectorFourierSobolevNorm (s : ℝ) u + max 1 Hhi * ‖u‖) := by
  obtain ⟨Cpos, hCpos, hforward⟩ := exists_canonicalGraph_integer_tame_constant_all_data
    (r := q) (Nat.succ_pos d) R s M
  obtain ⟨Cneg, hCneg, hreverse⟩ := exists_canonicalGraph_adjoint_integer_tame_constant_all_data
    (r := q) (Nat.succ_pos d) R s M
  refine ⟨(q : ℝ) * q * (Cpos + Cneg), by positivity, ?_⟩
  intro χout χsource c hb Hhi hhi W hW u hu
  have hnonneg : 0 ≤ vectorFourierSobolevNorm (s : ℝ) u + max 1 Hhi * ‖u‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (norm_nonneg _))
  rcases hW with rfl | rfl
  · obtain ⟨hm, hn⟩ := hforward _ hb.smooth hb.support Hhi hb.derivative hhi u hu
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCneg) (by positivity)) hnonneg)⟩
  · obtain ⟨hm, hn⟩ := hreverse _ hb.smooth hb.support Hhi hb.derivative hhi u hu
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hCpos) (by positivity)) hnonneg)⟩

/-- Absorb the original high symbol profile into frequency, for the same
masked PDO in either literal orientation. Both `s+b` and `D` precede `ρ`,
`L`, the current symbol and the datum. The fixed reserve is `2*(d+2)`;
there is no accuracy parameter or frequency-dependent replacement operator
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_maskedPhysicalPDO_polynomial_fourier_constant
    (R M : ℝ) (s b : ℕ) (A : ℝ) (_hA : 0 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ (χout χsource : E → ℂ) (c : E → E → Mat),
        GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R M →
        (∀ ξ is, is.length ≤ 2 * (d + 1 + 1) + s → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is
            (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤ A * L ^ (s + b)) →
      ∀ W : H →L[ℂ] H,
        (W = maskedPhysicalPDO χout χsource c ∨
          W = (maskedPhysicalPDO χout χsource c).adjoint) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
        vectorFourierSobolevNorm (s : ℝ) (W u) ≤
          D * ρ ^ (s + b) * vectorFourierSobolevNorm (s : ℝ) u := by
  obtain ⟨C, hC, hbound⟩ := exists_maskedPhysicalPDO_integer_tame_constant
    (d := d) (q := q) R M s
  refine ⟨C * (1 + max 1 A), by positivity, ?_⟩
  intro ρ L hL hLρ χout χsource c hb hhi W hW u hu
  obtain ⟨hm, hn⟩ := hbound χout χsource c hb (A * L ^ (s + b)) hhi W hW u hu
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hp : 1 ≤ ρ ^ (s + b) := one_le_pow₀ hρ
  have hhigh : max 1 (A * L ^ (s + b)) ≤ max 1 A * ρ ^ (s + b) := by
    apply max_le
    · exact hp.trans (le_mul_of_one_le_left (by positivity) (le_max_left _ _))
    · exact mul_le_mul (le_max_right _ _)
        (pow_le_pow_left₀ (zero_le_one.trans hL) hLρ _) (by positivity)
        (zero_le_one.trans (le_max_left _ _))
  have hu0 : ‖u‖ ≤ vectorFourierSobolevNorm (s : ℝ) u := by
    simpa only [vectorFourierSobolevNorm_zero] using
      vectorFourierSobolevNorm_mono hu (Nat.cast_nonneg s)
  refine ⟨hm, hn.trans ?_⟩
  calc
    _ ≤ C * (ρ ^ (s + b) * vectorFourierSobolevNorm (s : ℝ) u +
        (max 1 A * ρ ^ (s + b)) * vectorFourierSobolevNorm (s : ℝ) u) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (le_mul_of_one_le_left (norm_nonneg _) hp)
        (mul_le_mul hhigh hu0 (norm_nonneg _) (by positivity))) hC
    _ = _ := by ring

/-- Primitive coordinate symbol profiles give the existing polynomial-cost
predicate on the existing Fourier Sobolev scale, for an actual physical PDO
family and its literal adjoints. In applications the profile is supplied by
the fixed initialized history and `AlgebraicSymbols`/`EndpointPdoBounds`;
no downstream cost or localization estimate is assumed
(`app:ch_regular:eq:chain-tail`). -/
theorem maskedPhysicalPDO_hasPolynomialFourierCost
    {ι : Type*} (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i)
    (χout χsource : E → ℂ) (c : ι → E → E → Mat) (R M : ℝ)
    (hb : ∀ i, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol χout χsource (c i)) R M)
    (b : ℕ) (A : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s)
    (hhi : ∀ s i ξ is, is.length ≤ 2 * (d + 1 + 1) + s → ∀ z,
      ‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol χout χsource (c i) ξ) z‖ ≤ A s * L i ^ (s + b))
    (W : ι → H →L[ℂ] H)
    (hW : ∀ i, W i = maskedPhysicalPDO χout χsource (c i) ∨
      W i = (maskedPhysicalPDO χout χsource (c i)).adjoint) :
    HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale ρ
      (fun i ↦ (W i).toLinearMap.restrictScalars ℝ) := by
  intro s
  obtain ⟨D, hD, hbound⟩ := exists_maskedPhysicalPDO_polynomial_fourier_constant
    (d := d) (q := q) R M s b (A s) (hA s)
  refine ⟨s, (s + b : ℕ), D, hD, ?_⟩
  intro i u hu
  obtain ⟨hm, hn⟩ := hbound (ρ i) (L i) (hL i) (hLρ i)
    χout χsource (c i) (hb i) (hhi s i) (W i) (hW i) u hu
  refine ⟨hm, ?_⟩
  change vectorFourierSobolevScale.gradeNorm s (W i u) ≤ _
  rw [vectorFourierSobolevScale_gradeNorm s hm, vectorFourierSobolevScale_gradeNorm s hu,
    Real.rpow_natCast]
  exact hn

/-- All FOUR literal direct symbols have polynomial Fourier costs, in both
orientations. In particular the negative-order algebraic solver, the endpoint
correction and the full `physicalSymbolApply` branch are retained. The primitive
budgets are for those exact symbols with both masks; this statement supplies
the PDO factors in `app:ch_regular:lem:finite-chain`, not their history profiles. -/
theorem directPDOSymbols_hasPolynomialFourierCost
    {ι : Type*} (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i)
    (χout χsource : E → ℂ)
    (Ac : ι → E → Fin (d + 1) → Mat) (Bc : ι → E → Mat)
    (W₁ : ι → EvolutionIntegral.TwoTimeAmplitude d q)
    (bminus : ι → E → E → Mat) (σ : ι → E → Euclidean d → ℂ) (β : E → ℂ)
    (R M : ℝ)
    (hb : ∀ i k, GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource
      (directPDOSymbols (Ac i) (Bc i) (W₁ i) (bminus i) (σ i) β k)) R M)
    (b : ℕ) (A : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s)
    (hhi : ∀ s i k ξ is, is.length ≤ 2 * (d + 1 + 1) + s → ∀ z,
      ‖matrixAmplitudeCoordinateDerivList is (maskedPhysicalPDOCycleSymbol χout χsource
        (directPDOSymbols (Ac i) (Bc i) (W₁ i) (bminus i) (σ i) β k) ξ) z‖ ≤
          A s * L i ^ (s + b)) :
    ∀ k : Fin 4, ∀ backward : Bool,
      HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale ρ
        (fun i ↦ (if backward then
          (maskedPhysicalPDO χout χsource
            (directPDOSymbols (Ac i) (Bc i) (W₁ i) (bminus i) (σ i) β k)).adjoint
          else maskedPhysicalPDO χout χsource
            (directPDOSymbols (Ac i) (Bc i) (W₁ i) (bminus i) (σ i) β k)).toLinearMap.restrictScalars ℝ) := by
  intro k backward
  apply maskedPhysicalPDO_hasPolynomialFourierCost ρ L hL hLρ χout χsource
    _ R M (fun i ↦ hb i k) b A hA (fun s i ↦ hhi s i k)
  intro i
  cases backward <;> simp

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
