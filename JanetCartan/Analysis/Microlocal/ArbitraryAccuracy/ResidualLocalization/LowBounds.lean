module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Reality

/-!
# Low bounds for the literal complete residual

The LOW estimates of the primitive regularizations pass to their strong
limits. Datum-wise integration constructs exactly the two direct elapsed
operators, with their literal Hilbert adjoints. The three residual terms and
principal defect are retained. These estimates are inputs to the low-norm
part of `finiteChain_observation_rapidDecayAt`, not Sobolev leakage estimates.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization

open FourierIntegral CharacteristicTransport.CompleteResidual
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Realization

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "H" => SpacetimeL2 d q
set_option backward.isDefEq.respectTransparency false

private theorem norm_le_of_strong_regularizations
    (T : H →L[ℂ] H) (Treg : ℕ → H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ j, ‖Treg j‖ ≤ C)
    (hlim : ∀ u, Tendsto (fun j ↦ Treg j u) atTop (𝓝 (T u))) : ‖T‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  apply le_of_tendsto (hlim u).norm
  exact Eventually.of_forall fun j ↦ ((Treg j).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (hbound j) (norm_nonneg u))

/-- The canonical masked PDO retains the LOW bound of its exact primitive
regularizations. The strong-limit input is the actual physical PDO producer's
output, not a localization estimate. Consumer: all four direct PDO branches
in `exists_completeResidual_low_bounds_of_regularizations`
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem norm_maskedPhysicalPDO_le_of_regularizations
    (χout χsource : E → ℂ) (c : E → E → Mat)
    (Preg : ℕ → H →L[ℂ] H) (C : ℝ) (hbound : ∀ j, ‖Preg j‖ ≤ C)
    (hlim : ∀ u, Tendsto (fun j ↦ Preg j u) atTop
      (𝓝 (maskedPhysicalPDO χout χsource c u))) :
    ‖maskedPhysicalPDO χout χsource c‖ ≤ C :=
  norm_le_of_strong_regularizations _ Preg C hbound hlim

/-- Construct the SAME two direct elapsed operators from finite LOW bounds,
measurability and strong limits, and bound the solver, the three-term
residual, and the full principal defect. All four PDO symbols are the literal
`directPDOSymbols`, with both original masks. Literal adjoints keep their
original order and conjugate the coefficient `1/i`.

The inputs are the realization outputs of
`exists_fullGraphFamily_of_wholeImage_phase` and the physical PDO producer;
finite measurability is supplied by `EvolutionIntegral.KernelIdentification`.
The operators agree by their action with those constructed by
`completeResidual_of_selected_physical_chart`. The theorem supplies no
Sobolev or leakage estimate (`app:ch_regular:lem:finite-chain`). -/
theorem exists_completeResidual_low_bounds_of_regularizations
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ)
    (β χout χsource : E → ℂ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (Treg : Bool → ℕ → ℝ → H →L[ℂ] H) (Cg : Bool → ℝ)
    (Preg : Fin 4 → ℕ → H →L[ℂ] H) (Cp : Fin 4 → ℝ)
    (hTbound : ∀ k j r, r ∈ Icc 0 Δ → ‖Treg k j r‖ ≤ Cg k)
    (hPm : ∀ k j, ‖Preg k j‖ ≤ Cp k)
    (hm : ∀ k j u, AEStronglyMeasurable (fun r ↦ Treg k j r u)
      (volume.restrict (Icc 0 Δ)))
    (hmAdj : ∀ k j u, AEStronglyMeasurable (fun r ↦ (Treg k j r).adjoint u)
      (volume.restrict (Icc 0 Δ)))
    (hTlim : ∀ k r, r ∈ Icc 0 Δ → ∀ u, Tendsto (fun j ↦ Treg k j r u) atTop
      (𝓝 (elapsedGraph Ψ (directRetardedAmplitudes A B W₀ W₁ k) χout χsource β r u)))
    (hTlimAdj : ∀ k r, r ∈ Icc 0 Δ → ∀ u, Tendsto (fun j ↦ (Treg k j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ (directRetardedAmplitudes A B W₀ W₁ k)
        χout χsource β r).adjoint u)))
    (hPlim : ∀ k u, Tendsto (fun j ↦ Preg k j u) atTop
      (𝓝 (maskedPhysicalPDO χout χsource (directPDOSymbols A B W₁ bminus σ β k) u))) :
    let P := fun k ↦ maskedPhysicalPDO χout χsource (directPDOSymbols A B W₁ bminus σ β k)
    ∃ Q : Bool → H →L[ℂ] H,
      (∀ k, ‖Q k‖ ≤ Δ * Cg k) ∧ (∀ k, ‖P k‖ ≤ Cp k) ∧
      (∀ k u, Q k u = elapsedGraphIntegral Δ Ψ
        (directRetardedAmplitudes A B W₀ W₁ k) χout χsource β u) ∧
      (∀ k u, (Q k).adjoint u = ∫ r in Icc 0 Δ,
        (elapsedGraph Ψ (directRetardedAmplitudes A B W₀ W₁ k) χout χsource β r).adjoint u) ∧
      let S := Q false + (1 / Complex.I) • P 0
      let R := P 2 + Q true + (1 / Complex.I) • P 3
      ‖S‖ ≤ Δ * Cg false + Cp 0 ∧
      ‖R‖ ≤ Cp 2 + Δ * Cg true + Cp 3 ∧
      ‖(P 1 - ContinuousLinearMap.id ℂ H) + R‖ ≤
        (Cp 1 + 1) + (Cp 2 + Δ * Cg true + Cp 3) ∧
      R.adjoint = (P 2).adjoint + (Q true).adjoint +
        star (1 / Complex.I) • (P 3).adjoint := by
  intro P
  let T k := elapsedGraph Ψ (directRetardedAmplitudes A B W₀ W₁ k) χout χsource β
  have hg (k : Bool) : 0 ≤ Cg k :=
    (norm_nonneg _).trans (hTbound k 0 0 ⟨le_rfl, hΔ⟩)
  have hbound (k : Bool) (r : ℝ) (hr : r ∈ Icc 0 Δ) : ‖T k r‖ ≤ Cg k :=
    norm_le_of_strong_regularizations _ (fun j ↦ Treg k j r) (Cg k)
      (fun j ↦ hTbound k j r hr) (hTlim k r hr)
  have hmT (k : Bool) (u : H) : AEStronglyMeasurable (fun r ↦ T k r u)
      (volume.restrict (Icc 0 Δ)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop (fun j ↦ hm k j u)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hTlim k r hr u
  have hmTA (k : Bool) (u : H) : AEStronglyMeasurable (fun r ↦ (T k r).adjoint u)
      (volume.restrict (Icc 0 Δ)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop (fun j ↦ hmAdj k j u)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hTlimAdj k r hr u
  let Q k := strongIntegral (T k) Δ (Cg k) (hmT k) (hbound k)
  have hQ (k : Bool) : ‖Q k‖ ≤ Δ * Cg k := norm_strongIntegral_le hΔ (hg k) (hmT k) (hbound k)
  have hP (k : Fin 4) : ‖P k‖ ≤ Cp k :=
    norm_maskedPhysicalPDO_le_of_regularizations χout χsource
      (directPDOSymbols A B W₁ bminus σ β k) (Preg k) (Cp k) (hPm k) (hPlim k)
  refine ⟨Q, hQ, hP, fun _ _ ↦ rfl,
    fun k u ↦ strongIntegral_adjoint_apply (hmT k) (hbound k) (hmTA k) u, ?_⟩
  intro S R
  have hunit (k : Fin 4) : ‖(1 / Complex.I) • P k‖ = ‖P k‖ := by simp [norm_smul]
  have hS : ‖S‖ ≤ Δ * Cg false + Cp 0 :=
    (norm_add_le _ _).trans (add_le_add (hQ false) ((hunit 0).le.trans (hP 0)))
  have hR : ‖R‖ ≤ Cp 2 + Δ * Cg true + Cp 3 :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (hP 2) (hQ true))) ((hunit 3).le.trans (hP 3)))
  refine ⟨hS, hR, ?_, ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (hP 1) ContinuousLinearMap.norm_id_le)) hR)
  · simp only [R, map_add, map_smulₛₗ, starRingEnd_apply]

/-- The physical plus pairing costs at most twice the sum of the actual
sector norms; real compression has the same bound. This is the pairing in
`CompleteResidual.Reality`, with no anti-real normalization inserted.
Consumer: the LOW estimate for the real complete residual in the finite
chain (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem norm_physicalPairedSectorSum_le_twice_sum {ι : Type*}
    (s : Finset ι) (S : ι → H →L[ℂ] H) :
    ‖physicalPairedSectorSum s S‖ ≤ 2 * ∑ j ∈ s, ‖S j‖ ∧
    ‖realCompression (physicalPairedSectorSum s S)‖ ≤ 2 * ∑ j ∈ s, ‖S j‖ := by
  let T := ∑ j ∈ s, S j
  have hc : ‖boundedConjugate T‖ ≤ ‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    change ‖star (T (star u))‖ ≤ ‖T‖ * ‖u‖
    simpa only [norm_star] using T.le_opNorm (star u)
  have h : ‖physicalPairedSectorSum s S‖ ≤ 2 * ∑ j ∈ s, ‖S j‖ := by
    calc
      ‖physicalPairedSectorSum s S‖ ≤ ‖T‖ + ‖boundedConjugate T‖ := norm_add_le _ _
      _ ≤ 2 * ‖T‖ := by linarith
      _ ≤ 2 * ∑ j ∈ s, ‖S j‖ := mul_le_mul_of_nonneg_left (norm_sum_le s S) (by norm_num)
  exact ⟨h, (realCompression_norm_le _).trans h⟩

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
