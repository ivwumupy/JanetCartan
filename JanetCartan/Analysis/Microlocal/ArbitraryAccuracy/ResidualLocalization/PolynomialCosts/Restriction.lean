module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.SobolevScale
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Scalar
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Projection
public import JanetCartan.Analysis.Sobolev.Local.Cutoff
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Chains.Decay

/-!
# Restriction and fixed interior masks for polynomial costs

The input comparison needed by the actual-factor costs in
`app:ch_regular:lem:finite-chain` is proved from genuine weak extensions.
Zero extension is used at positive order only AFTER a fixed interior bump.
The producers are the all-order weak Leibniz theorem in `Local.Cutoff` and
`scalarFourierSobolev_extension_bounds`; no Sobolev multiplier bound is assumed.
The downstream consumer is `finiteChain_observation_rapidDecayAt`'s `hcost`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization

open LocalSobolev Pseudodifferential ResponseTransfer

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Genuine complex vector weak extensions control the actual Fourier Sobolev
norm, with a constant chosen before the domain and the extension. This is the
input comparison for the restriction-scale polynomial costs of
`app:ch_regular:eq:chain-tail`. -/
theorem exists_vector_extension_fourier_constant (n r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (EuclideanSpace ℝ (Fin n)))
      (u : LocalL2 U (EuclideanSpace ℂ (Fin r))) (e : SobolevExtension U s u),
      MemVectorFourierSobolev (s : ℝ) e.toL2 ∧
      vectorFourierSobolevNorm (s : ℝ) e.toL2 ≤ C * e.jetNorm := by
  obtain ⟨C, hC, hscalar⟩ := scalarFourierSobolev_extension_bounds n s
  refine ⟨((r : ℝ) + 1) * C, by positivity, ?_⟩
  intro U u e
  let proj (i : Fin r) := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).restrictScalars ℝ
  have hproj (i : Fin r) : ‖proj i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x i‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using PiLp.norm_apply_le x i
  have heq (i : Fin r) : (e.mapCLM (proj i)).toL2 =
      finiteL2CoordinateIsometry volume e.toL2 i := by
    rw [e.toL2_mapCLM]
    apply Lp.ext
    filter_upwards [(proj i).coeFn_compLp e.toL2,
      finiteL2Coordinates_apply_ae volume e.toL2 i] with x hx hy
    exact hx.trans hy.symm
  have hcoord (i : Fin r) := hscalar U _ (e.mapCLM (proj i))
  simp only [heq] at hcoord
  refine ⟨fun i ↦ (hcoord i).1, ?_⟩
  calc
    _ ≤ ∑ i : Fin r, fourierSobolevNorm (s : ℝ)
        (finiteL2CoordinateIsometry volume e.toL2 i) := matrixFourierSobolevNorm_le_sum _ _
    _ ≤ ∑ _ : Fin r, C * e.jetNorm := by
      apply Finset.sum_le_sum
      intro i _
      exact (hcoord i).2.trans (mul_le_mul_of_nonneg_left
        ((e.jetNorm_mapCLM_le (proj i)).trans
          (mul_le_of_le_one_left e.jetNorm_nonneg (hproj i))) hC.le)
    _ ≤ (((r : ℝ) + 1) * C) * e.jetNorm := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      nlinarith [mul_nonneg hC.le e.jetNorm_nonneg]

/-- The literal zero extension of a fixed interior bump has Fourier membership
and a finite norm controlled by the genuine input restriction norm. The constant
precedes the domain and data, and the bump is independent of frequency and
accuracy (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_bump_zeroExtension_fourier_constant {n r : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (χ : ContDiffBump x) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U),
      tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ U →
      ∀ u : LocalL2 U (EuclideanSpace ℂ (Fin r)), MemRestrictionSobolev U s u →
      let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
      MemVectorFourierSobolev (s : ℝ) z ∧
      vectorFourierSobolevNorm (s : ℝ) z ≤ C * restrictionSobolevNorm U s u := by
  obtain ⟨A, hA, hweak⟩ := exists_bump_zeroExtension_weakJet_bound
    (F := EuclideanSpace ℂ (Fin r)) χ s
  obtain ⟨B, hB, hfourier⟩ := exists_vector_extension_fourier_constant n r s
  refine ⟨B * A, mul_pos hB (zero_lt_one.trans_le hA), ?_⟩
  intro U hU hs u hu z
  obtain ⟨J, hJ, hJmem, hJbound⟩ := hweak U hU hs u hu
  let v : LocalL2 univ (EuclideanSpace ℂ (Fin r)) := ((Lp.memLp z).restrict univ).toLp z
  let e : SobolevExtension univ s v :=
    { toFun := z
      jet := J
      weakJet := hJ
      memLp_fun := Lp.memLp z
      memLp_jet := hJmem
      restrict_eq := (MemLp.coeFn_toLp _).symm }
  have he : e.toL2 = z := Lp.ext e.toL2_coeFn
  obtain ⟨hm, hn⟩ := hfourier univ v e
  rw [he] at hm hn
  refine ⟨hm, hn.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hJbound hB.le).trans_eq (mul_assoc _ _ _).symm

/-- An existing fixed local bump has cost exponent zero on the actual
restriction Sobolev scale. This covers fixed interior source/output masks in
`app:ch_regular:lem:finite-chain` for real as well as complex fibers. -/
theorem bumpL2_hasPolynomialRestrictionCost
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ι : Type*} (ρ : ι → ℝ) {x : EuclideanSpace ℝ (Fin n)} (χ : ContDiffBump x)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (hs : tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ U) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ
      (fun _ ↦ (SmallSupport.bumpL2 (F := F) (μ := volume.restrict U)
        (p := 2) le_rfl χ).toLinearMap) := by
  intro s
  obtain ⟨C, hC, hbound⟩ := exists_bumpL2_sobolev_bound (F := F) χ s
  refine ⟨s, 0, C, zero_le_one.trans hC, ?_⟩
  intro i u hu
  obtain ⟨hm, hn⟩ := hbound U hU hs u hu
  refine ⟨hm, ?_⟩
  change (restrictionSobolevScale U F hU).gradeNorm s
    (SmallSupport.bumpL2 (p := 2) le_rfl χ u) ≤ _
  rw [restrictionSobolevScale_gradeNorm hU hm, restrictionSobolevScale_gradeNorm hU hu]
  simpa only [Real.rpow_zero, mul_one] using hn

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
