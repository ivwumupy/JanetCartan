module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.OriginalSymbolJets

/-!
# Half-order bounds for the actual adjoint derivative expansion

For `app:ch_background:prop:bg-adjoint`, primitive mixed jets imply bounds for
every generated coefficient. The extra symbol reserve q requires primitive
order at most s-k+q. The constants are independent of the high norm and frequency.
The full frequency reserve is available in `RescaledSymbols`, with its primitive
producer in `OriginalSymbolJets`. Geometric instantiation of the primitive
profiles belongs to the parent proof.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow
variable {n : ℕ}

/-- Mixed-jet estimate for each actual normalized coefficient, using only
primitive jets through `s-k+q` (`app:ch_background:prop:bg-adjoint`). The
constant is chosen before H,T,η and the base point. Thus primitive interpolation
profiles give a one-high estimate whenever `s-k+q ≤ T`. -/
theorem exists_expansion_primitiveJet_bound (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds a)
    (q : ℕ) (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0, ∀ (H T : ℝ), 1 ≤ H → 0 < T →
      ∀ (η : Euclidean (n-1)) (p : AdjointJetPoint n),
      (∀ i ≤ ds.length - t.dataDerivatives.length + q,
        ‖iteratedFDeriv ℝ i (fun p : AdjointJetPoint n ↦ a p.1 p.2 η) p‖ ≤
          B i * H ^ ((i : ℝ) / T)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + q →
        ‖iteratedFDeriv ℝ i (branchField L V d j) p‖ ≤ B i * H ^ ((i : ℝ) / T)) →
      ‖iteratedFDeriv ℝ q (fun p : AdjointJetPoint n ↦ t.amplitude p.1 p.2 η) p‖ ≤
        C * H ^ (((ds.length - t.dataDerivatives.length + q : ℕ) : ℝ) / T) := by
  obtain ⟨e, he, hdirs, hte⟩ := exists_expression_of_mem_adjointDerivativeExpansion
    L V a ha hfield ds t ht
  refine ⟨e.jetConstant B q, e.jetConstant_nonneg B hB q, ?_⟩
  intro H T hH hT η p hamp hcoeff
  have horder : e.degree + q ≤ ds.length - t.dataDerivatives.length + q := by omega
  rw [hte]
  apply (e.norm_iteratedFDeriv_evaluate_le_profile L V a η (ha η) hfield p _ B hB
    hH hT hamp ds hcoeff hdirs q horder).trans
  apply mul_le_mul_of_nonneg_left _ (e.jetConstant_nonneg B hB q)
  apply Real.rpow_le_rpow_of_exponent_le hH
  exact div_le_div_of_nonneg_right (by exact_mod_cast horder) hT.le

/-- Actual half-order frequency growth of every generated coefficient and its
mixed x/z jets. Only the original normalized amplitude and L,V are bounded in
the hypotheses (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_expansion_halfOrder_bound (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (hχ : ∀ r, |χ r| ≤ 1) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (q : ℕ) (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0, ∀ (H T : ℝ), 1 ≤ H → 0 < T →
      ∀ (η : Euclidean (n-1)) (p : AdjointJetPoint n),
      (∀ i ≤ ds.length - t.dataDerivatives.length + q,
        ‖iteratedFDeriv ℝ i (fun p : AdjointJetPoint n ↦ a p.1 p.2 η) p‖ ≤
          B i * H ^ ((i : ℝ) / T)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + q →
        ‖iteratedFDeriv ℝ i (branchField L V d j) p‖ ≤ B i * H ^ ((i : ℝ) / T)) →
      ‖iteratedFDeriv ℝ q (fun p : AdjointJetPoint n ↦ t.amplitude p.1 p.2 η) p‖ ≤
        C * H ^ (((ds.length - t.dataDerivatives.length + q : ℕ) : ℝ) / T) *
          Real.sqrt ‖η‖ := by
  rw [adjointDerivativeExpansion_halfOrderRadialFactor] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨C, hC, hbound⟩ := exists_expansion_primitiveJet_bound
    L V a ha hfield ds u hu q B hB
  refine ⟨C, hC, ?_⟩
  intro H T hH hT η p hamp hcoeff
  obtain ⟨e, _, _, hue⟩ := exists_expression_of_mem_adjointDerivativeExpansion
    L V a ha hfield ds u hu
  have huSmooth : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ u.amplitude p.1 p.2 η) := by
    rw [hue]
    exact e.contDiff_evaluate L V a η (ha η) hfield
  have hrad : ‖halfOrderRadialFactor (n := n) χ η‖ ≤ Real.sqrt ‖η‖ := by
    simp only [halfOrderRadialFactor, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa using mul_le_mul_of_nonneg_right (hχ ‖η‖) (Real.sqrt_nonneg ‖η‖)
  change ‖iteratedFDeriv ℝ q
    (fun p : AdjointJetPoint n ↦ halfOrderRadialFactor χ η • u.amplitude p.1 p.2 η) p‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (huSmooth.contDiffAt.of_le (by simp)), norm_smul]
  exact (mul_le_mul hrad (hbound H T hH hT η p hamp hcoeff) (norm_nonneg _)
    (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
