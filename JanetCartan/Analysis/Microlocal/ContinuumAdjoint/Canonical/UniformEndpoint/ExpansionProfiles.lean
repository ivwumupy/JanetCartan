module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.UniformEndpoint.ExpansionProfiles.FiniteFamily
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ReserveInterpolation.RescaledBounds

/-!
# Uniform reserve bounds for adjoint expansion profiles

For `app:ch_background:prop:bg-adjoint`, the constant is chosen from the finite
syntactic family determined by the derivative word, before the amplitude, radial
cutoff and trade fields. The primitive jet hypotheses and the `s-k+Q` range are
exactly those of `DerivativeKernels.exists_expansion_reserve_symbol_bound`.
The consumer is the parent's uniform raw Sobolev assembly; conic instantiation
and operator estimates are separate obligations.
-/

@[expose] public noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
open ContinuumRow DerivativeKernels
variable {n : ℕ}

/-- One constant for every actual differentiated amplitude and every symbol
derivative through the fixed reserve `Q`, chosen before `L`, `V`, the normalized
amplitude, the radial cutoff and all smoothness and jet hypotheses. The finite
syntactic family from `app:ch_background:eq:bg-derivative-trade` supplies this
uniform strengthening of `DerivativeKernels.exists_expansion_reserve_symbol_bound`
for the finite summation in `app:ch_background:prop:bg-adjoint`.
The empty derivative word is included, and the primitive derivative range stays
`ds.length - t.dataDerivatives.length + Q`. -/
theorem exists_uniform_expansion_reserve_symbol_bound
    (ds : List (InitialCarrierDerivative n)) (Q : ℕ)
    (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0,
      ∀ (L : CarrierParameter → Euclidean n → Euclidean (n-1) → Euclidean n)
        (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
        (a : AdjointAmplitude n)
        (_ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
        (_hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
        (χ : ℝ → ℝ) (t : AdjointDerivativeTerm n),
      t ∈ adjointDerivativeExpansion L V ds
        (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) →
      ∀ (H T R : ℝ), 1 ≤ H → 0 < T →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U →
      (∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞
        (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (R • p.2)) (p,η)) →
      ∀ (p : AdjointSymbolPoint n), p.2 ∈ U →
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p →
      (∀ i ≤ Q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + Q,
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / T)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / T)) →
      ∀ q ≤ Q, ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ ≤
        C * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / T) *
          Real.sqrt R := by
  classical
  let C := ∑ e ∈ (adjointExpansionExpressionProfiles ds).toFinset,
    ∑ q ∈ Finset.range (Q+1), adjointRadialJetConstant e W B q
  have hC : 0 ≤ C := Finset.sum_nonneg fun e _ ↦
    Finset.sum_nonneg fun q _ ↦ adjointRadialJetConstant_nonneg e W B hW hB q
  refine ⟨C, hC, ?_⟩
  intro L V a ha hfield χ t ht H T R hH hT U hU hlocal p hp hrad hradBound hamp hcoeff q hq
  rw [adjointDerivativeExpansion_halfOrderRadialFactor] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨e, hem, he, hdirs, hue⟩ := exists_profile_of_mem_adjointDerivativeExpansion
    L V a ha hfield ds u hu
  have hconst : adjointRadialJetConstant e W B q ≤ C := by
    apply (Finset.single_le_sum
      (fun j _ ↦ adjointRadialJetConstant_nonneg e W B hW hB j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))).trans
    exact Finset.single_le_sum
      (fun f _ ↦ Finset.sum_nonneg fun j _ ↦
        adjointRadialJetConstant_nonneg f W B hW hB j)
      (List.mem_toFinset.mpr hem)
  let aR : AdjointAmplitude n := fun z x η ↦ a z x (R • η)
  have hs := e.contDiffAt_evaluateSymbol L V aR p (hlocal p.2 hp p.1)
    (fun d j ↦ (hfield d j).contDiffAt.comp _ contDiffAt_fst)
  have heq := e.evaluateSymbol_eventuallyEq L V a (R • ·) U hU hlocal hfield p hp
  have heq' : (fun p : AdjointSymbolPoint n ↦
      halfOrderRadialFactor χ (R • p.2) * e.evaluateSymbol L V aR p) =ᶠ[𝓝 p]
      (fun p : AdjointSymbolPoint n ↦
        (frequencyScaleTerm (halfOrderRadialFactor χ) u).amplitude p.1.1 p.1.2
          (R • p.2)) := by
    filter_upwards [heq] with v hv
    simp only [frequencyScaleTerm, frequencyScaleAmplitude, hue]
    rw [← hv]
  calc
    _ ≤ adjointRadialJetConstant e W B q *
        H ^ (((ds.length - u.dataDerivatives.length : ℕ) : ℝ) / T) * Real.sqrt R := by
      rw [← (heq'.iteratedFDeriv ℝ q).eq_of_nhds]
      apply (adjoint_local_product_jet_bound q hrad hs).trans
      simp only [adjointRadialJetConstant, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have horder : e.degree + (q-i) ≤ ds.length - u.dataDerivatives.length + Q := by
        omega
      have hb := e.norm_iteratedFDeriv_evaluateSymbol_le_reserve_profile L V aR p
        (hlocal p.2 hp p.1) (fun d j ↦ (hfield d j).contDiffAt.comp _ contDiffAt_fst)
        Q _ B hB hH hT hamp ds hcoeff hdirs (q-i) horder
      have hmono : H ^ (((e.degree + (q-i) - Q : ℕ) : ℝ) / T) ≤
          H ^ (((ds.length - u.dataDerivatives.length : ℕ) : ℝ) / T) := by
        apply Real.rpow_le_rpow_of_exponent_le hH
        apply div_le_div_of_nonneg_right _ hT.le
        exact_mod_cast (show e.degree + (q-i) - Q ≤
          ds.length - u.dataDerivatives.length by omega)
      have hb' := hb.trans
        (mul_le_mul_of_nonneg_left hmono (e.jetConstant_nonneg B hB _))
      calc
        _ ≤ (q.choose i : ℝ) * (W i * Real.sqrt R) *
            (e.jetConstant B (q-i) *
              H ^ (((ds.length - u.dataDerivatives.length : ℕ) : ℝ) / T)) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (hradBound i (hiq.trans hq)) (Nat.cast_nonneg _))
            hb' (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hW i) (Real.sqrt_nonneg R)))
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (le_trans zero_le_one hH) _))
      (Real.sqrt_nonneg R)

end JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
