module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.JointJets

/-!
# Half-order symbol bounds on rescaled frequency shells

The full fixed reserve in `app:ch_background:prop:bg-adjoint` differentiates
jointly in (z,x,θ), with η = R θ. A bound proportional to sqrt R, uniform on
fixed frequency shells, is the rescaled form of symbol order one half.
Only primitive normalized amplitude, L,V, and radial scalar jets are inputs.
-/

@[expose] public noncomputable section
open scoped ContDiff
open Filter Topology
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow
variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- Full joint symbol reserve for an actual generated coefficient under any
frequency chart. The primitive order remains `s-k+q`, and the constant is
chosen before the chart, frequency point and high norm
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_expansion_jointJet_bound (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds a)
    (q : ℕ) (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0, ∀ (H T : ℝ), 1 ≤ H → 0 < T →
      ∀ (ν : Euclidean (n-1) → Euclidean (n-1))
        (U : Set (Euclidean (n-1))), IsOpen U →
      (∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞
        (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (ν p.2)) (p,η)) →
      ∀ (p : AdjointSymbolPoint n), p.2 ∈ U →
      (∀ i ≤ ds.length - t.dataDerivatives.length + q,
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (ν p.2)) p‖ ≤ B i * H ^ ((i : ℝ) / T)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + q →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ B i * H ^ ((i : ℝ) / T)) →
      ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (ν p.2)) p‖ ≤
        C * H ^ (((ds.length - t.dataDerivatives.length + q : ℕ) : ℝ) / T) := by
  obtain ⟨e, he, hdirs, hte⟩ := exists_expression_of_mem_adjointDerivativeExpansion
    L V a ha hfield ds t ht
  refine ⟨e.jetConstant B q, e.jetConstant_nonneg B hB q, ?_⟩
  intro H T hH hT ν U hU hlocal p hp hamp hcoeff
  have heq := e.evaluateSymbol_eventuallyEq L V a ν U hU hlocal hfield p hp
  rw [hte, ← (heq.iteratedFDeriv ℝ q).eq_of_nhds]
  have horder : e.degree + q ≤ ds.length - t.dataDerivatives.length + q := by omega
  apply (e.norm_iteratedFDeriv_evaluateSymbol_le_profile L V _ p
    (hlocal p.2 hp p.1)
    (fun d j ↦ (hfield d j).contDiffAt.comp _ contDiffAt_fst)
    _ B hB hH hT hamp ds hcoeff hdirs q horder).trans
  apply mul_le_mul_of_nonneg_left _ (e.jetConstant_nonneg B hB q)
  apply Real.rpow_le_rpow_of_exponent_le hH
  exact div_le_div_of_nonneg_right (by exact_mod_cast horder) hT.le

/-- Finite radial/normalized Leibniz constant for the full symbol reserve
(`app:ch_background:prop:bg-adjoint`). -/
def adjointRadialJetConstant (e : AdjointCoefficientExpression n)
    (W B : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (q+1), (q.choose i : ℝ) * W i * e.jetConstant B (q-i)

/-- Positivity of the full symbol constant (`app:ch_background:prop:bg-adjoint`). -/
theorem adjointRadialJetConstant_nonneg (e : AdjointCoefficientExpression n)
    (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i) (q : ℕ) :
    0 ≤ adjointRadialJetConstant e W B q :=
  Finset.sum_nonneg (fun i _ ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (hW i)) (e.jetConstant_nonneg B hB (q-i)))

/-- Full half-order shell estimate for each actual term. The original angular
amplitude is differentiated jointly in carrier, measurement, and normalized
frequency. Radial scalar jets cost no high norm; the generated coefficient uses
primitive order at most `s-k+q`. Radial and primitive geometry profiles are
explicit inputs, never estimates on generated symbols
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_expansion_rescaled_halfOrder_bound (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (q : ℕ) (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0, ∀ (H T R : ℝ), 1 ≤ H → 0 < T →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U →
      (∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞
        (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (R • p.2)) (p,η)) →
      ∀ (p : AdjointSymbolPoint n), p.2 ∈ U →
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p →
      (∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + q,
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ B i * H ^ ((i : ℝ) / T)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + q →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ B i * H ^ ((i : ℝ) / T)) →
      ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ ≤
        C * H ^ (((ds.length - t.dataDerivatives.length + q : ℕ) : ℝ) / T) *
          Real.sqrt R := by
  rw [adjointDerivativeExpansion_halfOrderRadialFactor] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨e, he, hdirs, hue⟩ := exists_expression_of_mem_adjointDerivativeExpansion
    L V a ha hfield ds u hu
  refine ⟨adjointRadialJetConstant e W B q,
    adjointRadialJetConstant_nonneg e W B hW hB q, ?_⟩
  intro H T R hH hT U hU hlocal p hp hrad hradBound hamp hcoeff
  let aR : AdjointAmplitude n := fun z x η ↦ a z x (R • η)
  have hs := e.contDiffAt_evaluateSymbol L V aR p (hlocal p.2 hp p.1)
    (fun d j ↦ (hfield d j).contDiffAt.comp _ contDiffAt_fst)
  have heq := e.evaluateSymbol_eventuallyEq L V a (R • ·) U hU hlocal hfield p hp
  have heq' : (fun p : AdjointSymbolPoint n ↦
      halfOrderRadialFactor χ (R • p.2) * e.evaluateSymbol L V aR p) =ᶠ[𝓝 p]
      (fun p : AdjointSymbolPoint n ↦
        (frequencyScaleTerm (halfOrderRadialFactor χ) u).amplitude p.1.1 p.1.2 (R • p.2)) := by
    filter_upwards [heq] with v hv
    simp only [frequencyScaleTerm, frequencyScaleAmplitude, hue]
    rw [← hv]
  rw [← (heq'.iteratedFDeriv ℝ q).eq_of_nhds]
  apply (adjoint_local_product_jet_bound q hrad hs).trans
  simp only [adjointRadialJetConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have horder : e.degree + (q-i) ≤ ds.length - u.dataDerivatives.length + q := by omega
  have hb := e.norm_iteratedFDeriv_evaluateSymbol_le_profile L V aR p
    (hlocal p.2 hp p.1) (fun d j ↦ (hfield d j).contDiffAt.comp _ contDiffAt_fst)
    _ B hB hH hT hamp ds hcoeff hdirs (q-i) horder
  have hmono : H ^ (((e.degree + (q-i) : ℕ) : ℝ) / T) ≤
      H ^ (((ds.length - u.dataDerivatives.length + q : ℕ) : ℝ) / T) :=
    Real.rpow_le_rpow_of_exponent_le hH
      (div_le_div_of_nonneg_right (by exact_mod_cast horder) hT.le)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hmono (e.jetConstant_nonneg B hB _))
  calc
    _ ≤ (q.choose i : ℝ) * (W i * Real.sqrt R) *
        (e.jetConstant B (q-i) *
          H ^ (((ds.length - u.dataDerivatives.length + q : ℕ) : ℝ) / T)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hradBound i hiq) (Nat.cast_nonneg _)) hb'
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hW i) (Real.sqrt_nonneg R)))
    _ = _ := by dsimp only [frequencyScaleTerm]; ring

end JanetCartan.ContinuumAdjoint.DerivativeKernels
