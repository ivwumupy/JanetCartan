module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ReserveInterpolation.Expressions

/-!
# Rescaled half-order bounds with a fixed low baseline

The coefficient excess after `app:ch_background:eq:bg-derivative-trade`
excludes the fixed symbol reserve when q ≤ Q. The radial scalar costs sqrt R,
and its derivatives never consume the high primitive norm.
-/

@[expose] public noncomputable section
open scoped ContDiff
open Filter Topology
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow
variable {n : ℕ}

/-- Fixed-baseline refinement of the actual half-order expansion estimate in
`app:ch_background:prop:bg-adjoint`. The constant precedes H, T, R and all
jet hypotheses; the only symbol hypotheses concern the original normalized
amplitude, L,V, and the fixed radial profile. -/
theorem exists_expansion_rescaled_reserve_bound (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (Q q : ℕ) (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i) :
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
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / T)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + q →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / T)) →
      ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ ≤
        C * H ^ (((ds.length - t.dataDerivatives.length + q - Q : ℕ) : ℝ) / T) *
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
  have hb := e.norm_iteratedFDeriv_evaluateSymbol_le_reserve_profile L V aR p
    (hlocal p.2 hp p.1) (fun d j ↦ (hfield d j).contDiffAt.comp _ contDiffAt_fst)
    Q _ B hB hH hT hamp ds hcoeff hdirs (q-i) horder
  have hmono : H ^ (((e.degree + (q-i) - Q : ℕ) : ℝ) / T) ≤
      H ^ (((ds.length - u.dataDerivatives.length + q - Q : ℕ) : ℝ) / T) :=
    Real.rpow_le_rpow_of_exponent_le hH
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_right horder Q) hT.le)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hmono (e.jetConstant_nonneg B hB _))
  calc
    _ ≤ (q.choose i : ℝ) * (W i * Real.sqrt R) *
        (e.jetConstant B (q-i) *
          H ^ (((ds.length - u.dataDerivatives.length + q - Q : ℕ) : ℝ) / T)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hradBound i hiq) (Nat.cast_nonneg _)) hb'
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hW i) (Real.sqrt_nonneg R)))
    _ = _ := by dsimp only [frequencyScaleTerm]; ring

/-- After a positive-length derivative word, a reserve q ≤ Q does not
increase the coefficient exponent (s-k)/s. This is the coefficient input to
the joint data interpolation after `app:ch_background:eq:bg-derivative-trade`.
The primitive hypotheses use natural subtraction, i.e. max(j-Q,0). -/
theorem exists_expansion_fixedReserve_halfOrder_bound (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (hs : 0 < ds.length) (Q q : ℕ) (hq : q ≤ Q) (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0, ∀ (H R : ℝ), 1 ≤ H →
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
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + q →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ ≤
        C * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / ds.length) *
          Real.sqrt R := by
  obtain ⟨C, hC, hb⟩ := exists_expansion_rescaled_reserve_bound L V a ha hfield
    ds χ t ht Q q W B hW hB
  refine ⟨C, hC, ?_⟩
  intro H R hH U hU hlocal p hp hrad hradBound hamp hcoeff
  have hs' : (0 : ℝ) < ds.length := by exact_mod_cast hs
  apply (hb H ds.length R hH hs' U hU hlocal p hp hrad hradBound hamp hcoeff).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg R)
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hH
  apply div_le_div_of_nonneg_right _ hs'.le
  exact_mod_cast (show ds.length - t.dataDerivatives.length + q - Q ≤
    ds.length - t.dataDerivatives.length by omega)

/-- One constant for the whole fixed symbol reserve q ≤ Q, chosen before H
and the frequency scale. The original primitive profiles are needed only
through s-k+Q. This is the direct symbol input for the raw adjoint operator
assembly in `app:ch_background:prop:bg-adjoint`. -/
theorem exists_expansion_fixedReserve_symbol_bound (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (hs : 0 < ds.length) (Q : ℕ) (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0, ∀ (H R : ℝ), 1 ≤ H →
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
          a p.1.1 p.1.2 (R • p.2)) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + Q →
        ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          branchField L V d j p.1) p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / ds.length)) →
      ∀ q ≤ Q, ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ ≤
        C * H ^ (((ds.length - t.dataDerivatives.length : ℕ) : ℝ) / ds.length) *
          Real.sqrt R := by
  classical
  have hex (q : Fin (Q+1)) := exists_expansion_fixedReserve_halfOrder_bound
    L V a ha hfield ds χ t ht hs Q q (Nat.le_of_lt_succ q.isLt) W B hW hB
  choose C hC hb using hex
  refine ⟨∑ q, C q, Finset.sum_nonneg (fun q _ ↦ hC q), ?_⟩
  intro H R hH U hU hlocal p hp hrad hradBound hamp hcoeff q hq
  let i : Fin (Q+1) := ⟨q, Nat.lt_succ_of_le hq⟩
  have hci : C i ≤ ∑ j, C j := Finset.single_le_sum
    (fun j _ ↦ hC j) (Finset.mem_univ i)
  apply (hb i H R hH U hU hlocal p hp hrad
    (fun j hj ↦ hradBound j (hj.trans hq))
    (fun j hj ↦ hamp j (hj.trans (Nat.add_le_add_left hq _)))
    (fun d hd j l hl ↦ hcoeff d hd j l (hl.trans (Nat.add_le_add_left hq _)))).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hci (Real.rpow_nonneg (le_trans zero_le_one hH) _))
    (Real.sqrt_nonneg R)

/-- The empty derivative word in `app:ch_background:prop:bg-adjoint` needs
only the fixed low amplitude and radial jets. No division by s, high norm,
or assumptions on L,V enter this base case. -/
theorem exists_expansion_zero_halfOrder_bound (L V) (a : AdjointAmplitude n)
    (χ : ℝ → ℝ) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V []
      (frequencyScaleAmplitude (halfOrderRadialFactor χ) a))
    (q : ℕ) (W B : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hB : ∀ i, 0 ≤ B i) :
    ∃ C ≥ 0, ∀ (R : ℝ) (p : AdjointSymbolPoint n),
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (R • p.2)) p →
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ halfOrderRadialFactor χ (R • p.2)) p →
      (∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        a p.1.1 p.1.2 (R • p.2)) p‖ ≤ B i) →
      ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
        t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ ≤ C * Real.sqrt R := by
  simp only [adjointDerivativeExpansion, List.mem_singleton] at ht
  subst t
  refine ⟨adjointLeibnizBudget W B q, adjointLeibnizBudget_nonneg hW hB q, ?_⟩
  intro R p ha hrad hradBound hamp
  apply (adjoint_local_product_jet_bound q hrad ha).trans
  simp only [adjointLeibnizBudget, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    _ ≤ (q.choose i : ℝ) * (W i * Real.sqrt R) * B (q-i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hradBound i hiq) (Nat.cast_nonneg _))
        (hamp (q-i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hW i) (Real.sqrt_nonneg R)))
    _ = _ := by ring

end JanetCartan.ContinuumAdjoint.DerivativeKernels
