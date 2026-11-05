module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.RescaledSymbols
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.OriginalAmplitude

/-!
# Primitive producer for the full angular symbol reserve

The original amplitude for `app:ch_background:prop:bg-adjoint` retains the
angular mask rho(z,eta-hat), scalar r(z,Y(z,x)), and flow factor. All three
are differentiated in the full joint symbol variables. The two compositions
are bounded from their primitive jets using the shared partition API.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CompositionBounds FourierIntegral.NormalOneHigh
variable {n : ℕ}

/-- Multiplication preserves the total primitive interpolation exponent.
This is applied to all factors of the original adjoint amplitude, including
the angular mask and flow factor (`app:ch_background:prop:bg-adjoint`). -/
private theorem local_product_profile {f g : AdjointSymbolPoint n → ℂ}
    (p : AdjointSymbolPoint n) (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (q : ℕ) (A B : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i)
    {H T : ℝ} (hH : 0 < H)
    (hfa : ∀ i ≤ q, ‖iteratedFDeriv ℝ i f p‖ ≤ A i * H ^ ((i : ℝ) / T))
    (hgb : ∀ i ≤ q, ‖iteratedFDeriv ℝ i g p‖ ≤ B i * H ^ ((i : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p ↦ f p * g p) p‖ ≤
      adjointLeibnizBudget A B q * H ^ ((q : ℝ) / T) := by
  apply (adjoint_local_product_jet_bound q hf hg).trans
  unfold adjointLeibnizBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    _ ≤ (q.choose i : ℝ) * (A i * H ^ ((i : ℝ) / T)) *
        (B (q-i) * H ^ (((q-i : ℕ) : ℝ) / T)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfa i hiq) (Nat.cast_nonneg _))
        (hgb (q-i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i) (Real.rpow_nonneg hH.le _)))
    _ = _ := by
      rw [show (q.choose i : ℝ) * (A i * H ^ ((i : ℝ) / T)) *
          (B (q-i) * H ^ (((q-i : ℕ) : ℝ) / T)) =
          ((q.choose i : ℝ) * A i * B (q-i)) *
            (H ^ ((i : ℝ) / T) * H ^ (((q-i : ℕ) : ℝ) / T)) by ring,
        ← Real.rpow_add hH, ← add_div, ← Nat.cast_add, Nat.add_sub_of_le hiq]

/-- The scalar pullback profile for the actual composition `r(z,Y(z,x))`.
The initial scalar uses its full derivative order; each positive-order
derivative of the geometry map uses its baseline-one excess. The shared
partition identity makes the combined exponent exactly q/T, including q=0
(`app:ch_background:prop:bg-adjoint`). -/
private theorem local_pullback_profile
    (Y : AdjointSymbolPoint n → CarrierParameter × Euclidean (n-1))
    (r : CarrierParameter × Euclidean (n-1) → ℂ) (p : AdjointSymbolPoint n)
    (hY : ContDiffAt ℝ ∞ Y p) (hr : ContDiffAt ℝ ∞ r (Y p)) (q : ℕ)
    (A B : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) {H T : ℝ} (hH : 0 < H)
    (hrA : ∀ i ≤ q, ‖iteratedFDeriv ℝ i r (Y p)‖ ≤ A i * H ^ ((i : ℝ) / T))
    (hYB : ∀ i, 1 ≤ i → i ≤ q →
      ‖iteratedFDeriv ℝ i Y p‖ ≤
        B i * H ^ (((i-1 : ℕ) : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦ r (Y p)) p‖ ≤
      compositionBudget A B q * H ^ ((q : ℝ) / T) := by
  apply (norm_iteratedFDeriv_comp_le_partition_sum
    (hr.of_le (show (q : ℕ∞ω) ≤ ∞ by simp))
    (hY.of_le (show (q : ℕ∞ω) ≤ ∞ by simp)) (le_refl q)).trans
  unfold compositionBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro π _
  calc
    _ ≤ (A π.length * H ^ ((π.length : ℝ) / T)) *
        ∏ i, B (π.partSize i) * H ^ (((π.partSize i - 1 : ℕ) : ℝ) / T) :=
      mul_le_mul (hrA _ π.length_le)
        (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦
          hYB _ (π.partSize_pos i) (π.partSize_le i)))
        (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
        (mul_nonneg (hA _) (Real.rpow_nonneg hH.le _))
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hH,
        mul_mul_mul_comm, ← Real.rpow_add hH, ← Finset.sum_div, ← add_div,
        ← Nat.cast_sum, ← Nat.cast_add]
      rw [Nat.add_comm π.length, FlowForcing.sum_partSize_sub_one_add_length]


/-- Actual angular substitution in the shell symbol of
`app:ch_background:eq:bg-T`. Carrier derivatives act on its first coordinate. -/
def adjointAngularGraph (R : ℝ) (p : AdjointSymbolPoint n) :
    CarrierParameter × Euclidean (n-1) :=
  (p.1.1, ‖R • p.2‖⁻¹ • (R • p.2))

/-- Actual transported-scalar substitution, independent of frequency
(`app:ch_background:prop:bg-adjoint`). -/
def adjointScalarGraph (Y : AdjointJetPoint n → Euclidean (n-1))
    (p : AdjointSymbolPoint n) : CarrierParameter × Euclidean (n-1) :=
  (p.1.1, Y p.1)

/-- Local smoothness of the actual angular/transport amplitude in full symbol
variables. No global smoothness at zero frequency is required
(`app:ch_background:prop:bg-adjoint`). -/
theorem contDiffAt_normalizedTransportAmplitude_symbol (c ρ r Y flow) (R : ℝ)
    (p : AdjointSymbolPoint n)
    (hc : ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ c p.1) p)
    (hρ : ContDiffAt ℝ ∞ (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2)
      (adjointAngularGraph R p))
    (hN : ContDiffAt ℝ ∞ (adjointAngularGraph R) p)
    (hr : ContDiffAt ℝ ∞ r (adjointScalarGraph Y p))
    (hY : ContDiffAt ℝ ∞ (adjointScalarGraph Y) p)
    (hf : ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ flow p.1) p) :
    ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
      normalizedTransportAmplitude c ρ r Y flow p.1.1 p.1.2 (R • p.2)) p :=
  ((hc.mul (hρ.comp p hN)).mul (hr.comp p hY)).mul hf

/-- Producer of the full primitive amplitude profile for
`exists_expansion_rescaled_halfOrder_bound`. Jets of rho and r are estimated
before composition. The angular normalization, actual map `(z,x) ↦ (z,Y(z,x))`,
and flow factor all remain differentiated. The partition sums preserve a
single total interpolation exponent q/T (`app:ch_background:prop:bg-adjoint`). -/
theorem normalizedTransportAmplitude_symbol_jet_profile (c ρ r Y flow) (R : ℝ)
    (p : AdjointSymbolPoint n) (q : ℕ)
    (hc : ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ c p.1) p)
    (hρ : ContDiffAt ℝ ∞ (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2)
      (adjointAngularGraph R p))
    (hN : ContDiffAt ℝ ∞ (adjointAngularGraph R) p)
    (hr : ContDiffAt ℝ ∞ r (adjointScalarGraph Y p))
    (hY : ContDiffAt ℝ ∞ (adjointScalarGraph Y) p)
    (hf : ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ flow p.1) p)
    (C P N A B F : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hP : ∀ i, 0 ≤ P i) (hNpos : ∀ i, 0 ≤ N i)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    {H T : ℝ} (hH : 0 < H)
    (hcC : ∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦ c p.1) p‖ ≤
      C i * H ^ ((i : ℝ) / T))
    (hρP : ∀ i ≤ q, ‖iteratedFDeriv ℝ i
      (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2) (adjointAngularGraph R p)‖ ≤
        P i * H ^ ((i : ℝ) / T))
    (hNN : ∀ i, 1 ≤ i → i ≤ q →
      ‖iteratedFDeriv ℝ i (adjointAngularGraph R) p‖ ≤ N i * H ^ (((i-1 : ℕ) : ℝ) / T))
    (hrA : ∀ i ≤ q, ‖iteratedFDeriv ℝ i r (adjointScalarGraph Y p)‖ ≤
      A i * H ^ ((i : ℝ) / T))
    (hYB : ∀ i, 1 ≤ i → i ≤ q →
      ‖iteratedFDeriv ℝ i (adjointScalarGraph Y) p‖ ≤ B i * H ^ (((i-1 : ℕ) : ℝ) / T))
    (hfF : ∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦ flow p.1) p‖ ≤
      F i * H ^ ((i : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
        normalizedTransportAmplitude c ρ r Y flow p.1.1 p.1.2 (R • p.2)) p‖ ≤
      adjointLeibnizBudget
        (adjointLeibnizBudget (adjointLeibnizBudget C (compositionBudget P N))
          (compositionBudget A B)) F q * H ^ ((q : ℝ) / T) := by
  have hPN := compositionBudget_nonneg hP hNpos
  apply local_product_profile p (((hc.mul (hρ.comp p hN)).mul (hr.comp p hY))) hf q _ F
    (adjointLeibnizBudget_nonneg (adjointLeibnizBudget_nonneg hC hPN)
      (compositionBudget_nonneg hA hB)) hH _ hfF
  intro i hi
  apply local_product_profile p (hc.mul (hρ.comp p hN)) (hr.comp p hY) i _ _
    (adjointLeibnizBudget_nonneg hC hPN) hH
  · intro j hj
    apply local_product_profile p hc (hρ.comp p hN) j C _ hC hH
      (fun k hk ↦ hcC k (hk.trans (hj.trans hi)))
    intro k hk
    exact local_pullback_profile (adjointAngularGraph R) _ p hN hρ k P N hP hH
      (fun l hl ↦ hρP l (hl.trans (hk.trans (hj.trans hi))))
      (fun l hl hl' ↦ hNN l hl (hl'.trans (hk.trans (hj.trans hi))))
  · intro j hj
    exact local_pullback_profile (adjointScalarGraph Y) r p hY hr j A B hA hH
      (fun k hk ↦ hrA k (hk.trans (hj.trans hi)))
      (fun k hk hk' ↦ hYB k hk (hk'.trans (hj.trans hi)))

/-- The original-amplitude profile, before adding the independent L,V profile,
for the full symbol reserve in `app:ch_background:prop:bg-adjoint`. -/
def transportSymbolJetBudget (C P N A B F : ℕ → ℝ) : ℕ → ℝ :=
  adjointLeibnizBudget
    (adjointLeibnizBudget (adjointLeibnizBudget C (compositionBudget P N))
      (compositionBudget A B)) F

/-- Nonnegativity needed by the expansion's primitive profile
(`app:ch_background:prop:bg-adjoint`). -/
theorem transportSymbolJetBudget_nonneg (C P N A B F : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hP : ∀ i, 0 ≤ P i) (hN : ∀ i, 0 ≤ N i)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (hF : ∀ i, 0 ≤ F i) :
    ∀ i, 0 ≤ transportSymbolJetBudget C P N A B F i :=
  adjointLeibnizBudget_nonneg
    (adjointLeibnizBudget_nonneg
      (adjointLeibnizBudget_nonneg hC (compositionBudget_nonneg hP hN))
      (compositionBudget_nonneg hA hB)) hF

set_option maxHeartbeats 800000 in
/-- Assembly for the actual transported scalar amplitude in
`app:ch_background:prop:bg-adjoint`. Every extra amplitude premise of
`exists_expansion_rescaled_halfOrder_bound` is discharged by the primitive
product and composition bounds. Only primitive geometry/scalar profiles and
the fixed radial scalar profile remain for geometric instantiation. The full
joint symbol reserve costs at most `s-k+q` primitive derivatives. -/
theorem exists_transportExpansion_rescaled_halfOrder_bound (L V c ρ r Y flow)
    (hc : ContDiff ℝ ∞ (c : AdjointJetPoint n → ℂ))
    (hρ : ContDiff ℝ ∞ (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2))
    (hr : ContDiff ℝ ∞ r)
    (hY : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ (p.1, Y p)))
    (hf : ContDiff ℝ ∞ flow)
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ)
    (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds
      (frequencyScaleAmplitude (halfOrderRadialFactor χ)
        (normalizedTransportAmplitude c ρ r Y flow)))
    (q : ℕ) (C P N A B F D W : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hP : ∀ i, 0 ≤ P i) (hNpos : ∀ i, 0 ≤ N i)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (hF : ∀ i, 0 ≤ F i)
    (hD : ∀ i, 0 ≤ D i) (hW : ∀ i, 0 ≤ W i) :
    ∃ K ≥ 0, ∀ (H T R : ℝ), 1 ≤ H → 0 < T →
      ∀ (U : Set (Euclidean (n-1))), IsOpen U →
      (∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞ (adjointAngularGraph R) (p,η)) →
      ∀ (p : AdjointSymbolPoint n), p.2 ∈ U →
      ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ halfOrderRadialFactor χ (R • p.2)) p →
      (∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
        halfOrderRadialFactor χ (R • p.2)) p‖ ≤ W i * Real.sqrt R) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + q,
        ‖iteratedFDeriv ℝ i c p.1‖ ≤
          C i * H ^ ((i : ℝ) / T)) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + q,
        ‖iteratedFDeriv ℝ i (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2)
          (adjointAngularGraph R p)‖ ≤ P i * H ^ ((i : ℝ) / T)) →
      (∀ i, 1 ≤ i → i ≤ ds.length - t.dataDerivatives.length + q →
        ‖iteratedFDeriv ℝ i (adjointAngularGraph R) p‖ ≤
          N i * H ^ (((i-1 : ℕ) : ℝ) / T)) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + q,
        ‖iteratedFDeriv ℝ i r (adjointScalarGraph Y p)‖ ≤ A i * H ^ ((i : ℝ) / T)) →
      (∀ i, 1 ≤ i → i ≤ ds.length - t.dataDerivatives.length + q →
        ‖iteratedFDeriv ℝ i (fun v : AdjointJetPoint n ↦ (v.1, Y v)) p.1‖ ≤
          B i * H ^ (((i-1 : ℕ) : ℝ) / T)) →
      (∀ i ≤ ds.length - t.dataDerivatives.length + q,
        ‖iteratedFDeriv ℝ i flow p.1‖ ≤
          F i * H ^ ((i : ℝ) / T)) →
      (∀ d ∈ ds, ∀ j i, i ≤ ds.length - t.dataDerivatives.length + q →
        ‖iteratedFDeriv ℝ i (branchField L V d j) p.1‖ ≤
          D i * H ^ ((i : ℝ) / T)) →
      ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
          t.amplitude p.1.1 p.1.2 (R • p.2)) p‖ ≤
        K * H ^ (((ds.length - t.dataDerivatives.length + q : ℕ) : ℝ) / T) * Real.sqrt R := by
  let J := transportSymbolJetBudget C P N A B F
  have hJ : ∀ i, 0 ≤ J i := transportSymbolJetBudget_nonneg C P N A B F
    hC hP hNpos hA hB hF
  have hsm := contDiff_normalizedTransportAmplitude c ρ r Y flow hc
    (fun θ ↦ hρ.comp (contDiff_fst.prodMk contDiff_const)) hr hY hf
  obtain ⟨K, hK, hbound⟩ := exists_expansion_rescaled_halfOrder_bound L V _ hsm hfield
    ds χ t ht q W (fun i ↦ J i + D i) hW (fun i ↦ add_nonneg (hJ i) (hD i))
  refine ⟨K, hK, ?_⟩
  intro H T R hH hT U hU hN p hp hrad hradBound hcC hρP hNN hrA hYB hfF hcoeff
  have hc' : ContDiff ℝ ∞ (fun p : AdjointSymbolPoint n ↦ c p.1) := hc.comp contDiff_fst
  have hf' : ContDiff ℝ ∞ (fun p : AdjointSymbolPoint n ↦ flow p.1) := hf.comp contDiff_fst
  have hY' : ContDiff ℝ ∞ (adjointScalarGraph Y) := hY.comp contDiff_fst
  apply hbound H T R hH hT U hU
    (fun η hη v ↦ contDiffAt_normalizedTransportAmplitude_symbol c ρ r Y flow R (v,η)
      hc'.contDiffAt hρ.contDiffAt (hN η hη v) hr.contDiffAt hY'.contDiffAt hf'.contDiffAt)
    p hp hrad hradBound
  · intro i hi
    have hb := normalizedTransportAmplitude_symbol_jet_profile c ρ r Y flow R p i
      hc'.contDiffAt hρ.contDiffAt (hN p.2 hp p.1) hr.contDiffAt hY'.contDiffAt hf'.contDiffAt
      C P N A B F hC hP hNpos hA hB (lt_of_lt_of_le zero_lt_one hH)
      (fun j hj ↦ (adjoint_spatial_jet_lift_bound c hc j p).trans (hcC j (hj.trans hi)))
      (fun j hj ↦ hρP j (hj.trans hi))
      (fun j hj hj' ↦ hNN j hj (hj'.trans hi)) (fun j hj ↦ hrA j (hj.trans hi))
      (fun j hj hj' ↦ (adjoint_spatial_jet_lift_bound _ hY j p).trans
        (hYB j hj (hj'.trans hi))) (fun j hj ↦
        (adjoint_spatial_jet_lift_bound flow hf j p).trans (hfF j (hj.trans hi)))
    exact hb.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hD i))
      (Real.rpow_nonneg (le_trans zero_le_one hH) _))
  · intro d hd j i hi
    exact ((adjoint_spatial_jet_lift_bound _ (hfield d j) i p).trans (hcoeff d hd j i hi)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hJ i))
        (Real.rpow_nonneg (le_trans zero_le_one hH) _))

end JanetCartan.ContinuumAdjoint.DerivativeKernels
