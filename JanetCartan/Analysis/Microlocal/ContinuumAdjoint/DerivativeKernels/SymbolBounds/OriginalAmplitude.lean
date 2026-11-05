module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Quantitative.OneHigh.Composition

/-!
# Original angular and transported-scalar amplitude jets

The producer for the original-amplitude input of
`exists_expansion_primitiveJet_bound`, for `app:ch_background:prop:bg-adjoint`.
The scalar is composed with the actual map `(z,x) ↦ (z,Y(z,x))` before
differentiation. Neither the angular cutoff nor the flow factor is frozen.
Primitive geometry/scalar interpolation profiles are explicit inputs; their
instantiation on buffered charts remains with the geometric construction.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CompositionBounds FourierIntegral.NormalOneHigh
variable {n : ℕ}

/-- Leibniz convolution of primitive profile constants, used for the original
full amplitude in `app:ch_background:eq:bg-T`. -/
def adjointLeibnizBudget (A B : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (q+1), (q.choose i : ℝ) * A i * B (q-i)

/-- Nonnegativity of the original-amplitude product budget
(`app:ch_background:prop:bg-adjoint`). -/
theorem adjointLeibnizBudget_nonneg {A B : ℕ → ℝ}
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (q : ℕ) :
    0 ≤ adjointLeibnizBudget A B q :=
  Finset.sum_nonneg (fun i _ ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB (q-i)))

/-- Multiplication preserves the total primitive interpolation exponent.
This is applied to all factors of the original adjoint amplitude, including
the angular mask and flow factor (`app:ch_background:prop:bg-adjoint`). -/
theorem adjoint_product_jet_profile {f g : AdjointJetPoint n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : AdjointJetPoint n) (q : ℕ) (A B : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i)
    {H T : ℝ} (hH : 0 < H)
    (hfa : ∀ i ≤ q, ‖iteratedFDeriv ℝ i f p‖ ≤ A i * H ^ ((i : ℝ) / T))
    (hgb : ∀ i ≤ q, ‖iteratedFDeriv ℝ i g p‖ ≤ B i * H ^ ((i : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p ↦ f p * g p) p‖ ≤
      adjointLeibnizBudget A B q * H ^ ((q : ℝ) / T) := by
  apply (norm_iteratedFDeriv_mul_le hf hg p (by simp)).trans
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
theorem adjoint_scalar_pullback_jet_profile
    (Y : AdjointJetPoint n → Euclidean (n-1))
    (r : CarrierParameter × Euclidean (n-1) → ℂ)
    (hY : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ (p.1, Y p)))
    (hr : ContDiff ℝ ∞ r) (p : AdjointJetPoint n) (q : ℕ)
    (A B : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) {H T : ℝ} (hH : 0 < H)
    (hrA : ∀ i ≤ q, ‖iteratedFDeriv ℝ i r (p.1, Y p)‖ ≤ A i * H ^ ((i : ℝ) / T))
    (hYB : ∀ i, 1 ≤ i → i ≤ q →
      ‖iteratedFDeriv ℝ i (fun p : AdjointJetPoint n ↦ (p.1, Y p)) p‖ ≤
        B i * H ^ (((i-1 : ℕ) : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p : AdjointJetPoint n ↦ r (p.1, Y p)) p‖ ≤
      compositionBudget A B q * H ^ ((q : ℝ) / T) := by
  apply (norm_iteratedFDeriv_comp_le_partition_sum
    (hr.contDiffAt.of_le (show (q : ℕ∞ω) ≤ ∞ by simp))
    (hY.contDiffAt.of_le (show (q : ℕ∞ω) ≤ ∞ by simp)) (le_refl q)).trans
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

/-- The original normalized scalar entry, with geometry/measurement factor c,
the angular mask, actual initial-scalar composition, and flow factor. The
frequency-only cutoff and square root are supplied separately by
`halfOrderRadialFactor` (`app:ch_background:eq:bg-T`). -/
def normalizedTransportAmplitude
    (c : AdjointJetPoint n → ℂ)
    (ρ : CarrierParameter → Euclidean (n-1) → ℂ)
    (r : CarrierParameter × Euclidean (n-1) → ℂ)
    (Y : AdjointJetPoint n → Euclidean (n-1)) (flow : AdjointJetPoint n → ℂ) :
    AdjointAmplitude n := fun z x η ↦
  c (z,x) * ρ z (‖η‖⁻¹ • η) * r (z, Y (z,x)) * flow (z,x)

/-- Smoothness of the full normalized amplitude, retaining all carrier
dependence (`app:ch_background:prop:bg-adjoint`). -/
theorem contDiff_normalizedTransportAmplitude (c ρ r Y flow)
    (hc : ContDiff ℝ ∞ (c : AdjointJetPoint n → ℂ))
    (hρ : ∀ θ, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ ρ p.1 θ))
    (hr : ContDiff ℝ ∞ r)
    (hY : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ (p.1, Y p)))
    (hf : ContDiff ℝ ∞ flow) (η : Euclidean (n-1)) :
    ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦
      normalizedTransportAmplitude c ρ r Y flow p.1 p.2 η) :=
  ((hc.mul (hρ _)).mul (hr.comp hY)).mul hf

/-- Primitive geometry, angular-mask, initial-scalar and flow profiles produce
the original-amplitude input required by `exists_expansion_primitiveJet_bound`.
No jet bound on a generated amplitude or on the scalar composition is a premise
(`app:ch_background:prop:bg-adjoint`). -/
theorem normalizedTransportAmplitude_jet_profile (c ρ r Y flow)
    (hc : ContDiff ℝ ∞ (c : AdjointJetPoint n → ℂ))
    (hρ : ∀ θ, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ ρ p.1 θ))
    (hr : ContDiff ℝ ∞ r)
    (hY : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ (p.1, Y p)))
    (hf : ContDiff ℝ ∞ flow) (η : Euclidean (n-1)) (p : AdjointJetPoint n) (q : ℕ)
    (C P A B F : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hP : ∀ i, 0 ≤ P i)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    {H T : ℝ} (hH : 0 < H)
    (hcC : ∀ i ≤ q, ‖iteratedFDeriv ℝ i c p‖ ≤ C i * H ^ ((i : ℝ) / T))
    (hρP : ∀ i ≤ q, ‖iteratedFDeriv ℝ i
      (fun p : AdjointJetPoint n ↦ ρ p.1 (‖η‖⁻¹ • η)) p‖ ≤ P i * H ^ ((i : ℝ) / T))
    (hrA : ∀ i ≤ q, ‖iteratedFDeriv ℝ i r (p.1, Y p)‖ ≤ A i * H ^ ((i : ℝ) / T))
    (hYB : ∀ i, 1 ≤ i → i ≤ q →
      ‖iteratedFDeriv ℝ i (fun p : AdjointJetPoint n ↦ (p.1, Y p)) p‖ ≤
        B i * H ^ (((i-1 : ℕ) : ℝ) / T))
    (hfF : ∀ i ≤ q, ‖iteratedFDeriv ℝ i flow p‖ ≤ F i * H ^ ((i : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p : AdjointJetPoint n ↦
        normalizedTransportAmplitude c ρ r Y flow p.1 p.2 η) p‖ ≤
      adjointLeibnizBudget
        (adjointLeibnizBudget (adjointLeibnizBudget C P) (compositionBudget A B)) F q *
          H ^ ((q : ℝ) / T) := by
  apply adjoint_product_jet_profile
    (((hc.mul (hρ _)).mul (hr.comp hY))) hf p q _ F
    (adjointLeibnizBudget_nonneg (adjointLeibnizBudget_nonneg hC hP)
      (compositionBudget_nonneg hA hB)) hH _ hfF
  intro i hi
  apply adjoint_product_jet_profile (hc.mul (hρ _)) (hr.comp hY) p i _ _
    (adjointLeibnizBudget_nonneg hC hP) hH
  · intro j hj
    exact adjoint_product_jet_profile hc (hρ _) p j C P hC hH
      (fun k hk ↦ hcC k (hk.trans (hj.trans hi)))
      (fun k hk ↦ hρP k (hk.trans (hj.trans hi)))
  · intro j hj
    exact adjoint_scalar_pullback_jet_profile Y r hY hr p j A B hA hH
      (fun k hk ↦ hrA k (hk.trans (hj.trans hi)))
      (fun k hk hk' ↦ hYB k hk (hk'.trans (hj.trans hi)))

end JanetCartan.ContinuumAdjoint.DerivativeKernels
