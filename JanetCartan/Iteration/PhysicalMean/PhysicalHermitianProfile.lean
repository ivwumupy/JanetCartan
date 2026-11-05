module

public import JanetCartan.Iteration.PhysicalMean.IndividualPhysicalProfile
public import JanetCartan.Analysis.Fourier.SeparatedSampling
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Matrix

/-!
# The full unmeasured physical Hermitian profile on the original samples

Consumer: the physical H^s input to RevisedStage.increment_estimates_of_physicalSobolev_profiles.
The complete full-amplitude field plus its actual native source correction is
squared BEFORE any estimate. Complementary derivative orders are retained.
The original unscaled sample mass is bounded by SeparatedSampling.totalMass_le;
no sample-count or band-count factor, weight division, or new sample is used.
The native correction C-profile producer is IndividualPhysicalProfile.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff BigOperators Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open CurrentMean SeparatedSampling

/-- Complementary derivative-order counts for the FULL physical tensor in
`main:prop:mean`; no sample or annular cardinality occurs. -/
def hermitianPhysicalOrderConstant (C : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (s+1), ∑ j ∈ Finset.range (q+1), (q.choose j : ℝ)*C j*C (q-j)

private theorem hermitianPhysicalOrderConstant_nonneg (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (s : ℕ) :
    0 ≤ hermitianPhysicalOrderConstant C s :=
  Finset.sum_nonneg fun _q _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC j)) (hC _)

private theorem physicalHermitian_cNorm_le_profile {n N : ℕ}
    {K : Set (Euclidean n)} (hK : IsCompact K) (s : ℕ)
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) {R : ℝ} (hR : 1 ≤ R)
    (F : Euclidean n → Matrix (Fin N) (Fin n) ℂ) (hF : ContDiff ℝ ∞ F)
    (hprofile : ∀ j ≤ s, cNorm K j F ≤ C j*R^j) :
    cNorm K s (fun x ↦ hermitianTensor (F x)) ≤ hermitianPhysicalOrderConstant C s*R^s := by
  let H := fun q ↦ ∑ j ∈ Finset.range (q+1), (q.choose j : ℝ)*C j*C (q-j)
  have hH (q : ℕ) : 0 ≤ H q := Finset.sum_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC j)) (hC _)
  have hj (q : ℕ) (hqs : q ≤ s) (x : Euclidean n) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ q (fun y ↦ hermitianTensor (F y)) x‖ ≤ H q*R^s := by
    have hbil := (hermitianContinuousBilinear (m := Fin N) (n := Fin n)).norm_iteratedFDeriv_le_of_bilinear
      (hF.of_le (by simp : (s : ℕ∞ω) ≤ (∞ : ℕ∞ω))) (hF.of_le (by simp : (s : ℕ∞ω) ≤ (∞ : ℕ∞ω))) x
      (show (q : ℕ∞ω) ≤ s by exact_mod_cast hqs)
    simp only [hermitianContinuousBilinear_apply, mixedHermitianTensor_self] at hbil
    apply hbil.trans
    calc
      _ ≤ 1*(∑ j ∈ Finset.range (q+1), (q.choose j : ℝ)*‖iteratedFDeriv ℝ j F x‖*
          ‖iteratedFDeriv ℝ (q-j) F x‖) :=
        mul_le_mul_of_nonneg_right norm_hermitianContinuousBilinear_le
          (Finset.sum_nonneg fun _ _ ↦ by positivity)
      _ = _ := one_mul _
      _ ≤ H q*R^s := by
        dsimp only [H]
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j hjq
        have hjq' : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hjq)
        have hleft := (norm_iteratedFDeriv_le_cNorm hK
          (hF.of_le (by simp : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω))) hx le_rfl).trans (hprofile j (hjq'.trans hqs))
        have hright := (norm_iteratedFDeriv_le_cNorm hK
          (hF.of_le (by simp : ((q-j : ℕ) : ℕ∞ω) ≤ (∞ : ℕ∞ω))) hx le_rfl).trans
            (hprofile (q-j) ((Nat.sub_le _ _).trans hqs))
        calc
          _ ≤ (q.choose j : ℝ)*(C j*R^j)*(C (q-j)*R^(q-j)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hleft (Nat.cast_nonneg _)) hright
              (norm_nonneg _) (by positivity [hC j, zero_le_one.trans hR])
          _ = ((q.choose j : ℝ)*C j*C (q-j))*(R^j*R^(q-j)) := by ring
          _ ≤ ((q.choose j : ℝ)*C j*C (q-j))*R^s := by
            apply mul_le_mul_of_nonneg_left _ (by positivity [hC j, hC (q-j)])
            rw [← pow_add, Nat.add_sub_of_le hjq']
            exact pow_le_pow_right₀ hR hqs
  have hb := cNorm_le_sum_of_bounds
    (fun q (_ : q ≤ s) ↦ mul_nonneg (hH q) (pow_nonneg (zero_le_one.trans hR) s)) hj
  simpa only [← Finset.sum_mul, H, hermitianPhysicalOrderConstant] using hb

/-- The fixed physical self-tensor constant sums only original PATCH mass
budgets and derivative-order counts. It is independent of mesh, shifts,
number of original samples, shell ceiling and current/source choices. -/
def originalFullHermitianProfileConstant {I : Type*} [Fintype I]
    (p : ℕ) (B : ℝ) (P : I → ℝ) (W : ℝ) (Cbase Cchange : ℕ → ℝ) (s : ℕ) : ℝ :=
  (∑ i, countConstant p B*(P i*W^3))*hermitianPhysicalOrderConstant (fun j ↦ Cbase j+Cchange j) s

/-- Bound the FULL original physical Hermitian tensor, including all native
cross-shell terms of each individual correction. The source correction's
physical C-profile is the output of individualNativeInverseField_cNorm_source_profile;
the full base profile comes from the retained full corrected amplitude and
original positive initializer. The original weight mass is proved internally,
not imposed as a successful-sampling hypothesis (`main:prop:mean`). -/
theorem cNorm_original_fullHermitian_source_profile {n N : ℕ} {I : Type*} [Fintype I]
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (p : ℕ) (B W : ℝ) (P : I → ℝ)
    (Cbase Cchange : ℕ → ℝ) (hCbase : ∀ j, 0 ≤ Cbase j) (hCchange : ∀ j, 0 ≤ Cchange j)
    (φ : I → Point → ℝ) (window : ℝ → ℝ)
    (hwindow : WindowBounds p window W) (hφ : ∀ i, PatchBounds (φ i) B (P i))
    {mesh : ℝ} (hmesh : 0 < mesh) (hmesh1 : mesh ≤ 1) (U : I → Lattice → Point)
    {R h : ℝ} (hR : 1 ≤ R) (hh1 : h ≤ 1)
    (base change : I → Sample → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hbase : ∀ i a, a ∈ samples p B (φ i) window mesh (U i) → ContDiff ℝ ∞ (base i a))
    (hchange : ∀ i a, a ∈ samples p B (φ i) window mesh (U i) → ContDiff ℝ ∞ (change i a))
    (hbaseProfile : ∀ j i a, a ∈ samples p B (φ i) window mesh (U i) → cNorm K j (base i a) ≤ Cbase j*R^j)
    (hchangeProfile : ∀ j i a, a ∈ samples p B (φ i) window mesh (U i) → cNorm K j (change i a) ≤ Cchange j*h*R^j)
    (s : ℕ) :
    0 ≤ originalFullHermitianProfileConstant p B P W Cbase Cchange s ∧
      cNorm K s (fun x ↦ ∑ i, ∑ a ∈ samples p B (φ i) window mesh (U i),
        weight (φ i) window mesh (U i) a • hermitianTensor (base i a x+change i a x)) ≤
          originalFullHermitianProfileConstant p B P W Cbase Cchange s*R^s := by
  classical
  let C := fun j ↦ Cbase j+Cchange j
  have hC (j : ℕ) : 0 ≤ C j := add_nonneg (hCbase j) (hCchange j)
  let CH := hermitianPhysicalOrderConstant C s
  have hCH : 0 ≤ CH := hermitianPhysicalOrderConstant_nonneg C hC s
  have hmass (i : I) : totalMass p B (φ i) window mesh (U i) ≤ countConstant p B*(P i*W^3) :=
    totalMass_le hwindow (hφ i) hmesh hmesh1
  have hbudget (i : I) : 0 ≤ countConstant p B*(P i*W^3) :=
    (totalMass_nonneg hwindow (hφ i) hmesh.le).trans (hmass i)
  refine ⟨mul_nonneg (Finset.sum_nonneg fun i _ ↦ hbudget i) hCH, ?_⟩
  let F := fun i a x ↦ hermitianTensor (base i a x+change i a x)
  have hF (i : I) (a : Sample) (ha : a ∈ samples p B (φ i) window mesh (U i)) : ContDiff ℝ ∞ (F i a) := by
    have hs := (hbase i a ha).add (hchange i a ha)
    simpa only [F, Function.comp_apply, Pi.add_apply, hermitianContinuousBilinear_apply, mixedHermitianTensor_self] using
      ((hermitianContinuousBilinear (m := Fin N) (n := Fin n)).contDiff.comp hs).clm_apply hs
  have hFn (i : I) (a : Sample) (ha : a ∈ samples p B (φ i) window mesh (U i)) :
      cNorm K s (F i a) ≤ CH*R^s := by
    apply physicalHermitian_cNorm_le_profile hK s C hC hR (fun x ↦ base i a x+change i a x)
      ((hbase i a ha).add (hchange i a ha))
    intro j _
    have hd : Cchange j*h*R^j ≤ Cchange j*R^j :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hCchange j) hh1)
        (pow_nonneg (zero_le_one.trans hR) j)
    exact ((cNorm_add_le hK ((hbase i a ha).of_le (by simp)) ((hchange i a ha).of_le (by simp))).trans
      (add_le_add (hbaseProfile j i a ha) ((hchangeProfile j i a ha).trans hd))).trans_eq (by dsimp only [C]; ring)
  let S := fun i x ↦ ∑ a ∈ samples p B (φ i) window mesh (U i), weight (φ i) window mesh (U i) a • F i a x
  have hS (i : I) : ContDiff ℝ ∞ (S i) := by
    apply ContDiff.sum
    intro a ha
    exact (hF i a ha).const_smul _
  have hSn (i : I) : cNorm K s (S i) ≤ (countConstant p B*(P i*W^3))*(CH*R^s) := by
    apply (cNorm_sum_smul_le _ _ hK (fun a ha ↦ (hF i a ha).of_le (by simp))).trans
    calc
      _ ≤ ∑ a ∈ samples p B (φ i) window mesh (U i), weight (φ i) window mesh (U i) a*(CH*R^s) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [Real.norm_of_nonneg (weight_nonneg hwindow (hφ i) hmesh.le a)]
        exact mul_le_mul_of_nonneg_left (hFn i a ha) (weight_nonneg hwindow (hφ i) hmesh.le a)
      _ = totalMass p B (φ i) window mesh (U i)*(CH*R^s) := by rw [← Finset.sum_mul]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right (hmass i) (mul_nonneg hCH (pow_nonneg (zero_le_one.trans hR) s))
  change cNorm K s (fun x ↦ ∑ i, S i x) ≤ _
  apply (cNorm_sum_le _ hK (fun i _ ↦ (hS i).of_le (by simp))).trans
  apply (Finset.sum_le_sum fun i _ ↦ hSn i).trans_eq
  rw [← Finset.sum_mul]
  dsimp only [originalFullHermitianProfileConstant, CH, C]
  ring

end JanetCartan.PhysicalMean
