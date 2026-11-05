module
public import JanetCartan.Iteration.PhysicalMean.CanonicalForcingProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.PullbackGrades

/-!
# Joint full-Hermitian bounds on the literal retained carrier

Consumer: the actual original weighted kernel in
`app:ch_mean_pairs:eq:comparison-input` and its `p+q` quadrature source profile.
The literal carrier insertion is measured in the true Euclidean and sup norms.
Fixed composition and product budgets precede the varying measurement and
corrected matrix amplitude, every history scale, and every color rate.

The first deduction covers an already-cut annular amplitude. The second uses
only whole-parent local smoothness of the UNCUT positive amplitude: the original
measurement and outer weight supply its zero germs. It requires no support of
the positive scalar in the inner collar. Both keep the full Hermitian tensor,
with no response recut, angular-factor insertion, Fourier normalization or
reserve change. The parent must instantiate the primitive profiles and exact
geometry; neither independent deduction alone is an actual baseline or Main.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.HermitianCarrierPullback
open SeparatedSampling CurrentMean RawPrimary.SliceBounds FourierIntegral.NormalOneHigh

private theorem budget_nonneg {A B : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (q : ℕ) :
    0 ≤ backgroundJointBilinearBudget A B q := by
  exact Finset.sum_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA j)) (hB _)

/-- Exact carrier insertion for the same cut amplitude. The compact and the
weight precede both varying coefficients, so the resulting budget is static.
This deduction will be instantiated with the actual original amplitude jets. -/
theorem exists_weighted_carrier_hermitian_profiles {n d N : ℕ}
    (K : Set (Euclidean n × (Euclidean 3 × Euclidean d))) (hK : IsCompact K)
    (ζ : Euclidean 3 → Euclidean d) (hζ : ContDiff ℝ ∞ ζ)
    (φ : Point → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (CM CB : ℕ → ℝ) (hCM : ∀ j, 0 ≤ CM j) (hCB : ∀ j, 0 ≤ CB j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n), ContDiff ℝ ∞ C →
      ∀ (B : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin N) (Fin n) ℂ),
        ContDiff ℝ ∞ B → tsupport B ⊆ K →
      ∀ (L : ℝ) (r : ℕ), 1 ≤ L →
      HasDerivativeProfile K (fun v ↦ C v.1) r L CM →
      (∀ j v, ‖iteratedFDeriv ℝ j B v‖ ≤ CB j * L^(j-r)) →
      let H := fun w : Euclidean n × Point ↦ φ w.2 • C w.1
        (hermitianTensor (B (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))))
      ContDiff ℝ ∞ H ∧
        ∀ j w, ‖iteratedFDeriv ℝ j H w‖ ≤ D j * L^(j-r) := by
  let π : Euclidean n × (Euclidean 3 × Euclidean d) → Euclidean n × Point :=
    fun v ↦ (v.1, WithLp.ofLp v.2.1)
  have hπ : Continuous π := by dsimp [π]; fun_prop
  let S := π '' K
  have hS : IsCompact S := hK.image hπ
  let g : Euclidean n × Point → Euclidean n × (Euclidean 3 × Euclidean d) :=
    fun w ↦ (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))
  have hz : ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ WithLp.toLp 2 w.2) := by
    fun_prop
  have hg : ContDiff ℝ ∞ g := contDiff_fst.prodMk (hz.prodMk (hζ.comp hz))
  let mask : Euclidean n × Point → ℝ := fun w ↦ φ w.2
  have hm : ContDiff ℝ ∞ mask := hφ.comp contDiff_snd
  let b := fun j ↦ cNorm S j g
  let a := fun j ↦ cNorm S j mask
  have hb (j) : 0 ≤ b j := cNorm_nonneg _ _ _
  have ha (j) : 0 ≤ a j := cNorm_nonneg _ _ _
  let M := compositionBudget CM b
  let A := compositionBudget CB b
  have hM : ∀ j, 0 ≤ M j := compositionBudget_nonneg hCM hb
  have hA : ∀ j, 0 ≤ A j := compositionBudget_nonneg hCB hb
  let D := backgroundJointBilinearBudget a
    (backgroundJointBilinearBudget M (backgroundJointBilinearBudget A A))
  have hD : ∀ j, 0 ≤ D j := budget_nonneg ha (budget_nonneg hM (budget_nonneg hA hA))
  refine ⟨D, hD, ?_⟩
  intro C hC B hB hBK L r hL hMC hBC H
  let Mr : Euclidean n × (Euclidean 3 × Euclidean d) → MetricTensor n →L[ℝ] Euclidean n :=
    fun v ↦ C v.1
  have hMr : ContDiff ℝ ∞ Mr := hC.comp contDiff_fst
  let Mp : Euclidean n × Point → MetricTensor n →L[ℝ] Euclidean n := fun w ↦ C w.1
  have hMp : ContDiff ℝ ∞ Mp := hC.comp contDiff_fst
  let Bp := B ∘ g
  have hBp : ContDiff ℝ ∞ Bp := hB.comp hg
  have hHB : ContDiff ℝ ∞ (fun w ↦ hermitianTensor (Bp w)) := by
    simpa only [Function.comp_def, hermitianContinuousBilinear_apply, mixedHermitianTensor_self] using
      (hermitianContinuousBilinear (m := Fin N) (n := Fin n)).isBoundedBilinearMap.contDiff.comp
        (hBp.prodMk hBp)
  have hH : ContDiff ℝ ∞ H := hm.smul (hMp.clm_apply hHB)
  refine ⟨hH, ?_⟩
  intro j w
  by_cases hw : g w ∈ K
  · have hwS : w ∈ S := ⟨g w, hw, rfl⟩
    have hgj (k : ℕ) : ‖iteratedFDeriv ℝ k g w‖ ≤ b k :=
      norm_iteratedFDeriv_le_cNorm hS (hg.of_le (by simp)) hwS le_rfl
    have hMj (k : ℕ) : ‖iteratedFDeriv ℝ k Mp w‖ ≤ M k * L^(k-r) := by
      change ‖iteratedFDeriv ℝ k (Mr ∘ g) w‖ ≤ _
      apply norm_iteratedFDeriv_comp_le_sliceGrade hg.contDiffAt hMr.contDiffAt
        (fun q _ ↦ hCM q) hL _ (fun q _ _ ↦ hgj q)
      intro q _
      exact (norm_iteratedFDeriv_le_cNorm hK (hMr.of_le (by simp)) hw le_rfl).trans (hMC q)
    have hBj (k : ℕ) : ‖iteratedFDeriv ℝ k Bp w‖ ≤ A k * L^(k-r) :=
      norm_iteratedFDeriv_comp_le_sliceGrade hg.contDiffAt hB.contDiffAt
        (fun q _ ↦ hCB q) hL (fun q _ ↦ hBC q (g w)) (fun q _ _ ↦ hgj q)
    exact norm_jointFullMeasuredHermitian_kernel_source_profile mask Mp Bp hm hMp hBp
      a M A ha hM hA r j hL w
      (fun q _ ↦ norm_iteratedFDeriv_le_cNorm hS (hm.of_le (by simp)) hwS le_rfl)
      (fun q _ ↦ hMj q) (fun q _ ↦ hBj q)
  · have hzero : B =ᶠ[𝓝 (g w)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hb ↦ hw (hBK hb))
    have hzH : H =ᶠ[𝓝 w] 0 := by
      filter_upwards [hzero.comp_tendsto hg.continuous.continuousAt] with v hv
      change B (g v) = 0 at hv
      change φ v.2 • C v.1 (hermitianTensor (B (g v))) = 0
      rw [hv]
      have h0 : hermitianTensor (0 : Matrix (Fin N) (Fin n) ℂ) = 0 := by
        ext a b
        simp [hermitianTensor_apply]
      rw [h0, map_zero, smul_zero]
    rw [(hzH.iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (hD j) (pow_nonneg (zero_le_one.trans hL) _)

open RawPrimary.AmplitudeGrades.Polynomial

/-- The actual whole-parent budget depends only on the fixed carrier, outer
weight and primitive costs, never on a history or its domain certificates. -/
noncomputable def weightedLocalCarrierBudget {n d N : ℕ}
    (X : Set (Euclidean n)) (ζ : Euclidean 3 → Euclidean d) (φ : Point → ℝ)
    (CM CB : ℕ → ℝ) : ℕ → ℝ :=
  let S := X ×ˢ tsupport φ
  let g : Euclidean n × Point → Euclidean n × (Euclidean 3 × Euclidean d) :=
    fun w ↦ (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))
  let b := fun j ↦ cNorm S j g
  let a := fun j ↦ cNorm S j (fun w : Euclidean n × Point ↦ φ w.2)
  let M := compositionBudget CM b
  let A := compositionBudget CB b
  productProfile (ContinuousLinearMap.lsmul ℝ ℝ (E := Euclidean n)) a
    (productProfile (ContinuousLinearMap.id ℝ (MetricTensor n →L[ℝ] Euclidean n)) M
      (productProfile (hermitianContinuousBilinear (m := Fin N) (n := Fin n)) A A))

/-- Nonnegativity requires only the original two primitive costs. -/
theorem weightedLocalCarrierBudget_nonneg {n d N : ℕ}
    (X : Set (Euclidean n)) (ζ : Euclidean 3 → Euclidean d) (φ : Point → ℝ)
    (CM CB : ℕ → ℝ) (hCM : ∀ j, 0 ≤ CM j) (hCB : ∀ j, 0 ≤ CB j) :
    ∀ j, 0 ≤ weightedLocalCarrierBudget (N := N) X ζ φ CM CB j := by
  unfold weightedLocalCarrierBudget
  exact productProfile_nonneg _ (fun _ ↦ cNorm_nonneg _ _ _)
    (productProfile_nonneg _ (compositionBudget_nonneg hCM (fun _ ↦ cNorm_nonneg _ _ _))
      (productProfile_nonneg _ (compositionBudget_nonneg hCB (fun _ ↦ cNorm_nonneg _ _ _))
        (compositionBudget_nonneg hCB (fun _ ↦ cNorm_nonneg _ _ _))))

/-- Whole-parent weighted Hermitian jets; the original weight and measurement
supply all zero germs. Neither the positive scalar nor its uncut amplitude is
assumed supported in an inner coefficient collar. -/
theorem weighted_local_carrier_profiles {n d N : ℕ}
    (X : Set (Euclidean n)) (hX : IsCompact X)
    (ζ : Euclidean 3 → Euclidean d) (φ : Point → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (O : Set (Euclidean n × Point)) (hO : IsOpen O)
    (hg : ContDiffOn ℝ ∞ (fun w : Euclidean n × Point ↦
      (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))) O)
    (hXO : X ×ˢ tsupport φ ⊆ O)
    (K Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d)))
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hgΩ : MapsTo (fun w : Euclidean n × Point ↦
      (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))) O Ω)
    (hgK : MapsTo (fun w : Euclidean n × Point ↦
      (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))) (X ×ˢ tsupport φ) K)
    (CM CB : ℕ → ℝ) (hCM : ∀ j, 0 ≤ CM j) (hCB : ∀ j, 0 ≤ CB j) :
    let D := weightedLocalCarrierBudget (N := N) X ζ φ CM CB
    (∀ j, 0 ≤ D j) ∧
      ∀ (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n), ContDiff ℝ ∞ C →
        tsupport C ⊆ X →
      ∀ (B : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin N) (Fin n) ℂ),
        ContDiffOn ℝ ∞ B Ω →
      ∀ (L : ℝ) (r : ℕ), 1 ≤ L →
      HasDerivativeProfile K (fun v ↦ C v.1) r L CM →
      (∀ j v, v ∈ K → ‖iteratedFDeriv ℝ j B v‖ ≤ CB j * L^(j-r)) →
      let H := fun w : Euclidean n × Point ↦ φ w.2 • C w.1
        (hermitianTensor (B (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))))
      ContDiff ℝ ∞ H ∧
        ∀ j w, ‖iteratedFDeriv ℝ j H w‖ ≤ D j * L^(j-r) := by
  let S := X ×ˢ tsupport φ
  have hS : IsCompact S := hX.prod hφc
  let g : Euclidean n × Point → Euclidean n × (Euclidean 3 × Euclidean d) :=
    fun w ↦ (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))
  let mask : Euclidean n × Point → ℝ := fun w ↦ φ w.2
  have hm : ContDiff ℝ ∞ mask := hφ.comp contDiff_snd
  let b := fun j ↦ cNorm S j g
  let a := fun j ↦ cNorm S j mask
  have hb (j) : 0 ≤ b j := cNorm_nonneg _ _ _
  have ha (j) : 0 ≤ a j := cNorm_nonneg _ _ _
  let M := compositionBudget CM b
  let A := compositionBudget CB b
  have hM : ∀ j, 0 ≤ M j := compositionBudget_nonneg hCM hb
  have hA : ∀ j, 0 ≤ A j := compositionBudget_nonneg hCB hb
  let HB := hermitianContinuousBilinear (m := Fin N) (n := Fin n)
  let E := ContinuousLinearMap.id ℝ (MetricTensor n →L[ℝ] Euclidean n)
  let F := ContinuousLinearMap.lsmul ℝ ℝ (E := Euclidean n)
  let D := productProfile F a (productProfile E M (productProfile HB A A))
  have hD : ∀ j, 0 ≤ D j := productProfile_nonneg F ha
    (productProfile_nonneg E hM (productProfile_nonneg HB hA hA))
  refine ⟨hD, ?_⟩
  intro C hC hCX B hB L r hL hMC hBC H
  let Mr : Euclidean n × (Euclidean 3 × Euclidean d) → MetricTensor n →L[ℝ] Euclidean n :=
    fun v ↦ C v.1
  have hMr : ContDiff ℝ ∞ Mr := hC.comp contDiff_fst
  let Mp : Euclidean n × Point → MetricTensor n →L[ℝ] Euclidean n := fun w ↦ C w.1
  have hMp : ContDiff ℝ ∞ Mp := hC.comp contDiff_fst
  let Bp := B ∘ g
  have hBp : ContDiffOn ℝ ∞ Bp O := hB.comp hg hgΩ
  let Ht := fun w ↦ HB (Bp w) (Bp w)
  have hHt : ContDiffOn ℝ ∞ Ht O :=
    (HB.contDiff.comp_contDiffOn hBp).clm_apply hBp
  let Hm := fun w ↦ E (Mp w) (Ht w)
  have hHm : ContDiffOn ℝ ∞ Hm O := hMp.contDiffOn.clm_apply hHt
  have heq : H = fun w ↦ F (mask w) (Hm w) := by
    funext w
    change φ w.2 • C w.1 (hermitianTensor (Bp w)) =
      φ w.2 • C w.1 (HB (Bp w) (Bp w))
    simp only [HB, hermitianContinuousBilinear_apply, mixedHermitianTensor_self]
  have hHO : ContDiffOn ℝ ∞ H O := by
    rw [heq]
    exact (F.contDiff.comp_contDiffOn hm.contDiffOn).clm_apply hHm
  have hz (w : Euclidean n × Point) (hw : w ∉ S) : H =ᶠ[𝓝 w] 0 := by
    by_cases hx : w.1 ∈ X
    · have hp : w.2 ∉ tsupport φ := fun hp ↦ hw ⟨hx, hp⟩
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
        (continuous_snd.continuousAt (x := w))] with v hv
      change φ v.2 = 0 at hv
      simp only [H, hv, zero_smul, Pi.zero_apply]
    · have hc : w.1 ∉ tsupport C := fun hc ↦ hx (hCX hc)
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hc).comp_tendsto
        (continuous_fst.continuousAt (x := w))] with v hv
      change C v.1 = 0 at hv
      simp only [H, hv, zero_apply, smul_zero, Pi.zero_apply]
  refine ⟨contDiff_iff_contDiffAt.mpr (fun w ↦ ?_), ?_⟩
  · by_cases hw : w ∈ S
    · exact hHO.contDiffAt (hO.mem_nhds (hXO hw))
    · exact contDiffAt_const.congr_of_eventuallyEq (hz w hw)
  intro j w
  by_cases hw : w ∈ S
  · have hwO := hXO hw
    have hgw := hgK hw
    have hgAt : ContDiffAt ℝ ∞ g w := hg.contDiffAt (hO.mem_nhds hwO)
    have hgj (k : ℕ) : ‖iteratedFDeriv ℝ k g w‖ ≤ b k :=
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
        (fun v hv ↦ (hg.contDiffAt (hO.mem_nhds (hXO hv))).of_le (by simp)) hw le_rfl
    have hMj (k : ℕ) : ‖iteratedFDeriv ℝ k Mp w‖ ≤ M k * L^(k-r) := by
      change ‖iteratedFDeriv ℝ k (Mr ∘ g) w‖ ≤ _
      apply norm_iteratedFDeriv_comp_le_sliceGrade hgAt hMr.contDiffAt
        (fun q _ ↦ hCM q) hL _ (fun q _ _ ↦ hgj q)
      intro q _
      exact (norm_iteratedFDeriv_le_cNorm hK (hMr.of_le (by simp)) hgw le_rfl).trans (hMC q)
    have hBj (k : ℕ) : ‖iteratedFDeriv ℝ k Bp w‖ ≤ A k * L^(k-r) :=
      norm_iteratedFDeriv_comp_le_sliceGrade hgAt (hB.contDiffAt (hΩ.mem_nhds (hKΩ hgw)))
        (fun q _ ↦ hCB q) hL (fun q _ ↦ hBC q (g w) hgw) (fun q _ _ ↦ hgj q)
    have hHtj (k : ℕ) : ‖iteratedFDeriv ℝ k Ht w‖ ≤
        productProfile HB A A k * L^(k-r) :=
      jet_bilinear_le HB hO hBp hBp hwO hL hA hA hBj hBj k
    have hHmj (k : ℕ) : ‖iteratedFDeriv ℝ k Hm w‖ ≤
        productProfile E M (productProfile HB A A) k * L^(k-r) :=
      jet_bilinear_le E hO hMp.contDiffOn hHt hwO hL hM
        (productProfile_nonneg HB hA hA) hMj hHtj k
    have hmask (k : ℕ) : ‖iteratedFDeriv ℝ k mask w‖ ≤ a k * L^(k-r) :=
      (norm_iteratedFDeriv_le_cNorm hS (hm.of_le (by simp)) hw le_rfl).trans
        (le_mul_of_one_le_right (ha k) (one_le_pow₀ hL))
    rw [heq]
    exact jet_bilinear_le F hO hm.contDiffOn hHm hwO hL ha
      (productProfile_nonneg E hM (productProfile_nonneg HB hA hA)) hmask hHmj j
  · rw [((hz w hw).iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (hD j) (pow_nonneg (zero_le_one.trans hL) _)


/-- Existential form of the same explicitly fixed budget. -/
theorem exists_weighted_local_carrier_profiles {n d N : ℕ}
    (X : Set (Euclidean n)) (hX : IsCompact X)
    (ζ : Euclidean 3 → Euclidean d) (φ : Point → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (O : Set (Euclidean n × Point)) (hO : IsOpen O)
    (hg : ContDiffOn ℝ ∞ (fun w : Euclidean n × Point ↦
      (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))) O)
    (hXO : X ×ˢ tsupport φ ⊆ O)
    (K Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d)))
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hgΩ : MapsTo (fun w : Euclidean n × Point ↦
      (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))) O Ω)
    (hgK : MapsTo (fun w : Euclidean n × Point ↦
      (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))) (X ×ˢ tsupport φ) K)
    (CM CB : ℕ → ℝ) (hCM : ∀ j, 0 ≤ CM j) (hCB : ∀ j, 0 ≤ CB j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n), ContDiff ℝ ∞ C →
        tsupport C ⊆ X →
      ∀ (B : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin N) (Fin n) ℂ),
        ContDiffOn ℝ ∞ B Ω →
      ∀ (L : ℝ) (r : ℕ), 1 ≤ L →
      HasDerivativeProfile K (fun v ↦ C v.1) r L CM →
      (∀ j v, v ∈ K → ‖iteratedFDeriv ℝ j B v‖ ≤ CB j * L^(j-r)) →
      let H := fun w : Euclidean n × Point ↦ φ w.2 • C w.1
        (hermitianTensor (B (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))))
      ContDiff ℝ ∞ H ∧
        ∀ j w, ‖iteratedFDeriv ℝ j H w‖ ≤ D j * L^(j-r) := by
  exact ⟨weightedLocalCarrierBudget (N := N) X ζ φ CM CB,
    weighted_local_carrier_profiles (N := N) X hX ζ φ hφ hφc O hO hg hXO
      K Ω hK hΩ hKΩ hgΩ hgK CM CB hCM hCB⟩


end JanetCartan.PhysicalMean.HermitianCarrierPullback
