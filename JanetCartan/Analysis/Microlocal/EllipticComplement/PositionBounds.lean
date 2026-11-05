module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.Symbol
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.WeightedPhysicalBudget

/-!
# Position derivatives of the complementary symbols

Normalize the inverse only on the actual closed elliptic support. Tame
composition on the compact coefficient-direction product gives a single high
norm of the original field. The reciprocal radius supplies the full frequency
weight, uniformly in the enlarged radial threshold.
Source: `app:ch_regular_base:sec:energy-construction` and
`app:ch_regular_base:eq:sector-theorem-solution`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticComplement
open ActualCarriers FiniteMasks.ActualFamily Characteristic.ResidualCoordinates
open Characteristic.AlgebraicSymbols FullPhaseCharts.InverseEstimates
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

private theorem pencil_inv_complex_eq_radial {A : Coeff} {ξ : E} (hξ : 0 < ‖ξ‖)
    (hu : IsUnit (pencil A (NormedSpace.normalize ξ)).det) :
    ((pencil A ξ)⁻¹).map Complex.ofReal =
      ((‖ξ‖⁻¹ : ℝ) : ℂ) • ((pencil A (NormedSpace.normalize ξ))⁻¹).map Complex.ofReal := by
  have he : pencil A ξ = ‖ξ‖ • pencil A (NormedSpace.normalize ξ) := by
    conv_lhs => rw [← NormedSpace.norm_smul_normalize ξ]
    exact (pencilContinuousLinearMap A).map_smul _ _
  let := invertibleOfNonzero hξ.ne'
  rw [he, Matrix.inv_smul _ _ hu, invOf_eq_inv]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]

/-- The actual elliptic inverse has reserve zero in physical derivatives.
All constants precede the radial threshold and the varying coefficient.
It is enough that `Q` be smooth on the original open coefficient domain
(`app:ch_regular_base:sec:energy-construction`). -/
theorem exists_ellipticInverseSymbol_weighted_cNorm (hΩ : IsOpen Ω)
    (hRQΩ : closedBall x RQ ⊆ Ω) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
      ∀ L ≥ f.radialThreshold, ∀ Q : E → Coeff, ContDiffOn ℝ ∞ Q Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) → ∀ ξ m,
        (1 + ‖ξ‖) * cNorm (closedBall x (2*f.physicalRadius)) m
          (fun y ↦ ellipticInverseSymbol f hK L Q y ξ) ≤
          D m * (1 + cNorm (closedBall x RQ) m Q) := by
  let S := closedBall x (2*f.physicalRadius)
  have hR : 0 < 2*f.physicalRadius := mul_pos zero_lt_two f.physicalRadius_pos
  have hSQ : S ⊆ closedBall x RQ := (closedBall_subset_closedBall (by
    linarith [f.physicalRadius_pos] : 2*f.physicalRadius ≤ 4*f.physicalRadius)).trans
      f.physicalBall_coefficientDomain
  let T := closedBall A₀ f.coefficientRadius ×ˢ tsupport (ellipticAngularMask f hK)
  have hT : IsCompact T := (isCompact_closedBall _ _).prod (ellipticAngularMask_spec f hK).2.1
  let G : Coeff × E → CMat := fun p ↦ ((pencil p.1 p.2)⁻¹).map Complex.ofReal
  have hunit (p : Coeff × E) (hp : p ∈ T) : IsUnit (pencil p.1 p.2).det :=
    isUnit_iff_ne_zero.mpr (abs_pos.mp ((half_pos f.determinantGap_pos).trans
      ((ellipticAngularMask_spec f hK).2.2.2.2 _ hp.1 _ hp.2)))
  have hG (p : Coeff × E) (hp : p ∈ T) : ContDiffAt ℝ ∞ G p :=
    contDiff_matrix_map_ofReal.contDiffAt.comp p
      ((contDiffAt_matrix_inv ((Matrix.isUnit_iff_isUnit_det _).mpr (hunit p hp))).comp p
        contDiff_pencil.contDiffAt)
  choose C hC hcomp using fun m ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn x hR hT
      (le_refl m) (fun p hp ↦ (hG p hp).of_le (by simp))
  refine ⟨fun m ↦ 2 * C m * (m + 2 : ℝ), fun m ↦ mul_pos (mul_pos zero_lt_two (hC m)) (by positivity), ?_⟩
  intro L hL Q hQ hmap ξ m
  let a := ellipticSourceMask f hK L ξ
  have ha := (ellipticSourceMask_properties f hK L).2 ξ
  by_cases hz : a = 0
  · have he : (fun y ↦ ellipticInverseSymbol f hK L Q y ξ) = 0 := by
      funext y
      simp only [ellipticInverseSymbol, show ellipticSourceMask f hK L ξ = 0 from hz,
        Complex.ofReal_zero, zero_smul, smul_zero, Pi.zero_apply]
    rw [he, cNorm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (hC m).le) (by positivity))
      (by linarith [cNorm_nonneg (closedBall x RQ) m Q])
  have hL1 := f.radialThreshold_ge_one.trans hL
  obtain ⟨hr, hdir⟩ := ellipticSourceMask_support f hK (zero_lt_one.trans_le hL1)
    (subset_tsupport _ hz)
  have hξ : 1 ≤ ‖ξ‖ := by linarith
  have hξp := zero_lt_one.trans_le hξ
  let F : E → Coeff × E := fun y ↦ (Q y, NormedSpace.normalize ξ)
  have hF : ContDiffOn ℝ ∞ F Ω := hQ.prodMk contDiffOn_const
  have hFT : MapsTo F Ω T := fun _ hy ↦ ⟨hmap hy, hdir⟩
  have hsΩ := hSQ.trans hRQΩ
  have hnorm := hcomp m Ω hΩ hsΩ F hF (hFT.mono_left hsΩ)
  have hQm := cNorm_mono_set_of_contDiffAt (f := Q) (r := m) hSQ (isCompact_closedBall x RQ)
    (fun y hy ↦ (hQ.contDiffAt (hΩ.mem_nhds (hRQΩ hy))).of_le (by simp))
  have hc : cNorm S m (fun _ : E ↦ NormedSpace.normalize ξ) ≤ (m + 1 : ℝ) := by
    have hb (j : ℕ) (_hj : j ≤ m) (y : E) (_hy : y ∈ S) :
        ‖iteratedFDeriv ℝ j (fun _ : E ↦ NormedSpace.normalize ξ) y‖ ≤ 1 := by
      rcases eq_or_ne j 0 with rfl | hj
      · rw [norm_iteratedFDeriv_zero, NormedSpace.norm_normalize (norm_pos_iff.mp hξp)]
      · simp [iteratedFDeriv_const_of_ne hj]
    simpa using cNorm_le_sum_of_bounds (fun _ _ ↦ zero_le_one) hb
  have hpair : cNorm S m F ≤ cNorm (closedBall x RQ) m Q + (m+1 : ℝ) :=
    (cNorm_prodMk_le_on S (isCompact_closedBall _ _) m
      (fun y hy ↦ (hQ.contDiffAt (hΩ.mem_nhds (hsΩ hy))).of_le (by simp))
      (fun _ _ ↦ contDiffAt_const)).trans (add_le_add hQm hc)
  let k : ℂ := ((a * ‖ξ‖⁻¹ : ℝ) : ℂ)
  have he (y : E) (hy : y ∈ S) : (fun z ↦ ellipticInverseSymbol f hK L Q z ξ) =ᶠ[𝓝 y]
      (fun z ↦ k • (G ∘ F) z) := by
    filter_upwards [ellipticInverseSymbol_eq_near f hK L Q hy ξ, hΩ.mem_nhds (hsΩ hy)]
      with z hz hzΩ
    rw [hz, pencil_inv_complex_eq_radial hξp (hunit (F z) (hFT hzΩ)), smul_smul]
    simp only [k, Complex.ofReal_mul, a, F, G, Function.comp_apply]
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq he m, cNorm_const_complex_smul m k
    (fun y hy ↦ ((hG (F y) (hFT (hsΩ hy))).comp y
      (hF.contDiffAt (hΩ.mem_nhds (hsΩ hy)))).of_le (by simp)), ← mul_assoc]
  have hk : (1 + ‖ξ‖) * ‖k‖ ≤ 2 := by
    rw [show ‖k‖ = a * ‖ξ‖⁻¹ by
      simp only [k, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (mul_nonneg ha.1 (inv_nonneg.mpr hξp.le)), ← mul_assoc, ← div_eq_mul_inv]
    apply (div_le_iff₀ hξp).mpr
    have h := mul_le_of_le_one_right (by positivity : 0 ≤ 1 + ‖ξ‖) ha.2
    dsimp only [a]
    linarith
  have hhigh : 1 + cNorm S m F ≤ (m+2 : ℝ) * (1 + cNorm (closedBall x RQ) m Q) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (cNorm_nonneg (closedBall x RQ) m Q),
      cNorm_nonneg (closedBall x RQ) m Q]
  exact (mul_le_mul hk (hnorm.trans (mul_le_mul_of_nonneg_left hhigh (hC m).le))
    (cNorm_nonneg S m (G ∘ F)) zero_le_two).trans_eq (by ring)

/-- The full residual uses one more derivative and retains additive original
`Q,B` profiles at every order. Constants are common to every permitted
enlarged radial threshold (`energy-complete-residual`). -/
theorem exists_ellipticSymbols_weighted_cNorm (hΩ : IsOpen Ω)
    (hRQΩ : closedBall x RQ ⊆ Ω) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ L ≥ f.radialThreshold,
      ∀ (Q : E → Coeff) (B : E → Mat), ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
      MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
      cNorm (closedBall x RQ) 1 Q ≤ M → cNorm (closedBall x RQ) 0 B ≤ M →
      ∀ s ∈ ({ellipticInverseSymbol f hK L Q, ellipticResidualSymbol f hK L Q B} :
        Set (E → E → CMat)), ContDiff ℝ ∞ (Function.uncurry s) ∧
        ∀ ξ m, (1 + ‖ξ‖) * cNorm (closedBall x (2*f.physicalRadius)) m (fun y ↦ s y ξ) ≤
          C m * (1 + cNorm (closedBall x RQ) (m+1) Q + cNorm (closedBall x RQ) (m+1) B) := by
  obtain ⟨D, hD, hinv⟩ := exists_ellipticInverseSymbol_weighted_cNorm f hK hΩ hRQΩ
  have hR : 0 < 2*f.physicalRadius := mul_pos zero_lt_two f.physicalRadius_pos
  have hid (y : E) : physicalCoordinates (0 : Fin (d+1)) y = y := by simp [physicalCoordinates]
  have hphysical : MapsTo (physicalCoordinates (0 : Fin (d+1)))
      (closedBall x (2*f.physicalRadius)) (closedBall x RQ) := by
    intro y hy
    rw [hid]
    exact f.physicalBall_coefficientDomain (closedBall_subset_closedBall (by
      linarith [f.physicalRadius_pos] : 2*f.physicalRadius ≤ 4*f.physicalRadius) hy)
  obtain ⟨P, hP, hact⟩ := exists_physicalSymbolApply_weighted_cNorm_transfer 0 x hR x RQ
    hphysical M D hD
  refine ⟨fun m ↦ D m + P m, fun m ↦ add_pos (hD m) (hP m), ?_⟩
  intro L hL Q B hQ hB hmap hQM hBM s hs
  have hLp := zero_lt_one.trans_le (f.radialThreshold_ge_one.trans hL)
  have he := hinv L hL Q hQ hmap
  have hsi := contDiff_ellipticInverseSymbol f hK hΩ hLp Q hQ hmap
  have hsr := contDiff_ellipticResidualSymbol f hK hΩ hLp Q B hQ hB hmap
  have hnon (m : ℕ) : 0 ≤ 1 + cNorm (closedBall x RQ) (m+1) Q + cNorm (closedBall x RQ) (m+1) B :=
    by linarith [cNorm_nonneg (closedBall x RQ) (m+1) Q, cNorm_nonneg (closedBall x RQ) (m+1) B]
  simp only [mem_insert_iff, mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · refine ⟨hsi, fun ξ m ↦ (he ξ m).trans ?_⟩
    have hb := cNorm_nonneg (closedBall x RQ) (m+1) B
    exact mul_le_mul (le_add_of_nonneg_right (hP m).le)
      (by linarith [cNorm_mono_order (s := closedBall x RQ) (f := Q) (Nat.le_succ m)])
      (by linarith [cNorm_nonneg (closedBall x RQ) m Q]) (add_pos (hD m) (hP m)).le
  · have hh := hact Ω hΩ hRQΩ Q B (ellipticInverseSymbol f hK L Q) hQ hB hsi
    simp only [coefficient, zeroth, hid] at hh
    have hp := hh hsr hQM hBM he
    exact ⟨hsr, fun ξ m ↦ (hp ξ m).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hD m).le) (hnon m))⟩

end JanetCartan.RegularSector.EllipticComplement
