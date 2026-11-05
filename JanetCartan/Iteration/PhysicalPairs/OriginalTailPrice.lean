module
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedInverseRemainder

/-! # Pay the original finite current coefficient shift only twice

The original graph supplies `sectorLowOrder d` coefficient reserve. The native
strong gain uses the shifted index `sectorLowOrder d + (d+2)`. Do NOT assume
that the former is the latter. The additive one-gain induction is linear in its
coefficient prices: a factor `L^(d+2)` is paid just twice, not once per power.
The actual true-frequency `1/1000` gap absorbs both fixed powers. Consumer: the
Neumann tail in `app:ch_regular:eq:inverse-remainder` for `main:prop:pairs`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.OriginalTailPrice
open LocalSobolev ArbitraryAccuracy FixedDomainInverse GeometricProfile JanetCartan.Localization RegularSector.FiniteAssembly.CoefficientNorms

/-- A constant price in the actual additive gain is paid once, uniformly in
power depth. This would fail for a multiplicative high-coefficient recurrence. -/
theorem dilated_gain (G D : ℕ → ℝ) (hG : ∀ k, 0 ≤ G k) (t : ℝ) (ht : 1 ≤ t) (k : ℕ) :
    powerGainConstant G (fun j ↦ D j*t) k ≤ powerGainConstant G D k*t := by
  induction k with
  | zero => simpa only [powerGainConstant,one_mul] using ht
  | succ k ih =>
    simp only [powerGainConstant]
    calc
      _ ≤ G (k+1)*(powerGainConstant G D k*t+D (k+1)*t) := mul_le_mul_of_nonneg_left (add_le_add ih le_rfl) (hG (k+1))
      _ = _ := by ring

/-- Use the unstrengthened original reserve on both actual coefficient slots.
The `offset` is the unchanged fixed shift in the strong gain theorem. -/
theorem coefficient_price {n : ℕ} (x : Euclidean n) {r R : ℝ} (hr : 0 < r) (hR : r < R)
    (AQ AB : ℕ → ℝ) (hp : ∀ k, 0 ≤ AQ k) (hb : ∀ k, 0 ≤ AB k) (reserve offset : ℕ) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
        (hQ : ContDiff ℝ ∞ Q) (hB : ContDiff ℝ ∞ B) (L : ℝ), 1 ≤ L →
      HasDerivativeProfile (closedBall x R) Q reserve L AQ → HasDerivativeProfile (closedBall x R) B reserve L AB →
      let W := ball x r
      let q := smoothCoefficientL2 isOpen_univ hr (subset_univ _) Q hQ.contDiffOn
      let b := smoothCoefficientL2 isOpen_univ hr (subset_univ _) B hB.contDiffOn
      ∀ k : ℕ, 1+(restrictionSobolevNorm W (k+(reserve+offset)) q+restrictionSobolevNorm W (k+(reserve+offset)) b) ≤
        D k * L^(k+offset) := by
  obtain ⟨D,hD,bound⟩ := exists_coefficient_pair_inverse_profile x hr hR AQ AB hp hb reserve reserve le_rfl
  refine ⟨fun k ↦ D (k+offset),fun k ↦ (hD _).le,?_⟩
  intro Q B hQ hB L hL hQj hBj W q b k
  simpa only [W,q,b,←add_assoc,show k+reserve+offset = k+offset+reserve by omega] using
    bound isOpen_univ (subset_univ _) Q B hQ hB L hL hQj hBj (k+offset)

/-- Uniform tail at every requested physical observation order and accuracy.
Its only analytic slots are the native forward/adjoint one-gain and the original
once-measured input's negative Fourier norm, not a tail-output estimate. -/
theorem inverse_tail {n : ℕ} (θ : ℝ) (hθ : θ < 1) (G D CN : ℕ → ℝ)
    (hG : ∀ k, 0 ≤ G k) (hD : ∀ k, 0 ≤ D k) (hN : ∀ k, 0 ≤ CN k) (offset s q : ℕ) :
    ∃ depth : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (W : Set (Euclidean n)) (hW : MeasurableSet W)
      (K : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n)), ‖K‖ ≤ θ →
      ∀ (L ρ : ℝ), 1 ≤ L → 1 ≤ ρ → L ≤ ρ^(1-(1/1000:ℝ)) →
      ∀ (a : ℕ → ℝ) (b : ℕ), (∀ j, 0 ≤ a j) → Monotone a →
      (∀ k, 1 + a (k+b) ≤ D k * L ^ (k+offset)) →
      (∀ (k : ℕ) (v : LocalL2 W (Euclidean n)), MemRestrictionSobolev W k v →
        (MemRestrictionSobolev W (k+1) (K v) ∧ restrictionSobolevNorm W (k+1) (K v) ≤
          G (k+1)*(restrictionSobolevNorm W k v + (1+a (k+1+b))*‖v‖)) ∧
        (MemRestrictionSobolev W (k+1) (K.adjoint v) ∧ restrictionSobolevNorm W (k+1) (K.adjoint v) ≤
          G (k+1)*(restrictionSobolevNorm W k v + (1+a (k+1+b))*‖v‖))) →
      ∀ v : LocalL2 W (Euclidean n), componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin n) ℝ)
        (-(depth:ℝ)) (SmallSupport.zeroExtend hW v) ≤ CN depth / ρ^depth →
      MemRestrictionSobolev W s (neumannInverse K ((K^(depth+s)) v)) ∧
        restrictionSobolevNorm W s (neumannInverse K ((K^(depth+s)) v)) ≤ B*(ρ^q)⁻¹ := by
  obtain ⟨depth,_,hdepth⟩ := exists_tail_order (by norm_num : (0:ℝ) < 1/1000) ((s+2*offset : ℕ) : ℝ) q
  let lc := localDualityConstant n depth (EuclideanSpace.basisFun (Fin n) ℝ)
  let ic := inverseTameConstant θ G s
  have hIc : 0 ≤ ic := (inverseTameConstant_pos hθ hG s).le
  have hLc : 0 ≤ lc := (localDualityConstant_pos _ _ _).le
  let B := ic * (powerGainConstant G D s + D s) * ((lc*CN depth)*powerGainConstant G D depth)
  have hPG := powerGainConstant_nonneg hG hD
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hIc (add_nonneg (hPG _) (hD _)))
    (mul_nonneg (mul_nonneg hLc (hN _)) (hPG _))
  refine ⟨depth,B,hB,?_⟩
  intro W hW K hK L ρ hL hρ hg a b ha ham hprofile hgain v hv
  let t := L^offset
  have ht : 1 ≤ t := one_le_pow₀ hL
  let D' := fun k ↦ D k*t
  have hD' (k : ℕ) : 0 ≤ D' k := mul_nonneg (hD _) (zero_le_one.trans ht)
  have hp (k : ℕ) : 1 + a (k+b) ≤ D' k*L^k := (hprofile k).trans_eq (by dsimp [D',t]; rw [pow_add]; ring)
  obtain ⟨hm,hnorm⟩ := inverse_remainder_restrictionSobolev (EuclideanSpace.basisFun (Fin n) ℝ) hW K
    hK hθ hL (zero_lt_one.trans_le hρ) (by norm_num : (0:ℝ) ≤ 1) (hN depth) hG hG hD' ha ham hp
    (fun k z hz ↦ (hgain k z hz).1.1) (fun k z hz ↦ (hgain k z hz).1.2)
    (fun k z hz ↦ (hgain k z hz).2.1) (fun k z hz ↦ (hgain k z hz).2.2) depth s v (by simpa only [mul_one] using hv)
  have hleft : powerGainConstant G D' s + D' s ≤ powerGainConstant G D s*t + D s*t :=
    add_le_add (dilated_gain G D hG t ht s) le_rfl
  have hright := dilated_gain G D hG t ht depth
  have hf : ic*(powerGainConstant G D' s+D' s) * ((lc*CN depth)*powerGainConstant G D' depth) ≤ B*t^2 := by
    calc
      _ ≤ (ic*(powerGainConstant G D s*t+D s*t))*((lc*CN depth)*(powerGainConstant G D depth*t)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hleft hIc) (mul_le_mul_of_nonneg_left hright (mul_nonneg hLc (hN _)))
          (mul_nonneg (mul_nonneg hLc (hN _)) (powerGainConstant_nonneg hG hD' _))
          (mul_nonneg hIc (add_nonneg (mul_nonneg (hPG _) (zero_le_one.trans ht)) (hD' _)))
      _ = _ := by dsimp [B]; ring
  have hLp := hg.trans (Real.rpow_le_self_of_one_le hρ (by norm_num : (1-1/1000 : ℝ) ≤ 1))
  have hl := zero_le_one.trans hL
  have hdecay : t^2*L^s*(L/ρ)^depth ≤ (ρ^q)⁻¹ := by
    rw [show t^2*L^s = L^(s+2*offset) by dsimp [t]; rw [two_mul,pow_add,pow_add,pow_two]; ring]
    apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl hLp _) (by positivity)).trans
    simpa only [Real.rpow_natCast,Real.rpow_neg (zero_le_one.trans hρ)] using tail_factor_le_negative_power hρ hl hg hdepth
  refine ⟨hm,hnorm.trans ?_⟩
  calc
    _ ≤ B*t^2 * 1 * L^s * (L/ρ)^depth := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf zero_le_one) (pow_nonneg hl _)) (by positivity)
    _ = B*(t^2*L^s*(L/ρ)^depth) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay hB
end JanetCartan.PhysicalPairs.OriginalTailPrice
end
