module
public import JanetCartan.Iteration.PhysicalPairs.OriginalMaskRows
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedNegativeSource
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.QuadratureNorm

/-! # Negative Fourier prices for the SAME once-measured reduced quadrature

Only the auxiliary *envelope used in the estimate* uses `χ₃`, which is one on
the measured `χ₂` support. Neither the physical tensor nor its corrected input
is replaced. No high-order norm of the inverse is an input. These are the
original-source slots of `app:ch_regular:eq:inverse-remainder` for `main:prop:pairs`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory Filter
open scoped ContDiff NNReal ENNReal ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.OriginalNegativeRows
open GeometricProfile LocalSobolev ArbitraryAccuracy ResponseTransfer.SourceNegative Pseudodifferential
open FixedDomainInverse SmallSupport SignedProductEstimates ResponseSourceExtension Sampling.BackgroundModulation
variable {d N : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))

theorem lower (K : Set E) (hK : IsCompact K) (hn : ∀ x ∈ K, x ≠ 0) : ∃ a : ℝ, 0 < a ∧ ∀ y ∈ K, a ≤ ‖y‖ := by
  by_cases h : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn h continuous_norm.continuousOn
    exact ⟨‖x‖,norm_pos_iff.mpr (hn _ hx),fun _ hy ↦ hmin hy⟩
  · exact ⟨1,zero_lt_one,fun y hy ↦ False.elim (h ⟨y,hy⟩)⟩

def cut_price (χ : E → ℝ) (j : ℕ) : ℝ := cNorm (tsupport χ) j χ

theorem cut_nonneg (χ : E → ℝ) (j : ℕ) : 0 ≤ cut_price χ j := cNorm_nonneg ..

theorem cut_jets (χ : E → ℝ) (hc : HasCompactSupport χ) (hχ : ContDiff ℝ ∞ χ) (L : ℝ) (hL : 1 ≤ L) :
    ∀ y j, ‖iteratedFDeriv ℝ j χ y‖ ≤ cut_price χ j*L^j := by
  intro y j
  apply le_trans _ (le_mul_of_one_le_right (cut_nonneg χ j) (one_le_pow₀ hL))
  by_cases hy : y ∈ tsupport χ
  · exact norm_iteratedFDeriv_le_cNorm hc (hχ.of_le (by simp)) hy le_rfl
  · rw [show iteratedFDeriv ℝ j χ y = 0 from image_eq_zero_of_notMem_tsupport (fun hh ↦ hy (tsupport_iteratedFDeriv_subset j hh)),norm_zero]
    exact cut_nonneg χ j

/-- Convert the compact protected frequency range into the genuine lower dual
bound for the original phase, including the nonuniform near-diagonal beat. -/
theorem geometry (χ φ : E → ℝ) (K U : Set E) (c G L : ℝ) (P : ℕ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) (hs : ContDiff ℝ ∞ φ)
    (hp : 0 < c) (hK : ∀ y ∈ K, c ≤ ‖y‖) (hL : 1 ≤ L) (hP : ∀ k, 0 ≤ P k)
    (hgrad : ∀ y ∈ U, gradient φ y ∈ K) (hup : ∀ y ∈ U, ‖fderiv ℝ φ y‖ ≤ G)
    (hj : ∀ y ∈ U, ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ (j+1) φ y‖ ≤ P j*L^j) :
    SourceGeometry χ φ (tsupport χ) c (max c G + 1) L P (cut_price χ) := by
  refine ⟨hχ,hs,hc,Subset.rfl,hp,lt_of_le_of_lt (le_max_left _ _) (lt_add_one _),hL,hP,cut_nonneg χ,?_,?_,?_,cut_jets χ hc hχ L hL⟩
  · intro x hx
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hK _ (hgrad x (hχU hx))
  · intro x hx
    exact ((hup x (hχU hx)).trans (le_max_right _ _)).trans (lt_add_one _).le
  · exact fun y hy ↦ hj y (hχU hy)

theorem original_quadrature {W : Set E} (hW : MeasurableSet W) (u : LocalL2 W E) (f : E → CV)
    (hf : MemLp f 2 volume) (he : zeroExtend hW u =ᵐ[volume] fun x ↦ euclideanRealPart (f x))
    (k : ℕ) (D : ℝ) (hm : MemVectorFourierSobolev (-(k:ℝ)) (hf.toLp f))
    (hb : vectorFourierSobolevNorm (-(k:ℝ)) (hf.toLp f) ≤ D) :
    componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ) (-(k:ℝ)) (zeroExtend hW u) ≤ D := by
  have eq : zeroExtend hW u = l2RealPart volume (hf.toLp f) := by
    apply Lp.ext
    filter_upwards [he,euclideanRealPart.coeFn_compLpL (hf.toLp f),hf.coeFn_toLp] with x hx hr hv
    exact hx.trans (hr.trans (congrArg euclideanRealPart hv)).symm
  rw [eq]
  exact (componentFourierSobolevNorm_l2RealPart_le hm).trans hb

/-- The uniform polynomial family is selected before both full Schwartz waves,
both source labels and either frequency. All estimates are on the original
local input under its one and only zero extension. -/
theorem exists_price (χ ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hone : EqOn ψ (fun _ ↦ 1) (tsupport χ)) (c G : ℝ) (hpos : 0 < c) (P Z CQ C : ℕ → ℝ)
    (hZ : ∀ k, 0 ≤ Z k) (hCQ : ∀ k, 0 ≤ CQ k) (hC : ∀ k, 0 ≤ C k) :
    ∃ CN : ℕ → ℝ, (∀ k, 0 ≤ CN k) ∧ ∀ (U W : Set E), IsOpen U → ∀ hW : MeasurableSet W,
      tsupport ψ ⊆ U → ∀ (η φ : E → ℝ) (L ρ : ℝ), SourceGeometry χ φ (tsupport χ) c G L P (cut_price χ) →
      1 ≤ ρ → L ≤ ρ^(1-(1/1000:ℝ)) → ∀ (Q : E → Fin (d+1) → MetricTensor (d+1))
        (A B : E → Matrix (Fin N) (Fin (d+1)) ℂ), ContDiffOn ℝ ∞ η U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      (∀ y ∈ U, ∀ k, ‖iteratedFDeriv ℝ k η y‖ ≤ Z k*L^k) →
      (∀ y ∈ U, ∀ k, ‖iteratedFDeriv ℝ k Q y‖ ≤ CQ k*L^k) →
      (∀ y ∈ U, ∀ k, ‖iteratedFDeriv ℝ k A y‖ ≤ C k*L^k) →
      (∀ y ∈ U, ∀ k, ‖iteratedFDeriv ℝ k B y‖ ≤ C k*L^k) →
      ∀ (minus : Bool) (u : LocalL2 W E), (zeroExtend hW u =ᵐ[volume] fun y ↦
        euclideanRealPart (SampledMask.reduced_wave χ η Q A B minus φ ρ y)) →
      ∀ k : ℕ, componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ) (-(k:ℝ))
        (zeroExtend hW u) ≤ CN k / ρ^k := by
  obtain ⟨D,hD,price⟩ := exists_reduced_signed_negative_source_constants (N := N) (G := G) hc (tsupport χ) hpos
    (by norm_num : (0:ℝ) < 1/1000) (by norm_num) P (cut_price χ) (cut_price ψ) Z CQ C
    (cut_nonneg χ) (cut_nonneg ψ) hZ hCQ hC
  refine ⟨D,hD,?_⟩
  intro U W hU hW hψU η φ L ρ hg hρ hgap Q A B hη hQ hA hB hηj hQj hAj hBj minus u he k
  obtain ⟨hp,hm,hs⟩ := price U hU χ ψ η φ φ L ρ ρ hg hg hψ (Subset.refl _) hψU hone hρ hρ hgap hgap
    Q A B hη hQ hA hB (fun y _ ↦ cut_jets ψ hc hψ L hg.scale_one_le y) hηj hQj hAj hBj
  cases minus with
  | false =>
    apply original_quadrature hW u _ hp he k _ (hs k).1.1
    simpa only [div_eq_mul_inv] using (hs k).1.2
  | true =>
    apply original_quadrature hW u _ hm he k _ (hs k).2.1
    simpa only [div_eq_mul_inv] using (hs k).2.2
end JanetCartan.PhysicalPairs.OriginalNegativeRows
end
