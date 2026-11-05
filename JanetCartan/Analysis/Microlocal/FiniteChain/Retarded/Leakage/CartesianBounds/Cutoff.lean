module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Leakage.CartesianBounds.Jets
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.AmplitudeGrades.Products
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Fixed cutoff profiles and quantitative coordinate transfer

The parent supplies directional output bounds from `KernelDecay` and the shell
construction. The cutoff profile comes from `exists_uniform_literalOutputCutoff`.
Neither a Sobolev estimate nor a differentiated operator formula is assumed.
All constants below are independent of the requested integration order in
`app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open scoped ContDiff BigOperators
open Set
open JanetCartan.RetardedSobolev.Spaces

namespace JanetCartan.FiniteChain.Retarded.Leakage
open KernelDecay KernelSobolev LocalizedKernel

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Directional bounds produced by the half-space estimate control the full
multilinear norm, including order zero (`app:ch_regular:lem:finite-chain`). -/
theorem norm_multilinear_le_of_unit_directions {k : ℕ}
    (a : V [×k]→L[ℝ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v : Fin k → V, (∀ i, ‖v i‖ ≤ 1) → ‖a v‖ ≤ C) : ‖a‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  have hn : ∀ i, ‖NormedSpace.normalize (v i)‖ ≤ 1 := by
    intro i
    by_cases h : v i = 0
    · simp [h]
    · exact (NormedSpace.norm_normalize h).le
  have he : a v = (∏ i, ‖v i‖) • a (fun i => NormedSpace.normalize (v i)) := by
    rw [← a.map_smul_univ]
    congr 1
    funext i
    exact (NormedSpace.norm_smul_normalize (v i)).symm
  rw [he, norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg (fun i _ => norm_nonneg _))]
  calc
    _ ≤ (∏ i, ‖v i‖) * C := mul_le_mul_of_nonneg_left (hb _ hn) (by positivity)
    _ = _ := mul_comm _ _

/-- The fixed output cutoff contributes the ordinary Leibniz convolution.
The arbitrary prefactor `P` is retained once, and the frequency exponent is
exactly the requested output order (`app:ch_regular:eq:chain-tail`). -/
theorem norm_cutoff_mul_iteratedFDeriv_le {χ : V → ℝ} {f : V → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    {H B : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hB : ∀ j, 0 ≤ B j)
    {R P : ℝ} (hR : 1 ≤ R) (hP : 0 ≤ P) (k : ℕ) (x : V)
    (hc : ∀ j ≤ k, ‖iteratedFDeriv ℝ j χ x‖ ≤ H j)
    (hb : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f x‖ ≤ B j * R ^ j * P) :
    ‖iteratedFDeriv ℝ k (fun y => (χ y : ℂ) * f y) x‖ ≤
      derivativeConvolution H B k * R ^ k * P := by
  apply (norm_iteratedFDeriv_mul_le (Complex.ofRealCLM.contDiff.comp hχ) hf x
    (show (k : ℕ∞ω) ≤ ∞ by simp)).trans
  simp only [derivativeConvolution, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hc' : ‖iteratedFDeriv ℝ j (fun y => (χ y : ℂ)) x‖ ≤ H j := by
    change ‖iteratedFDeriv ℝ j (Complex.ofRealLI ∘ χ) x‖ ≤ _
    rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hχ.contDiffAt (by simp)]
    exact hc j hjk
  calc
    _ ≤ (k.choose j : ℝ) * H j * (B (k - j) * R ^ (k - j) * P) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg _))
        (hb _ (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (hH j))
    _ = ((k.choose j : ℝ) * H j * B (k - j)) * R ^ (k - j) * P := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (Nat.sub_le _ _))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hH j)) (hB _))) hP

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Output coordinate map used by the actual compact kernel; time is unchanged
(`app:ch_regular:eq:chain-tail`). -/
def cartesianOutputMap {n : ℕ} (J : (Fin n → ℝ) ≃L[ℝ] E) :
    (ℝ × (Fin n → ℝ)) →L[ℝ] (ℝ × E) :=
  (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).prod
    (J.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))

/-- Finite cutoff/coordinate loss at Sobolev order `m`. The profiles and this
constant are selected independently of the integration order and shell radius
(`app:ch_regular:eq:chain-tail`). -/
def cartesianCutoffJetConstant {n : ℕ} (J : (Fin n → ℝ) ≃L[ℝ] E)
    (H B : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    derivativeConvolution H B k * (max 1 ‖cartesianOutputMap J‖) ^ k

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Nonnegativity of the fixed coordinate and cutoff constant
(`app:ch_regular:eq:chain-tail`). -/
theorem cartesianCutoffJetConstant_nonneg {n : ℕ} (J : (Fin n → ℝ) ≃L[ℝ] E)
    {H B : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hB : ∀ j, 0 ≤ B j) (m : ℕ) :
    0 ≤ cartesianCutoffJetConstant J H B m := by
  exact Finset.sum_nonneg fun k _ => mul_nonneg (derivativeConvolution_nonneg hH hB k)
    (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)

/-- Transfer from directional derivatives of the uncut concrete Fourier kernel
to every Cartesian kernel jet. Bounds are needed only on the explicit compact
base supports. `P` can contain all fixed symbol powers and the entire shell decay
factor; it is unchanged by this transfer (`app:ch_regular:eq:chain-tail`). -/
theorem norm_supportedFourierKernel_jet_le {n m : ℕ}
    (J : (Fin n → ℝ) ≃L[ℝ] E) (upper : Bool)
    (χ α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r)
    (hsχ : HasCompactSupport χ) (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi)) (hsr : HasCompactSupport r)
    {H B : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hB : ∀ j, 0 ≤ B j)
    {R P : ℝ} (hR : 1 ≤ R) (hP : 0 ≤ P)
    (hc : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ H j)
    (hb : ∀ xi ∈ Prod.fst '' tsupport (Function.uncurry mi), ∀ xo ∈ tsupport χ,
      ∀ j ≤ m, ∀ v : Fin j → ℝ × E, (∀ i, ‖v i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ j (fun z => if upper then upperFourierKernel α β mi mo r xi z
          else lowerFourierKernel α β mi mo r xi z) xo v‖ ≤ B j * R ^ j * P)
    (i : JetIndex n m) (p y : (Fin n → ℝ) × ℝ) :
    ‖kernelJet (supportedFourierKernel J upper χ α β mi mo r hχ hα hβ hi ho hr
      hsχ hsα hsβ hsi hsr) i p y‖ ≤ cartesianCutoffJetConstant J H B m * R ^ m * P := by
  let K := supportedFourierKernel J upper χ α β mi mo r hχ hα hβ hi ho hr
    hsχ hsα hsβ hsi hsr
  have hnon : 0 ≤ cartesianCutoffJetConstant J H B m * R ^ m * P :=
    mul_nonneg (mul_nonneg (cartesianCutoffJetConstant_nonneg J hH hB m)
      (pow_nonneg (zero_le_one.trans hR) _)) hP
  change ‖kernelJet K i p y‖ ≤ _
  by_cases hy : y ∈ K.inputSupport
  swap
  · rw [kernelJet_zero_off_input K i p y hy, norm_zero]
    exact hnon
  by_cases hx : (p.2, p.1) ∈ K.outputSupport
  swap
  · rw [kernelJet_zero_off_output K i p y hx, norm_zero]
    exact hnon
  let k := i.1.val + i.2.2.val
  have hkm : k ≤ m := by dsimp [k]; have := i.1.isLt; have := i.2.2.isLt; omega
  let f : ℝ × E → ℂ := fun z => if upper then upperFourierKernel α β mi mo r (y.2, J y.1) z
    else lowerFourierKernel α β mi mo r (y.2, J y.1) z
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_fourierKernel_joint upper α β mi mo r hα hβ hi ho hr hsα hsβ hsi hsr).comp
      (contDiff_const.prodMk contDiff_id)
  have hcut := norm_cutoff_mul_iteratedFDeriv_le hχ hf hH hB hR hP k (p.2, J p.1)
    (fun j hj => hc j (hj.trans hkm) _) (fun j hj =>
      norm_multilinear_le_of_unit_directions _
        (mul_nonneg (mul_nonneg (hB _) (pow_nonneg (zero_le_one.trans hR) _)) hP)
        (hb _ hy _ hx j (hj.trans hkm)))
  apply (norm_cartesianJet_le_iteratedFDeriv (kernelColumn_contDiff K y) i p).trans
  change ‖iteratedFDeriv ℝ k ((fun z => (χ z : ℂ) * f z) ∘ cartesianOutputMap J)
    (p.2, p.1)‖ ≤ _
  have hcf : ContDiff ℝ ∞ (fun z => (χ z : ℂ) * f z) :=
    (Complex.ofRealCLM.contDiff.comp hχ).mul hf
  rw [(cartesianOutputMap J).iteratedFDeriv_comp_right hcf (p.2, p.1) (i := k) (by simp)]
  apply ((iteratedFDeriv ℝ k (fun z => (χ z : ℂ) * f z) _).norm_compContinuousLinearMap_le _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hconst : derivativeConvolution H B k * (max 1 ‖cartesianOutputMap J‖) ^ k ≤
      cartesianCutoffJetConstant J H B m := by
    unfold cartesianCutoffJetConstant
    apply Finset.single_le_sum (f := fun l : ℕ =>
      derivativeConvolution H B l * (max 1 ‖cartesianOutputMap J‖) ^ l)
      (s := Finset.range (m + 1)) (a := k)
    · intro l _
      exact mul_nonneg (derivativeConvolution_nonneg hH hB l)
        (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hkm)
  calc
    _ ≤ (derivativeConvolution H B k * R ^ k * P) * (max 1 ‖cartesianOutputMap J‖) ^ k :=
      mul_le_mul hcut (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) k)
        (pow_nonneg (norm_nonneg _) _)
        (mul_nonneg (mul_nonneg (derivativeConvolution_nonneg hH hB _) (by positivity)) hP)
    _ = (derivativeConvolution H B k * (max 1 ‖cartesianOutputMap J‖) ^ k) * R ^ k * P := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hconst (pow_le_pow_right₀ hR hkm) (by positivity)
        (cartesianCutoffJetConstant_nonneg J hH hB m)) hP

end JanetCartan.FiniteChain.Retarded.Leakage
