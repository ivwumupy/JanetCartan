module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.Sobolev
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Finite derivative reserves for the initial source estimate

The integration constant at order `q` uses mask and amplitude jets only
through `q`, and phase jets only through `q+1`. Higher derivatives exist by
smoothness but need no uniform bound. This is the finite reserve required by
the original initialized source application of `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph JanetCartan.Localization Pseudodifferential
open FiniteChain.Retarded.KernelDecay

private theorem transpose_constant_congr_through_order
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (e : ι → E) (B C B' C' : ℕ → ℝ) (q r : ℕ)
    (hB : ∀ j ≤ q+r, B j = B' j) (hC : ∀ j ≤ q+r, C j = C' j) :
    transposeDerivativeConstant e B C q r = transposeDerivativeConstant e B' C' q r := by
  induction q generalizing r with
  | zero => exact hC r (by omega)
  | succ q ih =>
    simp only [transposeDerivativeConstant]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ r+1 := by have := Finset.mem_range.mp hj; omega
    rw [hB j (by omega), ih (r+1-j)
      (fun k hk ↦ hB k (by omega)) (fun k hk ↦ hC k (by omega))]

/-- Only finitely many primitive jets enter the initial-source integration
constant. In particular unused high derivatives of different histories never
alter the chosen constant (`app:ch_regular:eq:source-tail`). -/
theorem sourceLocalizationKernelConstant_congr_through_order
    {n : ℕ} (K : Set (Euclidean n)) (δ G : ℝ)
    (P D C P' D' C' : ℕ → ℝ) (q : ℕ)
    (hP : ∀ j ≤ q, P j = P' j) (hD : ∀ j ≤ q, D j = D' j)
    (hC : ∀ j ≤ q, C j = C' j) :
    sourceLocalizationKernelConstant K δ G P D C q =
      sourceLocalizationKernelConstant K δ G P' D' C' q := by
  unfold sourceLocalizationKernelConstant
  congr 1
  apply transpose_constant_congr_through_order
  · intro j hj
    unfold phaseCoefficientDerivativeBound phaseDerivativeMajorant
    congr 3
    apply Finset.sum_congr rfl
    intro k hk
    rw [hP k (by have := Finset.mem_range.mp hk; omega)]
  · intro j hj
    unfold derivativeConvolution
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    dsimp only
    rw [hD k (by omega), hC (j-k) (by omega)]

private theorem exists_extension_of_finite_jet_profile
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} (hK : IsCompact K) (f : E → F)
    (hf : ∀ y ∈ K, ContDiffAt ℝ ∞ f y)
    (P w : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (hw : ∀ j, 0 < w j)
    (q shift low : ℕ)
    (hb : ∀ y ∈ K, ∀ j, low ≤ j → j ≤ q →
      ‖iteratedFDeriv ℝ (j+shift) f y‖ ≤ P j * w j) :
    ∃ P' : ℕ → ℝ, (∀ j, 0 ≤ P' j) ∧ (∀ j ≤ q, P' j = P j) ∧
      ∀ y ∈ K, ∀ j, low ≤ j → ‖iteratedFDeriv ℝ (j+shift) f y‖ ≤ P' j * w j := by
  let P' j := if j ≤ q then P j else cNorm K (j+shift) f / w j
  refine ⟨P', fun j ↦ ?_, fun j hj ↦ by simp [P', hj], fun y hy j hj ↦ ?_⟩
  · dsimp only [P']
    split_ifs
    · exact hP j
    · exact div_nonneg (cNorm_nonneg _ _ _) (hw j).le
  · dsimp only [P']
    split_ifs with hjq
    · exact hb y hy j hj hjq
    · rw [div_mul_cancel₀ _ (hw j).ne']
      exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun z hz ↦ (hf z hz).of_le (by simp)) hy le_rfl

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The actual initial defect estimate needs only mask/amplitude derivatives
through `q` and phase derivatives through `q+1`. Higher derivatives are extended
using compactness, then eliminated from the integration constant. The original
amplitude budget, including zero, is preserved (`app:ch_regular:eq:source-tail`). -/
theorem bounded_initialSource_defect_sobolev_bound_finite
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (φ : E → ℝ) (a : E → V)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U) (hs : tsupport a ⊆ K)
    {S : Set (E × E)} {δ G A L ρ : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (hL : 1 ≤ L) (hρ : 1 ≤ ρ) (b : ℕ)
    (hgraph : ∀ y ∈ tsupport a, (y, gradient φ y) ∈ S)
    (hplateau : cthickening δ S ⊆ interior {p | m p = 1})
    (hupper : ∀ y ∈ U, ‖fderiv ℝ φ y‖ ≤ G)
    (P D C : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (hD : ∀ j, 0 ≤ D j)
    (hC : ∀ j, 0 ≤ C j)
    (q : ℕ)
    (hmjet : ∀ j, j ≤ q → ∀ p, ‖iteratedFDeriv ℝ j m p‖ ≤ D j)
    (hp : ∀ y ∈ tsupport a, ∀ j, 1 ≤ j → j ≤ q →
      ‖iteratedFDeriv ℝ (j + 1) φ y‖ ≤ P j * L ^ j)
    (hajet : ∀ y ∈ tsupport a, ∀ j, j ≤ q →
      ‖iteratedFDeriv ℝ j a y‖ ≤ C j * ((A * L ^ b) * L ^ j))
    (M : H →L[ℂ] H)
    (hM : ∀ v : H, M v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ m (fun y ↦ (v y).ofLp) x))
    (u : H) (hu : u =ᵐ[volume] fun y ↦ phaseOscillation (fun z ↦ ρ * φ z) y • a y)
    {s : ℝ} (hszero : 0 ≤ s) (hq : s + (n : ℝ) / 2 < q) :
    MemVectorFourierSobolev s (u - M u) ∧
      vectorFourierSobolevNorm s (u - M u) ≤
        ((r : ℝ) * sourceLocalizationKernelConstant K δ G P D C q *
          Real.sqrt (∫ ξ : E, (1 + ‖ξ‖) ^ (-(2 * (q : ℝ) - 2 * s)))) *
            (A * L ^ b) * (ρ ^ (s + (n : ℝ) / 2) * (L / ρ) ^ q) := by
  have hKa : IsCompact (tsupport a) := hK.of_isClosed_subset (isClosed_tsupport _) hs
  have hLp : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨P', hP', hPeq, hp'⟩ := exists_extension_of_finite_jet_profile hKa φ
    (fun y hy ↦ hφ.contDiffAt (hU.mem_nhds (hKU (hs hy))))
    P (fun j ↦ L^j) hP (fun j ↦ pow_pos hLp j) q 1 1 hp
  obtain ⟨D', hD', hDeq, hd'⟩ := exists_extension_of_finite_jet_profile hmc m
    (fun _ _ ↦ hm.contDiffAt) D (fun _ ↦ 1) hD (fun _ ↦ zero_lt_one) q 0 0
    (fun y _ j _ hj ↦ by simpa using hmjet j hj y)
  have hmjet' j p : ‖iteratedFDeriv ℝ j m p‖ ≤ D' j := by
    by_cases hp : p ∈ tsupport m
    · simpa using hd' p hp j (Nat.zero_le j)
    · have hz : iteratedFDeriv ℝ j m p = 0 :=
        Function.notMem_support.mp (fun h ↦ hp (support_iteratedFDeriv_subset j h))
      rw [hz, norm_zero]
      exact hD' j
  obtain ⟨C', hC', hCeq, ha'⟩ : ∃ C' : ℕ → ℝ,
      (∀ j, 0 ≤ C' j) ∧ (∀ j ≤ q, C' j = C j) ∧
      ∀ y ∈ tsupport a, ∀ j,
        ‖iteratedFDeriv ℝ j a y‖ ≤ C' j * ((A * L^b) * L^j) := by
    rcases hA.eq_or_lt with hAz | hAp
    · have ha0 : a = 0 := by
        funext y
        by_cases hy : y ∈ tsupport a
        · have hz := hajet y hy 0 (Nat.zero_le q)
          rw [← hAz] at hz
          simpa only [norm_iteratedFDeriv_zero, zero_mul, mul_zero, norm_le_zero_iff,
            Pi.zero_apply] using hz
        · exact image_eq_zero_of_notMem_tsupport hy
      refine ⟨C, hC, fun _ _ ↦ rfl, ?_⟩
      intro y _ j
      simp only [ha0, iteratedFDeriv_zero, Pi.zero_apply, norm_zero, ← hAz, zero_mul,
        mul_zero, le_refl]
    · obtain ⟨C', hC', hCeq, ha'⟩ := exists_extension_of_finite_jet_profile hKa a
        (fun y hy ↦ ha.contDiffAt (hU.mem_nhds (hKU (hs hy))))
        C (fun j ↦ (A * L^b) * L^j) hC (fun j ↦ by positivity) q 0 0
        (fun y hy j _ hj ↦ by simpa only [Nat.add_zero] using hajet y hy j hj)
      exact ⟨C', hC', hCeq, fun y hy j ↦ by simpa using ha' y hy j (Nat.zero_le j)⟩
  have hb := bounded_initialSource_defect_sobolev_bound m hm hmc φ a hU hK hKU hφ ha hs
    hδ hA hL hρ b hgraph hplateau hupper P' D' C' hP' hD' hC' hmjet' hp' ha'
    M hM u hu hszero q hq
  rwa [sourceLocalizationKernelConstant_congr_through_order K δ G P' D' C' P D C q
    hPeq hDeq hCeq] at hb

end JanetCartan.InitialSourceLocalization
