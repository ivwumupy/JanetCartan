module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.WeightedBounds.Support
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.PrimitiveInputs
public import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Finite normalized jets of the weighted amplitude

The order-zero normalized amplitude of
`app:ch_regular_base:eq:actual-matrix-inverse` uses the original phase through
order `N+2` and original mask and matrix through order `N`. All constants are
chosen before the data and shell. The consuming whole-image graph theorem takes
`N = primitiveNormalReserve n`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison WholeImageGeometry LowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The finite composition cost for the weighted coefficient is explicit:
`N! C (max 1 M)^N`, where `C` bounds the fixed coefficient jets. The primitive
field in this intermediate lemma is produced from original phase derivatives
by `normalized_weightedPhaseDifferential_jets_le`, never from weighted jets.
Source: `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem exists_weightedPrimitiveField_jet_bound (N : ℕ) (M : ℝ)
    {δJ δU : ℝ} (hδJ : 0 < δJ) (hδU : 0 < δU) :
    ∃ C > 0, ∀ (f : E × E → WeightedPrimitiveCoefficients n r) (Ω : Set (E × E)),
      IsOpen Ω → ContDiffOn ℝ ∞ f Ω →
      (∀ q ∈ Ω, δJ ≤ |(f q).2.1.det|) →
      (∀ q ∈ Ω, δU ≤ ‖(f q).2.2.det‖) →
      (∀ q ∈ Ω, ∀ k ≤ N, ‖iteratedFDeriv ℝ k f q‖ ≤ M) →
      ∀ q ∈ Ω, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (weightedPrimitiveCoefficient ∘ f) q‖ ≤
          (N.factorial : ℝ) * C * (max 1 M)^N := by
  obtain ⟨C, hC, hb⟩ := exists_weightedPrimitiveCoefficient_jet_bound (n := n) (r := r)
    N M hδJ hδU
  refine ⟨C, hC, ?_⟩
  intro f Ω hΩ hf hJ hU hj q hq k hk
  let V : Set (WeightedPrimitiveCoefficients n r) :=
    {p | p.2.1.det ≠ 0 ∧ p.2.2.det ≠ 0}
  have hV : IsOpen V :=
    (isOpen_ne.preimage (ContinuousLinearMap.continuous_det.comp continuous_snd.fst)).inter
      (isOpen_ne.preimage continuous_snd.snd.matrix_det)
  have hcoeff : ContDiffOn ℝ ∞ (@weightedPrimitiveCoefficient n r) V :=
    fun p hp ↦ (weightedPrimitiveCoefficient_contDiffAt hp.1 hp.2).contDiffWithinAt
  have hmap : MapsTo f Ω V := fun p hp ↦
    ⟨abs_pos.mp (hδJ.trans_le (hJ p hp)), norm_pos_iff.mp (hδU.trans_le (hU p hp))⟩
  apply (InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le hΩ hV hf hcoeff hmap hq k
    (fun i hi ↦ hb (f q) (by simpa using hj q hq 0 (Nat.zero_le N))
      (hJ q hq) (hU q hq) i (hi.trans hk))
    (fun i _ hi ↦ hj q hq i (hi.trans hk))).trans
  have hfac : (k.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hk
  gcongr
  exact le_max_left _ _

/-- Normalized order-zero jets of the literal weighted amplitude follow from
original normalized phase, mask and matrix jets, with costs `N+2`, `N`, `N`.
The phase and matrix gaps are required only on the buffered chart. In particular,
no derivative of an inverse, absolute determinant or weighted amplitude is an
input. Source: `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem exists_maskedWeightedAmplitude_normalized_jet_bound (N : ℕ) (M Bφ : ℝ)
    {δJ δU : ℝ} (hδJ : 0 < δJ) (hδU : 0 < δU) :
    ∃ C > 0, ∀ (X D : Set E) (S : E → E → ℝ) (c : E → E → ℝ) (U : E → E → Mat),
      IsOpen X → IsOpen D → Convex ℝ X →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      ContDiffOn ℝ ∞ (Function.uncurry c) (X ×ˢ D) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (X ×ˢ D) →
      (∀ x ∈ X, ∀ u ∈ D, δJ ≤ phaseJacobian S x u) →
      (∀ x ∈ X, ∀ u ∈ D, δU ≤ ‖(U x u).det‖) →
      ∀ (ρ a b : ℝ), ρ ≠ 0 →
      (∀ z ∈ X ×ˢ normalizedSourceBand D ρ a b, ∀ k ≤ N + 2,
        ‖iteratedFDeriv ℝ k (Function.uncurry (normalizedPhase ρ S)) z‖ ≤ Bφ) →
      (∀ z ∈ X ×ˢ normalizedSourceBand D ρ a b, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : E × E ↦ c q.1 (ρ • q.2)) z‖ ≤ M) →
      (∀ z ∈ X ×ˢ normalizedSourceBand D ρ a b, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (Function.uncurry (normalizedNormalMatrix ρ 0 U)) z‖ ≤ M) →
      ∀ z ∈ X ×ˢ normalizedSourceBand D ρ a b, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ρ 0 (maskedWeightedAmplitude S c U))) z‖ ≤ C := by
  let M' := max M ((3 : ℝ)^(N + 1) * |Bφ|)
  obtain ⟨C, hC, hb⟩ := exists_weightedPrimitiveField_jet_bound (n := n) (r := r)
    N M' hδJ hδU
  refine ⟨(N.factorial : ℝ) * C * (max 1 M')^N, by positivity, ?_⟩
  intro X D S c U hX hD hcX hS hc hU hJ hdet ρ a b hρ hφjet hcjet hUjet z hz k hk
  let Ω := X ×ˢ normalizedSourceBand D ρ a b
  let c' : E × E → ℝ := fun q ↦ c q.1 (ρ • q.2)
  let J' : E × E → (E →L[ℝ] E) := fun q ↦ weightedPhaseDifferential S q.1 (ρ • q.2)
  let U' : E × E → Mat := Function.uncurry (normalizedNormalMatrix ρ 0 U)
  let f : E × E → WeightedPrimitiveCoefficients n r := fun q ↦ (c' q, J' q, U' q)
  have hΩ : IsOpen Ω := hX.prod (isOpen_normalizedSourceBand hD ρ a b)
  have hd : ContDiffOn ℝ ∞ (fun q : E × E ↦ (q.1, ρ • q.2)) Ω :=
    contDiffOn_fst.prodMk (contDiffOn_snd.const_smul ρ)
  have hmap : MapsTo (fun q : E × E ↦ (q.1, ρ • q.2)) Ω (X ×ˢ D) :=
    fun _ hq ↦ ⟨hq.1, hq.2.1⟩
  have hc' : ContDiffOn ℝ ∞ c' Ω := hc.comp hd hmap
  have hJ' : ContDiffOn ℝ ∞ J' Ω :=
    (weightedPhaseDifferential_contDiffOn hX hD hcX hS).comp hd hmap
  have hU' : ContDiffOn ℝ ∞ U' Ω := normalizedMatrix_contDiffOn_sourceBand hU ρ a b
  have hf : ContDiffOn ℝ ∞ f Ω := hc'.prodMk (hJ'.prodMk hU')
  have he : EqOn
      (Function.uncurry (normalizedNormalMatrix ρ 0 (maskedWeightedAmplitude S c U)))
      (weightedPrimitiveCoefficient ∘ f) Ω := by
    intro q hq
    simp only [normalizedNormalMatrix, neg_zero, Real.rpow_zero, one_smul,
      Function.uncurry_def, Function.comp_def, weightedPrimitiveCoefficient, f,
      c', J', U', maskedWeightedAmplitude]
    rw [phaseJacobian_eq_abs_weightedPhaseDifferential hX hD hcX hS hq.1 hq.2.1]
  have hejet := iteratedFDerivWithin_congr (𝕜 := ℝ) he hz k
  rw [iteratedFDerivWithin_of_isOpen _ hΩ hz,
    iteratedFDerivWithin_of_isOpen _ hΩ hz] at hejet
  rw [hejet]
  apply hb f Ω hΩ hf
  · intro q hq
    change δJ ≤ |(weightedPhaseDifferential S q.1 (ρ • q.2)).det|
    rw [← phaseJacobian_eq_abs_weightedPhaseDifferential hX hD hcX hS hq.1 hq.2.1]
    exact hJ q.1 hq.1 _ hq.2.1
  · intro q hq
    simpa [f, U', Function.uncurry_def, normalizedNormalMatrix] using hdet q.1 hq.1 _ hq.2.1
  · intro q hq i hi
    dsimp [f]
    rw [iteratedFDeriv_prodMk (hc'.contDiffAt (hΩ.mem_nhds hq))
      ((hJ'.prodMk hU').contDiffAt (hΩ.mem_nhds hq)) (by simp),
      iteratedFDeriv_prodMk (hJ'.contDiffAt (hΩ.mem_nhds hq))
        (hU'.contDiffAt (hΩ.mem_nhds hq)) (by simp),
      ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
    exact max_le ((hcjet q hq i hi).trans (le_max_left _ _))
      (max_le ((normalized_weightedPhaseDifferential_jets_le N Bφ hX hD hcX hS
        hρ a b hφjet hq hi).trans (le_max_right _ _))
        ((hUjet q hq i hi).trans (le_max_left _ _)))
  · exact hz
  · exact hk

/-- The masked transport amplitude has the explicit finite product cost
`2^N (max 1 M)^2`, using only original mask and matrix jets through `N`.
It is the other graph in `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem maskedTransportAmplitude_normalized_jets_le (N : ℕ) (M : ℝ)
    {c : E → E → ℝ} {U : E → E → Mat} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D)
    (hc : ContDiffOn ℝ ∞ (Function.uncurry c) (X ×ˢ D))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (X ×ˢ D)) (ρ a b : ℝ)
    (hcjet : ∀ z ∈ X ×ˢ normalizedSourceBand D ρ a b, ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (fun q : E × E ↦ c q.1 (ρ • q.2)) z‖ ≤ M)
    (hUjet : ∀ z ∈ X ×ˢ normalizedSourceBand D ρ a b, ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (Function.uncurry (normalizedNormalMatrix ρ 0 U)) z‖ ≤ M)
    {z : E × E} (hz : z ∈ X ×ˢ normalizedSourceBand D ρ a b)
    {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k
      (Function.uncurry (normalizedNormalMatrix ρ 0 (maskedTransportAmplitude c U))) z‖ ≤
        (2 : ℝ)^N * max 1 M ^ 2 := by
  let Ω := X ×ˢ normalizedSourceBand D ρ a b
  let c' : E × E → ℝ := fun q ↦ c q.1 (ρ • q.2)
  let U' := Function.uncurry (normalizedNormalMatrix ρ 0 U)
  have hΩ : IsOpen Ω := hX.prod (isOpen_normalizedSourceBand hD ρ a b)
  have hd : ContDiffOn ℝ ∞ (fun q : E × E ↦ (q.1, ρ • q.2)) Ω :=
    contDiffOn_fst.prodMk (contDiffOn_snd.const_smul ρ)
  have hc' : ContDiffOn ℝ ∞ c' Ω := hc.comp hd (fun _ hq ↦ ⟨hq.1, hq.2.1⟩)
  have hU' : ContDiffOn ℝ ∞ U' Ω := normalizedMatrix_contDiffOn_sourceBand hU ρ a b
  have hcast (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (Complex.ofRealCLM ∘ c') z‖ ≤ max 1 M := by
    apply (Complex.ofRealCLM.norm_iteratedFDeriv_comp_left
      (hc'.contDiffAt (hΩ.mem_nhds hz)) (by simp)).trans
    rw [Complex.ofRealCLM_norm, one_mul]
    exact (hcjet z hz i (hi.trans hk)).trans (le_max_right _ _)
  have hb := InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
    (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Mat →L[ℝ] Mat)
    ContinuousLinearMap.opNorm_lsmul_le hΩ (Complex.ofRealCLM.contDiff.comp_contDiffOn hc')
    hU' (le_trans zero_le_one (le_max_left 1 M)) hz k hcast
    (fun i hi ↦ (hUjet z hz i (hi.trans hk)).trans (le_max_right 1 M))
  have he : Function.uncurry (normalizedNormalMatrix ρ 0 (maskedTransportAmplitude c U)) =
      fun q ↦ (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Mat →L[ℝ] Mat)
        ((Complex.ofRealCLM ∘ c') q) (U' q) := by
    funext q
    simp [normalizedNormalMatrix, maskedTransportAmplitude, c', U', Function.uncurry_def]
  rw [he]
  apply hb.trans
  rw [mul_assoc, ← pow_two]
  gcongr
  norm_num

end JanetCartan.FourierIntegral.UncutNormal
