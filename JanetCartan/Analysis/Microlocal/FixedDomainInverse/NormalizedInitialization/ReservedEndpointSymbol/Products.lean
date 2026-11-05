module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.SourceEndpoint.Products
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Calculus

/-!
# Reserve-preserving multiplication in the selected endpoint symbol

The actual endpoint in `app:ch_regular_base:eq:energy-complete-residual`
multiplies the fixed source masks, the original time coefficient and the
retained diagonal amplitude. Applying the existing graded bilinear calculus
locally preserves the natural low-order plateau of these three factors.
The consumer is the normalized endpoint input of
`DiagonalPdo.exists_diagonalPDO_joint_sobolev_of_primitive_jets`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization

open FiniteChain.Retarded.KernelDecay ResponseTransfer.GradedPrimitives

variable {d : ℕ}
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- The local product of the endpoint's actual matrix factors preserves
one reserve, with the frequency factors kept outside the fixed convolution.
This is the `Q₀W₁` step of `app:ch_regular:eq:high-amplitude`; the proof
instantiates the existing reserve-graded bilinear theorem. -/
theorem norm_iteratedFDeriv_endpoint_product_reserved_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : V → Mat} {v : V} (hf : ContDiffAt ℝ ∞ f v) (hg : ContDiffAt ℝ ∞ g v)
    {A B : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) {S T L : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hL : 1 ≤ L) (R : ℕ)
    (ha : ∀ j, ‖iteratedFDeriv ℝ j f v‖ ≤ S * A j * L ^ (j-R))
    (hb : ∀ j, ‖iteratedFDeriv ℝ j g v‖ ≤ T * B j * L ^ (j-R)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun w ↦ f w * g w) v‖ ≤
      (S * T) * derivativeConvolution A B n * L ^ (n-R) := by
  obtain ⟨U, hUv, hUf⟩ := hf.contDiffOn (m := n) (by simp) (by simp)
  obtain ⟨U', hU'v, hUg⟩ := hg.contDiffOn (m := n) (by simp) (by simp)
  obtain ⟨O, hOU, hO, hv⟩ := _root_.mem_nhds_iff.mp (Filter.inter_mem hUv hU'v)
  let mulMap := ContinuousLinearMap.mul ℝ Mat
  have h := norm_jet_bilinear_le mulMap hO
    (hUf.mono (hOU.trans inter_subset_left))
    (hUg.mono (hOU.trans inter_subset_right)) (k := n) le_rfl hv
    (fun j ↦ S*A j) (fun j ↦ T*B j)
    (fun j ↦ mul_nonneg hS (hA j)) (fun j ↦ mul_nonneg hT (hB j)) hL R
    (fun j _ ↦ ha j) (fun j _ ↦ hb j)
  have he : bilinearConstant mulMap (fun j ↦ S*A j) (fun j ↦ T*B j) n =
      ‖mulMap‖ * ((S*T) * derivativeConvolution A B n) := by
    unfold bilinearConstant derivativeConvolution
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at h
  apply h.trans
  exact mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ Mat)
      (mul_nonneg (mul_nonneg hS hT) (derivativeConvolution_nonneg hA hB n))).trans_eq
        (one_mul _)) (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
