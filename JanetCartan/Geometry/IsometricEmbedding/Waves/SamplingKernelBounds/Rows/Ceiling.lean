module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Rows.HilbertSchmidt
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Bounds

/-! # Uniform prefix estimates at the fixed sampling ceiling -/

@[expose] public noncomputable section
namespace JanetCartan.SamplingKernelBounds
open RawInputRealization

/-- The geometric summation step shared by the two row bounds in
`app:ch_waves:eq:sampling-operator-bounds`. It is uniform over every subset,
hence over all later choices of prefix. -/
theorem sum_prefix_dyadic_bound {J m : ℕ} (hm : 1 ≤ m) (s : Finset (Fin J))
    (a : Fin J → ℝ) {C C_ceiling Λ : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, a i ≤ C * ((2 : ℝ) ^ i.val) ^ m)
    (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) :
    (∑ i ∈ s, a i) ≤ (C * C_ceiling ^ m) * Λ ^ m := by
  calc
    _ ≤ ∑ i ∈ s, C * ((2 : ℝ) ^ i.val) ^ m := Finset.sum_le_sum (fun i _ ↦ ha i)
    _ ≤ ∑ i : Fin J, C * ((2 : ℝ) ^ i.val) ^ m :=
      Finset.sum_le_univ_sum_of_nonneg (fun i ↦ mul_nonneg hC (by positivity))
    _ = C * ∑ i : Fin J, ((2 : ℝ) ^ i.val) ^ m := (Finset.mul_sum ..).symm
    _ ≤ C * ((2 : ℝ) ^ J) ^ m :=
      mul_le_mul_of_nonneg_left (sum_dyadic_radii_pow_le hm J) hC
    _ ≤ C * (C_ceiling * Λ) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hceil m) hC
    _ = _ := by rw [mul_pow]; ring

variable {n J : ℕ}

/-- Uniform squared operator bound for every prefix, conditional on the sharp
per-band oscillatory estimate from `jc-raw-primary-slice-l2`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_prefixRow_sq_ceiling_le (s : Finset (Fin J))
    (T : ∀ i : Fin J, AnnularL2 n ((2 : ℝ) ^ i.val) →L[ℂ] Output n)
    {C_op C_ceiling Λ : ℝ} (hC : 0 ≤ C_op)
    (hT : ∀ i, ‖T i‖ ^ 2 ≤ C_op * (2 : ℝ) ^ i.val)
    (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) :
    ‖prefixRow s T‖ ^ 2 ≤ (C_op * C_ceiling) * Λ := by
  apply (norm_prefixRow_sq_le s T).trans
  simpa using sum_prefix_dyadic_bound (m := 1) le_rfl s (fun i ↦ ‖T i‖ ^ 2) hC
    (by simpa using hT) hceil

/-- Uniform squared Hilbert–Schmidt bound for all prefixes. The per-band
hypotheses are supplied by `BandKernelData.operator_hilbertSchmidt_bound`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem hilbertSchmidtSq_prefixRow_ceiling_le {κ : Fin J → Type*} {δ : Type*}
    (hn : 1 ≤ n) (s : Finset (Fin J))
    (T : ∀ i : Fin J, AnnularL2 n ((2 : ℝ) ^ i.val) →L[ℂ] Output n)
    (c : ∀ i, HilbertBasis (κ i) ℂ (AnnularL2 n ((2 : ℝ) ^ i.val)))
    (b : HilbertBasis δ ℂ (Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val)))
    {C_HS C_ceiling Λ : ℝ} (hC : 0 ≤ C_HS)
    (hT : ∀ i, IsHilbertSchmidt (c i) (T i))
    (hband : ∀ i, hilbertSchmidtSq (c i) (T i) ≤ C_HS * ((2 : ℝ) ^ i.val) ^ n)
    (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) :
    hilbertSchmidtSq b (prefixRow s T) ≤ (C_HS * C_ceiling ^ n) * Λ ^ n := by
  rw [(prefixRow_hilbertSchmidt s T c b (fun i _ ↦ hT i)).2]
  exact sum_prefix_dyadic_bound hn s _ hC hband hceil

/-- Uniform trace bound for every finite compression of every prefix normal
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem trace_finiteCompression_prefixRow_ceiling_le {κ : Fin J → Type*}
    (hn : 1 ≤ n) (s : Finset (Fin J))
    (T : ∀ i : Fin J, AnnularL2 n ((2 : ℝ) ^ i.val) →L[ℂ] Output n)
    (c : ∀ i, HilbertBasis (κ i) ℂ (AnnularL2 n ((2 : ℝ) ^ i.val)))
    {C_HS C_ceiling Λ : ℝ} (hC : 0 ≤ C_HS)
    (hT : ∀ i, IsHilbertSchmidt (c i) (T i))
    (hband : ∀ i, hilbertSchmidtSq (c i) (T i) ≤ C_HS * ((2 : ℝ) ^ i.val) ^ n)
    (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ)
    (U : Submodule ℂ (Output n)) [FiniteDimensional ℂ U] :
    RCLike.re (LinearMap.trace ℂ U
      (finiteCompression U (prefixRow s T ∘L (prefixRow s T).adjoint)).toLinearMap) ≤
        (C_HS * C_ceiling ^ n) * Λ ^ n :=
  (trace_finiteCompression_prefixRow_normal_le s T c (fun i _ ↦ hT i) U).trans
    (sum_prefix_dyadic_bound hn s _ hC hband hceil)

end JanetCartan.SamplingKernelBounds
