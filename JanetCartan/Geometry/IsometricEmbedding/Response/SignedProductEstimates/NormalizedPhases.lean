module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.PhaseJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Sources
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Normalized phases of the same signed-pair witness

The source substitution in `app:ch_pairs:prop:pairs-lag-sum`, Step 1, uses
`rho = lam * q.beat` for the SAME `SignedPairs.Pair` returned by the sampling
geometry. The unnormalized phase, its physical derivative and its protected
direction are identified here before applying the source estimates. The convex
segment estimate cancels the short-chord divisor in every higher phase jet.
No independent pair, reference, cutoff, row or response is selected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open SignedPairs InnerProductSpace NormedSpace
variable {n : ℕ} {G Z : Type*} [NormedAddCommGroup Z] {S : G → Set Z}

/-- Differentiate the exact phase of the supplied signed pair at its true
beat (`app:ch_pairs:setup:pairs-lag`). This identifies the derivative used by
the source estimates with the covector of the ORIGINAL pair; radial labels
remain inside the supplied individual phases. -/
theorem fderiv_normalized_signed_pair_phase (q : Pair G Z S) (φ : G → Z → Euclidean n → ℝ)
    {x : Euclidean n}
    (hφ : ∀ g z, z ∈ S g → DifferentiableAt ℝ (φ g z) x) :
    fderiv ℝ (fun y ↦ q.vector (fun g z ↦ φ g z y) / q.beat) x =
      q.beat⁻¹ • q.vector (fun g z ↦ fderiv ℝ (φ g z) x) := by
  have hd : HasFDerivAt (fun y ↦ q.vector (fun g z ↦ φ g z y))
      (q.vector (fun g z ↦ fderiv ℝ (φ g z) x)) x := by
    cases q with
    | difference g z w hne =>
      exact ((hφ g z z.property).hasFDerivAt.sub (hφ g w w.property).hasFDerivAt)
    | sum g z w =>
      exact ((hφ g z z.property).hasFDerivAt.add (hφ g w w.property).hasFDerivAt)
    | cross g h hne z w s t hs ht =>
      exact (((hφ g z z.property).hasFDerivAt.const_smul s).add
        ((hφ h w w.property).hasFDerivAt.const_smul t))
  have he : (fun y ↦ q.vector (fun g z ↦ φ g z y) / q.beat) =
      q.beat⁻¹ • (fun y ↦ q.vector (fun g z ↦ φ g z y)) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he]
  exact (hd.const_smul q.beat⁻¹).fderiv

/-- The original signed covector band and angular set give the normalized
phase's derivative band and the SAME protected set under the canonical dual
isometry (`app:ch_pairs:setup:pairs-lag`). Division by the positive true beat
cancels its size, without changing any geometric constant. This supplies the
first-derivative inputs of `SourceGeometry` and the full-mask tail estimate. -/
theorem normalized_signed_pair_phase_geometry
    (q : Pair G Z S) (φ : G → Z → Euclidean n → ℝ) {x : Euclidean n}
    (hφ : ∀ g z, z ∈ S g → DifferentiableAt ℝ (φ g z) x)
    {a b : ℝ} {K : Set (Euclidean n)}
    (hband : a * q.beat ≤ ‖q.vector (fun g z ↦ gradient (φ g z) x)‖ ∧
      ‖q.vector (fun g z ↦ gradient (φ g z) x)‖ ≤ b * q.beat)
    (hK : normalize (q.vector (fun g z ↦ gradient (φ g z) x)) ∈ K) :
    let d := fderiv ℝ (fun y ↦ q.vector (fun g z ↦ φ g z y) / q.beat) x
    a ≤ ‖d‖ ∧ ‖d‖ ≤ b ∧ normalize d ∈ (toDual ℝ (Euclidean n)) '' K := by
  have hdual : q.vector (fun g z ↦ fderiv ℝ (φ g z) x) =
      toDual ℝ (Euclidean n) (q.vector (fun g z ↦ gradient (φ g z) x)) := by
    cases q <;> simp only [Pair.vector, map_sub, map_add, map_smul, toDual_gradient]
  dsimp only
  rw [fderiv_normalized_signed_pair_phase q φ hφ, hdual]
  have hnorm : ‖q.beat⁻¹ • toDual ℝ (Euclidean n)
      (q.vector (fun g z ↦ gradient (φ g z) x))‖ =
      q.beat⁻¹ * ‖q.vector (fun g z ↦ gradient (φ g z) x)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr q.beat_pos),
      LinearIsometryEquiv.norm_map]
  rw [hnorm]
  refine ⟨?_, ?_, ?_⟩
  · calc
      a = q.beat⁻¹ * (a * q.beat) := by field_simp [q.beat_pos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hband.1 (inv_nonneg.mpr q.beat_pos.le)
  · calc
      _ ≤ q.beat⁻¹ * (b * q.beat) :=
        mul_le_mul_of_nonneg_left hband.2 (inv_nonneg.mpr q.beat_pos.le)
      _ = b := by field_simp [q.beat_pos.ne']
  · rw [normalize_smul_of_pos (inv_pos.mpr q.beat_pos)]
    refine ⟨_, hK, ?_⟩
    simp only [NormedSpace.normalize, map_smul, LinearIsometryEquiv.norm_map]

open ResponseTransfer.SourceNegative ResponseSourceExtension
variable {N : ℕ} {J : Type*}

/-- The literal sampled plus source equals the real quadrature at
`lam * q.beat` for the SAME supplied pair witness
(`app:ch_pairs:eq:pairs-lag-one-error`). The witness comes from
`sample_plus_represented_with_beat`; doubled carriers are included. The whole
source cutoff and actual tensor amplitudes remain unchanged. -/
theorem cutoff_plusSource_eq_real_signedPair_source
    (q : Pair G Z S) (φ : G → Z → Euclidean n → ℝ)
    (group : J → G) (z : J → Z) (i j : J)
    (hpair : ∀ f : G → Z → ℝ, q.vector f = f (group i) (z i) + f (group j) (z j))
    (χ : Euclidean n → ℝ) (A : J → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    {lam : ℝ} (hlam : lam ≠ 0) :
    (fun x ↦ χ x • ProductSum.plusSource (fun k y ↦ lam * φ (group k) (z k) y) A i j x) =
      tensorFieldRealPart (modulatedSource χ
        (fun x ↦ q.vector (fun g z ↦ φ g z x) / q.beat)
        (fun x ↦ symmetricBilinearTensor (A i x) (A j x)) (lam * q.beat)) := by
  have he : (fun x ↦ (lam * φ (group i) (z i) x + lam * φ (group j) (z j) x) /
      (lam * q.beat)) = (fun x ↦ q.vector (fun g z ↦ φ g z x) / q.beat) := by
    funext x
    rw [hpair (fun g z ↦ φ g z x)]
    field_simp
  rw [cutoff_plusSource_eq_real_modulatedSource χ _ A i j
    (mul_ne_zero hlam q.beat_pos.ne'), he]

/-- The literal sampled difference source uses the SAME separated-pair
witness and its true beat (`app:ch_pairs:eq:pairs-lag-one-error`). Supply the
witness from `sample_minus_represented_with_beat`; no equality between
independently selected pairs is required. The complete conjugated tensor and
original source cutoff are retained. -/
theorem cutoff_minusSource_eq_real_signedPair_source
    (q : Pair G Z S) (φ : G → Z → Euclidean n → ℝ)
    (group : J → G) (z : J → Z) (i j : J)
    (hpair : ∀ f : G → Z → ℝ, q.vector f = f (group i) (z i) - f (group j) (z j))
    (χ : Euclidean n → ℝ) (A : J → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    {lam : ℝ} (hlam : lam ≠ 0) :
    (fun x ↦ χ x • ProductSum.minusSource (fun k y ↦ lam * φ (group k) (z k) y) A i j x) =
      tensorFieldRealPart (modulatedSource χ
        (fun x ↦ q.vector (fun g z ↦ φ g z x) / q.beat)
        (fun x ↦ symmetricBilinearTensor (A i x) ((A j x).map conj)) (lam * q.beat)) := by
  have he : (fun x ↦ (lam * φ (group i) (z i) x - lam * φ (group j) (z j) x) /
      (lam * q.beat)) = (fun x ↦ q.vector (fun g z ↦ φ g z x) / q.beat) := by
    funext x
    rw [hpair (fun g z ↦ φ g z x)]
    field_simp
  rw [cutoff_minusSource_eq_real_modulatedSource χ _ A i j
    (mul_ne_zero hlam q.beat_pos.ne'), he]

/-- Primitive individual and mixed parameter/spatial phase jets yield one
profile for every normalized signed pair (`app:ch_pairs:setup:pairs-lag`).
The convex segment formula cancels the difference beat; sums, doubled carriers
and both cross-group signs cost at most the fixed factor two. This supplies
the higher-phase field in `sourceGeometry_normalized_signed_pair`. -/
theorem norm_iteratedFDeriv_normalized_signed_pair_phase_le
    {H : Type*} {T : H → Set (Euclidean 3)}
    (hT : ∀ g, Convex ℝ (T g)) (q : Pair H (Euclidean 3) T)
    (φ : H → Euclidean 3 → Euclidean n → ℝ) {r : ℕ} {x : Euclidean n}
    (D : H → Euclidean 3 → Euclidean 3 →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ Euclidean n) ℝ)
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hφ : ∀ g z, z ∈ T g → ContDiffAt ℝ r (φ g z) x)
    (hbase : ∀ g z, z ∈ T g → ‖iteratedFDeriv ℝ r (φ g z) x‖ ≤ C * L ^ (r - 1))
    (hD : ∀ g z, z ∈ T g →
      HasFDerivWithinAt (fun w ↦ iteratedFDeriv ℝ r (φ g w) x) (D g z) (T g) z)
    (hDb : ∀ g z, z ∈ T g → ‖D g z‖ ≤ C * L ^ (r - 1)) :
    ‖iteratedFDeriv ℝ r (fun y ↦ q.vector (fun g z ↦ φ g z y) / q.beat) x‖ ≤
      (2 * C) * L ^ (r - 1) := by
  cases q with
  | difference g z w hne =>
    have hz : (z : Euclidean 3) ≠ w := fun he ↦ hne (Subtype.ext he)
    have hd := norm_iteratedFDeriv_divided_phase_le (hT g) (φ g) (D g)
      (hD g) (hDb g) z.property w.property hz (hφ g z z.property) (hφ g w w.property)
    apply hd.trans
    nlinarith [mul_nonneg hC (pow_nonneg hL (r - 1))]
  | sum g z w =>
    change ‖iteratedFDeriv ℝ r (fun y ↦ (φ g z y + φ g w y) / 1) x‖ ≤ _
    simp only [div_one]
    change ‖iteratedFDeriv ℝ r (φ g z + φ g w) x‖ ≤ _
    rw [iteratedFDeriv_add_apply (hφ g z z.property) (hφ g w w.property)]
    apply (norm_add_le _ _).trans
    nlinarith [hbase g z z.property, hbase g w w.property]
  | cross g h hne z w s t hs ht =>
    change ‖iteratedFDeriv ℝ r (fun y ↦ (s * φ g z y + t * φ h w y) / 1) x‖ ≤ _
    simp only [div_one]
    have he : (fun y ↦ s * φ g z y + t * φ h w y) = s • φ g z + t • φ h w := rfl
    rw [he, iteratedFDeriv_add_apply (f := s • φ g z) (g := t • φ h w)
      ((hφ g z z.property).const_smul s) ((hφ h w w.property).const_smul t),
      iteratedFDeriv_const_smul_apply (hφ g z z.property),
      iteratedFDeriv_const_smul_apply (hφ h w w.property)]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hs, ht, one_mul, one_mul]
    nlinarith [hbase g z z.property, hbase h w w.property]

/-- Instantiate the EXISTING source geometry for the normalized phase of
the supplied signed pair (`app:ch_pairs:prop:pairs-lag-sum`, Step 1). All
higher phase bounds are derived from the original individual and mixed jets;
no normalized-phase bound is assumed. Signed geometry supplies `hgrad`, while
the retained history/phase producer supplies the primitive jets on the same
support and parameter patches. Consumers are the shell and negative-source
estimates. This does not construct the fixed response or its residual chains. -/
theorem sourceGeometry_normalized_signed_pair
    {H : Type*} {T : H → Set (Euclidean 3)}
    (hT : ∀ g, Convex ℝ (T g)) (q : Pair H (Euclidean 3) T)
    (χ : Euclidean n → ℝ) (φ : H → Euclidean 3 → Euclidean n → ℝ)
    {Ssrc : Set (Euclidean n)} (hSsrc : IsCompact Ssrc) (hs : tsupport χ ⊆ Ssrc)
    (hχ : ContDiff ℝ ∞ χ) (hφ : ∀ g z, z ∈ T g → ContDiff ℝ ∞ (φ g z))
    {a b L : ℝ} (ha : 0 < a) (hab : a < b) (hL : 1 ≤ L)
    (P X : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (hX : ∀ j, 0 ≤ X j)
    (hgrad : ∀ x ∈ Ssrc,
      a * q.beat ≤ ‖q.vector (fun g z ↦ gradient (φ g z) x)‖ ∧
      ‖q.vector (fun g z ↦ gradient (φ g z) x)‖ ≤ b * q.beat)
    (hbase : ∀ x ∈ Ssrc, ∀ j, 1 ≤ j → ∀ g z, z ∈ T g →
      ‖iteratedFDeriv ℝ (j + 1) (φ g z) x‖ ≤ P j * L ^ j)
    (hmixed : ∀ x ∈ Ssrc, ∀ j, 1 ≤ j → ∀ g z, z ∈ T g →
      DifferentiableAt ℝ (fun w ↦ iteratedFDeriv ℝ (j + 1) (φ g w) x) z)
    (hmixedBound : ∀ x ∈ Ssrc, ∀ j, 1 ≤ j → ∀ g z, z ∈ T g →
      ‖fderiv ℝ (fun w ↦ iteratedFDeriv ℝ (j + 1) (φ g w) x) z‖ ≤ P j * L ^ j)
    (hcut : ∀ x j, ‖iteratedFDeriv ℝ j χ x‖ ≤ X j * L ^ j) :
    SourceGeometry χ (fun x ↦ q.vector (fun g z ↦ φ g z x) / q.beat)
      Ssrc a b L (fun j ↦ 2 * P j) X := by
  have hp : ContDiff ℝ ∞ (fun y ↦ q.vector (fun g z ↦ φ g z y)) := by
    cases q with
    | difference g z w hne => exact (hφ g z z.property).sub (hφ g w w.property)
    | sum g z w => exact (hφ g z z.property).add (hφ g w w.property)
    | cross g h hne z w s t hs ht =>
      exact ((hφ g z z.property).const_smul s).add ((hφ h w w.property).const_smul t)
  have hband (x : Euclidean n) (hx : x ∈ Ssrc) :=
    normalized_signed_pair_phase_geometry q φ
      (fun g z hz ↦ ((hφ g z hz).differentiable (by simp)).differentiableAt)
      (hgrad x hx) (K := Set.univ) (Set.mem_univ _)
  refine ⟨hχ, hp.div_const q.beat, hSsrc, hs, ha, hab, hL,
    fun j ↦ mul_nonneg (by norm_num) (hP j), hX,
    fun x hx ↦ (hband x hx).1, fun x hx ↦ (hband x hx).2.1, ?_, hcut⟩
  intro x hx j hj
  have hh := norm_iteratedFDeriv_normalized_signed_pair_phase_le hT q φ
    (fun g z ↦ fderiv ℝ (fun w ↦ iteratedFDeriv ℝ (j + 1) (φ g w) x) z)
    (hP j) (zero_le_one.trans hL)
    (fun g z hz ↦ (hφ g z hz).contDiffAt.of_le (by simp))
    (by simpa only [Nat.add_sub_cancel] using hbase x hx j hj)
    (fun g z hz ↦ (hmixed x hx j hj g z hz).hasFDerivAt.hasFDerivWithinAt)
    (by simpa only [Nat.add_sub_cancel] using hmixedBound x hx j hj)
  simpa only [Nat.add_sub_cancel] using hh

end JanetCartan.SignedProductEstimates
