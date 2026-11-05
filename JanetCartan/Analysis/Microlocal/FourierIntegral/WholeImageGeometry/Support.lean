module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Basic
public import Mathlib.Topology.Sequences

/-!
# Transporting the original closed support

The whole normal image need not contain the closure of a smaller common target.
Instead, frequency comparison makes the forward chart proper on the original
closed support. This gives the closed-image and buffer fields of
`LowBounds.PrimitiveNormalGeometry` in `app:ch_regular_base:eq:actual-normal-amplitude`.
The frequency comparison below is an explicit remaining obligation of the
homogeneous phase construction; no estimate on the inverse is assumed.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Forward frequency comparison transports any original closed support
strictly inside the chart to a closed set. Unbounded frequency tails are allowed.
This is the support step of `app:ch_regular_base:eq:actual-normal-amplitude`.
The homogeneous phase and determinant gap must produce `hfrequency`. -/
theorem isClosed_normalForward_image_of_frequency_bound
    {S : E → E → ℝ} {X D : Set E} {K : Set (NormalVariables n)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hK : IsClosed K) (hKsub : K ⊆ X ×ˢ (X ×ˢ D))
    {C : ℝ} (hC : 0 ≤ C)
    (hfrequency : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
      ‖u‖ ≤ C * ‖averagedGradient S x y u‖) :
    IsClosed (normalForwardCoordinates S '' K) := by
  have hforward : ContinuousOn (normalForwardCoordinates S) (X ×ˢ (X ×ˢ D)) :=
    continuousOn_fst.prodMk (continuousOn_snd.fst.prodMk
      (averagedGradient_contDiffOn hX hD hcX hS).continuousOn)
  apply IsSeqClosed.isClosed
  intro f y hf hlim
  choose q hq heq using hf
  obtain ⟨R, hR, hbound⟩ := (Metric.isBounded_range_of_tendsto f hlim).exists_pos_norm_le
  have hqbound (i : ℕ) : ‖q i‖ ≤ max 1 C * R := by
    have hb : ‖normalForwardCoordinates S (q i)‖ ≤ R :=
      (heq i).symm ▸ hbound _ (mem_range_self i)
    have hmem := hKsub (hq i)
    have hx : ‖(q i).1‖ ≤ R := (norm_fst_le (normalForwardCoordinates S (q i))).trans hb
    have hy : ‖(q i).2.1‖ ≤ R :=
      ((norm_fst_le (normalForwardCoordinates S (q i)).2).trans
        (norm_snd_le (normalForwardCoordinates S (q i)))).trans hb
    have hξ : ‖averagedGradient S (q i).1 (q i).2.1 (q i).2.2‖ ≤ R :=
      ((norm_snd_le (normalForwardCoordinates S (q i)).2).trans
        (norm_snd_le (normalForwardCoordinates S (q i)))).trans hb
    have hRle : R ≤ max 1 C * R := le_mul_of_one_le_left hR.le (le_max_left _ _)
    change max ‖(q i).1‖ (max ‖(q i).2.1‖ ‖(q i).2.2‖) ≤ _
    refine max_le (hx.trans hRle) (max_le (hy.trans hRle) ?_)
    exact (hfrequency _ hmem.1 _ hmem.2.1 _ hmem.2.2).trans
      ((mul_le_mul_of_nonneg_left hξ hC).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hR.le))
  have hcompact : IsCompact (Metric.closedBall (0 : NormalVariables n) (max 1 C * R) ∩ K) :=
    (isCompact_closedBall _ _).inter_right hK
  obtain ⟨p, hp, φ, hφ, ht⟩ := hcompact.tendsto_subseq
    (fun i ↦ ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hqbound i, hq i⟩)
  have hm : Tendsto (q ∘ φ) atTop (𝓝[K] p) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun i ↦ hq (φ i))⟩
  have hflim := ((hforward.mono hKsub) p hp.2).tendsto.comp hm
  have he : normalForwardCoordinates S ∘ (q ∘ φ) = f ∘ φ := by
    funext i
    exact heq (φ i)
  rw [he] at hflim
  exact ⟨p, hp.2, tendsto_nhds_unique hflim (hlim.comp hφ.tendsto_atTop)⟩

/-- An original support inside the source chart automatically has its full
transported image inside the buffered normal domain. No common target occurs
in this buffer law (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem normalForward_image_subset_bufferedNormalDomain
    {S : E → E → ℝ} {X D : Set E} {K : Set (NormalVariables n)}
    (hKsub : K ⊆ X ×ˢ (X ×ˢ D)) :
    normalForwardCoordinates S '' K ⊆ bufferedNormalDomain X D S := by
  rw [← normalForwardCoordinates_image]
  exact image_mono hKsub

/-- Construct all fields of `PrimitiveNormalGeometry` from the original
smooth amplitudes and closed supported source set, once forward frequency
comparison is supplied by the homogeneous phase construction. The original
amplitude hypotheses are local smoothness, paired support in `K`, and vanishing
off the physical output box. No transported support or inverse regularity is
an input. Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem primitiveNormalGeometry_of_frequency_bound
    {S : E → E → ℝ} {X D : Set E} {K : Set (NormalVariables n)}
    {A B : E → E → Mat}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hinj : ∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|)
    {C : ℝ} (hC : 0 ≤ C)
    (hfrequency : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
      ‖u‖ ≤ C * ‖averagedGradient S x y u‖)
    (hK : IsClosed K) (hKsub : K ⊆ X ×ˢ (X ×ˢ D))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (X ×ˢ D))
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) (X ×ˢ D))
    (hsupport : ∀ q ∈ X ×ˢ (X ×ˢ D), A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K)
    (hleft : ∀ x u, x ∉ X → A x u = 0)
    (hright : ∀ y u, y ∉ X → B y u = 0) :
    PrimitiveNormalGeometry X D S A B (wholeImageInverse S D) (averagedJacobian S)
      (X ×ˢ (X ×ˢ D)) K := by
  refine ⟨isOpen_bufferedNormalDomain hX hD hcX hS hinj hδ hgap,
    wholeImageInverse_contDiffOn hX hD hcX hS hinj hδ hgap,
    mapsTo_wholeImageInverse, ?_, ?_, fun _ hq ↦ normalForward_wholeImageInverse hq,
    hsupport, isClosed_normalForward_image_of_frequency_bound hX hD hcX hS hK hKsub hC hfrequency,
    normalForward_image_subset_bufferedNormalDomain hKsub, hleft, hright⟩
  · exact (averagedJacobian_contDiffOn hX hD hcX hS).prodMk
      ((hA.comp (contDiffOn_fst.prodMk contDiffOn_snd.snd) (fun _ hq ↦ ⟨hq.1, hq.2.2⟩)).prodMk
        (hB.comp (contDiffOn_snd.fst.prodMk contDiffOn_snd.snd) (fun _ hq ↦ hq.2)))
  · intro q hq
    exact abs_pos.mp (hδ.trans_le (hgap _ hq.1 _ hq.2.1 _ hq.2.2))

end JanetCartan.FourierIntegral.WholeImageGeometry
