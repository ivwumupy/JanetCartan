module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.Spatial

/-!
# Normalized spatial expressions supply the transfer interface

The only operator inputs below are bounded realizations agreeing with the
literal kernels. Smooth coefficients and their equalities on the original
supports supply the expression identities and support closure, rather than
postulating either one. Consumer: `DerivativeBounds.SobolevAssembly`, for
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NormalizedTransfer
open FourierIntegral FullAmplitudePrimitiveBudget.Local
open IsometricEmbedding.Response.NearCarrier SpatialRealization
variable {n : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin 1)) 2 (volume : Measure E)

/-- Smoothness and the original normalized support, with no operator
assertion. Consumer: `app:ch_response:eq:direct-envelope-profile`. -/
def SupportedAmplitude (K : Set (Point n)) (b : Point n → ℂ) : Prop :=
  ContDiff ℝ ∞ b ∧ tsupport b ⊆ K

/-- The original compact masks imply the support predicate used by spatial
induction (`app:ch_response:eq:direct-envelope-profile`). -/
theorem supportedAmplitude_of_masks {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {b : Point n → ℂ} (hb : ContDiff ℝ ∞ b)
    (hs : ∀ x y ε, x ∉ X ∨ y ∉ Y ∨ ε ∉ F → b ((x, y), ε) = 0) :
    SupportedAmplitude ((X ×ˢ Y) ×ˢ F) b := by
  refine ⟨hb, closure_minimal ?_ ((hX.prod hY).prod hF).isClosed⟩
  intro z hz
  by_contra hn
  exact hz (hs z.1.1 z.1.2 z.2 (by simpa only [mem_prod, not_and_or, or_assoc] using hn))

/-- All datum branches retain the original supports, from primitive
smoothness (`app:ch_response:eq:direct-envelope-profile`). -/
theorem supportedAmplitude_coefficientProduct (a : ι → Point n → ℂ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (b : AmplitudeExpression (Point n) ℂ ι)
    {K : Set (Point n)} (hb : SupportedAmplitude K (b.evaluate a))
    (i : ι) (M : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) :
    SupportedAmplitude K ((b.coefficientProduct M i).evaluate a) :=
  ⟨(b.coefficientProduct M i).contDiff_evaluate a ha,
    (tsupport_coefficientProduct a b M i).trans hb.2⟩

/-- All divergence branches retain the original supports, including every
derivative of masks and coefficients (`app:ch_response:eq:direct-envelope-profile`). -/
theorem supportedAmplitude_divergenceTransfer (a : ι → Point n → ℂ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (b : AmplitudeExpression (Point n) ℂ ι)
    {K : Set (Point n)} (hb : SupportedAmplitude K (b.evaluate a))
    (v : Point n) (qs : List (Point n × ι × (ℂ →L[ℝ] ℂ →L[ℝ] ℂ))) :
    SupportedAmplitude K ((b.divergenceTransfer v qs).evaluate a) :=
  ⟨(b.divergenceTransfer v qs).contDiff_evaluate a ha,
    (tsupport_divergenceTransfer a b v qs).trans hb.2⟩

/-- Source slices of the recovered amplitude lie in the preimage of its
original closed support. This localizes the inverse/phase premises in the
reverse spatial transfer (`app:ch_response:eq:direct-envelope-profile`). -/
theorem source_slice_support {r : ℕ} (ρ : ℝ) {b : Point n → ℂ}
    {K : Set (Point n)} (hs : tsupport b ⊆ K) (x δ : E) :
    tsupport (fun y ↦ scalarPhysicalAmplitude (r := r) ρ b x y δ) ⊆
      (fun y ↦ ((x, y), ρ⁻¹ • δ)) ⁻¹' K := by
  have hzero : scalarMatrixMap (r := r) (0 : ℂ) = 0 := map_zero _
  exact (tsupport_comp_subset hzero (fun y ↦ b ((x, y), ρ⁻¹ • δ))).trans
    ((tsupport_comp_subset_preimage b
      ((continuous_const.prodMk continuous_id).prodMk continuous_const)).trans
        (preimage_mono hs))

/-- Normalized forward expressions satisfy the exact spatial-transfer
interface. `hgrad` is the primitive phase identity; all expression identities
and support preservation are proved here. `T` is supplied by FullLow or
BranchRealization. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasSpatialAmplitudeTransfer_forward_normalized
    {ρ : ℝ} (hρ : ρ ≠ 0) {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {Φ : E → E → ℝ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ))
    (B : E → E → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun z : E × E ↦ B z.1 z.2 i j))
    (hgrad : ∀ i x δ, partialDeriv (fun z ↦ Φ z δ) x i = ∑ j, B x δ i j * δ j)
    (a : ι → Point n → ℂ) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (idx : Fin n → Fin n → ι)
    (he : ∀ i j z, z ∈ (X ×ˢ Y) ×ˢ F →
      a (idx i j) z = (B z.1.1 (ρ • z.2) i j : ℂ))
    (T : (Point n → ℂ) → H →L[ℂ] H)
    (hT : ∀ b, SupportedAmplitude ((X ×ˢ Y) ×ˢ F) b → ∀ t : graphTestSpace n 1,
      T b (graphTestToLp t) =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (graphOperator Φ (scalarPhysicalAmplitude ρ b) (fun y ↦ (t.val y).ofLp) x)) :
    HasSpatialAmplitudeTransfer outputDirection (fun i ↦ spatialSourceTerms (idx i))
      (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ) idx a
      (fun b ↦ scalarGraphOperator (T b)) (SupportedAmplitude ((X ×ˢ Y) ×ˢ F)) := by
  apply hasSpatialAmplitudeTransfer_forward outputDirection
    (fun i ↦ spatialSourceTerms (idx i)) (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ)
    idx a T _ (scalarPhysicalAmplitude ρ) hX hY
    (hF.image (continuous_const_smul ρ)) hΦ hB hgrad
  · intro b hb
    exact admissible_scalarPhysicalAmplitude hρ hb.1 hb.2
  · intro b hb i
    exact supportedAmplitude_divergenceTransfer a ha b hb _ _
  · intro b hb i j
    exact supportedAmplitude_coefficientProduct a ha b hb _ _
  · intro b hb i
    exact physical_forwardRemainder hρ a b hb.1 B idx i (fun j ↦ ha (idx i j))
      (fun j z hz ↦ he i j z (hb.2 hz))
  · intro b hb i j
    exact physical_forwardDatum hρ a b B idx i j (fun z hz ↦ he i j z (hb.2 hz))
  · exact hT

/-- Normalized reverse expressions satisfy the exact spatial-transfer
interface. The primitive inverse and gradient identities are required only on
the original source/frequency carrier; no transfer identity or graph estimate
is assumed. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasSpatialAmplitudeTransfer_reverse_normalized
    {ρ : ℝ} (hρ : ρ ≠ 0) {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {S : E → E → ℝ} {ζ : E}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry (phaseIncrement S ζ ρ)))
    (B J : E → E → Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ i j, ContDiff ℝ ∞ (fun z : E × E ↦ J z.1 z.2 i j))
    (hinv : ∀ x ∈ Y, ∀ ε ∈ F, J x (ρ • ε) * B x (ρ • ε) = 1)
    (hgrad : ∀ x ∈ Y, ∀ ε ∈ F, ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z (ρ • ε)) x l =
        (B x (ρ • ε)).mulVec (fun k ↦ (ρ • ε) k) l)
    (a : ι → Point n → ℂ) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (idx : Fin n → Fin n → ι)
    (he : ∀ i j z, z ∈ (X ×ˢ Y) ×ˢ F →
      a (idx i j) z = (J z.1.2 (ρ • z.2) i j : ℂ))
    (T : (Point n → ℂ) → H →L[ℂ] H)
    (hT : ∀ b, SupportedAmplitude ((X ×ˢ Y) ×ˢ F) b → ∀ t : graphTestSpace n 1,
      T b (graphTestToLp t) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (ReverseDerivative.envelopeGraph S ζ ρ (scalarPhysicalAmplitude ρ b)
          (fun x ↦ (t.val x).ofLp) y)) :
    HasSpatialAmplitudeTransfer outputDirection (fun i ↦ spatialSourceTerms (idx i))
      (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ) idx a
      (fun b ↦ scalarGraphOperator (T b)) (SupportedAmplitude ((X ×ˢ Y) ×ˢ F)) := by
  apply hasSpatialAmplitudeTransfer_reverse outputDirection
    (fun i ↦ spatialSourceTerms (idx i)) (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ)
    idx a T _ (scalarPhysicalAmplitude ρ) hX hY
    (hF.image (continuous_const_smul ρ)) hΦ hJ
  · intro b hb y δ x hx
    have hs := source_slice_support ρ hb.2 y δ hx
    simpa only [smul_smul, mul_inv_cancel₀ hρ, one_smul] using
      hinv x hs.1.2 (ρ⁻¹ • δ) hs.2
  · intro b hb y δ x hx l
    have hs := source_slice_support ρ hb.2 y δ hx
    simpa only [smul_smul, mul_inv_cancel₀ hρ, one_smul] using
      hgrad x hs.1.2 (ρ⁻¹ • δ) hs.2 l
  · intro b hb
    exact admissible_scalarPhysicalAmplitude hρ hb.1 hb.2
  · intro b hb i
    exact supportedAmplitude_divergenceTransfer a ha b hb _ _
  · intro b hb i j
    exact supportedAmplitude_coefficientProduct a ha b hb _ _
  · intro b hb i
    exact physical_reverseRemainder hρ a b hb.1 J idx i (fun j ↦ ha (idx i j))
      (fun j z hz ↦ he i j z (hb.2 hz))
  · intro b hb i j
    exact physical_reverseDatum hρ a b J idx i j (fun z hz ↦ he i j z (hb.2 hz))
  · exact hT

end JanetCartan.ResponseTransfer.NormalizedTransfer
