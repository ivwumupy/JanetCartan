module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.JointPrimitives
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.SupportedParameterAssembly

/-!
# Concrete scalar coordinates of the selected primitive tuple

These fixed linear maps extract the selected matrix entry, forward and reverse
spatial coefficients, and both signed parameter coefficients. They instantiate
the formerly abstract extraction maps in `NormalizedTransfer.JointPrimitives`.
The global tuple and its reserve come from
`GradedPrimitives.exists_global_selected_primitives` (or its literal inverse
specialization). Consumer: the spatial and joint parameter estimates in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.NearCarrierAssembly
open FourierIntegral GradedPrimitives NormalizedTransfer NearCarrierParameter
variable {n r p m : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean p
local notation "Z" => JointAmplitudePoint n p
local notation "W" => ParameterAmplitudePoint n P

local instance primitiveFieldsRealMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace
local instance primitiveFieldsComplexMatrixTopology (r : ℕ) :
    TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- Indices of the actual scalar primitives in the selected graph induction.
The inverse amplitude remains an amplitude entry, independently of the
spatial inverse coefficient. Source: `app:ch_response:eq:direct-envelope-profile`. -/
inductive SelectedPrimitiveEntry (n r m : ℕ)
  | amplitude (i j : Fin r)
  | forwardSpatial (i j : Fin n)
  | reverseSpatial (i j : Fin n)
  | forwardParameter (i : Fin m) (j : Fin n)
  | reverseParameter (i : Fin m) (j : Fin n)

/-- Fixed linear entry extraction. Its norm depends on the chosen parameter
directions and dimensions only, preceding scale and frequency in the estimates.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
def selectedPrimitiveExtraction (w : Fin m → P) (k : SelectedPrimitiveEntry n r m) :
    SelectedPrimitiveValues n r p →L[ℝ] ℂ := by
  let l : SelectedPrimitiveValues n r p →ₗ[ℝ] ℂ := match k with
  | .amplitude i j =>
      { toFun := fun v ↦ v.1 i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
  | .forwardSpatial i j =>
      { toFun := fun v ↦ (v.2.1 i j : ℂ)
        map_add' := by intros; simp
        map_smul' := by intros; simp }
  | .reverseSpatial i j =>
      { toFun := fun v ↦ (v.2.2.1 i j : ℂ)
        map_add' := by intros; simp
        map_smul' := by intros; simp }
  | .forwardParameter i j =>
      { toFun := fun v ↦ (v.2.2.2.1 (EuclideanSpace.single j 1) (w i) : ℂ)
        map_add' := by intros; simp
        map_smul' := by intros; simp }
  | .reverseParameter i j =>
      { toFun := fun v ↦ (v.2.2.2.2 (EuclideanSpace.single j 1) (w i) : ℂ)
        map_add' := by intros; simp
        map_smul' := by intros; simp }
  exact LinearMap.toContinuousLinearMap l

/-- The concrete scalar primitive fields used by the spatial and parameter
expression inductions (`app:ch_response:eq:direct-envelope-profile`). -/
def selectedPrimitiveFields (w : Fin m → P)
    (f : W → SelectedPrimitiveValues n r p) : SelectedPrimitiveEntry n r m → Z → ℂ :=
  jointPrimitiveFields (selectedPrimitiveExtraction w) f

/-- Every required joint reserve jet follows from the actual producer tuple;
no coefficient, inverse, or modified-amplitude estimate is assumed separately.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem selectedPrimitiveFields_smooth_and_jets
    (w : Fin m → P) {f : W → SelectedPrimitiveValues n r p} (hf : ContDiff ℝ ∞ f)
    {G : ℕ → ℝ} (hG : ∀ j, 0 ≤ G j) {L : ℝ} {N Rstar : ℕ}
    (hj : ∀ j ≤ N, ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ G j * L ^ (j + 2 - Rstar)) :
    (∀ i, ContDiff ℝ ∞ (selectedPrimitiveFields w f i)) ∧
    (∀ (i : SelectedPrimitiveEntry n r m) j, 0 ≤ ‖selectedPrimitiveExtraction w i‖ * G j) ∧
    ∀ i j, j ≤ N → ∀ z, ‖iteratedFDeriv ℝ j (selectedPrimitiveFields w f i) z‖ ≤
      (‖selectedPrimitiveExtraction w i‖ * G j) * L ^ (j + 2 - Rstar) :=
  ⟨fun i ↦ contDiff_jointPrimitiveFields _ hf i,
    fun _ j ↦ mul_nonneg (norm_nonneg _) (hG j),
    fun i _ hjN z ↦ norm_jet_jointPrimitiveFields_le _ hf hj i hjN z⟩

/-- The initial scalar amplitude is the entire original selected matrix entry,
not an entry of a cutoff-altered amplitude. The tuple producer proves `hfirst`
using its plateau on the complete selected support.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem selectedPrimitiveFields_amplitude
    (w : Fin m → P) {f : W → SelectedPrimitiveValues n r p}
    (A : FullAmplitude n r) (q : P × E → ℂ) (ζ : P → E) (ρ : ℝ)
    (hfirst : (fun z ↦ (f z).1) = normalizedParameterAmplitude A q ζ ρ)
    (i j : Fin r) (z : Z) :
    selectedPrimitiveFields w f (.amplitude i j) z =
      normalizedParameterAmplitude A q ζ ρ (jointPrimitivePointMap z) i j := by
  exact congrArg (fun v : Matrix (Fin r) (Fin r) ℂ ↦ v i j)
    (congrFun hfirst (jointPrimitivePointMap z))

/-- The forward spatial field agrees with the actual normalized averaged
mixed matrix on the original joint support. This discharges the coefficient
agreement input to the normalized transfer leaves.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem selectedPrimitiveFields_forwardSpatial
    (w : Fin m → P) {f : W → SelectedPrimitiveValues n r p}
    (A : FullAmplitude n r) (q : P × E → ℂ) (S : E → E → ℝ) (ζ : P → E) (ρ : ℝ)
    {Ω : Set W} {K : Set Z} (hK : MapsTo jointPrimitivePointMap K Ω)
    (he : ∀ z ∈ Ω, f =ᶠ[𝓝 z] selectedPrimitives A q S ζ ρ)
    (i j : Fin n) {z : Z} (hz : z ∈ K) :
    selectedPrimitiveFields w f (.forwardSpatial i j) z =
      (averagedMixedMatrix S (ζ z.1.1) 1 z.1.2.1 z.2 i j : ℂ) :=
  jointPrimitiveFields_eqOn_of_eventuallyEq (selectedPrimitiveExtraction w) hK he
    (.forwardSpatial i j) hz

/-- The reverse spatial field is the inverse of the actual averaged matrix
at the source position; the matrix is inverted before entry extraction.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem selectedPrimitiveFields_reverseSpatial
    (w : Fin m → P) {f : W → SelectedPrimitiveValues n r p}
    (A : FullAmplitude n r) (q : P × E → ℂ) (S : E → E → ℝ) (ζ : P → E) (ρ : ℝ)
    {Ω : Set W} {K : Set Z} (hK : MapsTo jointPrimitivePointMap K Ω)
    (he : ∀ z ∈ Ω, f =ᶠ[𝓝 z] selectedPrimitives A q S ζ ρ)
    (i j : Fin n) {z : Z} (hz : z ∈ K) :
    selectedPrimitiveFields w f (.reverseSpatial i j) z =
      ((averagedMixedMatrix S (ζ z.1.1) 1 z.1.2.2 z.2)⁻¹ i j : ℂ) :=
  jointPrimitiveFields_eqOn_of_eventuallyEq (selectedPrimitiveExtraction w) hK he
    (.reverseSpatial i j) hz

/-- The parameter field agrees with the actual physical-frequency phase
coefficient: the frequency cancels in its normalized displacement.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem selectedPrimitiveFields_forwardParameter
    (w : Fin m → P) {f : W → SelectedPrimitiveValues n r p}
    (A : FullAmplitude n r) (q : P × E → ℂ) (S : E → E → ℝ) (ζ : P → E)
    {ρ : ℝ} (hρ : ρ ≠ 0)
    {Ω : Set W} {K : Set Z} (hK : MapsTo jointPrimitivePointMap K Ω)
    (he : ∀ z ∈ Ω, f =ᶠ[𝓝 z] selectedPrimitives A q S ζ ρ)
    (i : Fin m) (j : Fin n) {z : Z} (hz : z ∈ K) :
    selectedPrimitiveFields w f (.forwardParameter i j) z =
      (phaseCoefficient S ζ ρ z.1.1 (w i) z.1.2.1 (ρ • z.2) j : ℂ) := by
  have h := jointPrimitiveFields_eqOn_of_eventuallyEq (selectedPrimitiveExtraction w) hK he
    (.forwardParameter i j) hz
  change selectedPrimitiveFields w f (.forwardParameter i j) z =
    (parameterPhaseCoefficient S ζ z.1.2.1 z.2 z.1.1 (EuclideanSpace.single j 1) (w i) : ℂ) at h
  simpa only [phaseCoefficient, smul_smul, inv_mul_cancel₀ hρ, one_smul] using h

/-- Evaluation of the signed inverse coefficient gives the literal matrix row
`-C B⁻¹`, with the same normalized covector and source position. In particular,
there is no transpose or adjoint substitution in the reverse parameter transfer.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem signedReverseParameterCoefficient_eq_reverseParameterRow
    (S : E → E → ℝ) (ζ : P → E) {ρ : ℝ} (hρ : ρ ≠ 0)
    (c v : P) (x ε : E) (j : Fin n) :
    (signedReverseParameterCoefficient S ζ (x, ε, c) (EuclideanSpace.single j 1) v : ℂ) =
      reverseParameterRow S ζ ρ
        (fun y δ ↦ (averagedMixedMatrix S (ζ c) 1 y (ρ⁻¹ • δ))⁻¹)
        c v x (ρ • ε) j := by
  let B := averagedMixedMatrix S (ζ c) 1 x ε
  have hinv : Ring.inverse (averagedMixedOperator S (ζ c) 1 x ε) =
      mixedMatrixOperatorEquiv n B⁻¹ := by
    apply (mixedMatrixOperatorEquiv n).symm.injective
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mixedMatrixOperatorEquiv_symm_inverse B
  have hv : Ring.inverse (averagedMixedOperator S (ζ c) 1 x ε)
      (EuclideanSpace.single j 1) =
      ∑ k, B⁻¹ k j • EuclideanSpace.single k 1 := by
    rw [hinv]
    ext k
    rw [mixedMatrixOperatorEquiv_apply]
    simp [Pi.single_apply, eq_comm]
  rw [signedReverseParameterCoefficient_apply, hv]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul,
    reverseParameterRow, reverseCoefficient, Matrix.vecMul, dotProduct,
    phaseCoefficient, smul_smul, inv_mul_cancel₀ hρ, one_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The concrete reverse parameter field agrees with the literal signed row
on the complete original support, including derivatives of the inverse and
all amplitude masks in subsequent transfers.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem selectedPrimitiveFields_reverseParameter
    (w : Fin m → P) {f : W → SelectedPrimitiveValues n r p}
    (A : FullAmplitude n r) (q : P × E → ℂ) (S : E → E → ℝ) (ζ : P → E)
    {ρ : ℝ} (hρ : ρ ≠ 0)
    {Ω : Set W} {K : Set Z} (hK : MapsTo jointPrimitivePointMap K Ω)
    (he : ∀ z ∈ Ω, f =ᶠ[𝓝 z] selectedPrimitives A q S ζ ρ)
    (i : Fin m) (j : Fin n) {z : Z} (hz : z ∈ K) :
    selectedPrimitiveFields w f (.reverseParameter i j) z =
      reverseParameterRow S ζ ρ
        (fun y δ ↦ (averagedMixedMatrix S (ζ z.1.1) 1 y (ρ⁻¹ • δ))⁻¹)
        z.1.1 (w i) z.1.2.2 (ρ • z.2) j := by
  have h := jointPrimitiveFields_eqOn_of_eventuallyEq (selectedPrimitiveExtraction w) hK he
    (.reverseParameter i j) hz
  change selectedPrimitiveFields w f (.reverseParameter i j) z =
    (signedReverseParameterCoefficient S ζ (z.1.2.2, z.2, z.1.1)
      (EuclideanSpace.single j 1) (w i) : ℂ) at h
  exact h.trans (signedReverseParameterCoefficient_eq_reverseParameterRow S ζ hρ _ _ _ _ j)

/-- The original matrix-amplitude support supplies the initial joint expression
support. Thus support closure in the parameter estimate starts with the actual
selected symbol and is not a new analytic assumption about its scalar fields.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem selectedPrimitiveFields_amplitude_supported
    (w : Fin m → P) {f : W → SelectedPrimitiveValues n r p} (hf : ContDiff ℝ ∞ f)
    (A : FullAmplitude n r) (q : P × E → ℂ) (ζ : P → E) (ρ : ℝ)
    (hfirst : (fun z ↦ (f z).1) = normalizedParameterAmplitude A q ζ ρ)
    {Ksel : Set W} (hs : tsupport (normalizedParameterAmplitude A q ζ ρ) ⊆ Ksel)
    {U : Set P} {X Y F : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hK : ∀ z ∈ Ksel, z.1.1 ∈ X ∧ z.1.2.1 ∈ Y ∧ z.1.2.2 ∈ F)
    (i j : Fin r) :
    SupportedJointAmplitude U X Y F (jointPrimitivePointMap ⁻¹' Ksel)
      (selectedPrimitiveFields w f (.amplitude i j)) := by
  have heq : selectedPrimitiveFields w f (.amplitude i j) =
      AmplitudeBound.matrixEntryEvaluation i j ∘
        (normalizedParameterAmplitude A q ζ ρ ∘ jointPrimitivePointMap) :=
    funext (selectedPrimitiveFields_amplitude w A q ζ ρ hfirst i j)
  have hs' : tsupport (selectedPrimitiveFields w f (.amplitude i j)) ⊆
      jointPrimitivePointMap ⁻¹' Ksel := by
    rw [heq]
    exact ((tsupport_comp_subset (map_zero (AmplitudeBound.matrixEntryEvaluation i j)) _).trans
      (tsupport_comp_subset_preimage _ jointPrimitivePointMap.continuous)).trans
        (preimage_mono hs)
  refine ⟨parameterAmplitudeAdmissible_of_masks hX hY
    (contDiff_jointPrimitiveFields _ hf _).contDiffOn ?_, hs'⟩
  intro c _ x y ε hmask
  by_contra hn
  have hk := hK _ (hs' (subset_tsupport _ hn))
  exact (by rcases hmask with h | h | h; exact h hk.1; exact h hk.2.1; exact h hk.2.2)

/-- Recovering physical displacement yields the exact selected full amplitude
entry used by the literal graph and finite-fiber assembly. Both physical
positions and every original weight are unchanged.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem scalarPhysicalAmplitude_selectedPrimitiveFields
    (w : Fin m → P) {f : W → SelectedPrimitiveValues n r p}
    (A : FullAmplitude n r) (q : P × E → ℂ) (ζ : P → E)
    {ρ : ℝ} (hρ : ρ ≠ 0)
    (hfirst : (fun z ↦ (f z).1) = normalizedParameterAmplitude A q ζ ρ)
    (c : P) (i j : Fin r) :
    scalarPhysicalAmplitude (r := 1) ρ
      (frozenField c (selectedPrimitiveFields w f (.amplitude i j))) =
      fun x y δ _ _ ↦ forwardSelectedAmplitude A (ζ c) ρ
        (fun δ ↦ q (c, ρ⁻¹ • δ)) x y δ i j := by
  ext x y δ k l
  rw [scalarPhysicalAmplitude_apply]
  change selectedPrimitiveFields w f (.amplitude i j) ((c, (x, y)), ρ⁻¹ • δ) = _
  rw [selectedPrimitiveFields_amplitude w A q ζ ρ hfirst]
  simp [normalizedParameterAmplitude, forwardSelectedAmplitude, selectedAmplitude,
    smul_add, smul_smul, hρ]

end JanetCartan.ResponseTransfer.NearCarrierAssembly
