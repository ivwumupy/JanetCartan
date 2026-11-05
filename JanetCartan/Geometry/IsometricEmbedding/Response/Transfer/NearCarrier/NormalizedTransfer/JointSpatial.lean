module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.FrozenJets

/-!
# Spatial transfer on joint normalized amplitudes

Spatial and parameter modifications act on the same `JointAmplitudePoint`.
Freezing is applied to the evaluated expression, so parameter derivatives
already present in an expression are retained. These identities supply the
spatial input of `DerivativeBounds.ParameterAssembly` for
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NormalizedTransfer
open FourierIntegral FullAmplitudePrimitiveBudget.Local
open IsometricEmbedding.Response.NearCarrier NearCarrierParameter
variable {n p r : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "P" => Euclidean p
local notation "Z" => JointAmplitudePoint n p

/-- Output differentiation in the common joint expression space of
`app:ch_response:eq:direct-envelope-profile`. -/
def jointOutputDirection (i : Fin n) : Z := ((0, (EuclideanSpace.single i 1, 0)), 0)

/-- The frozen chain rule for any spatial/frequency direction, leaving all
previous parameter derivatives intact (`app:ch_response:eq:direct-envelope-profile`). -/
theorem fderiv_frozenField {b : Z → ℂ} {c : P} {z : Point n}
    (hb : DifferentiableAt ℝ b ((c, z.1), z.2)) (v : Point n) :
    fderiv ℝ (frozenField c b) z v = fderiv ℝ b ((c, z.1), z.2) (frozenDirectionMap v) := by
  change fderiv ℝ (fun w : Point n ↦ b ((c, w.1), w.2)) z v = _
  have h := hb.hasFDerivAt.comp z
    (((hasFDerivAt_const (𝕜 := ℝ) c z).prodMk
      (ContinuousLinearMap.fst ℝ (E × E) E).hasFDerivAt).prodMk
        (ContinuousLinearMap.snd ℝ (E × E) E).hasFDerivAt)
  simpa [frozenField, frozenDirectionMap, Function.comp_def] using
    congrArg (fun L : Point n →L[ℝ] ℂ ↦ L v) h.fderiv

/-- The joint output direction is the derivative of the physical-position
slice (`app:ch_response:eq:direct-envelope-profile`). -/
theorem fderiv_jointOutputDirection {b : Z → ℂ} {c : P} {z : E × E} {ε : E}
    (hb : DifferentiableAt ℝ b ((c, z), ε)) (i : Fin n) :
    fderiv ℝ b ((c, z), ε) (jointOutputDirection i) =
      fderiv ℝ (fun x ↦ b ((c, (x, z.2)), ε)) z.1 (EuclideanSpace.single i 1) := by
  have h := hb.hasFDerivAt.comp z.1
    (((hasFDerivAt_const (𝕜 := ℝ) c z.1).prodMk
      ((hasFDerivAt_id (𝕜 := ℝ) z.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) z.2 z.1))).prodMk
        (hasFDerivAt_const (𝕜 := ℝ) ε z.1))
  simpa [jointOutputDirection, Function.comp_def] using
    (congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1)) h.fderiv).symm

/-- Output derivatives preserve the original compact physical carriers and
frequency selector (`app:ch_response:eq:direct-envelope-profile`). -/
theorem admissible_jointOutputDerivative {U : Set P} (hU : IsOpen U)
    {X Y F : Set E} {b : Z → ℂ} (hb : ParameterAmplitudeAdmissible U X Y F b)
    (i : Fin n) :
    ParameterAmplitudeAdmissible U X Y F (fun z ↦ fderiv ℝ b z (jointOutputDirection i)) := by
  refine ⟨(hb.1.fderiv_of_isOpen ((hU.prod isOpen_univ).prod isOpen_univ)
    (by simp)).clm_apply contDiffOn_const, ?_, ?_⟩
  · intro c hc ε hε
    have he : (fun z : E × E ↦ fderiv ℝ b ((c, z), ε) (jointOutputDirection i)) =
        fun z ↦ fderiv ℝ (fun w : E × E ↦ b ((c, w), ε)) z
          (EuclideanSpace.single i 1, 0) := by
      funext z
      have h := (hb.differentiableAt hU hc z ε).hasFDerivAt.comp z
        (((hasFDerivAt_const (𝕜 := ℝ) c z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z)).prodMk
          (hasFDerivAt_const (𝕜 := ℝ) ε z))
      simpa [jointOutputDirection, Function.comp_def] using
        (congrArg (fun L : E × E →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1, 0)) h.fderiv).symm
    rw [he]
    exact (tsupport_fderiv_apply_subset ℝ _).trans (hb.2.1 c hc ε hε)
  · intro c hc z ε hε
    dsimp only
    rw [fderiv_jointOutputDirection (hb.differentiableAt hU hc z ε)]
    have he : (fun x ↦ b ((c, (x, z.2)), ε)) = fun _ ↦ (0 : ℂ) :=
      funext fun x ↦ hb.2.2 c hc (x, z.2) ε hε
    rw [he]
    simp

/-- Exact divergence interpretation in the common joint expression space.
The source list is shared with parameter transfer, including the signed
coefficient entries (`app:ch_response:eq:direct-envelope-profile`). -/
theorem evaluate_jointSpatialSourceTerms (a : ι → Z → ℂ)
    (b : AmplitudeExpression Z ℂ ι) (i : Fin n) (idx : Fin n → ι) (z : Z) :
    (b.divergenceTransfer (jointOutputDirection i) (parameterSourceTerms idx)).evaluate a z =
      fderiv ℝ (b.evaluate a) z (jointOutputDirection i) +
        ∑ j, fderiv ℝ (fun w ↦ a (idx j) w * b.evaluate a w) z (sourceAmplitudeDirection j) := by
  rw [AmplitudeExpression.evaluate_divergenceTransfer]
  simp [parameterSourceTerms, List.map_ofFn, List.sum_ofFn, add_comm]

/-- Spatial remainder branches preserve the same admissibility predicate as
parameter branches, closing the mixed induction's support obligation.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem admissible_jointSpatialSourceTerms {U : Set P} (hU : IsOpen U)
    {X Y F : Set E} (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι)
    (i : Fin n) (idx : Fin n → ι)
    (hb : ParameterAmplitudeAdmissible U X Y F (b.evaluate a))
    (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx j)) ((U ×ˢ univ) ×ˢ univ)) :
    ParameterAmplitudeAdmissible U X Y F
      ((b.divergenceTransfer (jointOutputDirection i) (parameterSourceTerms idx)).evaluate a) := by
  rw [funext (evaluate_jointSpatialSourceTerms a b i idx)]
  exact (admissible_jointOutputDerivative hU hb i).add
    (ParameterAmplitudeAdmissible.sum fun j ↦ (hb.mul (ha j)).sourceDerivative hU j)

/-- Freeze the evaluated spatial remainder, retaining arbitrary parameter
derivatives already inside the expression. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem frozenField_jointSpatialSourceTerms {U : Set P} (hU : IsOpen U)
    {X Y F : Set E} (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι)
    (i : Fin n) (idx : Fin n → ι)
    (hb : ParameterAmplitudeAdmissible U X Y F (b.evaluate a))
    (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx j)) ((U ×ˢ univ) ×ˢ univ))
    {c : P} (hc : c ∈ U) :
    frozenField c ((b.divergenceTransfer (jointOutputDirection i)
      (parameterSourceTerms idx)).evaluate a) = fun z ↦
        fderiv ℝ (frozenField c (b.evaluate a)) z (outputDirection i) +
          ∑ j, fderiv ℝ (frozenField c (fun w ↦ a (idx j) w * b.evaluate a w)) z
            (sourceDirection j) := by
  funext z
  change (b.divergenceTransfer _ _).evaluate a ((c, z.1), z.2) = _
  rw [evaluate_jointSpatialSourceTerms, fderiv_frozenField (hb.differentiableAt hU hc z.1 z.2)]
  simp_rw [fderiv_frozenField ((hb.mul (ha _)).differentiableAt hU hc z.1 z.2)]
  rfl

/-- Physical recovery of the joint spatial remainder is the full physical
divergence, including every coefficient and mask derivative.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_jointSpatialSourceTerms {U : Set P} (hU : IsOpen U)
    {X Y F : Set E} (ρ : ℝ) (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι)
    (i : Fin n) (idx : Fin n → ι)
    (hb : ParameterAmplitudeAdmissible U X Y F (b.evaluate a))
    (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx j)) ((U ×ˢ univ) ×ˢ univ))
    {c : P} (hc : c ∈ U) (x y δ : E) :
    scalarPhysicalAmplitude (r := r) ρ (frozenField c
      ((b.divergenceTransfer (jointOutputDirection i) (parameterSourceTerms idx)).evaluate a)) x y δ =
      partialDeriv (fun z ↦ scalarPhysicalAmplitude ρ (frozenField c (b.evaluate a)) z y δ) x i +
        ∑ j, partialDeriv (fun z ↦ scalarPhysicalAmplitude ρ
          (frozenField c (fun w ↦ a (idx j) w * b.evaluate a w)) x z δ) y j := by
  rw [frozenField_jointSpatialSourceTerms hU a b i idx hb ha hc,
    ← physical_outputDerivative ρ (contDiff_frozenField hb.1 hc)]
  simp_rw [← physical_sourceDerivative ρ (contDiff_frozenField ((ha _).mul hb.1) hc)]
  ext k l
  simp only [scalarPhysicalAmplitude_apply, Matrix.add_apply, Matrix.sum_apply]

/-- The complete original joint support is retained as well as the compact
physical carriers. Taking `K = tsupport b₀` supplies this predicate for the
initial amplitude directly. No transfer conclusion is a field.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
def SupportedJointAmplitude (U : Set P) (X Y F : Set E) (K : Set Z) (b : Z → ℂ) : Prop :=
  ParameterAmplitudeAdmissible U X Y F b ∧ tsupport b ⊆ K

/-- The original compact masks give joint admissibility directly. The
complete joint support is then retained by `supportedJointAmplitude_self`
and the proved branch closure lemmas; it is never a transfer assumption.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem parameterAmplitudeAdmissible_of_masks {U : Set P} {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) {b : Z → ℂ}
    (hb : ContDiffOn ℝ ∞ b ((U ×ˢ univ) ×ˢ univ))
    (hs : ∀ c ∈ U, ∀ x y ε, x ∉ X ∨ y ∉ Y ∨ ε ∉ F → b ((c, (x, y)), ε) = 0) :
    ParameterAmplitudeAdmissible U X Y F b := by
  refine ⟨hb, ?_, fun c hc z ε hε ↦ hs c hc z.1 z.2 ε (Or.inr (Or.inr hε))⟩
  intro c hc ε _
  apply closure_minimal _ (hX.prod hY).isClosed
  intro z hz
  by_contra hn
  exact hz (hs c hc z.1 z.2 ε (by simpa only [mem_prod, not_and_or, or_assoc] using Or.inl hn))

/-- The original compactly supported amplitude starts the mixed transfer
induction with its exact support (`app:ch_response:eq:direct-envelope-profile`). -/
theorem supportedJointAmplitude_self {U : Set P} {X Y F : Set E} {b : Z → ℂ}
    (hb : ParameterAmplitudeAdmissible U X Y F b) :
    SupportedJointAmplitude U X Y F (tsupport b) b := ⟨hb, Subset.rfl⟩

/-- Every datum branch retains the complete original joint support, including
all parameter masks (`app:ch_response:eq:direct-envelope-profile`). -/
theorem supportedJointAmplitude_coefficientProduct {U : Set P} {X Y F : Set E}
    {K : Set Z} (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι) (i : ι)
    (hb : SupportedJointAmplitude U X Y F K (b.evaluate a))
    (ha : ContDiffOn ℝ ∞ (a i) ((U ×ˢ univ) ×ˢ univ)) :
    SupportedJointAmplitude U X Y F K
      ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) i).evaluate a) :=
  ⟨hb.1.mul ha, (tsupport_coefficientProduct a b _ i).trans hb.2⟩

/-- Spatial remainder branches cannot enlarge the original joint support.
Consumer: the spatial half of `DerivativeBounds.ParameterAssembly`, for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem supportedJointAmplitude_spatial {U : Set P} (hU : IsOpen U)
    {X Y F : Set E} {K : Set Z} (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι)
    (i : Fin n) (idx : Fin n → ι)
    (hb : SupportedJointAmplitude U X Y F K (b.evaluate a))
    (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx j)) ((U ×ˢ univ) ×ˢ univ)) :
    SupportedJointAmplitude U X Y F K
      ((b.divergenceTransfer (jointOutputDirection i) (parameterSourceTerms idx)).evaluate a) :=
  ⟨admissible_jointSpatialSourceTerms hU a b i idx hb.1 ha,
    (tsupport_divergenceTransfer a b _ _).trans hb.2⟩

/-- Parameter remainder branches retain exactly the same joint support as
spatial branches (`app:ch_response:eq:direct-envelope-profile`). -/
theorem supportedJointAmplitude_parameter {U : Set P} (hU : IsOpen U)
    {X Y F : Set E} (hX : IsClosed X) (hY : IsClosed Y) {K : Set Z}
    (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι) (v : P) (idx : Fin n → ι)
    (hb : SupportedJointAmplitude U X Y F K (b.evaluate a))
    (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx j)) ((U ×ˢ univ) ×ˢ univ)) :
    SupportedJointAmplitude U X Y F K
      ((b.divergenceTransfer (parameterAmplitudeDirection v) (parameterSourceTerms idx)).evaluate a) :=
  ⟨admissible_parameterSourceTerms hU hX hY a b v idx hb.1 ha,
    (tsupport_divergenceTransfer a b _ _).trans hb.2⟩

/-- A frozen slice lies in the preimage of the complete joint support. This
permits coefficient agreement only on the producer's buffered selected set.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem tsupport_frozenField {b : Z → ℂ} {K : Set Z} (hb : tsupport b ⊆ K) (c : P) :
    tsupport (frozenField c b) ⊆ (fun z : Point n ↦ ((c, z.1), z.2)) ⁻¹' K :=
  (tsupport_comp_subset_preimage b
    ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).trans (preimage_mono hb)

/-- Literal datum recovery on joint expressions, with coefficient agreement
only on the complete original support (`app:ch_response:eq:direct-envelope-profile`). -/
theorem physical_jointProduct {ρ : ℝ} (hρ : ρ ≠ 0) {b q : Z → ℂ} {K : Set Z}
    (hb : tsupport b ⊆ K) (Q : P → E → E → E → ℂ)
    (hq : ∀ z ∈ K, q z = Q z.1.1 z.1.2.1 z.1.2.2 (ρ • z.2)) (c : P) :
    scalarPhysicalAmplitude (r := r) ρ (frozenField c (fun z ↦ q z * b z)) =
      fun x y δ ↦ Q c x y δ • scalarPhysicalAmplitude ρ (frozenField c b) x y δ := by
  apply physical_product_of_eqOn_support hρ (frozenField c b) (frozenField c q) (Q c)
  intro z hz
  exact hq _ (tsupport_frozenField hb c hz)

/-- Literal forward joint remainder, including all derivatives of the
selected amplitude and no frequency rescaling of physical positions.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_jointForwardRemainder {ρ : ℝ} (hρ : ρ ≠ 0)
    {U : Set P} (hU : IsOpen U) {X Y F : Set E} {K : Set Z}
    (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι)
    (hb : SupportedJointAmplitude U X Y F K (b.evaluate a))
    (B : P → E → E → Matrix (Fin n) (Fin n) ℝ) (idx : Fin n → Fin n → ι)
    (i : Fin n) (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx i j)) ((U ×ˢ univ) ×ˢ univ))
    (he : ∀ j z, z ∈ K → a (idx i j) z = (B z.1.1 z.1.2.1 (ρ • z.2) i j : ℂ))
    {c : P} (hc : c ∈ U) :
    scalarPhysicalAmplitude (r := r) ρ (frozenField c
      ((b.divergenceTransfer (jointOutputDirection i) (parameterSourceTerms (idx i))).evaluate a)) =
      forwardRemainderAmplitude (B c) (scalarPhysicalAmplitude ρ (frozenField c (b.evaluate a))) i := by
  funext x y δ
  rw [physical_jointSpatialSourceTerms hU ρ a b i (idx i) hb.1 ha hc]
  unfold forwardRemainderAmplitude
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [physical_jointProduct hρ hb.2 (fun c x _ δ ↦ (B c x δ i j : ℂ)) (he j) c]
  have hd : Differentiable ℝ (fun z ↦ scalarPhysicalAmplitude (r := r) ρ
      (frozenField c (b.evaluate a)) x z δ) :=
    ((contDiff_scalarPhysicalAmplitude ρ (contDiff_frozenField hb.1.1 hc)).comp
      ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)).differentiable (by simp)
  simp only [partialDeriv, fderiv_fun_const_smul (hd y), smul_apply]

/-- Literal reverse joint remainder. The source derivative applies to the
entire `B⁻¹ A` product, preserving inverse and mask derivatives.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_jointReverseRemainder {ρ : ℝ} (hρ : ρ ≠ 0)
    {U : Set P} (hU : IsOpen U) {X Y F : Set E} {K : Set Z}
    (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι)
    (hb : SupportedJointAmplitude U X Y F K (b.evaluate a))
    (J : P → E → E → Matrix (Fin n) (Fin n) ℝ) (idx : Fin n → Fin n → ι)
    (i : Fin n) (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx i j)) ((U ×ˢ univ) ×ˢ univ))
    (he : ∀ j z, z ∈ K → a (idx i j) z = (J z.1.1 z.1.2.2 (ρ • z.2) i j : ℂ))
    {c : P} (hc : c ∈ U) :
    scalarPhysicalAmplitude (r := r) ρ (frozenField c
      ((b.divergenceTransfer (jointOutputDirection i) (parameterSourceTerms (idx i))).evaluate a)) =
      ReverseDerivative.remainderAmplitude (J c)
        (scalarPhysicalAmplitude ρ (frozenField c (b.evaluate a))) i := by
  funext x y δ
  rw [physical_jointSpatialSourceTerms hU ρ a b i (idx i) hb.1 ha hc]
  unfold ReverseDerivative.remainderAmplitude
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [physical_jointProduct hρ hb.2 (fun c _ y δ ↦ (J c y δ i j : ℂ)) (he j) c]
  rfl

end JanetCartan.ResponseTransfer.NormalizedTransfer
