module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SymbolBudget
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.Expressions

/-!
# Support and normalized scalar amplitude operations

These are the literal amplitude inputs of
`app:ch_response:eq:direct-envelope-profile`. The support lemmas apply to the
complete expression, hence include all original masks. Coefficients need not
have compact support. Physical recovery uses the published `SymbolBudget`
map, entry by entry, with no change to the Fourier normalization.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NormalizedTransfer
open FourierIntegral FullAmplitudePrimitiveBudget.Local
open IsometricEmbedding.Response.NearCarrier NearCarrierParameter NearCarrierSymbol

variable {n r : ℕ} {ι : Type*}
local notation "E" => Euclidean n

section Support
variable {Z Fld : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup Fld] [NormedSpace ℝ Fld]

/-- Coefficient multiplication retains the original closed amplitude support.
Consumer: all datum branches in `app:ch_response:eq:direct-envelope-profile`. -/
theorem tsupport_coefficientProduct (a : ι → Z → Fld)
    (b : AmplitudeExpression Z Fld ι) (M : Fld →L[ℝ] Fld →L[ℝ] Fld) (i : ι) :
    tsupport ((b.coefficientProduct M i).evaluate a) ⊆ tsupport (b.evaluate a) := by
  apply closure_mono
  intro z hz
  contrapose! hz
  simp only [Function.mem_support, ne_eq, not_not] at hz ⊢
  simp [hz]

/-- The full source divergence preserves support, including derivatives of
coefficient products (`app:ch_response:eq:direct-envelope-profile`). -/
theorem tsupport_divergenceTransfer (a : ι → Z → Fld)
    (b : AmplitudeExpression Z Fld ι) (v : Z)
    (qs : List (Z × ι × (Fld →L[ℝ] Fld →L[ℝ] Fld))) :
    tsupport ((b.divergenceTransfer v qs).evaluate a) ⊆ tsupport (b.evaluate a) := by
  induction qs with
  | nil => exact tsupport_fderiv_apply_subset ℝ v
  | cons q qs ih =>
    exact (tsupport_add _ _).trans (union_subset
      ((tsupport_fderiv_apply_subset ℝ q.1).trans
        (tsupport_coefficientProduct a b q.2.2 q.2.1)) ih)

end Support

/-- Output direction in the normalized variables `((x,y),ε)` for
`app:ch_response:eq:direct-envelope-profile`. -/
def outputDirection (i : Fin n) : Point n := ((EuclideanSpace.single i 1, 0), 0)

/-- Source direction in the normalized variables `((x,y),ε)` for
`app:ch_response:eq:direct-envelope-profile`. -/
def sourceDirection (j : Fin n) : Point n := ((0, EuclideanSpace.single j 1), 0)

/-- The exact spatial source-divergence list; signs belong to the primitive
coefficient fields (`app:ch_response:eq:direct-envelope-profile`). -/
def spatialSourceTerms (idx : Fin n → ι) :
    List (Point n × ι × (ℂ →L[ℝ] ℂ →L[ℝ] ℂ)) :=
  List.ofFn fun j ↦ (sourceDirection j, idx j, ContinuousLinearMap.mul ℝ ℂ)

/-- Scalar interpretation of the complete spatial remainder. This keeps
derivatives of inverse coefficients inside the product in the reverse graph.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem evaluate_spatialSourceTerms (a : ι → Point n → ℂ)
    (b : AmplitudeExpression (Point n) ℂ ι) (i : Fin n) (idx : Fin n → ι) (z : Point n) :
    (b.divergenceTransfer (outputDirection i) (spatialSourceTerms idx)).evaluate a z =
      fderiv ℝ (b.evaluate a) z (outputDirection i) +
        ∑ j, fderiv ℝ (fun w ↦ a (idx j) w * b.evaluate a w) z (sourceDirection j) := by
  rw [AmplitudeExpression.evaluate_divergenceTransfer]
  simp [spatialSourceTerms, List.map_ofFn, List.sum_ofFn, add_comm]

/-- Entrywise scalar insertion with the Frobenius matrix norm. Consumer:
`app:ch_response:eq:direct-envelope-profile`. -/
def scalarMatrixMap : ℂ →L[ℝ] Matrix (Fin r) (Fin r) ℂ :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight (fun _ _ ↦ 1)

/-- Entry evaluation of the scalar insertion. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
@[simp] theorem scalarMatrixMap_apply (c : ℂ) (i j : Fin r) :
    scalarMatrixMap c i j = c := mul_one c

/-- A scalar field is inserted entrywise before the published physical
recovery map. Consumer: the scalar spatial realization leaves of
`app:ch_response:eq:direct-envelope-profile`. -/
def scalarPhysicalAmplitude (ρ : ℝ) (b : Point n → ℂ) : FullAmplitude n r :=
  physicalAmplitudeOfNormalized ρ (fun z ↦ scalarMatrixMap (b z))

/-- Scalar physical recovery is literally the existing full-amplitude map,
with both physical positions retained. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
@[simp] theorem scalarPhysicalAmplitude_apply (ρ : ℝ) (b : Point n → ℂ)
    (x y δ : E) (i j : Fin r) :
    scalarPhysicalAmplitude ρ b x y δ i j = b ((x, y), ρ⁻¹ • δ) := scalarMatrixMap_apply _ i j

/-- Normalization recovers every scalar entry exactly; there is no additional
`2π` factor (`app:ch_response:eq:direct-envelope-profile`). -/
theorem normalizedField_scalarPhysicalAmplitude {ρ : ℝ} (hρ : ρ ≠ 0)
    (b : Point n → ℂ) :
    PrimitiveProfiles.normalizedField ρ
      (uncurry (scalarPhysicalAmplitude (r := r) ρ b)) = fun z _ _ ↦ b z :=
  by
    rw [scalarPhysicalAmplitude, normalizedField_physicalAmplitudeOfNormalized hρ]
    funext z i j
    exact scalarMatrixMap_apply _ i j

/-- The complete scalar field is smooth after physical recovery.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiff_scalarPhysicalAmplitude (ρ : ℝ) {b : Point n → ℂ}
    (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (uncurry (scalarPhysicalAmplitude (r := r) ρ b)) :=
  contDiff_physicalAmplitudeOfNormalized ρ (scalarMatrixMap.contDiff.comp hb)


/-- Output differentiation does not rescale: frequency is fixed throughout
the spatial transfer (`app:ch_response:eq:direct-envelope-profile`). -/
theorem fderiv_outputDirection {b : Point n → ℂ} {x y ε : E}
    (hb : DifferentiableAt ℝ b ((x, y), ε)) (i : Fin n) :
    fderiv ℝ b ((x, y), ε) (outputDirection i) =
      fderiv ℝ (fun z ↦ b ((z, y), ε)) x (EuclideanSpace.single i 1) := by
  have h := hb.hasFDerivAt.comp x
    (((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const y x)).prodMk
      (hasFDerivAt_const ε x))
  simpa [outputDirection, Function.comp_def] using
    (congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1)) h.fderiv).symm

/-- Source differentiation fixes the physical output and normalized covector.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem fderiv_sourceDirection {b : Point n → ℂ} {x y ε : E}
    (hb : DifferentiableAt ℝ b ((x, y), ε)) (j : Fin n) :
    fderiv ℝ b ((x, y), ε) (sourceDirection j) =
      fderiv ℝ (fun z ↦ b ((x, z), ε)) y (EuclideanSpace.single j 1) := by
  have h := hb.hasFDerivAt.comp y
    (((hasFDerivAt_const (𝕜 := ℝ) x y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)).prodMk
      (hasFDerivAt_const ε y))
  simpa [sourceDirection, Function.comp_def] using
    (congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.single j 1)) h.fderiv).symm

/-- Closed original supports suffice for the scalar physical amplitude's
admissibility. The frequency carrier is the image of the normalized one.
Consumer: `SpatialRealization.hasSpatialAmplitudeTransfer_forward`. -/
theorem admissible_scalarPhysicalAmplitude {ρ : ℝ} (hρ : ρ ≠ 0)
    {X Y F : Set E} {b : Point n → ℂ} (hb : ContDiff ℝ ∞ b)
    (hs : tsupport b ⊆ (X ×ˢ Y) ×ˢ F) :
    ForwardAmplitudeAdmissible X Y ((fun ε ↦ ρ • ε) '' F)
      (scalarPhysicalAmplitude (r := r) ρ b) := by
  refine ⟨(contDiff_scalarPhysicalAmplitude ρ hb).comp
    ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd), ?_⟩
  intro x y δ h
  have hz : b ((x, y), ρ⁻¹ • δ) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    have hp' := hs hp
    have hf : δ ∈ (fun ε : E ↦ ρ • ε) '' F :=
      ⟨ρ⁻¹ • δ, hp'.2, by simp [smul_smul, hρ]⟩
    rcases h with h | h | h
    · exact h hp'.1.1
    · exact h hp'.1.2
    · exact h hf
  ext i j
  simpa using hz

end JanetCartan.ResponseTransfer.NormalizedTransfer
