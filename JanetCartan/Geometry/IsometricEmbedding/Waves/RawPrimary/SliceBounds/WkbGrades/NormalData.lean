module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WkbGrades.Profiles
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.PhysicalBranches
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.NormalInput

/-!
# Low normal data from the remaining WKB grades

This bridge replaces only the primitive reserve in the original normal-data
assembler. All four phase-geometric fields, the original shifted domains,
cutoffs and literal normalized amplitudes are retained. The consuming theorem
is `exists_rawSliceNormalizedBranchOperators_wkbGrades`
(`app:ch_waves:thm:wkb`, `app:ch_waves:eq:individual-raw-slice`).
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open NormalComparison

variable {d r : ℕ}
local notation "Y" => Euclidean d
local notation "X" => ℝ × Y
local notation "Z" => Y × Y
local notation "Qₛ" => ℝ × Z
local notation "Qₚ" => ℝ × X × Y

private def insertTimeLinear : Qₛ →L[ℝ] Qₚ :=
  (ContinuousLinearMap.fst ℝ ℝ Z).prod
    (((0 : Qₛ →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.fst ℝ Y Y).comp (ContinuousLinearMap.snd ℝ ℝ Z))).prod
      ((ContinuousLinearMap.snd ℝ Y Y).comp (ContinuousLinearMap.snd ℝ ℝ Z)))

private theorem norm_iteratedFDeriv_insertTime_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set Qₚ} (hQ : IsOpen Q) {B : Qₚ → E} (hB : ContDiffOn ℝ ∞ B Q)
    (t : ℝ) {q : Qₛ} (hq : (q.1, (t, q.2.1), q.2.2) ∈ Q) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w : Qₛ ↦ B (w.1, (t, w.2.1), w.2.2)) q‖ ≤
      ‖iteratedFDeriv ℝ k B (q.1, (t, q.2.1), q.2.2)‖ := by
  let T : Qₛ →L[ℝ] Qₚ := insertTimeLinear
  let c : Qₚ := (0, (t, 0), 0)
  let U := (fun z : Qₚ ↦ c + z) ⁻¹' Q
  let f : Qₚ → E := fun z ↦ B (c + z)
  have hU : IsOpen U := hQ.preimage (by fun_prop)
  have hf : ContDiffOn ℝ ∞ f U := hB.comp (by fun_prop) (fun _ h ↦ h)
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound zero_le_one
    intro z
    simp [T, insertTimeLinear, Prod.norm_def, norm_nonneg]
  have hmem : T q ∈ U := by
    simpa [T, U, c, insertTimeLinear] using hq
  have hb := norm_iteratedFDeriv_comp_linear_on_open_le T hU hf hmem k
  have he : (fun w : Qₛ ↦ B (w.1, (t, w.2.1), w.2.2)) = f ∘ T := by
    funext w
    simp [f, c, T, insertTimeLinear]
  rw [he]
  apply hb.trans
  apply (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) hT)).trans_eq
  simp only [f, iteratedFDeriv_comp_add_left]
  simp [c, T, insertTimeLinear]

/-- Original amplitude jets with baseline `r_par`, and covector jets with
baseline `r_par+1`, construct the low normal data for every physical derivative
branch. Only original jets through `s+M+1` are needed, including the additional
parameter derivative. Constants precede the masks, fields, scale and order.

The parent must instantiate the displayed original profiles on its actual
`fullDerivativeAmplitude` and phase. The normal-data phase and its geometry
are inherited from the supplied original phase chart; the new amplitude fields
are proved from those profiles (`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_rawSlicePrimitiveBranchNormalData_wkbGrades
    (G : UniformNormalGeometry d r) (C : ℕ → ℝ)
    {U : Set X} {V Ω : Set Y} {Q K : Set Qₚ} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (ζ : Y)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    (a p bmask : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hbmask : ∀ j, 0 ≤ bmask j) :
    ∃ a' p' : ℕ → ℝ, (∀ j, 0 ≤ a' j) ∧ (∀ j, 0 ≤ p' j) ∧
      ∀ (χ : X → ℝ) (m : Y → ℂ) (S : X → Y → ℝ) (A : X → Y → Fin r → ℂ),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ m Ω →
      (∀ x, χ x ≠ 0 → x.2 ∈ G.X₀) → (Function.support m ⊆ G.D₀) →
      ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V) →
      ∀ (s : ℕ) (L : ℝ), 1 ≤ L →
      (∀ q ∈ K, ∀ j ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ j (fun z : Qₚ ↦ (χ z.2.1 : ℂ) * m z.2.2) q‖ ≤ bmask j) →
      (∀ z ∈ U ×ˢ V, ∀ j ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ j (Function.uncurry A) z‖ ≤
          a j * L ^ (j - rawSliceParameterOrder (d + 1))) →
      (∀ z ∈ U ×ˢ V, ∀ j ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ j (fun w : X × Y ↦ fderiv ℝ (S w.1) w.2) z‖ ≤
          p j * L ^ (j - 1 - rawSliceParameterOrder (d + 1))) →
      ∀ (v : Fin s → X), (∀ i, ‖v i‖ ≤ 1) →
      ∀ (b : SliceDerivativeBranch s) (t : ℝ) (F : UniformNormalData G C),
      (∀ q ∈ F.parameterDomain ×ˢ F.extensionDomain,
        (q.1, (t, q.2.1), q.2.2) ∈ Q) →
      (∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ G.D, (ε, (t, z.1), z.2) ∈ K) →
      (∀ ε y u, F.phase ε y u = rawSlicePhaseExtension S ζ (ε, (t, y), u)) →
      ∃ H : UniformNormalData G (sliceBranchInputConstant C a' p' b),
        H.phase = F.phase ∧
        H.phase = (fun ε y u ↦ rawSlicePhaseExtension S ζ (ε, (t, y), u)) ∧
        H.amplitude = fun ε y u ↦ normalizedSliceDerivativeAmplitude
          (rawSlicePhaseExtension S ζ) (rawSliceAmplitudeExtension A χ m ζ)
          (fun i ↦ rawSlicePhysicalLift (v i)) b L (ε, (t, y), u) := by
  obtain ⟨a', p', ha', hp', hprofiles⟩ := exists_normalizedRawSliceBranch_uniformProfiles_parameterReserve
    (F := Fin r → ℂ) hU hV hQ hW hIW hK hKQ ζ hshift hθ a p bmask ha hp hbmask
  refine ⟨a', p', ha', hp', ?_⟩
  intro χ m S A hχ hm hχsupp hmsupp hS hA s L hL hmask hAj hDj v hv b t F hchart hpoints hphase
  let φ := rawSlicePhaseExtension S ζ
  let B := rawSliceAmplitudeExtension A χ m ζ
  let v' : Fin s → Qₚ := fun i ↦ rawSlicePhysicalLift (v i)
  let Hfull := normalizedSliceDerivativeAmplitude φ B v' b L
  let Hslice : Qₛ → Fin r → ℂ := fun q ↦ Hfull (q.1, (t, q.2.1), q.2.2)
  have hφ : ContDiffOn ℝ ∞ φ Q := contDiffOn_rawSlicePhaseExtension hU hV hQ hW hIW hS hshift
  have hB : ContDiffOn ℝ ∞ B Q := contDiffOn_rawSliceAmplitudeExtension hA hχ hm
    (hshift 1 (hIW (by simp))) hθ
  have hfull : ContDiffOn ℝ ∞ Hfull Q :=
    contDiffOn_normalizedSliceDerivativeAmplitude hQ hφ hB v' b L
  have hslice : ContDiffOn ℝ ∞ Hslice (F.parameterDomain ×ˢ F.extensionDomain) :=
    hfull.comp (by fun_prop) hchart
  have hsupp : tsupport Hfull ⊆ {q : Qₚ | (q.2.1.2, q.2.2) ∈ G.X₀ ×ˢ G.D₀} := by
    apply (tsupport_smul_subset_right _ _).trans
    apply (tsupport_sliceDerivativeAmplitude_subset φ B v' b).trans
    apply closure_minimal
    · intro q hq
      have hn : B q ≠ 0 := hq
      have hc : χ q.2.1 ≠ 0 := by
        intro hz
        apply hn
        simp [B, rawSliceAmplitudeExtension, hz]
      have hm' : m q.2.2 ≠ 0 := by
        intro hz
        apply hn
        simp [B, rawSliceAmplitudeExtension, hz]
      exact ⟨hχsupp _ hc, hmsupp hm'⟩
    · exact (G.compact_X₀.isClosed.prod G.compact_D₀.isClosed).preimage (by fun_prop)
  have hjoint (ε : ℝ) (hε : ε ∈ Icc 0 G.ε₀) (z : Z) (hz : z ∈ G.X ×ˢ G.D)
      (k : ℕ) (hk : k ≤ rawSliceJetOrder (d + 1) + 1) :
      ‖iteratedFDeriv ℝ k Hslice (ε, z)‖ ≤ sliceDerivativeJetConstant a' p' b k := by
    apply (norm_iteratedFDeriv_insertTime_le hQ hfull t
      (hKQ (hpoints ε hε z hz)) k).trans
    exact hprofiles χ m S A hχ hm hS hA (d + 1) s L hL hmask hAj hDj v'
      (fun i ↦ by simpa only [v', norm_rawSlicePhysicalLift] using hv i)
      b _ (hpoints ε hε z hz) k hk
  let H : UniformNormalData G (sliceBranchInputConstant C a' p' b) := {
    phase := F.phase
    amplitude := fun ε y u ↦ Hslice (ε, (y, u))
    parameterDomain := F.parameterDomain
    extensionDomain := F.extensionDomain
    isOpen_parameterDomain := F.isOpen_parameterDomain
    isOpen_extensionDomain := F.isOpen_extensionDomain
    parameter_subset := F.parameter_subset
    spatial_subset := F.spatial_subset
    phase_smooth := F.phase_smooth
    amplitude_smooth := hslice
    amplitude_support := by
      intro ε _ z hz
      exact hsupp (subset_tsupport Hfull (show Hfull (ε, (t, z.1), z.2) ≠ 0 from hz))
    input_jets := by
      intro ε hε z hz k hk
      have he := F.parameter_subset hε
      have hz' := F.spatial_subset ⟨subset_closure hz.1, subset_closure hz.2⟩
      have hzero := (norm_iteratedFDeriv_slice_le_joint F.isOpen_parameterDomain
        F.isOpen_extensionDomain hslice he hz' k).trans
        (hjoint ε hε z hz k (by simp only [rawSliceJetOrder] at *; omega))
      have hone := (norm_deriv_sliceJet_le_joint F.isOpen_parameterDomain
        F.isOpen_extensionDomain hslice he hz' k).trans
        (hjoint ε hε z hz (k + 1) (by simp only [rawSliceJetOrder] at *; omega))
      have hbase := F.input_jets ε hε z hz k hk
      have hn₀ := norm_nonneg (iteratedFDeriv ℝ k (Function.uncurry (F.amplitude ε)) z)
      have hn₁ := norm_nonneg
        (deriv (fun u ↦ iteratedFDeriv ℝ k (Function.uncurry (F.amplitude u)) z) ε)
      change ‖iteratedFDeriv ℝ k (Function.uncurry (F.phase ε)) z‖ +
        ‖iteratedFDeriv ℝ k (fun y ↦ Hslice (ε, y)) z‖ +
        ‖deriv (fun u ↦ iteratedFDeriv ℝ k (Function.uncurry (F.phase u)) z) ε‖ +
        ‖deriv (fun u ↦ iteratedFDeriv ℝ k (fun y ↦ Hslice (u, y)) z) ε‖ ≤ _
      dsimp only [sliceBranchInputConstant]
      linarith
    gradient_injective := F.gradient_injective
    image_buffer := F.image_buffer
    chart_buffer := F.chart_buffer
    jacobian_gap := F.jacobian_gap }
  exact ⟨H, rfl, by funext ε y u; exact hphase ε y u, rfl⟩

end JanetCartan.RawPrimary.SliceBounds
