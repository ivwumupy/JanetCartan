module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.ParameterJets

/-!
# The normalized differentiated single-channel input

The original phase geometry is retained literally. All new quantitative fields
are proved from joint grades of the undifferentiated chart phase and amplitude,
with the fixed reserve of `app:ch_waves:thm:wkb`. The WKB/history construction
still has to produce those chart grades by pullback from its original buffered
charts; this module does not identify that separate production with an operator
estimate. The consumer is `jc-raw-differentiated-slice-assembly`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open NormalComparison

/-- Finite input budget of a normalized differentiation branch, including the
one parameter derivative (`app:ch_waves:eq:individual-raw-slice`). -/
def sliceBranchInputConstant (C a p : ℕ → ℝ) {s : ℕ}
    (b : SliceDerivativeBranch s) (k : ℕ) : ℝ :=
  C k + sliceDerivativeJetConstant a p b k + sliceDerivativeJetConstant a p b (k + 1)

variable {d r : ℕ} {G : UniformNormalGeometry d r} {C : ℕ → ℝ}

local notation "Z" => Euclidean d × Euclidean d
local notation "Q" => ℝ × Z

/-- Construct the SingleChannel primitive input for an exact differentiated
branch. Primitive joint grades of the original chart functions are the only
new quantitative premises. No differentiated-symbol bound or channel estimate
is assumed. All four phase-geometric fields are inherited unchanged, and
`input_jets` is proved including its parameter derivative
(`app:ch_waves:eq:individual-raw-slice`).

The physical dimension is `d+1`, so the manuscript reserve is
`Dpr + (20*((d+1)+1)+3) + 2`, independent of `s`. The finite primitive jet
orders used are at most `s + 20*((d+1)+1) + 1`. The global support premise
is supplied by the original physical/input cutoffs, including in the open
parameter extension, rather than by a differentiated support hypothesis. -/
theorem exists_normalizedSliceDerivativeNormalData (F : UniformNormalData G C)
    {s Dpr : ℕ} (v : Fin s → Q) (b : SliceDerivativeBranch s)
    (hv : ∀ i, ‖v i‖ ≤ 1) {L : ℝ} (hL : 1 ≤ L) (a p : ℕ → ℝ)
    (ha : ∀ j ≤ s + rawSliceJetOrder (d + 1) + 1, 0 ≤ a j)
    (hp : ∀ j, 1 ≤ j → j ≤ s + rawSliceJetOrder (d + 1) + 1 → 0 ≤ p j)
    (hsupp : Function.support (fun q : Q ↦ F.amplitude q.1 q.2.1 q.2.2) ⊆
      univ ×ˢ (G.X₀ ×ˢ G.D₀))
    (hAj : ∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ G.D,
      ∀ j ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ j (fun q : Q ↦ F.amplitude q.1 q.2.1 q.2.2) (ε, z)‖ ≤
          a j * L ^ (j + Dpr - rawSlicePrimitiveReserve (d + 1) Dpr))
    (hφj : ∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ G.D,
      ∀ j, 1 ≤ j → j ≤ s + rawSliceJetOrder (d + 1) + 1 →
        ‖iteratedFDeriv ℝ j (fun q : Q ↦ F.phase q.1 q.2.1 q.2.2) (ε, z)‖ ≤
          p j * L ^ (j - 1 + Dpr - rawSlicePrimitiveReserve (d + 1) Dpr)) :
    ∃ H : UniformNormalData G (sliceBranchInputConstant C a p b),
      H.phase = F.phase ∧
      H.amplitude = fun ε y u ↦ normalizedSliceDerivativeAmplitude
        (fun q : Q ↦ F.phase q.1 q.2.1 q.2.2)
        (fun q : Q ↦ F.amplitude q.1 q.2.1 q.2.2) v b L (ε, (y, u)) := by
  let φ : Q → ℝ := fun q ↦ F.phase q.1 q.2.1 q.2.2
  let A : Q → Fin r → ℂ := fun q ↦ F.amplitude q.1 q.2.1 q.2.2
  let B := normalizedSliceDerivativeAmplitude φ A v b L
  have hB : ContDiffOn ℝ ∞ B (F.parameterDomain ×ˢ F.extensionDomain) :=
    contDiffOn_normalizedSliceDerivativeAmplitude
      (F.isOpen_parameterDomain.prod F.isOpen_extensionDomain)
      F.phase_smooth F.amplitude_smooth v b L
  have hBsupport : Function.support B ⊆ univ ×ˢ (G.X₀ ×ˢ G.D₀) := by
    apply (subset_tsupport B).trans
    apply (tsupport_smul_subset_right _ _).trans
    apply (tsupport_sliceDerivativeAmplitude_subset φ A v b).trans
    exact closure_minimal hsupp (isClosed_univ.prod
      (G.compact_X₀.isClosed.prod G.compact_D₀.isClosed))
  have hjoint (ε : ℝ) (hε : ε ∈ Icc 0 G.ε₀) (z : Z) (hz : z ∈ G.X ×ˢ G.D)
      (k : ℕ) (hk : k ≤ rawSliceJetOrder (d + 1) + 1) :
      ‖iteratedFDeriv ℝ k B (ε, z)‖ ≤ sliceDerivativeJetConstant a p b k := by
    exact norm_iteratedFDeriv_normalizedSliceDerivativeAmplitude_le
      (F.isOpen_parameterDomain.prod F.isOpen_extensionDomain)
      F.phase_smooth F.amplitude_smooth hk v b hv hL
      (fun j hj ↦ ha j (by omega)) (fun j hj hj' ↦ hp j hj (by omega))
      ⟨F.parameter_subset hε, F.spatial_subset ⟨subset_closure hz.1, subset_closure hz.2⟩⟩
      (fun j hj ↦ hAj ε hε z hz j (by omega))
      (fun j hj hj' ↦ hφj ε hε z hz j hj (by omega))
  let H : UniformNormalData G (sliceBranchInputConstant C a p b) := {
    phase := F.phase
    amplitude := fun ε y u ↦ B (ε, (y, u))
    parameterDomain := F.parameterDomain
    extensionDomain := F.extensionDomain
    isOpen_parameterDomain := F.isOpen_parameterDomain
    isOpen_extensionDomain := F.isOpen_extensionDomain
    parameter_subset := F.parameter_subset
    spatial_subset := F.spatial_subset
    phase_smooth := F.phase_smooth
    amplitude_smooth := hB
    amplitude_support := fun ε _ z hz ↦ (hBsupport
      (show (ε, z) ∈ Function.support B from hz)).2
    input_jets := by
      intro ε hε z hz k hk
      have he := F.parameter_subset hε
      have hz' := F.spatial_subset ⟨subset_closure hz.1, subset_closure hz.2⟩
      have hzero := (norm_iteratedFDeriv_slice_le_joint F.isOpen_parameterDomain
        F.isOpen_extensionDomain hB he hz' k).trans
        (hjoint ε hε z hz k (by simp only [rawSliceJetOrder] at *; omega))
      have hone := (norm_deriv_sliceJet_le_joint F.isOpen_parameterDomain
        F.isOpen_extensionDomain hB he hz' k).trans
        (hjoint ε hε z hz (k + 1) (by simp only [rawSliceJetOrder] at *; omega))
      have hbase := F.input_jets ε hε z hz k hk
      have hn₀ := norm_nonneg (iteratedFDeriv ℝ k (Function.uncurry (F.amplitude ε)) z)
      have hn₁ := norm_nonneg
        (deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (F.amplitude t)) z) ε)
      change ‖iteratedFDeriv ℝ k (Function.uncurry (F.phase ε)) z‖ +
        ‖iteratedFDeriv ℝ k (fun y ↦ B (ε, y)) z‖ +
        ‖deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (F.phase t)) z) ε‖ +
        ‖deriv (fun t ↦ iteratedFDeriv ℝ k (fun y ↦ B (t, y)) z) ε‖ ≤ _
      dsimp only [sliceBranchInputConstant]
      linarith
    gradient_injective := F.gradient_injective
    image_buffer := F.image_buffer
    chart_buffer := F.chart_buffer
    jacobian_gap := F.jacobian_gap }
  exact ⟨H, rfl, rfl⟩

end JanetCartan.RawPrimary.SliceBounds
