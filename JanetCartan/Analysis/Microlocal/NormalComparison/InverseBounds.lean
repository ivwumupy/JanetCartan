module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension

/-!
# Uniform inverse-chart and transport coefficients

Geometric prerequisites for `app:ch_osc:prop:osc-normal` in `paper.tex`.
The input-only setup gives joint inverse regularity, the exact phase transport
identity, and quantitative inverse, velocity, flux and coefficient jets. The
actual inverse amplitude and transport coefficients have smooth buffered zero
extensions. Both supply `MatrixNormalAmplitudeBounds` with common constants
chosen before the family, using only the geometry and the finite input jets.
The operator construction and norm comparison are downstream obligations.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ}

local instance (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- The local geometric estimates at the exact orders consumed by
`app:ch_osc:prop:osc-normal`: two extra inverse jets for Step 1 and
`2(n+1)` coefficient jets for Step 2. The only inputs are the original
setup and finite input sequence; every forward-jet premise is discharged.
Global zero extension is not part of this local assertion. -/
theorem UniformNormalGeometry.exists_normalComparison_local_jet_bounds
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ K > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀,
      (∀ z ∈ G.X ×ˢ (G.X ×ˢ G.V), ∀ k ≤ 2 * (n + 1) + 2,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          F.inverseChart ε q.1 q.2.1 q.2.2) z‖ ≤ K) ∧
      (∀ c : Option (Fin n), ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ 2 * (n + 1),
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          F.normalTransportCoefficient ε c q.1 q.2.1 q.2.2) z‖ ≤ K) := by
  obtain ⟨I, hI, hi⟩ := G.exists_inverseChart_jet_bound_of_input C (2 * (n + 1) + 2) (by omega)
  obtain ⟨A, _hA, ha⟩ := G.exists_normalTransportCoefficient_jet_bound C (2 * (n + 1)) (by omega)
  refine ⟨max I A, lt_of_lt_of_le hI (le_max_left _ _), ?_⟩
  intro F ε hε
  exact ⟨fun z hz k hk ↦ (hi F ε hε z hz k hk).trans (le_max_left _ _),
    fun c z hz k hk ↦ (ha F ε hε c z hz k hk).trans (le_max_right _ _)⟩

variable {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The actual mask-free inverse amplitude in the paired-position convention
of `app:ch_osc:lem:osc-amplitude`, used in Step 1 of
`app:ch_osc:prop:osc-normal`. Both positions and the absolute Jacobian are
retained by the underlying buffered extension. -/
def UniformNormalData.pairedInverseAmplitude (F : UniformNormalData G C) (ε : ℝ) :=
  pairedNormalAmplitude (F.extendedInverseAmplitude ε)

/-- At every admissible parameter the paired amplitude agrees everywhere
with the literal zero-extended inverse amplitude of
`app:ch_osc:eq:osc-exact-normal-kernel`. -/
theorem UniformNormalData.pairedInverseAmplitude_eq (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) (x y v : Euclidean n) :
    F.pairedInverseAmplitude ε v (pairedPosition x y) =
      F.maskFreeInverseAmplitude ε x y v := by
  rw [pairedInverseAmplitude, pairedNormalAmplitude_pairedPosition]
  exact F.extendedInverseAmplitude_eq_maskFree hε (x, (y, v))

/-- The paired amplitude is exactly the full-image zero extension of the
inverse-Jacobian formula in `app:ch_osc:eq:osc-exact-normal-kernel`, with
mask one. This identifies the coefficient for the later change of variables. -/
theorem UniformNormalData.pairedInverseAmplitude_eq_image_indicator
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {x y : Euclidean n} (hx : x ∈ G.X) (hy : y ∈ G.X) (v : Euclidean n) :
    F.pairedInverseAmplitude ε v (pairedPosition x y) =
      (averagedGradient (F.phase ε) x y '' G.D).indicator
        (inverseJacobianAmplitude (F.amplitude ε) (fun _ ↦ 1) x y
          (F.inverseChart ε x y) (fderiv ℝ (averagedGradient (F.phase ε) x y))) v := by
  rw [F.pairedInverseAmplitude_eq hε]
  exact F.maskFreeInverseAmplitude_eq_image_indicator hε hx hy v

/-- Global spatial smoothness after identifying both physical positions,
as used in Step 1 of `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.pairedInverseAmplitude_contDiff
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    ContDiff ℝ ∞ (Function.uncurry (F.pairedInverseAmplitude ε)) :=
  contDiff_pairedNormalAmplitude (F.extendedInverseAmplitude_contDiff hε)

/-- Uniform positive physical-support and derivative constants for the
actual inverse amplitude in Step 1 of `app:ch_osc:prop:osc-normal`.
All inverse, determinant and extension estimates follow from the original
input data; the constants precede the family. -/
theorem UniformNormalGeometry.exists_pairedInverseAmplitude_bounds
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ R > 0, ∃ A > 0, ∀ F : UniformNormalData G C,
      ∀ ε ∈ Icc 0 G.ε₀,
        MatrixNormalAmplitudeBounds (F.pairedInverseAmplitude ε) R A := by
  obtain ⟨R, hR, hbox⟩ := G.compact_X₀.isBounded.exists_pos_norm_le
  obtain ⟨K, hK, hjet⟩ := G.exists_extendedInverseAmplitude_jet_bound C
  refine ⟨R, hR, K * normalPositionJetFactor n (2 * (n + 1)),
    mul_pos hK (normalPositionJetFactor_pos _ _), ?_⟩
  intro F ε hε
  have hf := F.extendedInverseAmplitude_contDiff hε
  have hp := F.pairedInverseAmplitude_contDiff hε
  refine ⟨hp.continuous.stronglyMeasurable, ?_, ?_, ?_⟩
  · intro v
    exact hp.comp (contDiff_const.prodMk contDiff_id)
  · intro v i j
    apply pairedNormalAmplitude_supportedInCenteredBox hbox
    intro q hq
    have hs := F.support_extendedInverseAmplitude_subset hε hq
    exact ⟨hs.1, hs.2.1⟩
  · intro v is hi z
    exact pairedNormalAmplitude_derivative_bound hf (fun q k hk ↦ hjet F ε hε q k hk)
      v is hi z

/-- The complete geometric coefficient bounds for both steps of
`app:ch_osc:prop:osc-normal`. A single pair of positive constants works for
the mask-free inverse amplitude and every literal transport coefficient,
for every family with the fixed original input jets. No inverse estimate,
coefficient bound, or mask derivative is an additional premise. -/
theorem UniformNormalGeometry.exists_normalComparison_amplitude_bounds
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ R > 0, ∃ A > 0, ∀ F : UniformNormalData G C,
      ∀ ε ∈ Icc 0 G.ε₀,
        MatrixNormalAmplitudeBounds (F.pairedInverseAmplitude ε) R A ∧
        ∀ c : Option (Fin n),
          MatrixNormalAmplitudeBounds (F.pairedTransportCoefficient ε c) R A := by
  obtain ⟨RI, hRI, AI, hAI, hI⟩ := G.exists_pairedInverseAmplitude_bounds C
  obtain ⟨RT, _hRT, AT, _hAT, hT⟩ := G.exists_pairedTransportCoefficient_bounds C
  have enlarge {a : Euclidean n → EuclideanSpace ℝ (Fin (2 * n)) →
      Matrix (Fin r) (Fin r) ℂ} {R A R' A' : ℝ}
      (h : MatrixNormalAmplitudeBounds a R A) (hR : R ≤ R') (hA : A ≤ A') :
      MatrixNormalAmplitudeBounds a R' A' := by
    refine ⟨h.measurable, h.smooth, ?_, ?_⟩
    · intro u i j z hz k
      exact (h.support u i j z hz k).trans hR
    · intro u is hi z
      exact (h.derivative u is hi z).trans hA
  refine ⟨max RI RT, hRI.trans_le (le_max_left _ _),
    max AI AT, hAI.trans_le (le_max_left _ _), ?_⟩
  intro F ε hε
  exact ⟨enlarge (hI F ε hε) (le_max_left _ _) (le_max_left _ _),
    fun c ↦ enlarge (hT F ε hε c) (le_max_right _ _) (le_max_right _ _)⟩

end JanetCartan.NormalComparison
