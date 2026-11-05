module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationPeriodization
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalObservation

/-!
# The unchanged positive baseline's auxiliary periodic representative

Consumers: `smoothRawCrossResponse_toL2_eq_rawIntegral_component` and
`app:ch_mean_pairs:defn:mean-canonical`. The actual application uses the full
corrected derivative amplitude at the original positive scalar, with the SAME
source observation cutoff. No inner incidence factor, detector, Fourier scalar,
mean carrier cutoff, source change, or extra physical output cutoff occurs here.
The local amplitude's real original-data producer remains explicit in the
actual application; these extension deductions do not assert its existence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalBaseline
open CurrentMean AmplitudeBound

variable {n N : ℕ} {X : Set (Euclidean n)}

/-- The original joint corrected amplitude is smooth at every supported outer
carrier, before applying any inner incidence or detector factor. -/
theorem sourceAmplitude_slice_smooth
    {V : Set (Euclidean 3 × Euclidean (n-1))}
    (A : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → Matrix (Fin N) (Fin n) ℂ)
    (hA : ContDiffOn ℝ ∞ A (X ×ˢ V))
    (c : Euclidean 3 × Euclidean (n-1)) (hc : c ∈ V) :
    ContDiffOn ℝ ∞ (fun x ↦ A (x,c)) X :=
  hA.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ ⟨hx,hc⟩)

/-- Restrict the actual full-parent amplitude to a fixed outer carrier. The
closed-parent inclusion is supplied by the original geometry, not by equating
the smaller PDE source cutoff with the common observation cutoff. -/
theorem parentAmplitude_slice_smooth {b : ℝ}
    {P Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (A : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → Matrix (Fin N) (Fin n) ℂ)
    (hA : ContDiffOn ℝ ∞ A Ω) (c : Euclidean 3 × Euclidean (n-1))
    (hparent : ∀ x ∈ closedBall (0 : Euclidean n) b, (x,c) ∈ P) (hP : P ⊆ Ω) :
    ContDiffOn ℝ ∞ (fun x ↦ A (x,c)) (ball (0 : Euclidean n) b) :=
  hA.comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun x hx ↦ hP (hparent x (ball_subset_closedBall hx)))

/-- The common observation has a strict support gap inside its four-radius
ball, independently of the smaller PDE source cutoff. -/
theorem sourceObservation_support_open {μ : ℝ} (hμ : 0 < μ) :
    tsupport (ContinuumRow.FixedCutoffs.physical (n := n) hμ 2) ⊆
      ball (0 : Euclidean n) (4*μ) := by
  have h := ContinuumRow.FixedCutoffs.physical_tsupport (n := n) hμ 2
  norm_num at h
  exact h

/-- Extend the SAME unscaled positive derivative amplitude only to the auxiliary
periodic space (`app:ch_mean_pairs:defn:mean-canonical`). Its actual full-parent
smoothness is supplied by the unchanged original response producer. -/
def observedBaseline (hX : IsOpen X)
    (A : Euclidean n → Matrix (Fin N) (Fin n) ℂ) (hA : ContDiffOn ℝ ∞ A X)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψX : tsupport ψ ⊆ X)
    {b : ℝ} (hcell : b < 1/2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b) :
    SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) :=
  ⟨fun z _ ↦ ψ (centeredTorusRepresentative z) • A (centeredTorusRepresentative z),
    fun _ ↦ by
      have hh := preparationMatrixExtension_regular ψ hψ hX hψX hcell hbox
        (fun p ↦ A p.1) (hA.comp contDiffOn_fst (fun _ hp ↦ hp.1))
      exact ⟨hh.1.comp (continuous_id.prodMk (continuous_const (y := 0))),
        hh.2.comp (contDiff_id.prodMk (contDiff_const (c := 0)))⟩⟩

/-- Literal values of the observed baseline; no positive scalar or sample
weight has been absorbed into the representative. -/
theorem observedBaseline_apply (hX : IsOpen X)
    (A : Euclidean n → Matrix (Fin N) (Fin n) ℂ) (hA : ContDiffOn ℝ ∞ A X)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψX : tsupport ψ ⊆ X)
    {b : ℝ} (hcell : b < 1/2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)
    (z : Torus n) :
    (observedBaseline hX A hA ψ hψ hψX hcell hbox).val z () =
      ψ (centeredTorusRepresentative z) • A (centeredTorusRepresentative z) := rfl

/-- On the original measurement plateau, the representative is precisely the
unchanged positive derivative amplitude (`app:ch_waves:eq:background-quadrature`). -/
theorem observedBaseline_eq_native (hX : IsOpen X)
    (A : Euclidean n → Matrix (Fin N) (Fin n) ℂ) (hA : ContDiffOn ℝ ∞ A X)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψX : tsupport ψ ⊆ X)
    {b : ℝ} (hcell : b < 1/2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)
    (z : Torus n) (hz : ψ (centeredTorusRepresentative z) = 1) :
    (observedBaseline hX A hA ψ hψ hψX hcell hbox).val z () =
      A (centeredTorusRepresentative z) := by
  rw [observedBaseline_apply, hz, one_smul]

end JanetCartan.PhysicalMean.OriginalCanonicalBaseline
end
