module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.Measurability

/-!
# Regularity only near the supported kernels

For `app:ch_regular_base:eq:fixed-time-representation`, continuity of the phase
is needed only where the amplitude can be nonzero. We absorb the phase into
the amplitude solely to apply the compact-kernel continuity lemmas. This does
not assert symbol estimates for that auxiliary amplitude. In particular the
original phase need not be continuous at the zero covector or outside its chart.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral
variable {n q : ℕ}
local notation "E" => Euclidean n

/-- Continuity of the phase-weighted full amplitude from regularity near its
closed physical/frequency carrier. Consumer: the compact forward and reverse
test curves in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_supported_phaseWeightedAmplitude
    (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude n q)
    {X F : Set E} (hX : IsClosed X) (hF : IsClosed F)
    (hS : ∀ r x ξ, x ∈ X → ξ ∈ F →
      ContinuousAt (fun p : (ℝ × E) × E ↦ S p.1.1 p.1.2 p.2) ((r, x), ξ))
    (hA : ∀ r x z ξ, x ∈ X → ξ ∈ F →
      ContinuousAt (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.1.1.2 p.1.2 p.2)
        (((r, x), z), ξ))
    (hs : ∀ r x z ξ, x ∉ X ∨ ξ ∉ F → A r x z ξ = 0) :
    Continuous (fun p : ((ℝ × E) × E) × E ↦
      Complex.exp (Complex.I * (S p.1.1.1 p.1.1.2 p.2 : ℂ)) •
        A p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  let C : Set (((ℝ × E) × E) × E) := {p | p.1.1.2 ∈ X ∧ p.2 ∈ F}
  have hc : IsClosed C := (hX.preimage continuous_fst.fst.snd).inter
    (hF.preimage continuous_snd)
  have hsupport : tsupport (fun p : ((ℝ × E) × E) × E ↦
      A p.1.1.1 p.1.1.2 p.1.2 p.2) ⊆ C := by
    apply closure_minimal _ hc
    intro p hp
    by_contra hn
    exact hp (hs _ _ _ _ (by change ¬(_ ∧ _) at hn; tauto))
  apply continuous_of_tsupport
  intro p hp
  have hx := hsupport (tsupport_smul_subset_right _ _ hp)
  have hpS : ContinuousAt (fun p : ((ℝ × E) × E) × E ↦ S p.1.1.1 p.1.1.2 p.2) p :=
    (hS p.1.1.1 p.1.1.2 p.2 hx.1 hx.2).comp
      (f := fun p : ((ℝ × E) × E) × E ↦ (p.1.1, p.2))
      (continuous_fst.fst.prodMk continuous_snd).continuousAt
  exact (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hpS)).cexp.smul
    (hA _ _ _ _ hx.1 hx.2)

/-- Absorbing the phase leaves the literal finite forward kernel unchanged.
This is an equality of actual integrals, used only for support-local regularity
in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem graphOperator_eq_phaseWeighted (S : E → E → ℝ) (A : FullAmplitude n q)
    (u : E → Fin q → ℂ) :
    graphOperator S A u = graphOperator (fun _ _ ↦ 0)
      (fun x z ξ ↦ Complex.exp (Complex.I * (S x ξ : ℂ)) • A x z ξ) u := by
  funext x
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [graphOscillation, Matrix.smul_mulVec, smul_smul]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The same absorption preserves the literal adjoint kernel. The amplitude
is conjugate-transposed in its original `(x,z,ξ)` order, as required in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem reverseGraphOperator_eq_phaseWeighted (S : E → E → ℝ)
    (A : FullAmplitude n q) (u : E → Fin q → ℂ) :
    reverseGraphOperator S (fun x z ξ ↦ (A x z ξ).conjTranspose) u =
      reverseGraphOperator (fun _ _ ↦ 0)
        (fun x z ξ ↦ (Complex.exp (Complex.I * (S x ξ : ℂ)) • A x z ξ).conjTranspose) u := by
  funext z
  unfold reverseGraphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mulVec, smul_smul, ← star_mul]
  congr 2
  simp only [graphOscillation]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Compact forward test curves require only local phase/amplitude continuity
on a closed supported chart. No continuous extension of the original phase
is assumed. Consumer: support-local measurability in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem aestronglyMeasurable_supported_compact_graph_apply
    (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude n q)
    {X Y K F : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hK : IsCompact K)
    (hF : IsClosed F)
    (hS : ∀ r x ξ, x ∈ X → ξ ∈ F →
      ContinuousAt (fun p : (ℝ × E) × E ↦ S p.1.1 p.1.2 p.2) ((r, x), ξ))
    (hA : ∀ r x z ξ, x ∈ X → ξ ∈ F →
      ContinuousAt (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.1.1.2 p.1.2 p.2)
        (((r, x), z), ξ))
    (hsF : ∀ r x z ξ, x ∉ X ∨ ξ ∉ F → A r x z ξ = 0)
    (hs : ∀ r x z ξ, x ∉ X ∨ z ∉ Y ∨ ξ ∉ K → A r x z ξ = 0)
    (T : ℝ → Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)) (μ : Measure ℝ)
    (hreal : ∀ u : graphTestSpace n q, ∀ᵐ r ∂μ,
      T r (graphTestToLp u) =ᵐ[volume] graphTestOutput (S r) (A r) u)
    (u : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)) :
    AEStronglyMeasurable (fun r ↦ T r u) μ := by
  apply aestronglyMeasurable_compact_graph_apply (fun _ _ _ ↦ 0)
    (fun r x z ξ ↦ Complex.exp (Complex.I * (S r x ξ : ℂ)) • A r x z ξ)
    continuous_const (continuous_supported_phaseWeightedAmplitude S A hX.isClosed hF hS hA hsF)
    hX hY hK (fun r x z ξ h ↦ by simp [hs r x z ξ h]) T μ _ u
  intro v
  filter_upwards [hreal v] with r hr
  convert hr using 1
  funext x
  exact congrArg (fun f ↦ WithLp.toLp 2 (f x))
    (graphOperator_eq_phaseWeighted (S r) (A r) (fun z ↦ (v.val z).ofLp)).symm

/-- The corresponding reverse curves have the same support-local regularity.
The actual primitive adjoint test realization is the sole operator input.
Consumer: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem aestronglyMeasurable_supported_compact_reverse_apply
    (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude n q)
    {X Y K F : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hK : IsCompact K)
    (hF : IsClosed F)
    (hS : ∀ r x ξ, x ∈ X → ξ ∈ F →
      ContinuousAt (fun p : (ℝ × E) × E ↦ S p.1.1 p.1.2 p.2) ((r, x), ξ))
    (hA : ∀ r x z ξ, x ∈ X → ξ ∈ F →
      ContinuousAt (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.1.1.2 p.1.2 p.2)
        (((r, x), z), ξ))
    (hsF : ∀ r x z ξ, x ∉ X ∨ ξ ∉ F → A r x z ξ = 0)
    (hs : ∀ r x z ξ, x ∉ X ∨ z ∉ Y ∨ ξ ∉ K → A r x z ξ = 0)
    (T : ℝ → Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)) (μ : Measure ℝ)
    (hreal : ∀ u : graphTestSpace n q, ∀ᵐ r ∂μ,
      T r (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (S r) (fun x z ξ ↦ (A r x z ξ).conjTranspose)
          (fun x ↦ (u.val x).ofLp) z))
    (u : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)) :
    AEStronglyMeasurable (fun r ↦ T r u) μ := by
  apply aestronglyMeasurable_compact_reverse_apply (fun _ _ _ ↦ 0)
    (fun r x z ξ ↦ (Complex.exp (Complex.I * (S r x ξ : ℂ)) • A r x z ξ).conjTranspose)
    continuous_const
    (continuous_supported_phaseWeightedAmplitude S A hX.isClosed hF hS hA hsF).matrix_conjTranspose
    hX hY hK (fun r x z ξ h ↦ by simp [hs r x z ξ (by tauto)]) T μ _ u
  intro v
  filter_upwards [hreal v] with r hr
  convert hr using 1
  funext z
  exact congrArg (fun f ↦ WithLp.toLp 2 (f z))
    (reverseGraphOperator_eq_phaseWeighted (S r) (A r) (fun x ↦ (v.val x).ofLp)).symm

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
