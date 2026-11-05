module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.SampledWholeSourceAmplitude

/-!
# Literal sample nodes and frequencies for the initial localizer

The original finite nonzero sample enumeration supplies node membership and
within-group separation with chart and color retained. The color-dependent
frequency gives exactly the radial carrier phase used by the signed source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.InitialSourceLocalization
open CanonicalRowComparison SeparatedSampling SamplingKernelBounds
open CurrentMean ActualCarriers FrozenMenu CurrentFullPhase

variable {Λ : Type*} {n p : ℕ} {B h : ℝ}
  {weights : Λ → Point → ℝ} {w : ℝ → ℝ} {shifts : Λ → Lattice → Point}

/-- Nonzero literal samples remain in their original parameter cubes
(`app:ch_waves:thm:sampling`, `app:ch_pairs:setup:pairs-lag`). -/
theorem original_sample_node_mem_parameterCube (radius : Λ → ℝ)
    (hsupport : ∀ a z, weights a z ≠ 0 → ∀ i, |z i| ≤ radius a)
    (i : SampleIndex p B weights w h shifts) :
    WithLp.toLp 2 (node h (shifts i.1) i.2) ∈ parameterCube (radius i.1) := by
  have hi : weight (weights i.1) w h (shifts i.1) i.2 ≠ 0 :=
    (Finset.mem_filter.mp i.2.property).2
  exact hsupport i.1 _ (weight_ne_zero_factors hi).1

/-- Keeping both chart and color gives exactly the within-group separation
of the actual nonzero samples (`app:ch_waves:thm:sampling`,
`app:ch_pairs:setup:pairs-lag`). -/
theorem original_sample_same_group_separation {W : ℝ}
    (hw : WindowBounds p w W) (hh : 0 < h)
    (i k : SampleIndex p B weights w h shifts) (hne : i ≠ k)
    (hgroup : (i.1,color p i.2.val.1) = (k.1,color p k.2.val.1)) :
    h/2 ≤ ‖(WithLp.toLp 2 (node h (shifts i.1) i.2) : Euclidean 3) -
      WithLp.toLp 2 (node h (shifts k.1) k.2)‖ := by
  rcases i with ⟨a,i⟩
  rcases k with ⟨b,k⟩
  have hab : a = b := congrArg Prod.fst hgroup
  subst b
  have hik : i.val ≠ k.val := by
    intro heq
    exact hne (congrArg (Sigma.mk a) (Subtype.ext heq))
  exact euclidean_nonzero_samples_separated hw hh
    (Finset.mem_filter.mp i.property).2 (Finset.mem_filter.mp k.property).2
    hik (congrArg Prod.snd hgroup)

/-- The literal color-dependent source frequency agrees with the radial
carrier used by the signed-pair localizer. This preserves its true beat
and the original sampled phase (`app:ch_pairs:setup:pairs-lag`). -/
theorem original_sample_phase_eq_radial_carrier
    {P : Λ → Patch n} {U : Λ → Set (Euclidean n)} {hU : ∀ a, IsOpen (U a)}
    (T : ∀ a, PatchQuantitativeFamily (P a) (U a) (hU a))
    (Q : ∀ a, {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (U a) ∧
      cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T a).family.threshold})
    (τext : Λ → ((Fin 3 → Fin (p+1)) × Point) → ℝ)
    (radial : Λ × (Fin 3 → Fin (p+1)) → ℝ) (frequency : ℝ)
    (hτ : ∀ i : SampleIndex p B weights w h shifts,
      τext i.1 (color p i.2.val.1,node h (shifts i.1) i.2) =
        (frequency * radial (i.1,color p i.2.val.1))⁻¹)
    (i : SampleIndex p B weights w h shifts) (x : Euclidean n) :
    wholeSourceSampledPhase B weights w h shifts T Q τext i x =
      frequency * (radial (i.1,color p i.2.val.1) *
        (T i.1).carrier (Q i.1) x (WithLp.toLp 2 (node h (shifts i.1) i.2))) := by
  unfold wholeSourceSampledPhase
  rw [hτ i, div_inv_eq_mul]
  ring

end JanetCartan.InitialSourceLocalization
