module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.ForwardWeakTransfer
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.ReverseWeakTransfer

/-!
# Supported first-output derivatives

These are the initial derivative identities for the order-minus-one gain in
`app:ch_regular_base:eq:fio-input`. The same literal operators and masks are
retained. Smooth auxiliary phases are used solely in compact kernel calculus;
no global homogeneous or nondegenerate extension is required.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory LineDeriv
open scoped ContDiff Topology SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Germ agreement preserves every ordered joint jet. This is used only to
transport the original phase jets in the gain-one seed estimate.
Source: `app:ch_regular_base:eq:fio-input`, gain-one paragraph. -/
theorem jet_eq_of_eventuallyEq {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : Field n W} {p : Point n} (h : uncurry f =ᶠ[𝓝 p] uncurry g)
    (w : List (Coordinate n)) : uncurry (jet w f) p = uncurry (jet w g) p := by
  induction w generalizing p with
  | nil => exact h.eq_of_nhds
  | cons c w ih =>
    apply derivative_congr
    filter_upwards [h.eventually_nhds] with q hq
    exact ih hq

/-- The complete first-output amplitude, including the derivative of its output
mask, is unchanged by germ agreement of the phase on its carrier.
Source: gain one following `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphFirstOutputAmplitude_phase_congr
    {K : Set (E × E)} {F : Set E} {A : FullAmplitude n r} {S S' : E → E → ℝ}
    (hsupp : tsupport (uncurry A) ⊆ K ×ˢ F)
    (he : ∀ p ∈ K ×ˢ F, Function.uncurry S' =ᶠ[𝓝 (p.1.1, p.2)] Function.uncurry S)
    (i : Fin n) : graphFirstOutputAmplitude S' A i = graphFirstOutputAmplitude S A i := by
  funext x y η
  by_cases ha : A x y η = 0
  · simp [graphFirstOutputAmplitude, ha]
  · have hc := hsupp (subset_tsupport (uncurry A) (a := ((x, y), η)) ha)
    have hd := (phase_outputPartial_eventuallyEq (he _ hc) i).eq_of_nhds
    simp only [graphFirstOutputAmplitude, hd]

private theorem forward_carrier {X Y F : Set E} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A) (hX : IsCompact X)
    (hY : IsCompact Y) (hF : IsClosed F) : tsupport (uncurry A) ⊆ (X ×ˢ Y) ×ˢ F := by
  apply tsupport_subset_carrier (hX.prod hY) hF
  intro p hp
  apply hA.support
  simpa only [Set.mem_prod, not_and_or, or_assoc] using hp

/-- Smoothness of the first output amplitude is local to the original supported
chart. The compact extension is eliminated by exact amplitude equality.
Source: gain one in `app:ch_regular_base:eq:fio-input`. -/
theorem graphFirstOutput_admissible_of_supported
    {X Y F : Set E} {O : Set (Point n)} {S : E → E → ℝ} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hO : IsOpen O) (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ O)
    (hS : SupportedPhaseRegularity S O) (i : Fin n) :
    ForwardAmplitudeAdmissible X Y F (graphFirstOutputAmplitude S A i) := by
  obtain ⟨S', hs', he⟩ := exists_smooth_supported_phase_extension
    (hX.prod hY) hF hF0 hO hcarrier S hS
  rw [← graphFirstOutputAmplitude_phase_congr (forward_carrier hA hX hY hF) he]
  exact hA.graphFirstOutput hX hY hF hF0 S' (fun _ _ _ ↦ hs'.contDiffAt) i

/-- The forward weak first derivative follows from the literal low realizations
on the original carrier. It is not an operator-derivative premise.
Source: gain one in `app:ch_regular_base:eq:fio-input`. -/
theorem graph_realization_weak_firstOutput_of_supported
    {X Y F : Set E} {O : Set (Point n)} {S : E → E → ℝ} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hO : IsOpen O) (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ O)
    (hS : SupportedPhaseRegularity S O)
    (χ : ℕ → E → ℂ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
    (hχs : ∀ k, HasCompactSupport (χ k)) (i : Fin n) (T W : H →L[ℂ] H)
    (hT : GraphDistributionalRealization (graphOperator S) χ A T)
    (hW : GraphDistributionalRealization (graphOperator S) χ (graphFirstOutputAmplitude S A i) W)
    (u : graphTestSpace n r) :
    lineDerivOp (EuclideanSpace.single i (1 : ℝ))
      (T (graphTestToLp u) : 𝓢'(E, V)) = (W (graphTestToLp u) : 𝓢'(E, V)) := by
  obtain ⟨S', hs', he⟩ := exists_smooth_supported_phase_extension
    (hX.prod hY) hF hF0 hO hcarrier S hS
  have hc := forward_carrier hA hX hY hF
  have hk (B : FullAmplitude n r) (hb : tsupport (uncurry B) ⊆ (X ×ˢ Y) ×ˢ F)
      (k : ℕ) (v : E → Fin r → ℂ) :
      graphOperator S' (frequencyCutFullAmplitude (χ k) B) v =
        graphOperator S (frequencyCutFullAmplitude (χ k) B) v := by
    apply graphOperator_phase_congr
    intro x y η hne
    have hn : B x y η ≠ 0 := by
      intro hz
      exact hne (by simp [frequencyCutFullAmplitude, hz])
    exact (he _ (hb (subset_tsupport (uncurry B) (a := ((x, y), η)) hn))).eq_of_nhds
  have hfirst := graphFirstOutputAmplitude_phase_congr hc he i
  apply graph_realization_weak_firstOutput hA hX hF hF0
    (fun _ _ _ ↦ hs'.contDiffAt) χ hχ hχs i T W _ _ u
  · intro v φ
    simpa only [hk A hc] using hT v φ
  · intro v φ
    simpa only [hfirst, hk _ ((GainOneBranches.support_graphFirstOutput S A i).trans hc)]
      using hW v φ

/-- The first weak derivative of the literal Hilbert adjoint retains the
once-conjugated full amplitude and regularizers. Phase smoothness is local to
the buffered carrier. Source: gain one and
`app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem adjointGraph_realization_weak_firstOutput_of_supported
    {K : Set (E × E)} {F : Set E} {O : Set (Point n)} {S : E → E → ℝ} {A : FullAmplitude n r}
    (hA : ReverseAmplitudeAdmissible K A)
    (hfreq : ∀ x y η, η ∉ F → A x y η = 0)
    (hK : IsCompact K) (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hO : IsOpen O) (hcarrier : K ×ˢ F ⊆ O) (hS : SupportedPhaseRegularity S O)
    (χ : ℕ → E → ℂ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
    (hχs : ∀ k, HasCompactSupport (χ k)) (hχ0 : ∀ k, (0 : E) ∉ tsupport (χ k))
    (i : Fin n) (T W : H →L[ℂ] H)
    (hT : GraphDistributionalRealization (reverseGraphOperator S)
      (fun k η ↦ star (χ k η)) (fun x y η ↦ (A x y η).conjTranspose) T.adjoint)
    (hW : GraphDistributionalRealization (reverseGraphOperator S)
      (fun k η ↦ star (χ k η)) (adjointFirstOutputAmplitude A i) W)
    (u : graphTestSpace n r) :
    lineDerivOp (EuclideanSpace.single i (1 : ℝ))
      (T.adjoint (graphTestToLp u) : 𝓢'(E, V)) = (W (graphTestToLp u) : 𝓢'(E, V)) := by
  obtain ⟨S', hs', he⟩ := exists_smooth_supported_phase_extension hK hF hF0 hO hcarrier S hS
  have hf : ∀ x y η, η ∉ F → (A x y η).conjTranspose = 0 := by
    intro x y η hη
    simp [hfreq x y η hη]
  have hf₁ : ∀ x y η, η ∉ F → adjointFirstOutputAmplitude A i x y η = 0 :=
    (adjoint_branches_frequency_support (S := S) hf i).2.2
  have ha₁ : ReverseAmplitudeAdmissible K (adjointFirstOutputAmplitude A i) :=
    hA.conjTranspose.reverseFirstOutputAmplitude i
  apply adjointGraph_realization_weak_firstOutput hA hK (fun _ _ _ ↦ hs'.contDiffAt)
    χ hχ hχs hχ0 i T W _ _ u
  · intro v φ
    simpa only [reverseGraphOperator_frequencyCut_phase_congr hA.conjTranspose hf he] using hT v φ
  · intro v φ
    simpa only [reverseGraphOperator_frequencyCut_phase_congr ha₁ hf₁ he] using hW v φ

end JanetCartan.FourierIntegral.SupportedSobolev
