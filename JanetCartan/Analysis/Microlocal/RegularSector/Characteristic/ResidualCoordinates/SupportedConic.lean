module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.BufferedMatrices
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.PhaseExtension
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.Basic
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.EvolutionCoordinates

/-!
# Supported conic continuation of the buffered matrices

The original angular and radial masks give a closed carrier inside the
positive frequency chart. An auxiliary frequency cutoff equal to one on
that carrier removes the vertex. This cutoff is constant in every physical
derivative, and is kept separate from the original right multiplier.
The local matrix's support margin, proved in `BufferedColumns`, becomes a
support margin on the entire unbounded cone. No smoothness at zero or
cancellation outside the supported chart is assumed.
Consumer: `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification AmplitudeBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d n : ℕ}
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- Supported continuation of a buffered local matrix, with the existing
radial order `-o`. The original physical masks and right multiplier remain
outside this definition. Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
def supportedConicMatrix (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (ρ : Euclidean d → ℝ) (f : T → Mat) (p : T) : Mat :=
  ρ p.2.2.2 • ConicAmplitude.extend ℓ o f p

/-- Construct a smooth frequency plateau on the original radial/angular
carrier. Its support stays strictly within the positive chart, even though
the carrier is unbounded. Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem exists_conicFrequency_plateau
    (ℓ : Euclidean d →L[ℝ] ℝ) {K : Set (Euclidean d)}
    (hK : IsClosed K) (hKℓ : K ⊆ {η | 0 < ℓ η}) :
    ∃ ρ : Euclidean d → ℝ, ContDiff ℝ ∞ ρ ∧
      tsupport ρ ⊆ {η | 0 < ℓ η} ∧ ∀ η ∈ K, ρ =ᶠ[𝓝 η] fun _ ↦ 1 := by
  have hO : IsOpen {η | 0 < ℓ η} := isOpen_lt continuous_const ℓ.continuous
  obtain ⟨U, hU, hKU, hUO⟩ := normal_exists_closure_subset hK hO hKℓ
  obtain ⟨V, hV, hUV, hVO⟩ := normal_exists_closure_subset isClosed_closure hO hUO
  obtain ⟨ρ, hρ, _, hsρ, hρone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hUV
  refine ⟨ρ, hρ, by simpa only [tsupport, hsρ] using hVO, ?_⟩
  intro η hη
  filter_upwards [hU.mem_nhds (hKU hη)] with ζ hζ
  exact (hρone ζ).mp (subset_closure hζ)

/-- Global smoothness follows from the constructed frequency margin and the
buffered local matrix. In particular no homogeneous expression is asserted
smooth at the cone vertex. Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_supportedConicMatrix
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (ρ : Euclidean d → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η})
    (f : T → Mat) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (supportedConicMatrix ℓ o ρ f) := by
  let O : Set T := {p | 0 < ℓ p.2.2.2}
  have hO : IsOpen O := isOpen_lt continuous_const
    (ℓ.continuous.comp continuous_snd.snd.snd)
  apply Localization.contDiff_of_contDiffOn_support_neighborhood hO
  · exact (hρ.comp contDiff_snd.snd.snd).contDiffOn.smul
      ((ConicAmplitude.contDiffOn_extend ℓ o isOpen_univ hf.contDiffOn).mono
        (fun p hp ↦ ⟨hp, mem_univ _⟩))
  · exact (tsupport_smul_subset_left _ _).trans
      ((tsupport_comp_subset_preimage ρ continuous_snd.snd.snd).trans (fun p hp ↦ hsρ hp))

/-- The topological support stays in the conic continuation of the SAME
local support neighborhood. This proves vanishing of all extension jets at
its boundary. Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem tsupport_supportedConicMatrix_subset
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (ρ : Euclidean d → ℝ)
    (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η}) (f : T → Mat)
    {V : Set T} (hf : tsupport f ⊆ V) :
    tsupport (supportedConicMatrix ℓ o ρ f) ⊆ ConicPhase.domain ℓ V := by
  intro p hp
  have hρp : p.2.2.2 ∈ tsupport ρ :=
    tsupport_comp_subset_preimage ρ continuous_snd.snd.snd
      (tsupport_smul_subset_left _ _ hp)
  refine ⟨hsρ hρp, hf ?_⟩
  by_contra hn
  have hz := ConicAmplitude.extend_eventuallyEq_zero ℓ o (hsρ hρp).ne'
    (notMem_tsupport_iff_eventuallyEq.mp hn)
  have hz' : supportedConicMatrix ℓ o ρ f =ᶠ[𝓝 p] 0 := by
    filter_upwards [hz] with q hq
    simp only [supportedConicMatrix, hq, Pi.zero_apply, smul_zero]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz') hp

/-- Outside the original transported support margin all joint derivatives
of the supported continuation vanish, including those entering `P W₁`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem iteratedFDeriv_supportedConicMatrix_eq_zero
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (ρ : Euclidean d → ℝ)
    (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η}) (f : T → Mat)
    {V : Set T} (hf : tsupport f ⊆ V) {p : T}
    (hp : p ∉ ConicPhase.domain ℓ V) (m : ℕ) :
    iteratedFDeriv ℝ m (supportedConicMatrix ℓ o ρ f) p = 0 := by
  have hn : p ∉ tsupport (supportedConicMatrix ℓ o ρ f) :=
    fun h ↦ hp (tsupport_supportedConicMatrix_subset ℓ o ρ hsρ f hf h)
  simpa using ((notMem_tsupport_iff_eventuallyEq.mp hn).iteratedFDeriv ℝ m).eq_of_nhds

/-- The frequency cutoff and normalization retain the exact original lower
source-time buffer for both the continued amplitude and its full physical
residual. Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem supportedConicMatrix_lower_buffer
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (ρ : Euclidean d → ℝ) (f : T → Mat)
    (A : Euclidean (d + 1) → Fin (d + 1) → Mat) (B : Euclidean (d + 1) → Mat)
    (a : ℝ) (hf : ∀ p : T, p.2.1 ≤ a → f p = 0) :
    ∀ t s y η, s ≤ a →
      curryCharacteristicMatrix (supportedConicMatrix ℓ o ρ f) t s y η = 0 ∧
      twoTimePhysicalApply A B (curryCharacteristicMatrix (supportedConicMatrix ℓ o ρ f))
        t s y η = 0 := by
  have hz : ∀ t s y η, s ≤ a →
      curryCharacteristicMatrix (supportedConicMatrix ℓ o ρ f) t s y η = 0 := by
    intro t s y η hs
    simp only [curryCharacteristicMatrix, supportedConicMatrix, ConicAmplitude.extend,
      hf (ConicPhase.normalize ℓ (t, (s, (y, η)))) hs, smul_zero]
  exact fun t s y η hs ↦ ⟨hz t s y η hs,
    twoTimePhysicalApply_eq_zero_of_lower_buffer A B _ a hz t s y η hs⟩

/-- The auxiliary frequency plateau changes neither physical mask nor the
original right multiplier in the literal elapsed graph. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedGraph_supportedConicMatrix_eq
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (ρ : Euclidean d → ℝ) (f : T → Mat)
    (Ψ : TwoTimePhase d) (χout χsource β : Euclidean (d + 1) → ℂ)
    (hρ : ∀ ξ, β ξ ≠ 0 → ρ (spatialPart ξ) = 1) (r : ℝ) :
    elapsedGraph Ψ (curryCharacteristicMatrix (supportedConicMatrix ℓ o ρ f))
      χout χsource β r =
      elapsedGraph Ψ (curryCharacteristicMatrix (ConicAmplitude.extend ℓ o f))
        χout χsource β r := by
  apply congrArg (FourierIntegral.FullLowBounds.fullGraphOperator (elapsedPhase Ψ r))
  funext x z ξ
  by_cases hβ : β ξ = 0
  · simp [elapsedAmplitude, hβ]
  · simp [elapsedAmplitude, curryCharacteristicMatrix, supportedConicMatrix, hρ ξ hβ]

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
