module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Assembly

/-!
# Geometry on the retained characteristic chart

These deductions keep the section `ℓ` and inverse chart `C` returned by
`UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes`.
The inputs `hbuffer`, `hs` and `hdiff` below are literal conclusions of that
producer, as is its closed-buffer mixed estimate. No second chart is chosen.

Consumer: the geometric inputs of
`EvolutionIntegral.exists_retardedOperator_signed_integer_bounds_of_primitive_data`
in `app:ch_regular_base:lem:retarded-kernel`. Matching the output mask and the
source-time buffer to the elapsed slab remains an assembly obligation.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open ConicPhase FourierIntegral EvolutionIntegral
variable {d : ℕ}
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "E" => Euclidean (d + 1)

/-- A fixed radius inside both the retained phase buffer and the amplitude
jet buffer (`app:ch_regular_base:lem:retarded-kernel`). -/
def retainedRadius (b ρ : ℝ) : ℝ := min b ρ / 4

/-- Both radius comparisons follow from the producer's positive radii; no
relation between its separately named buffers is assumed. -/
theorem retainedRadius_bounds {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ) :
    0 < retainedRadius b ρ ∧ 2 * retainedRadius b ρ ≤ b ∧
      retainedRadius b ρ ≤ ρ / 2 := by
  have hp := lt_min hb hρ
  have hb' := min_le_left b ρ
  have hρ' := min_le_right b ρ
  dsimp [retainedRadius]
  constructor
  · positivity
  constructor <;> linarith

/-- The inner physical box has a genuine closure margin in the outer box,
as required by the whole-image graph construction (`retarded-kernel`). -/
theorem closure_elapsedPhysicalBox_half_subset {z : Z} {ε : ℝ} (hε : 0 < ε) :
    closure (elapsedPhysicalBox z (ε / 2)) ⊆ elapsedPhysicalBox z ε := by
  let K : Set E := {x | dist (x 0) z.1 ≤ ε / 2 ∧
    dist (spatialPart x) z.2.1 ≤ ε / 2}
  have hK : IsClosed K :=
    (isClosed_le ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.dist
      continuous_const) continuous_const).inter
      (isClosed_le (spatialPartCLM.continuous.dist continuous_const) continuous_const)
  have hsub : elapsedPhysicalBox z (ε / 2) ⊆ K :=
    fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩
  intro x hx
  have h := closure_minimal hsub hK hx
  exact ⟨h.1.trans_lt (by linarith), h.2.trans_lt (by linarith)⟩

/-- A concrete physical norm bound for the inner box, independent of the
coefficient field (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem norm_le_on_elapsedPhysicalBox {z : Z} {ε : ℝ}
    {x : E} (hx : x ∈ elapsedPhysicalBox z ε) :
    ‖x‖ ≤ |z.1| + ‖z.2.1‖ + 2 * ε := by
  have ht := dist_triangle (x 0) z.1 0
  have hy := dist_triangle (spatialPart x) z.2.1 0
  simp only [dist_zero_right] at ht hy
  have hn := SymbolBudgets.norm_le_time_add_spatial x
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at ht
  have hx₁ : dist (x 0) z.1 < ε := hx.1
  have hx₂ : dist (spatialPart x) z.2.1 < ε := hx.2
  linarith

/-- The continued phase is smooth on the actual open product used by the
retarded theorem. Its only analytic input is the retained local smoothness
from `ConicConstruction` (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_retained_product (ℓ : Euclidean d →L[ℝ] ℝ)
    {C : OpenPartialHomeomorph T T} {z : Z} {ε b : ℝ}
    (hε : 0 < ε) (hεb : 2 * ε ≤ b) (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target) :
    ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase (curriedPhase ℓ C))
      (bufferedBase z ε ×ˢ angularCone ℓ z.2.2 ε) := by
  apply (contDiffOn_jointPhase_curriedExtend ℓ C.open_target hs).mono
  intro p hp
  refine ⟨hp.2.1, hbuffer ?_⟩
  apply closedBall_subset_closedBall hεb
  apply localPatch_bufferedBase_subset z ε
  exact ⟨hp.1, ball_subset_ball (by linarith) hp.2.2⟩

/-- The retained closed-buffer half-gap gives the literal spatial mixed
half-gap on the smaller whole cone. This instantiates `hnear` of the signed
retarded constructor with the SAME chart and section (`retarded-kernel`). -/
theorem retained_mixed_half_gap (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : Z → ℝ} {Φ : Z × ℝ → Z} {C : OpenPartialHomeomorph T T}
    {z : Z} {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ)
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hnear : ∀ q ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) :
    ∀ r ∈ Icc 0 (retainedRadius b ρ),
      ∀ x ∈ elapsedPhysicalBox z (retainedRadius b ρ),
      ∀ η ∈ angularCone ℓ z.2.2 (retainedRadius b ρ),
        ‖mixedPhaseMatrix (curriedPhase ℓ C (x 0) (x 0 - r))
          (spatialPart x) η - 1‖ ≤ 1 / 2 := by
  obtain ⟨hε, hεb, _⟩ := retainedRadius_bounds hb hρ
  have hsub := closedBall_subset_closedBall (x := (z.1, z)) hεb
  exact fun _ hr _ hx _ hη ↦ norm_mixedPhaseMatrix_phase_sub_one_le ℓ hε
    (hsub.trans hbuffer) hs hdiff (fun q hq ↦ hnear q (hsub hq)) hr hx hη

/-- Every inner-cone covector has a representative in the actual compact
jet set. This proves `hcoverMixed`, which is needed to control the time shear
from the same original phase budget (`fixed-time-representation`). -/
theorem retained_normalized_representative (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : Z} {ε a b r : ℝ} (hε : 0 < ε) (ha : a ≤ 1) (hb : 1 ≤ b)
    (hr : r ∈ Icc 0 ε) {x : E} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ angularCone ℓ z.2.2 (ε / 2)) :
    ∃ t : ℝ, 0 < t ∧ ∃ ζ ∈ angularCone ℓ z.2.2 ε,
      ((x 0, x 0 - r, spatialPart x), ζ) ∈ bufferedJetSet ℓ z ε a b ∧
        η = t • ζ := by
  let ζ := (ℓ η)⁻¹ • η
  have hℓζ : ℓ ζ = 1 := by simp [ζ, hη.1.ne']
  have hζ : ζ ∈ ball z.2.2 ε := ball_subset_ball (by linarith) hη.2
  refine ⟨ℓ η, hη.1, ζ, ?_, ?_, (smul_inv_smul₀ hη.1.ne' η).symm⟩
  · change 0 < ℓ ζ ∧ (ℓ ζ)⁻¹ • ζ ∈ ball z.2.2 ε
    simpa only [hℓζ, inv_one, one_smul] using
      And.intro (zero_lt_one : (0 : ℝ) < 1) hζ
  have ht := elapsedPoint_mem_twoTime_buffer hε hr hx hζ
  have htimes : dist (x 0) z.1 ≤ 2 * ε ∧
      dist (x 0 - r) z.1 ≤ 2 * ε ∧ dist (spatialPart x) z.2.1 ≤ 2 * ε := by
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1⟩
  refine ⟨htimes, (1, ζ), ⟨⟨ha, hb⟩, ball_subset_closedBall hζ, hℓζ⟩, ?_⟩
  exact one_smul ℝ ζ

end JanetCartan.RegularSector.Characteristic.UniformEvolution
