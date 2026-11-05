module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.JetFormula

/-!
# The fixed compact range of actual strain jets

For `app:ch_waves:eq:WKB-strain`, intersect the existing primitive metric and
normal gap range with the retained projected-frame Gram gap. This gives
uniform bounds for the actual inverse Gram and all its differentiated
reconstruction coefficients on the same reference neighborhood.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Matrix
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.RawPrimary.AmbientStrain
open ProjectedStressFrame GeometricProfile NullTransport.CoefficientBounds

/-- The primitive positive Gram energy makes the actual Frobenius Gram
invertible (`app:ch_waves:eq:WKB-residual`). -/
theorem stressGram_isUnit_of_energy {n : ℕ} (Q : Fin n → MetricTensor n)
    {γ : ℝ} (hγ : 0 < γ)
    (henergy : ∀ c : Euclidean n, γ * (∑ i, (c i)^2) ≤
      ∑ i, ∑ j, c i * c j * WKB.stressGram Q i j) :
    IsUnit (WKB.stressGram Q) := by
  apply Matrix.PosDef.isUnit
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_gram ℝ Q
  · intro c hc
    have hpos : 0 < ∑ i, (c i)^2 := by
      apply lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ sq_nonneg (c i))
      intro hz
      apply hc
      funext i
      have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg (c j))
        (Finset.mem_univ i)
      change c i = 0
      nlinarith
    have he := lt_of_lt_of_le (mul_pos hγ hpos) (henergy (WithLp.toLp 2 c))
    simpa only [PiLp.toLp_apply, dotProduct, Matrix.mulVec, Pi.star_apply,
      star_trivial, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using he

/-- The second-jet range uses the SAME Gram gap selected by the projected
basis producer (`app:ch_waves:eq:WKB-strain`). -/
def admissibleStrainJets (n N : ℕ) (M κ R γ : ℝ) : Set (StressJet n N) :=
  {J ∈ admissibleStressJets n N M κ R | ∀ c : Euclidean n,
    γ * (∑ i, (c i)^2) ≤ ∑ i, ∑ j, c i * c j * WKB.stressGram (jetFrame J) i j}

/-- The energy inequalities are closed on the existing compact geometric
range, so differentiated inversion needs no extra analytic premise
(`app:ch_waves:eq:WKB-strain`). -/
theorem isCompact_admissibleStrainJets {n N : ℕ} (M R γ : ℝ)
    {κ : ℝ} (hκ : 0 < κ) : IsCompact (admissibleStrainJets n N M κ R γ) := by
  let s := admissibleStressJets n N M κ R
  have hs : IsCompact s := isCompact_admissibleStressJets M hκ R
  have hQ : ContinuousOn (@jetFrame n N) s := by
    intro J hJ
    exact (contDiffAt_jetFrame (isUnit_jetMetric_of_lower_bound hκ hJ.2.1)
      (isUnit_jetAmbient_of_lower_bound hJ.2.2)).continuousAt.continuousWithinAt
  have hG : ContinuousOn (fun J : StressJet n N ↦ WKB.stressGram (jetFrame J)) s :=
    contDiff_stressGram.continuous.comp_continuousOn hQ
  have he (c : Euclidean n) : IsClosed {J ∈ s |
      γ * (∑ i, (c i)^2) ≤ ∑ i, ∑ j, c i * c j * WKB.stressGram (jetFrame J) i j} := by
    apply hs.isClosed.isClosed_le continuousOn_const
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact continuousOn_const.mul
      ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.continuous.comp_continuousOn hG)
  have hc : IsClosed (admissibleStrainJets n N M κ R γ) := by
    convert isClosed_iInter he using 1
    ext J
    simp only [admissibleStrainJets, mem_ofPred_eq, mem_iInter]
    exact ⟨fun h c ↦ ⟨h.1, h.2 c⟩, fun h ↦ ⟨(h 0).1, fun c ↦ (h c).2⟩⟩
  exact hs.of_isClosed_subset hc (fun _ h ↦ h.1)

/-- The common reference data place the actual immersion jet in that exact
compact range. No second frame witness is selected
(`app:ch_waves:eq:WKB-strain`). -/
theorem stressJet_mem_admissibleStrainJets {n : ℕ} (hn : 5 ≤ n)
    {F : Euclidean n → Euclidean (embeddingDimension n)}
    {U K : Set (Euclidean n)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    {M κmet κnormal : ℝ} (hκnormal : 0 < κnormal) (hlow : cNorm K 4 F ≤ M)
    (hmet : ∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2)
    (hnormal : ∀ x ∈ K, ∀ v ∈ normalSpace F x,
      κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖)
    (hclose : ∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
      ambientStrainFrameThreshold hn)
    {x : Euclidean n} (hx : x ∈ K) :
    stressJet F x ∈ admissibleStrainJets n (embeddingDimension n) (2 * M) κmet
      (max 1 (κnormal^2)⁻¹) (ambientStrainFrameGramGap hn) := by
  refine ⟨stressJet_mem_admissibleStressJets hK
    (fun y hy ↦ hF.contDiffAt (hU.mem_nhds (hKU hy))) hκnormal hlow hx
      (hi x (hKU hx)) (hmet x hx) (hnormal x hx), ?_⟩
  have he : jetFrame (stressJet F x) = projectedStress F x :=
    funext fun i ↦ jetStress_stressJet
      ((hF.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp)) (hi x (hKU hx)) i
  rw [he]
  exact projectedStress_gram_energy_of_cNorm_closeness hn hU hK hKU hF hi hrank hclose hx

end JanetCartan.RawPrimary.AmbientStrain
