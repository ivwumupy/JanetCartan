module

public import JanetCartan.Iteration.PhysicalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.Expansion
/-!
# Actual physical-history coefficients for ambient response reconstruction

The value, first-derivative and source coefficients in
`app:ch_response:eq:response-reconstruction-grading` are identified with their
literal second-jet formulas. The source coefficient retains `-N_G/2`, and the
value coefficient retains the complete Christoffel contraction. Smoothness
uses the metric and ambient inverse unit loci separately.

The proved physical compact jet range and revised derivative profile of the SAME
real Schwartz history supply the bounds. Constants precede histories, source amplitudes and
frequencies. The derivative shift is two at every order, including closed-ball
boundary derivatives. No reconstruction coefficient estimate is assumed.

Consumer: `PhysicalPairs.exists_completedVariation_physicalWeighted_size_of_restriction`,
and the three coefficient regularity and profile inputs of
`completedVariationComplex_graded_envelopes`, for the displacement and physical
derivative of the same fixed response.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs
open ResponseTransfer GeometricProfile ProjectedStressFrame AmbientResponse
variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "V" => Euclidean N

/-- The actual ambient inverse coefficient on the two original unit loci
(`app:ch_waves:eq:ambient-normal-inverse`). -/
private def reconstructionJetNormal (J : StressJet n N) : MetricTensor n →L[ℝ] V :=
  (Ring.inverse (jetAmbient J)).comp (jetNormalMap J)

/-- Literal value coefficient, retaining its inverse metric and full connection
term (`app:ch_response:eq:response-reconstruction-grading`). -/
private def reconstructionJetValueCoefficient (J : StressJet n N) (j : Fin n) : V :=
  (∑ i, ∑ a, ((firstJetMetric J.1)⁻¹ i a * ((Pi.single j (1 : ℝ) : Fin n → ℝ) a)) •
    J.1 (EuclideanSpace.single i 1)) -
    reconstructionJetNormal J (fun a b ↦ ∑ k, secondJetChristoffel J a b k * (Pi.single j (1 : ℝ) : Fin n → ℝ) k)

/-- Literal symmetric derivative coefficient, including its factor one-half
(`app:ch_response:eq:response-reconstruction-grading`). -/
private def reconstructionJetDerivativeCoefficient (J : StressJet n N)
    (ij : Fin n × Fin n) : V :=
  reconstructionJetNormal J (reconstructionSymmetricDerivativeCoordinates n (Pi.single ij 1))

/-- Literal source coefficient `-N_G/2` (`app:ch_response:eq:response-full-map`). -/
private def reconstructionJetSourceCoefficient (J : StressJet n N)
    (ij : Fin n × Fin n) : V :=
  (- (1 / 2 : ℝ)) • reconstructionJetNormal J (reconstructionTensorCoordinates n (Pi.single ij 1))

/-- Both original inverse gaps give smoothness of the normal coefficient
(`app:ch_waves:eq:ambient-normal-inverse`). -/
private theorem contDiffAt_reconstructionJetNormal {J : StressJet n N}
    (hmetric : IsUnit (jetMetric J)) (hambient : IsUnit (jetAmbient J)) :
    ContDiffAt ℝ ∞ (reconstructionJetNormal (n := n) (N := N)) J := by
  have hi : ContDiffAt ℝ ∞ Ring.inverse (jetAmbient J) := by
    simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ hambient.unit
  exact (hi.comp J (contDiffAt_jetAmbient hmetric)).clm_comp (contDiffAt_jetNormalMap hmetric)

/-- The complete value coefficient is smooth on the same second-jet unit loci
(`app:ch_response:eq:response-reconstruction-grading`). -/
private theorem contDiffAt_reconstructionJetValueCoefficient {J : StressJet n N}
    (hmetric : IsUnit (jetMetric J)) (hambient : IsUnit (jetAmbient J)) (j : Fin n) :
    ContDiffAt ℝ ∞ (fun J : StressJet n N ↦ reconstructionJetValueCoefficient J j) J := by
  have hinj : Function.Injective J.1 := J.1.adjoint_comp_self_injective_iff.mp
    (ContinuousLinearMap.isUnit_iff_bijective.mp hmetric).1
  have hm := firstJetMetric_isUnit_of_injective hinj
  let entry (i a : Fin n) : MetricTensor n →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) a).comp
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i))
  let matrix : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
    { LinearMap.id with cont := continuous_id }
  unfold reconstructionJetValueCoefficient
  apply ContDiffAt.sub
  · exact ContDiffAt.sum fun i _ ↦ ContDiffAt.sum fun a _ ↦
      (((entry i a).contDiff.contDiffAt.comp J
        ((contDiffAt_firstJetMetric_inv hm).comp J contDiffAt_fst)).mul contDiffAt_const).smul
          (contDiffAt_fst.clm_apply contDiffAt_const)
  · apply (contDiffAt_reconstructionJetNormal hmetric hambient).clm_apply
    apply matrix.contDiff.contDiffAt.comp J
    apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    change ContDiffAt ℝ ∞ (fun J : StressJet n N ↦
      ∑ k : Fin n, secondJetChristoffel J a b k * (Pi.single j (1 : ℝ) : Fin n → ℝ) k) J
    exact ContDiffAt.sum fun k _ ↦ (contDiffAt_secondJetChristoffel hm a b k).mul contDiffAt_const

/-- The jet inverse is exactly the canonical normal completion of the original
map (`app:ch_waves:eq:ambient-normal-inverse`). -/
private theorem reconstructionJetNormal_stressJet {F : E → V} (hF : ContDiff ℝ ∞ F)
    {x : E} (hi : Function.Injective (fderiv ℝ F x))
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set V)) :
    reconstructionJetNormal (stressJet F x) =
      (canonicalNormalCompletion F x).toContinuousLinearMap := by
  unfold reconstructionJetNormal
  rw [jetAmbient_stressJet (hF.contDiffAt.of_le (by simp)) hi,
    jetNormalMap_stressJet (hF.contDiffAt.of_le (by simp)) hi]
  ext H : 1
  exact (canonicalNormalCompletion_eq_ambient_inverse hrank H).symm

/-- Identify the actual value entry, with no connection term omitted
(`app:ch_response:eq:response-reconstruction-grading`). -/
private theorem reconstructionValueEntry_eq_jet {F : E → V} (hF : ContDiff ℝ ∞ F)
    {x : E} (hi : Function.Injective (fderiv ℝ F x))
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set V)) (k : Fin N) (j : Fin n) :
    reconstructionValueEntry F k j x =
      (reconstructionJetValueCoefficient (stressJet F x) j k : ℂ) := by
  have hn := reconstructionJetNormal_stressJet hF hi hrank
  simp only [reconstructionValueEntry, reconstructionValueCoefficient,
    LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, LinearMap.comp_apply, reconstructionConnectionCoefficient,
    reconstructionJetValueCoefficient, hn, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [show stressJet F x = secondJet F x from rfl, secondJetChristoffel_eq hF]
  rfl

/-- Identify the actual first-derivative entry in the existing tensor coordinates
(`app:ch_response:eq:response-reconstruction-grading`). -/
private theorem reconstructionDerivativeEntry_eq_jet {F : E → V} (hF : ContDiff ℝ ∞ F)
    {x : E} (hi : Function.Injective (fderiv ℝ F x))
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set V)) (k : Fin N)
    (ij : Fin n × Fin n) :
    reconstructionDerivativeEntry F k ij x =
      (reconstructionJetDerivativeCoefficient (stressJet F x) ij k : ℂ) := by
  rw [reconstructionJetDerivativeCoefficient, reconstructionJetNormal_stressJet hF hi hrank]
  rfl

/-- Identify the actual source entry and its original sign and factor
(`app:ch_response:eq:response-full-map`). -/
private theorem reconstructionSourceEntry_eq_jet {F : E → V} (hF : ContDiff ℝ ∞ F)
    {x : E} (hi : Function.Injective (fderiv ℝ F x))
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set V)) (k : Fin N)
    (ij : Fin n × Fin n) :
    reconstructionSourceEntry F k ij x =
      (reconstructionJetSourceCoefficient (stressJet F x) ij k : ℂ) := by
  rw [reconstructionJetSourceCoefficient, reconstructionJetNormal_stressJet hF hi hrank]
  rfl

/-- Index the three existing coefficient arrays for a common constant
(`app:ch_response:eq:response-reconstruction-grading`). -/
private abbrev ReconstructionEntryIndex (n N : ℕ) :=
  (Fin N × Fin n) ⊕ ((Fin N × (Fin n × Fin n)) ⊕ (Fin N × (Fin n × Fin n)))

/-- The three literal reconstruction entries, with their existing definitions
(`app:ch_response:eq:response-reconstruction-grading`). -/
private def reconstructionEntry (F : E → V) : ReconstructionEntryIndex n N → E → ℂ
  | .inl (k, j) => reconstructionValueEntry F k j
  | .inr (.inl (k, ij)) => reconstructionDerivativeEntry F k ij
  | .inr (.inr (k, ij)) => reconstructionSourceEntry F k ij

/-- Their actual second-jet formulas in the same component order
(`app:ch_response:eq:response-reconstruction-grading`). -/
private def reconstructionJetEntry : ReconstructionEntryIndex n N → StressJet n N → ℂ
  | .inl (k, j) => fun J ↦ (reconstructionJetValueCoefficient J j k : ℂ)
  | .inr (.inl (k, ij)) => fun J ↦ (reconstructionJetDerivativeCoefficient J ij k : ℂ)
  | .inr (.inr (k, ij)) => fun J ↦ (reconstructionJetSourceCoefficient J ij k : ℂ)

/-- Smoothness of every entry follows from the same two inverse gaps
(`app:ch_response:eq:response-reconstruction-grading`). -/
private theorem contDiffAt_reconstructionJetEntry (a : ReconstructionEntryIndex n N)
    {J : StressJet n N} (hg : IsUnit (jetMetric J)) (hA : IsUnit (jetAmbient J)) :
    ContDiffAt ℝ ∞ (reconstructionJetEntry a) J := by
  rcases a with ⟨k, j⟩ | (⟨k, ij⟩ | ⟨k, ij⟩)
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp J
      ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp J
        (contDiffAt_reconstructionJetValueCoefficient hg hA j))
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp J
      ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp J
        ((contDiffAt_reconstructionJetNormal hg hA).clm_apply contDiffAt_const))
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp J
      ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp J
        (((contDiffAt_reconstructionJetNormal hg hA).clm_apply contDiffAt_const).const_smul (- (1 / 2 : ℝ))))

/-- The literal and jet formulas agree in a neighborhood, hence at every
derivative order, including boundary points
(`app:ch_response:eq:response-reconstruction-grading`). -/
private theorem reconstructionEntry_eventuallyEq_jet {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E} (hi : Function.Injective (fderiv ℝ F x))
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set V))
    (a : ReconstructionEntryIndex n N) :
    reconstructionEntry F a =ᶠ[𝓝 x] reconstructionJetEntry a ∘ stressJet F := by
  have hopen := NormalRankStability.isOpen_fullNormalRank_immersionDomain
    isOpen_univ (hF.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffOn
  have hx : x ∈ {y | y ∈ immersionDomain F univ ∧
      Set.range (normalMap F y) = (normalSpace F y : Set V)} := ⟨⟨mem_univ _, hi⟩, hrank⟩
  filter_upwards [hopen.mem_nhds hx] with y hy
  rcases a with ⟨k, j⟩ | (⟨k, ij⟩ | ⟨k, ij⟩)
  · exact reconstructionValueEntry_eq_jet hF hy.1.2 hy.2 k j
  · exact reconstructionDerivativeEntry_eq_jet hF hy.1.2 hy.2 k ij
  · exact reconstructionSourceEntry_eq_jet hF hy.1.2 hy.2 k ij

/-- The existing closed-ball interpolation theorem gives one high map norm
with shift two for all three literal coefficient families. No coefficient
bound is a premise (`app:ch_response:eq:response-reconstruction-grading`). -/
private theorem exists_reconstruction_entry_tame_constants
    (x : E) {r : ℝ} (hr : 0 < r) {L : Set (StressJet n N)} (hL : IsCompact L)
    (hunit : ∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ (F : E → V), ContDiff ℝ ∞ F →
        IsImmersionOn F (closedBall x r) → HasFullNormalRankOn F (closedBall x r) →
        MapsTo (stressJet F) (closedBall x r) L →
      ∀ a : ReconstructionEntryIndex n N,
        (∀ y ∈ closedBall x r, ContDiffAt ℝ ∞ (reconstructionEntry F a) y) ∧
        ∀ m, cNorm (closedBall x r) m (reconstructionEntry F a) ≤
          C m * (1 + cNorm (closedBall x r) (m + 2) F) := by
  have hcomp (a : ReconstructionEntryIndex n N) (m : ℕ) :=
    exists_cNorm_secondJet_comp_le_closedBall x hr hL
      (fun J hJ ↦ (contDiffAt_reconstructionJetEntry a (hunit J hJ).1
        (hunit J hJ).2).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
  choose D hD hb using hcomp
  let C := fun m ↦ ∑ a : ReconstructionEntryIndex n N, D a m
  have hC m : 0 ≤ C m := Finset.sum_nonneg fun a _ ↦ (hD a m).le
  have hDC a m : D a m ≤ C m :=
    Finset.single_le_sum (fun a _ ↦ (hD a m).le) (Finset.mem_univ a)
  refine ⟨C, hC, ?_⟩
  intro F hF hi hrank hFL a
  have he y (hy : y ∈ closedBall x r) :=
    reconstructionEntry_eventuallyEq_jet hF (hi y hy) (hrank y hy) a
  refine ⟨?_, ?_⟩
  · intro y hy
    exact ((contDiffAt_reconstructionJetEntry a (hunit _ (hFL hy)).1
      (hunit _ (hFL hy)).2).comp y (contDiff_stressJet hF).contDiffAt).congr_of_eventuallyEq
        (he y hy)
  · intro m
    rw [cNorm_eq_of_eventuallyEq he m]
    exact (hb a m F hF hFL).trans
      (mul_le_mul_of_nonneg_right (hDC a m) (add_nonneg zero_le_one (cNorm_nonneg ..)))

open CurrentCoefficientProfiles

/-- The SAME admissible history supplies smoothness and all-order profiles
for the original value, derivative and source coefficients of ambient response
reconstruction. Compact jet containment, both inverse gaps and the map profile
are proved by the existing history producers. One common nonnegative profile
precedes the initial scale and every finite history; the fixed shift remains two.
This discharges the coefficient inputs of `completedVariationComplex_graded_envelopes`
without assuming its analytic conclusion
(`main:prop:current-scale`, `app:ch_response:eq:response-reconstruction-grading`). -/
theorem exists_physical_history_reconstruction_entry_profiles
    (G : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {Cband : ℝ} (hCband : 1 ≤ Cband)
    {rStar reserve kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      (∀ k l, (∀ x ∈ closedBall 0 r, ContDiffAt ℝ ∞ (reconstructionValueEntry F k l) x) ∧
        HasDerivativeProfile (closedBall 0 r) (reconstructionValueEntry F k l)
          reserve (currentCoefficientScale R₀ j) C) ∧
      (∀ k ij, (∀ x ∈ closedBall 0 r, ContDiffAt ℝ ∞ (reconstructionDerivativeEntry F k ij) x) ∧
        HasDerivativeProfile (closedBall 0 r) (reconstructionDerivativeEntry F k ij)
          reserve (currentCoefficientScale R₀ j) C) ∧
      (∀ k ij, (∀ x ∈ closedBall 0 r, ContDiffAt ℝ ∞ (reconstructionSourceEntry F k ij) x) ∧
        HasDerivativeProfile (closedBall 0 r) (reconstructionSourceEntry F k ij)
          reserve (currentCoefficientScale R₀ j) C) := by
  obtain ⟨L, hL, hunit, Sj, hSj, hjet⟩ :=
    PhysicalGeometry.exists_history_jet_range G hR hCband hStar horder
  obtain ⟨Sg, _hSg, _C₀, _hC₀, _κ, _hκ, hgeom⟩ :=
    PhysicalGeometry.exists_geometric_neighborhood G hr hrR hR hCband hStar horder
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨A, hA, hprofile⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : E) r) (fun _ _ ↦ G.contDiff.contDiffAt) hCband horder
  obtain ⟨C, hC, hbound⟩ := exists_reconstruction_entry_tame_constants 0 hr hL hunit
  refine ⟨max Sj Sg, hSj.trans (le_max_left _ _), fun m ↦ C m * (1 + A (m + 2)),
    fun m ↦ mul_nonneg (hC m) (add_nonneg zero_le_one (hA _)), ?_⟩
  intro R₀ hR₀ j u ell hu F
  have hRG := (le_max_right Sj Sg).trans hR₀
  have hRJ := (le_max_left Sj Sg).trans hR₀
  obtain ⟨hi, hrank, _⟩ := hgeom R₀ hRG j u ell hu
  have hp := hprofile R₀ (hSj.trans hRJ) j u ell hu _ Subset.rfl
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  have hK : closedBall (0 : E) r ⊆ ball 0 R := closedBall_subset_ball hrR
  have he (a : ReconstructionEntryIndex n (embeddingDimension n)) :=
    hbound F hF (fun x hx ↦ hi x (hK hx)) (fun x hx ↦ hrank x (hK hx))
      (fun x hx ↦ hjet R₀ hRJ j u ell hu (closedBall_subset_closedBall hrR.le hx)) a
  have hscale : 1 ≤ currentCoefficientScale R₀ j :=
    one_le_currentCoefficientScale (by linarith [hSj.trans hRJ]) j
  have hentry (a : ReconstructionEntryIndex n (embeddingDimension n)) :
      (∀ x ∈ closedBall 0 r, ContDiffAt ℝ ∞ (reconstructionEntry F a) x) ∧
      HasDerivativeProfile (closedBall 0 r) (reconstructionEntry F a) reserve
        (currentCoefficientScale R₀ j) (fun m ↦ C m * (1 + A (m + 2))) :=
    ⟨(he a).1,
      hp.transfer hscale hA hC hreserve (he a).2⟩
  exact ⟨fun k l ↦ hentry (.inl (k, l)),
    fun k ij ↦ hentry (.inr (.inl (k, ij))),
    fun k ij ↦ hentry (.inr (.inr (k, ij)))⟩

end JanetCartan.PhysicalPairs
