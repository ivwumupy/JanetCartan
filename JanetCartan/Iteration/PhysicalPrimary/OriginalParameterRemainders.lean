module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalHistoryFamily
public import JanetCartan.Iteration.PhysicalPrimary.OriginalObservationPhase
public import JanetCartan.Iteration.PhysicalPrimary.OriginalOperatorProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhaseProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalWordGradient
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Sobolev.LocalJets
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.InitializedParameterRemainders.MeasuredResidual
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.InitializedParameterRemainders.PairedSolver
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.DirectSmooth.CoefficientProfiles
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.OriginalObservedRemainders
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalParameterRemaindersTemplate

/-!
# The original full inverse's observed parameter remainder

Retain the SAME native measured complex residual, its actual real compression,
complete paired solver, full coefficients and original masks. The initialized
real contraction and gain/adjoint bounds transfer through the existing exact
measured-residual identity, not an equality of independently selected inverses.

The source already has its original chi2 factor. The existing chi3 plateau is
neutral on that forcing; it must not be replaced by an extra chi2 factor or an
output recut. The full observed remainder is consumed by
`complex_inverse_parameter_envelopes_of_actual_finite_words`
(`app:ch_regular:eq:inverse-remainder`, `app:ch_response:eq:response-graded-reduced`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius NNReal ENNReal
namespace JanetCartan.PhysicalPrimary.OriginalParameterRemainders
open LocalSobolev FixedDomainInverse ResponseTransfer.SourceNegative

/-- Preserve the original half-contraction when passing to the SAME complex
residual; no new contraction constant is chosen
(`app:ch_regular:eq:neumann-series`). -/
theorem lt_one_of_half_bound {x : ℝ} (hx : x ≤ (1/2 : ℝ)) : x < 1 := by
  linarith

/-- The native two coefficient classes give their SAME nonnegative monotone
restriction-norm profile, without replacing either coefficient or adding a
profile hypothesis to the actual current
(`app:ch_regular:eq:inverse-remainder`). -/
theorem coefficient_pair_nonneg_monotone {n : ℕ} {W : Set (Euclidean n)}
    (Q : LocalL2 W (Fin n → MetricTensor n)) (B : LocalL2 W (MetricTensor n))
    (hm : ∀ s, MemRestrictionSobolev W s Q ∧ MemRestrictionSobolev W s B) :
    (∀ s, 0 ≤ restrictionSobolevNorm W s Q + restrictionSobolevNorm W s B) ∧
      Monotone (fun s ↦ restrictionSobolevNorm W s Q + restrictionSobolevNorm W s B) := by
  refine ⟨fun _ ↦ add_nonneg restrictionSobolevNorm_nonneg restrictionSobolevNorm_nonneg, ?_⟩
  intro s t hst
  exact add_le_add (restrictionSobolevNorm_mono (hm t).1 hst)
    (restrictionSobolevNorm_mono (hm t).2 hst)

/-- The existing chi3 plateau is neutral on the actual chi2-localized source.
The right hand side is the unaltered forcing, not a chi2-squared forcing and
not an output recut. Equality of these functions retains all source jets
(`app:ch_response:eq:response-graded-source`). -/
theorem auxiliary_cutoff_preserves_forcing {n : ℕ}
    (χ₂ χ₃ : Euclidean n → ℝ)
    (hplateau : ∀ x ∈ tsupport χ₂, χ₃ x = 1)
    (a : Euclidean n → EuclideanSpace ℂ (Fin n))
    (hzero : ∀ x, x ∉ tsupport χ₂ → a x = 0)
    (φ : Euclidean n → ℝ) (ρ : ℝ) :
    modulatedSource χ₃ φ a ρ = fun x ↦ ResponseTransfer.carrier ρ φ x • a x := by
  funext x
  by_cases hx : x ∈ tsupport χ₂
  · simp only [modulatedSource, hplateau x hx, one_smul]
  · simp only [modulatedSource, hzero x hx, smul_zero]

open ResponseTransfer.FullSourceEnvelopes ResponseTransfer.Complement.ParameterDerivatives
open FourierIntegral Pseudodifferential

/-- The stored zeroth list jet is the literal original physical amplitude,
not a new representative (`app:ch_response:eq:response-graded-source`). -/
theorem amplitude_memLp_of_empty_source_jet {n : ℕ}
    (a : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → EuclideanSpace ℂ (Fin n))
    (c : Euclidean 3 × Euclidean (n-1))
    (hm : MemLp (fun x ↦ parameterListJet (fun z ↦ a (x,z)) [] c) 2 volume) :
    MemLp (fun x ↦ a (x,c)) 2 volume := by
  simpa only [parameterListJet, List.length_nil, iteratedFDeriv_zero_apply] using hm

/-- L² membership of the actual unmasked carrier forcing follows from the
existing chi3-neutral identity. The amplitude already contains chi2
(`app:ch_regular:eq:inverse-remainder`). -/
theorem original_source_memberships_of_forcing_eq {n : ℕ} (χ : ContDiffBump (0 : Euclidean n))
    (a : Euclidean n → EuclideanSpace ℂ (Fin n)) (ha : MemLp a 2 volume)
    (φ : Euclidean n → ℝ) (hφ : Continuous φ) (ρ : ℝ)
    (raw : Euclidean n → EuclideanSpace ℂ (Fin n)) (he : modulatedSource χ φ a ρ = raw) :
    MemLp raw 2 volume ∧ MemLp (modulatedSource χ φ a ρ) 2 volume := by
  have hm := modulatedSource_memLp χ.continuous hφ ha (JanetCartan.SmallSupport.bump_norm_le_one χ) ρ
  exact ⟨he ▸ hm,hm⟩

open RegularSector.Characteristic.RetardedLocalization in
/-- An equality of the ACTUAL carrier forcing functions gives equality of
local classes on the same inverse ball. This is not an output localization
or a factorization of an ambient atomic tensor (`app:ch_regular:eq:inverse-remainder`). -/
theorem restrict_original_source_classes_of_eq {d : ℕ} (W : Set (Euclidean (d+1)))
    (f g : Euclidean (d+1) → EuclideanSpace ℂ (Fin (d+1)))
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (he : f = g) :
    restrictL2 W (hf.toLp f) = restrictL2 W (hg.toLp g) :=
  congrArg (fun u ↦ restrictL2 W u) (hf.toLp_congr hg (Filter.EventuallyEq.of_eq he))

/-- Convert the actual full-source profile to the consumer's parameter-list
jets. Smoothness and support control arbitrary direction lists; the numerical
bound uses the original unit directions and only discards a nonnegative reserve.
The native specializer applies this to the literal original51 source, including
its already present chi2 factor (`app:ch_response:eq:response-graded-source`). -/
theorem full_source_parameter_primitives {n : ℕ}
    (χ₂ : ContDiffBump (0 : Euclidean n))
    (a : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → EuclideanSpace ℂ (Fin n))
    (C : ℕ → ℕ → ℝ) (A K : ℝ) (reserve : ℕ)
    (hC : ∀ k j, 0 ≤ C k j) (hA : 0 ≤ A) (hK : 1 ≤ K)
    (ha : LeadingReducedSourceFourierBounds a χ₂ C A K reserve) :
    let f := fun c y ↦ a (y,c)
    ContDiff ℝ ∞ (Function.uncurry f) ∧
      (∀ c, tsupport (f c) ⊆ tsupport (χ₂ : Euclidean n → ℝ)) ∧
      (∀ c (vs : List (Euclidean 3 × Euclidean (n-1))),
        MemLp (fun y ↦ parameterListJet (fun z ↦ f z y) vs c) 2 volume) ∧
      (∀ c (vs : List (Euclidean 3 × Euclidean (n-1))) (j : ℕ)
        (hm : MemLp (fun y ↦ parameterListJet (fun z ↦ f z y) vs c) 2 volume),
        MemVectorFourierSobolev (j : ℝ) (hm.toLp _)) ∧
      (∀ c (vs : List (Euclidean 3 × Euclidean (n-1))), (∀ w ∈ vs, ‖w‖ ≤ 1) →
        ∀ (j : ℕ) (hm : MemLp (fun y ↦ parameterListJet (fun z ↦ f z y) vs c) 2 volume),
        vectorFourierSobolevNorm (j : ℝ) (hm.toLp _) ≤ C vs.length j * (A * K ^ vs.length) * K ^ j) := by
  intro f
  have hd : ContDiff ℝ ∞ (Function.uncurry f) :=
    ha.1.comp (contDiff_snd.prodMk contDiff_fst)
  have hs c : tsupport (f c) ⊆ tsupport (χ₂ : Euclidean n → ℝ) := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro y hy
    by_contra h
    exact hy (ha.2.1 (y,c) h)
  refine ⟨hd, hs, ?_, ?_, ?_⟩
  · intro c vs
    exact fullSource_parameterJet_memLp χ₂.hasCompactSupport isOpen_univ hd.contDiffOn
      (fun z _ ↦ hs z) vs.length vs.get (mem_univ c)
  · intro c vs j hm
    let jet := fun y ↦ parameterListJet (fun z ↦ f z y) vs c
    have hj : ContDiff ℝ ∞ jet :=
      fullSource_parameterJet_contDiff isOpen_univ hd.contDiffOn vs.length vs.get (mem_univ c)
    have hc : HasCompactSupport jet := by
      apply HasCompactSupport.intro χ₂.hasCompactSupport
      intro y hy
      have he : (fun z ↦ f z y) = 0 := by
        funext z
        exact ha.2.1 (y,z) hy
      dsimp only [jet, parameterListJet]
      rw [he]
      simp
    exact graphTest_memVectorFourierSobolev (j : ℝ) ⟨jet,hj,hc⟩
  · intro c vs hvs j hm
    obtain ⟨hf, _, hb⟩ := ha.2.2 c vs.length vs.get
      (fun k ↦ hvs _ (List.get_mem ..)) j
    have hpow : K ^ (j + vs.length - reserve) ≤ K ^ (j + vs.length) :=
      pow_le_pow_right₀ hK (Nat.sub_le _ _)
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (hC _ _) hA)).trans_eq (by rw [pow_add]; ring))

/-- The existing prehistory threshold supplies the scale normalization used
by the source-profile weakening (`app:ch_regular:eq:inverse-remainder`). -/
theorem coefficient_scale_one_le_of_two_le {R₀ : ℝ} (hR₀ : 2 ≤ R₀) (stage : ℕ) :
    1 ≤ currentCoefficientScale R₀ stage :=
  one_le_currentCoefficientScale (by linarith) stage

open ProtectedFlow ResponseTransfer.RetainedFactors

/-- The ordinary paired solver has a separate classical high factor, supplied
by the SAME full coefficient profiles. Only its fixed coefficient shift is
paid by the retained reserve; no estimate on the solver output is assumed
(`app:ch_regular:eq:inverse-remainder`). -/
theorem paired_solver_high_profile {n : ℕ}
    (AQ AB : ℕ → ℝ) (hAQ : ∀ s, 0 ≤ AQ s) (hAB : ∀ s, 0 ≤ AB s)
    (shift reserve : ℕ) (hshift : shift ≤ reserve) :
    (∀ s, 0 ≤ 2 + AQ (s+shift) + AB (s+shift)) ∧
    ∀ (K : Set (Euclidean n)) (Q : Euclidean n → Fin n → MetricTensor n)
      (B : Euclidean n → MetricTensor n) (L : ℝ), 1 ≤ L →
      HasDerivativeProfile K Q reserve L AQ → HasDerivativeProfile K B reserve L AB →
      (∀ s, 0 ≤ 1 + cNorm K (s+shift) Q + cNorm K (s+shift) B) ∧
      ∀ s, 1 + (1 + cNorm K (s+shift) Q + cNorm K (s+shift) B) ≤
        (2 + AQ (s+shift) + AB (s+shift)) * L ^ s := by
  refine ⟨fun s ↦ add_nonneg (add_nonneg (by norm_num) (hAQ _)) (hAB _), ?_⟩
  intro K Q B L hL hpQ hpB
  refine ⟨fun s ↦ add_nonneg (add_nonneg zero_le_one (cNorm_nonneg _ _ _))
    (cNorm_nonneg _ _ _), ?_⟩
  intro s
  have hpow : L ^ (s+shift-reserve) ≤ L ^ s := pow_le_pow_right₀ hL (by omega)
  have hq := (hpQ (s+shift)).trans (mul_le_mul_of_nonneg_left hpow (hAQ _))
  have hb := (hpB (s+shift)).trans (mul_le_mul_of_nonneg_left hpow (hAB _))
  calc
    _ ≤ 2 * L^s + AQ (s+shift) * L^s + AB (s+shift) * L^s := by
      linarith [one_le_pow₀ hL (n := s)]
    _ = _ := by ring

/-- Reassociate the existing two-coefficient bound into the exact `1+a`
interface of the native inverse, without changing its coefficient classes
(`app:ch_regular:eq:inverse-remainder`). -/
theorem inverse_coefficient_profile_reassociate {q b C : ℝ}
    (h : 1 + q + b ≤ C) : 1 + (q+b) ≤ C := by
  simpa only [add_assoc] using h

open ResponseTransfer.SourceNegative

/-- Every derivative of the EXISTING auxiliary bump has a fixed profile before
any history or slow scale; no cutoff is selected
(`app:ch_regular:eq:inverse-remainder`). -/
theorem exists_auxiliary_cutoff_profiles {n : ℕ} (χ : ContDiffBump (0 : Euclidean n)) :
    ∃ X : ℕ → ℝ, (∀ j, 0 ≤ X j) ∧ ∀ L : ℝ, 1 ≤ L → ∀ x j,
      ‖iteratedFDeriv ℝ j (χ : Euclidean n → ℝ) x‖ ≤ X j * L ^ j := by
  choose X hX hb using fun j ↦ χ.hasCompactSupport.exists_bound_iteratedFDeriv χ.contDiff j
  refine ⟨X,hX,?_⟩
  intro L hL x j
  exact (hb j j le_rfl x).trans (le_mul_of_one_le_right (hX j) (one_le_pow₀ hL))

/-- The original whole-word gradient band and the reserved joint phase jets
supply source geometry on the COMPLETE auxiliary bump support. The phase and
bump are literal supplied objects; the actual original specializer closes
every geometric input (`app:ch_regular:eq:inverse-remainder`). -/
theorem source_geometry_of_joint_profiles {n : ℕ}
    (χ : ContDiffBump (0 : Euclidean n))
    (φ : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → ℝ)
    (hφ : ContDiff ℝ ∞ φ)
    (V : Set (Euclidean 3 × Euclidean (n-1))) (r R lo hi L : ℝ)
    (A X : ℕ → ℝ) (hmin : 0 < min r R)
    (hχ : tsupport (χ : Euclidean n → ℝ) ⊆ ball 0 (min r R))
    (hlo : 0 < lo) (hhi : lo < hi) (hL : 1 ≤ L)
    (hA : ∀ j, 0 ≤ A j) (hX : ∀ j, 0 ≤ X j)
    (hcut : ∀ x j, ‖iteratedFDeriv ℝ j (χ : Euclidean n → ℝ) x‖ ≤ X j * L ^ j)
    (hgrad : ∀ c ∈ V, ∀ x ∈ ball (0 : Euclidean n) (3*R),
      lo ≤ ‖fderiv ℝ (fun y ↦ φ (y,c)) x‖ ∧
      ‖fderiv ℝ (fun y ↦ φ (y,c)) x‖ ≤ hi)
    (hjets : ∀ k q, q ∈ closedBall (0 : Euclidean n) (3*R) ×ˢ closure V →
      ‖iteratedFDeriv ℝ k φ q‖ ≤ A k * L ^ (k-2)) :
    ∀ c ∈ V, SourceGeometry (χ : Euclidean n → ℝ) (fun x ↦ φ (x,c))
      (tsupport (χ : Euclidean n → ℝ)) lo hi L (fun j ↦ A (j+1)) X := by
  have hR : 0 < R := lt_of_lt_of_le hmin (min_le_right r R)
  have hbox : tsupport (χ : Euclidean n → ℝ) ⊆ ball 0 (3*R) :=
    hχ.trans (ball_subset_ball (by linarith [min_le_right r R]))
  intro c hc
  refine {
    cutoff_smooth := χ.contDiff
    phase_smooth := hφ.comp (contDiff_id.prodMk contDiff_const)
    compact := χ.hasCompactSupport
    support_subset := Subset.rfl
    lower_pos := hlo
    lower_lt_upper := hhi
    scale_one_le := hL
    phase_constants_nonneg := fun j ↦ hA (j+1)
    cutoff_constants_nonneg := hX
    gradient_lower := fun x hx ↦ (hgrad c hc x (hbox hx)).1
    gradient_upper := fun x hx ↦ (hgrad c hc x (hbox hx)).2
    cutoff_derivatives := hcut
    phase_derivatives := ?_ }
  intro x hx j _
  have hb := (ResponsePrimarySources.norm_iteratedFDeriv_primary_spatialSlice_le
    isOpen_univ isOpen_univ hφ.contDiffOn (mem_univ x) (mem_univ c) (j+1)).trans
    (hjets (j+1) (x,c) ⟨ball_subset_closedBall (hbox hx),subset_closure hc⟩)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (by omega)) (hA (j+1)))


/-- Paying the native inverse reserve once fixes the existing current and
coefficient orders before all response-jet orders and histories
(`app:ch_regular:eq:inverse-remainder`). -/
theorem native_orders_of_inverse_reserve {d rHistory : ℕ}
    (h : RegularSector.FiniteEvolution.sectorLowOrder d + (d+2) + 2 ≤ rHistory) :
    8 ≤ rHistory ∧ RegularSector.FiniteEvolution.sectorLowOrder d + 2 ≤ rHistory ∧
      2 + (RegularSector.FiniteEvolution.sectorLowOrder d + (d+2)) ≤ rHistory := by
  have hlow := (RegularSector.FiniteEvolution.sectorLowOrder_bounds d).2.2
  omega

open OriginalHistoryFamily in
/-- Pure data transport for the observed full-inverse remainder. Its actual
uniform depth and cost may be chosen from a nonempty family before every
queried history. The impossible branch uses zero only when there is NO
admitted datum (`app:ch_regular:eq:inverse-remainder`). -/
theorem uniform_depth_cost_of_admitted_retraction {d : ℕ} {Payload : Type}
    (Bband : ℝ) (kMin : ℕ) (ν S : ℝ) (sourceData : RawIndex d Payload → Prop)
    (P : ℕ → ℝ → {i : RawIndex d Payload // Admitted Bband kMin ν S i ∧ sourceData i} → Prop)
    (h : ∀ hne : Nonempty {i : RawIndex d Payload // Admitted Bband kMin ν S i ∧ sourceData i},
      ∃ (N : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ i,
        P N D (admittedRetraction Bband kMin ν S sourceData hne i)) :
    ∃ (N : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ i (hi : Admitted Bband kMin ν S i ∧ sourceData i),
      P N D ⟨i,hi⟩ := by
  classical
  by_cases hne : Nonempty {i : RawIndex d Payload // Admitted Bband kMin ν S i ∧ sourceData i}
  · obtain ⟨N,D,hD,hp⟩ := h hne
    refine ⟨N,D,hD,fun i hi ↦ ?_⟩
    simpa only [admittedRetraction_of_admitted Bband kMin ν S sourceData hne i hi] using hp i
  · exact ⟨0,0,le_rfl,fun i hi ↦ (hne ⟨⟨i,hi⟩⟩).elim⟩

end JanetCartan.PhysicalPrimary.OriginalParameterRemainders

retain_original_normalized_remainder_primitives
retain_original_inverse_coefficient_profiles
construct_original_auxiliary_source_geometry
retain_original_parameter_source_identity
retain_original_parameter_source_masks
retain_original_parameter_source_scale
retain_original_parameter_source_budget
retain_original_parameter_source_bundle
retain_original_parameter_source_fields
retain_original_parameter_source_primitives
retain_original_source_family_window
retain_original_source_family_admission
retain_original_source_domain
retain_original_source_amplitude_memLp
retain_original_source_memberships
retain_original_source_realization
prepare_original_remainder_family
retain_original_family_static_inputs
apply_original_observed_remainder_to_nonempty_family
transport_original_remainder_to_all_admitted_data
