module

public import JanetCartan.Iteration.PhysicalMean.MomentProfiles

/-!
# A single finite moment template list for the whole sampled row

The expansion in `app:ch_mean_pairs:eq:raw-adjoint-moments` must use one
finite family BEFORE the sampled parameter, frequency and history vary.
A pointwise existential expression is not enough to assemble measurable
amplitude operators. The templates below retain both the coefficient
expression and the source derivative word, and exactly compile to the
original integration-by-parts expansion. They introduce no choices depending
on the sampled parameters and no derivatives with respect to those parameters.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.PhysicalMean

open ContinuumAdjoint.DerivativeKernels ContinuumRow

variable {n : ℕ}

/-- The fixed coefficient expression and fixed source derivative word of one
term of `app:ch_mean_pairs:eq:raw-adjoint-moments`. -/
abbrev AdjointMomentTemplate (n : ℕ) := AdjointCoefficientExpression n × List (Fin n)

/-- The actual symbolic IBP family, chosen before any functions, frequency,
sample, inverse or history (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
def adjointMomentTemplates : List (InitialCarrierDerivative n) → List (AdjointMomentTemplate n)
  | [] => [(.amplitude, [])]
  | d :: ds => (adjointMomentTemplates ds).flatMap (fun t ↦
      (t.1.zeroBranch d, t.2) :: List.ofFn (fun j : Fin n ↦ (t.1.firstBranch d j, j :: t.2)))

/-- Evaluation uses the original coefficients, without selecting a new
expression or a new derivative word at each input frequency. -/
def AdjointMomentTemplate.toTerm (t : AdjointMomentTemplate n)
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (a : AdjointAmplitude n) : AdjointDerivativeTerm n :=
  ⟨fun z x η ↦ t.1.evaluate L V a η (z, x), t.2⟩

/-- Every template spends at most the total derivative-word budget. The
coefficient degree and the source derivative count are controlled together
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem adjointMomentTemplate_grade (ds : List (InitialCarrierDerivative n))
    (t : AdjointMomentTemplate n) (ht : t ∈ adjointMomentTemplates ds) :
    t.1.degree + t.2.length ≤ ds.length ∧ t.1.UsesDirections ds := by
  induction ds generalizing t with
  | nil =>
      simp only [adjointMomentTemplates, List.mem_singleton] at ht
      subst t
      exact ⟨by simp [AdjointCoefficientExpression.degree], trivial⟩
  | cons d ds ih =>
      obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨hg, hd⟩ := ih u hu
      simp only [List.mem_cons, List.mem_ofFn] at ht
      rcases ht with rfl | ⟨j, rfl⟩
      · refine ⟨?_, (u.1.usesDirections_branches ds d hd).1⟩
        have := u.1.degree_zeroBranch_le d
        simp only [List.length_cons]
        omega
      · refine ⟨?_, (u.1.usesDirections_branches ds d hd).2 j⟩
        simpa only [AdjointCoefficientExpression.degree_firstBranch, List.length_cons,
          ← Nat.add_assoc, Nat.add_le_add_iff_right] using hg

/-- Evaluating the fixed finite templates produces EXACTLY the actual IBP
list, in the same order and with the same source derivative words. This is
an equality of constructions, not an assumed expansion
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem map_adjointMomentTemplates_eq_expansion (L V) (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) :
    (adjointMomentTemplates ds).map (fun t ↦ t.toTerm L V a) =
      adjointDerivativeExpansion L V ds a := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp only [adjointMomentTemplates, List.map_flatMap, adjointDerivativeExpansion, ← ih,
        List.flatMap_map]
      apply congrArg (List.flatMap · (adjointMomentTemplates ds))
      funext t
      simp only [Function.comp_def, List.map_cons, List.map_ofFn, differentiateAdjointTerm]
      congr 1
      · change AdjointDerivativeTerm.mk _ t.2 = AdjointDerivativeTerm.mk _ t.2
        congr 1
        funext z x η
        exact t.1.evaluate_zeroBranch L V a η (ha η) hfield d (z, x)
      · congr 1
        funext j
        change AdjointDerivativeTerm.mk _ (j :: t.2) = AdjointDerivativeTerm.mk _ (j :: t.2)
        congr 1
        funext z x η
        exact t.1.evaluate_firstBranch L V a η d j (z, x)

/-- The fixed templates have the same compact measurement support as the
original amplitude, simultaneously for all choices of actual coefficients
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem sampledAdjointMomentTemplate_regular
    {K : Set (Euclidean n)} (hK : IsClosed K) {a : Euclidean n → ℂ}
    (ha : ContDiff ℝ ∞ a) (has : tsupport a ⊆ K)
    {L : Euclidean (n - 1) → Euclidean n → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (L h)) (ds : List (Euclidean (n - 1)))
    (t : AdjointMomentTemplate n)
    (ht : t ∈ adjointMomentTemplates (ds.map InitialCarrierDerivative.initial)) :
    SmoothSupportedAdjointAmplitude K
      (t.toTerm (fun _ x h ↦ L h x) (fun _ _ _ ↦ 0) (fun _ x _ ↦ a x)).amplitude := by
  have hfield : ∀ d j, ContDiff ℝ ∞
      (branchField (fun _ x h ↦ L h x) (fun _ _ _ ↦ 0) d j) := by
    intro d j
    cases d with
    | initial h =>
        change ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ (L h p.2 j : ℂ))
        exact Complex.ofRealCLM.contDiff.comp
          (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp (hL h)).comp contDiff_snd)
    | carrier h => exact contDiff_const
  have hmap := map_adjointMomentTemplates_eq_expansion
    (fun _ x h ↦ L h x) (fun _ _ _ ↦ 0) (fun _ x _ ↦ a x)
    (fun _ ↦ ha.comp contDiff_snd) hfield (ds.map InitialCarrierDerivative.initial)
  apply (sampledAdjointMomentExpansion_regular hK ha has hL ds _ ?_).2
  unfold sampledAdjointMomentExpansion
  rw [← hmap]
  exact List.mem_map.mpr ⟨t, ht, rfl⟩

/-- Frequency dependence of the primitive inverse directions causes no
selection problem: a FIXED coefficient expression remains jointly smooth.
Only physical derivatives are taken when evaluating its syntax; derivatives
of the spectator parameter are not used in the quantitative bound
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem contDiff_adjointMomentExpression_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (L : P → CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : P → CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (a : P → AdjointJetPoint n → ℂ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hfield : ∀ d j, ContDiff ℝ ∞ (fun q : P × AdjointJetPoint n ↦
      branchField (L q.1) (V q.1) d j q.2)) (e : AdjointCoefficientExpression n) :
    ContDiff ℝ ∞ (fun q : P × AdjointJetPoint n ↦
      e.evaluate (L q.1) (V q.1) (fun z x _ ↦ a q.1 (z, x)) 0 q.2) := by
  induction e with
  | amplitude => exact ha
  | field d j => exact hfield d j
  | add e f he hf => exact he.add hf
  | neg e he => exact he.neg
  | mul e f he hf => exact he.mul hf
  | deriv h e he =>
      exact (he.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv_apply
        contDiff_snd contDiff_const (by simp)

end JanetCartan.PhysicalMean
