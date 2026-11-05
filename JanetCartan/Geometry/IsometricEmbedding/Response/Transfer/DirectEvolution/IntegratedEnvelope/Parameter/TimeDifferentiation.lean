module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSobolev.KernelJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Terms

/-!
# Finite parameter differentiation of an elapsed-time integral

The consumer is the joint version of `app:ch_response:eq:direct-envelope-profile`.
Measurable original orbits and fixed-time parameter smoothness imply measurability
of every actual derivative, by difference quotients. Local uniform bounds on
ordered words through order `N` imply bounds on the required total derivatives
by a finite basis argument. Dominated differentiation then commutes the SAME
ordered action with the actual Bochner integral, without using order `N + 1`.

These are integration deductions, not the primitive annular endpoints. The
annular construction must supply fixed-time smoothness from its original compact
kernel and local bounds from `AnnularSobolev.JointAssembly` (or its literal-adjoint
counterpart) and the actual original-datum jets. Neither time smoothness of a
critical map nor an integrated estimate is a premise.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
open Pseudodifferential
variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set P} {Δ : ℝ} {f : ℝ → P → F}

/-- Fixed-time parameter smoothness survives each actual ordered derivative.
Consumer: measurable derivatives in `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_orderedParameterWord {g : P → F}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (ps : List P) :
    ContDiffOn ℝ ∞ (orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps g) U := by
  induction ps with
  | nil => exact hg
  | cons v ps ih =>
    intro a ha
    exact (((ih.contDiffAt (hU.mem_nhds ha)).fderiv_right (by simp)).clm_apply
      contDiffAt_const).contDiffWithinAt

private theorem orderedParameterWord_ofFn_eq_iteratedFDeriv {k : ℕ}
    {g : P → F} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (v : Fin k → P) {c : P} (hc : c ∈ U) :
    orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) (List.ofFn v) g c =
      iteratedFDeriv ℝ k g c v := by
  induction k generalizing c with
  | zero => simp [orderedTransferAction, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (orderedTransferAction (fun v F a ↦ fderiv ℝ F a v)
      (List.ofFn (fun i ↦ v i.succ)) g) c (v 0) = _
    have he : orderedTransferAction (fun v F a ↦ fderiv ℝ F a v)
        (List.ofFn (fun i ↦ v i.succ)) g =ᶠ[𝓝 c]
        (fun a ↦ iteratedFDeriv ℝ k g a (fun i ↦ v i.succ)) := by
      filter_upwards [hU.mem_nhds hc] with a ha
      exact ih _ ha
    rw [he.fderiv_eq, DifferentiableAt.iteratedFDeriv_succ_apply_left']
    · rfl
    · exact ((hg.contDiffAt (hU.mem_nhds hc)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top k : (k : ℕ∞ω) < ∞))

variable [FiniteDimensional ℝ P]

/-- The actual Fréchet jets are measurable in elapsed time on the SAME interval.
Only the original orbit measurability and fixed-time parameter smoothness are
used; no chosen critical map needs time regularity (`new:eq:carrier-ibp`). -/
theorem aestronglyMeasurable_elapsed_jet
    (hU : IsOpen U)
    (hm : ∀ c ∈ U, AEStronglyMeasurable (fun t ↦ f t c) (volume.restrict (Icc 0 Δ)))
    (hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (f t) U)
    (j : ℕ) {c : P} (hc : c ∈ U) :
    AEStronglyMeasurable (fun t ↦ iteratedFDeriv ℝ j (f t) c)
      (volume.restrict (Icc 0 Δ)) := by
  classical
  let g : ℝ → P → F := fun t ↦ if t ∈ Icc 0 Δ then f t else 0
  have hg (t : ℝ) : ContDiffOn ℝ ∞ (g t) U := by
    dsimp [g]
    split_ifs with ht
    · exact hf t ht
    · exact contDiffOn_const
  have hgm (a : P) (ha : a ∈ U) : AEStronglyMeasurable (fun t ↦ g t a)
      (volume.restrict (Icc 0 Δ)) := (hm a ha).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [g, ite_eq_left ht])
  apply (AnnularComplement.aestronglyMeasurable_annularKernel_jet hU hgm hg j hc).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [g, ite_eq_left ht]

/-- Every actual ordered parameter derivative is measurable in elapsed time.
Consumer: joint integration in `app:ch_response:eq:direct-envelope-profile`. -/
theorem aestronglyMeasurable_elapsed_word
    (hU : IsOpen U)
    (hm : ∀ c ∈ U, AEStronglyMeasurable (fun t ↦ f t c) (volume.restrict (Icc 0 Δ)))
    (hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (f t) U)
    (ps : List P) {c : P} (hc : c ∈ U) :
    AEStronglyMeasurable
      (fun t ↦ orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t) c)
      (volume.restrict (Icc 0 Δ)) := by
  have hmj := aestronglyMeasurable_elapsed_jet hU hm hf ps.length hc
  have hme := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin ps.length ↦ P) F ps.get).continuous.comp_aestronglyMeasurable hmj
  apply hme.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change iteratedFDeriv ℝ ps.length (f t) c ps.get = _
  symm
  simpa only [List.ofFn_get] using
    orderedParameterWord_ofFn_eq_iteratedFDeriv hU (hf t ht) ps.get hc

/-- The total derivative of an actual ordered word is measurable in time.
Consumer: the Bochner derivative passage in `new:eq:carrier-ibp`. -/
theorem aestronglyMeasurable_elapsed_word_fderiv
    (hU : IsOpen U)
    (hm : ∀ c ∈ U, AEStronglyMeasurable (fun t ↦ f t c) (volume.restrict (Icc 0 Δ)))
    (hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (f t) U)
    (ps : List P) {c : P} (hc : c ∈ U) :
    AEStronglyMeasurable
      (fun t ↦ fderiv ℝ (orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t)) c)
      (volume.restrict (Icc 0 Δ)) := by
  have hmj := aestronglyMeasurable_elapsed_jet hU
    (fun a ha ↦ aestronglyMeasurable_elapsed_word hU hm hf ps ha)
    (fun t ht ↦ contDiffOn_orderedParameterWord hU (hf t ht) ps) 1 hc
  apply ((continuousMultilinearCurryFin1 ℝ P F).continuous.comp_aestronglyMeasurable hmj).congr
  apply ae_of_all
  intro t
  ext v
  exact iteratedFDeriv_one_apply _

/-- One genuine Fréchet derivative passes through elapsed-time integration.
Derivative measurability is derived. The local bound is supplied by the primitive
fixed-time endpoint and original-datum smoothness (`new:eq:carrier-ibp`). -/
theorem hasFDerivAt_elapsedWordIntegral
    (hU : IsOpen U)
    (hm : ∀ c ∈ U, AEStronglyMeasurable (fun t ↦ f t c) (volume.restrict (Icc 0 Δ)))
    (hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (f t) U)
    (ps : List P) {c : P} (hc : c ∈ U)
    (hi : IntegrableOn
      (fun t ↦ orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t) c) (Icc 0 Δ))
    {V : Set P} (hV : V ∈ 𝓝 c) (hVU : V ⊆ U) (B : ℝ)
    (hb : ∀ t ∈ Icc 0 Δ, ∀ a ∈ V,
      ‖fderiv ℝ (orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t)) a‖ ≤ B) :
    HasFDerivAt
      (fun a ↦ ∫ t in Icc 0 Δ,
        orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t) a)
      (∫ t in Icc 0 Δ,
        fderiv ℝ (orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t)) c) c := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := V) (bound := fun _ ↦ B) hV
  · filter_upwards [hU.mem_nhds hc] with a ha
    exact aestronglyMeasurable_elapsed_word hU hm hf ps ha
  · exact hi
  · exact aestronglyMeasurable_elapsed_word_fderiv hU hm hf ps hc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hb t ht
  · exact integrable_const B
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro a ha
    exact (((contDiffOn_orderedParameterWord hU (hf t ht) ps).contDiffAt
      (hU.mem_nhds (hVU ha))).differentiableAt (by simp)).hasFDerivAt

/-- A uniform fixed-time bound makes the actual ordered derivative Bochner
integrable. Consumer: `app:ch_response:eq:direct-envelope-profile`. -/
theorem integrableOn_elapsed_word_of_bound
    (hU : IsOpen U)
    (hm : ∀ c ∈ U, AEStronglyMeasurable (fun t ↦ f t c) (volume.restrict (Icc 0 Δ)))
    (hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (f t) U)
    (ps : List P) {c : P} (hc : c ∈ U) (B : ℝ)
    (hb : ∀ t ∈ Icc 0 Δ,
      ‖orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t) c‖ ≤ B) :
    IntegrableOn
      (fun t ↦ orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t) c) (Icc 0 Δ) := by
  refine (integrable_const B).mono' (aestronglyMeasurable_elapsed_word hU hm hf ps hc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hb t ht

/-- Finite ordered differentiation of the actual integral, with every
interchange proved by dominated differentiation (`new:eq:carrier-ibp`). -/
private theorem orderedTransferAction_elapsedIntegral_of_local_bounds
    (hU : IsOpen U)
    (hm : ∀ c ∈ U, AEStronglyMeasurable (fun t ↦ f t c) (volume.restrict (Icc 0 Δ)))
    (hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (f t) U)
    (N : ℕ)
    (hb : ∀ qs : List P, qs.length ≤ N → ∀ c ∈ U, ∃ B : ℝ,
      ∀ t ∈ Icc 0 Δ,
        ‖orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) qs (f t) c‖ ≤ B)
    (hdb : ∀ qs : List P, qs.length < N → ∀ c ∈ U,
      ∃ V ∈ 𝓝 c, V ⊆ U ∧ ∃ B : ℝ, ∀ t ∈ Icc 0 Δ, ∀ a ∈ V,
        ‖fderiv ℝ (orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) qs (f t)) a‖ ≤ B)
    (ps : List P) (hps : ps.length ≤ N) {c : P} (hc : c ∈ U) :
    IntegrableOn
      (fun t ↦ orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t) c) (Icc 0 Δ) ∧
    orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps
      (fun a ↦ ∫ t in Icc 0 Δ, f t a) c =
        ∫ t in Icc 0 Δ, orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t) c := by
  have hi (qs : List P) (hqs : qs.length ≤ N) (a : P) (ha : a ∈ U) :
      IntegrableOn
        (fun t ↦ orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) qs (f t) a) (Icc 0 Δ) := by
    obtain ⟨B, hB⟩ := hb qs hqs a ha
    exact integrableOn_elapsed_word_of_bound hU hm hf qs ha B hB
  refine ⟨hi ps hps c hc, ?_⟩
  induction ps generalizing c with
  | nil => rfl
  | cons v ps ih =>
    have hlt : ps.length < N := lt_of_lt_of_le (Nat.lt_succ_self _) hps
    have he : orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps
        (fun a ↦ ∫ t in Icc 0 Δ, f t a) =ᶠ[𝓝 c]
        (fun a ↦ ∫ t in Icc 0 Δ,
          orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t) a) := by
      filter_upwards [hU.mem_nhds hc] with a ha
      exact ih hlt.le ha
    obtain ⟨V, hV, hVU, B, hB⟩ := hdb ps hlt c hc
    have hd := hasFDerivAt_elapsedWordIntegral hU hm hf ps hc (hi ps hlt.le c hc)
      hV hVU B hB
    have hid : IntegrableOn
        (fun t ↦ fderiv ℝ (orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t)) c)
        (Icc 0 Δ) := by
      refine (integrable_const B).mono'
        (aestronglyMeasurable_elapsed_word_fderiv hU hm hf ps hc) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hB t ht c (mem_of_mem_nhds hV)
    change fderiv ℝ _ c v = _
    rw [he.fderiv_eq, hd.fderiv, ContinuousLinearMap.integral_apply hid]
    rfl

/-- Local bounds on words through order `N` dominate the total derivative of
each shorter word, using finitely many parameter directions. This consumes no
additional jet order in `app:ch_response:lem:energy-carrier-jets`. -/
theorem local_fderiv_bound_of_local_word_bounds
    (N : ℕ)
    (hb : ∀ qs : List P, qs.length ≤ N → ∀ c ∈ U,
      ∃ V ∈ 𝓝 c, V ⊆ U ∧ ∃ B : ℝ, ∀ t ∈ Icc 0 Δ, ∀ a ∈ V,
        ‖orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) qs (f t) a‖ ≤ B)
    (ps : List P) (hps : ps.length < N) {c : P} (hc : c ∈ U) :
    ∃ V ∈ 𝓝 c, V ⊆ U ∧ ∃ B : ℝ, ∀ t ∈ Icc 0 Δ, ∀ a ∈ V,
      ‖fderiv ℝ (orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t)) a‖ ≤ B := by
  classical
  let b := Module.finBasis ℝ P
  let coord := fun i ↦ (b.coord i).toContinuousLinearMap
  obtain ⟨V₀, hV₀, hV₀U, _⟩ := hb [] (Nat.zero_le N) c hc
  choose V hV hVU B hB using fun i ↦ hb (b i :: ps) hps c hc
  refine ⟨V₀ ∩ ⋂ i, V i, inter_mem hV₀
    (Filter.iInter_mem.mpr hV), inter_subset_left.trans hV₀U, ∑ i, ‖coord i‖ * B i, ?_⟩
  intro t ht a ha
  let T := fderiv ℝ (orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t)) a
  have he : T = ∑ i, (coord i).smulRight (T (b i)) := by
    ext v
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
    change T v = ∑ i, b.repr v i • T (b i)
    calc
      _ = T (∑ i, b.repr v i • b i) := congrArg T (b.sum_repr v).symm
      _ = _ := by rw [map_sum]; congr 1; ext i; exact map_smul _ _ _
  change ‖T‖ ≤ _
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_mul_of_nonneg_left (hB i t ht a (mem_iInter.mp ha.2 i)) (norm_nonneg _)

/-- Actual ordered parameter differentiation commutes with the elapsed-time
Bochner integral. Its derivative is also Bochner integrable. The only quantitative
input is local uniform bounds on the original fixed-time words through the
requested order. For the annular envelope their producer is the primitive joint
endpoint with locally bounded original-datum jets. This implication alone does
not instantiate that producer (`app:ch_response:eq:direct-envelope-profile`). -/
theorem orderedTransferAction_elapsedIntegral
    (hU : IsOpen U)
    (hm : ∀ c ∈ U, AEStronglyMeasurable (fun t ↦ f t c) (volume.restrict (Icc 0 Δ)))
    (hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (f t) U)
    (N : ℕ)
    (hb : ∀ qs : List P, qs.length ≤ N → ∀ c ∈ U,
      ∃ V ∈ 𝓝 c, V ⊆ U ∧ ∃ B : ℝ, ∀ t ∈ Icc 0 Δ, ∀ a ∈ V,
        ‖orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) qs (f t) a‖ ≤ B)
    (ps : List P) (hps : ps.length ≤ N) {c : P} (hc : c ∈ U) :
    IntegrableOn
      (fun t ↦ orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t) c) (Icc 0 Δ) ∧
    orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps
      (fun a ↦ ∫ t in Icc 0 Δ, f t a) c =
        ∫ t in Icc 0 Δ, orderedTransferAction (fun v F a ↦ fderiv ℝ F a v) ps (f t) c := by
  apply orderedTransferAction_elapsedIntegral_of_local_bounds hU hm hf N _ _ ps hps hc
  · intro qs hqs a ha
    obtain ⟨V, hV, _, B, hB⟩ := hb qs hqs a ha
    exact ⟨B, fun t ht ↦ hB t ht a (mem_of_mem_nhds hV)⟩
  · intro qs hqs a ha
    exact local_fderiv_bound_of_local_word_bounds N hb qs hqs ha

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
