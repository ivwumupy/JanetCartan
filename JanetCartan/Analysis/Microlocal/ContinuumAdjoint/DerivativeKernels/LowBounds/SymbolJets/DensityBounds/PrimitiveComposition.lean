module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.PrimitiveBounds

/-!
# Composed jets from original weighted reserves

For `app:ch_background:prop:bg-adjoint`, freeze the frequency scale at the
point being differentiated. Apply the finite composition estimate first to
the original argument map, then to the normalized inverse. The resulting
amplitude and regularizer estimates supply the three complex factors in
`norm_iteratedFDeriv_weightedPair_le`. Geometry and original weighted reserves
remain inputs to the parent density construction.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open ContinuumRow NormalComparison

variable {n : ℕ}

/-- The common two-composition constant in `app:ch_background:prop:bg-adjoint`.
It depends only on the derivative order and primitive geometry budget. -/
def primitiveCompositionBound (N : ℕ) (B : ℝ) : ℝ :=
  ((N.factorial : ℝ) * (max 1 B)^N)^2

/-- Nonnegativity needed when inserting the composition bound into the
weighted density product estimate (`app:ch_background:prop:bg-adjoint`). -/
theorem primitiveCompositionBound_nonneg (N : ℕ) (B : ℝ) :
    0 ≤ primitiveCompositionBound N B := sq_nonneg _

/-- Smoothness of the original left argument map used in the first
composition for `app:ch_background:prop:bg-adjoint`. -/
theorem Chart.leftArguments_contDiff (g : Chart n) (he : ContDiff ℝ ∞ g.coordinates) :
    ContDiff ℝ ∞ g.leftArguments :=
  (g.carrier_contDiff he).fst.prodMk
    (contDiff_fst.fst.prodMk (g.carrier_contDiff he).snd)

/-- Smoothness of the original right argument map used in the first
composition for `app:ch_background:prop:bg-adjoint`. -/
theorem Chart.rightArguments_contDiff (g : Chart n) (he : ContDiff ℝ ∞ g.coordinates) :
    ContDiff ℝ ∞ g.rightArguments :=
  (g.carrier_contDiff he).fst.prodMk
    (contDiff_fst.snd.fst.prodMk (g.carrier_contDiff he).snd)

/-- Fixed frequency dilation preserves primitive amplitude smoothness
(`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveRegularity.scaledOriginalAmplitude_contDiff
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    (h : PrimitiveRegularity g a m) (r : ℝ) :
    ContDiff ℝ ∞ (scaledOriginalAmplitude a r) :=
  h.amplitude.comp (contDiff_fst.prodMk
    (contDiff_snd.fst.prodMk (contDiff_snd.snd.const_smul r)))

/-- Fixed frequency dilation preserves primitive regularizer smoothness
(`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveRegularity.scaledOriginalRegularizer_contDiff
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    (h : PrimitiveRegularity g a m) (r : ℝ) :
    ContDiff ℝ ∞ (scaledOriginalRegularizer m r) :=
  h.regularizer.comp (contDiff_fst.prodMk (contDiff_snd.const_smul r))

/-- Smooth normalized inverse for the second fixed-scale composition in
`app:ch_background:prop:bg-adjoint`. -/
theorem PrimitiveRegularity.normalizedPull_contDiffOn
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    (h : PrimitiveRegularity g a m) (s : JetRescaling g) (r : ℝ) :
    ContDiffOn ℝ ∞ (s.normalizedPull r) g.outputDomain :=
  (s.input r).symm.contDiff.comp_contDiffOn h.pull_contDiffOn

/-- Smoothness of the actual left factor consumed by
`norm_iteratedFDeriv_weightedPair_le` (`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveRegularity.composedLeftAmplitude_contDiffOn
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    (h : PrimitiveRegularity g a m) :
    ContDiffOn ℝ ∞ (fun q ↦
      a (g.carrier (g.pull q)).1 q.1.1 (g.carrier (g.pull q)).2) g.outputDomain := by
  have hc := (g.carrier_contDiff h.coordinates).comp_contDiffOn h.pull_contDiffOn
  exact h.amplitude.comp_contDiffOn
    (hc.fst.prodMk (contDiffOn_fst.fst.prodMk hc.snd))

/-- Smoothness of the actual right factor consumed by
`norm_iteratedFDeriv_weightedPair_le` (`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveRegularity.composedRightAmplitude_contDiffOn
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    (h : PrimitiveRegularity g a m) :
    ContDiffOn ℝ ∞ (fun q ↦
      a (g.carrier (g.pull q)).1 q.1.2.1 (g.carrier (g.pull q)).2) g.outputDomain := by
  have hc := (g.carrier_contDiff h.coordinates).comp_contDiffOn h.pull_contDiffOn
  exact h.amplitude.comp_contDiffOn
    (hc.fst.prodMk (contDiffOn_fst.snd.fst.prodMk hc.snd))

/-- Smoothness of the actual complex regularizer consumed by
`norm_iteratedFDeriv_weightedPair_le` (`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveRegularity.composedRegularizer_contDiffOn
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    (h : PrimitiveRegularity g a m) :
    ContDiffOn ℝ ∞ (fun q ↦ (m (g.carrier (g.pull q)) : ℂ)) g.outputDomain :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((h.regularizer.comp (g.carrier_contDiff h.coordinates)).comp_contDiffOn
      h.pull_contDiffOn)

private theorem norm_iteratedFDeriv_two_compositions_le
    {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    (h : PrimitiveRegularity g a m) (s : JetRescaling g)
    {v : JointVariables n → E} {f : E → W}
    (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f)
    {N : ℕ} {B D r : ℝ} (hD : 0 ≤ D)
    {p : JointVariables n} (hp : p ∈ g.outputDomain)
    (hfjet : ∀ i ≤ N, ‖iteratedFDeriv ℝ i f (v (s.normalizedPull r p))‖ ≤ D)
    (hvjet : ∀ i, 1 ≤ i → i ≤ N →
      ‖iteratedFDeriv ℝ i v (s.normalizedPull r p)‖ ≤ B)
    (hinvjet : ∀ i, 1 ≤ i → i ≤ N →
      ‖iteratedFDeriv ℝ i (s.normalizedPull r) p‖ ≤ B)
    {j : ℕ} (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j ((f ∘ v) ∘ s.normalizedPull r) p‖ ≤
      primitiveCompositionBound N B * D := by
  let C : ℝ := (N.factorial : ℝ) * (max 1 B)^N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcoef (i : ℕ) (hi : i ≤ N) :
      (i.factorial : ℝ) * (max 1 B)^i ≤ C := by
    have hfact : (i.factorial : ℝ) ≤ N.factorial := by
      exact_mod_cast Nat.factorial_le hi
    exact mul_le_mul hfact (pow_le_pow_right₀ (le_max_left 1 B) hi)
      (by positivity) (by positivity)
  have hfv (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (f ∘ v) (s.normalizedPull r p)‖ ≤ C * D := by
    have hb := InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le
      isOpen_univ isOpen_univ hv.contDiffOn hf.contDiffOn (mapsTo_univ _ _)
      (mem_univ (s.normalizedPull r p)) i
      (fun k hk ↦ hfjet k (hk.trans hi))
      (fun k hk hki ↦ hvjet k hk (hki.trans hi))
    calc
      _ ≤ (i.factorial : ℝ) * D * (max 1 B)^i := hb
      _ = ((i.factorial : ℝ) * (max 1 B)^i) * D := by ring
      _ ≤ C * D := mul_le_mul_of_nonneg_right (hcoef i hi) hD
  have hb := InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le
    h.output_open isOpen_univ (h.normalizedPull_contDiffOn s r)
    (hf.comp hv).contDiffOn (mapsTo_univ _ _) hp j
    (fun i hi ↦ hfv i (hi.trans hj))
    (fun i hi hij ↦ hinvjet i hi (hij.trans hj))
  calc
    _ ≤ (j.factorial : ℝ) * (C * D) * (max 1 B)^j := hb
    _ = ((j.factorial : ℝ) * (max 1 B)^j) * (C * D) := by ring
    _ ≤ C * (C * D) := mul_le_mul_of_nonneg_right (hcoef j hj) (mul_nonneg hC hD)
    _ = primitiveCompositionBound N B * D := by dsimp [primitiveCompositionBound, C]; ring

variable {g : Chart n} {s : JetRescaling g} {N : ℕ} {ρ B c : ℝ}
  {L : Set (JointVariables n)} {K : Set (Euclidean 2)}
  {X : Set (Euclidean n)} {Z : Set CarrierParameter} {Ω : Set (Euclidean (n - 1))}
  {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ} {A M : ℝ}

/-- Joint jets of the actual left amplitude, with the half-order weight
retained, derived from the original primitive reserve. This supplies the left
factor of `norm_iteratedFDeriv_weightedPair_le`
(`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveJetGeometry.norm_iteratedFDeriv_composedLeftAmplitude_le
    (hg : PrimitiveJetGeometry g s N ρ B c L K) (h : PrimitiveRegularity g a m)
    (ha : PrimitiveAmplitudeReserve g N ρ A X K Z Ω L a)
    {p : JointVariables n} (hp : p ∈ g.push '' L) (hpK : p.2 ∈ K)
    {j : ℕ} (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun q ↦
      a (g.carrier (g.pull q)).1 q.1.1 (g.carrier (g.pull q)).2) p‖ ≤
      primitiveCompositionBound N B * A * Real.sqrt ‖(g.carrier (g.pull p)).2‖ := by
  let r := ‖(g.carrier (g.pull p)).2‖
  have hrρ : ρ ≤ r := hg.high_frequency p hp hpK
  have hr : 0 < r := hg.threshold_pos.trans_le hrρ
  have hu : ‖(g.leftArguments (s.normalizedPull r p)).2.2‖ = 1 :=
    s.norm_carrier_normalizedPull p hr
  have he : ((scaledOriginalAmplitude a r ∘ g.leftArguments) ∘ s.normalizedPull r) =
      (fun q ↦ a (g.carrier (g.pull q)).1 q.1.1 (g.carrier (g.pull q)).2) :=
    funext (s.scaledOriginalAmplitude_left a hr)
  have hb := norm_iteratedFDeriv_two_compositions_le h s
    (g.leftArguments_contDiff h.coordinates) (h.scaledOriginalAmplitude_contDiff r)
    (mul_nonneg ha.budget_nonneg (Real.sqrt_nonneg r)) (ha.buffered.image_subset hp)
    (fun i hi ↦ ha.mixed_jets r hrρ _ hu i hi)
    (hg.left_jets p hp hpK) (hg.inverse_jets p hp hpK) hj
  simpa only [he, mul_assoc] using hb

/-- Joint jets of the actual right amplitude, with the half-order weight
retained, derived from the original primitive reserve. This supplies the right
factor of `norm_iteratedFDeriv_weightedPair_le`
(`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveJetGeometry.norm_iteratedFDeriv_composedRightAmplitude_le
    (hg : PrimitiveJetGeometry g s N ρ B c L K) (h : PrimitiveRegularity g a m)
    (ha : PrimitiveAmplitudeReserve g N ρ A X K Z Ω L a)
    {p : JointVariables n} (hp : p ∈ g.push '' L) (hpK : p.2 ∈ K)
    {j : ℕ} (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun q ↦
      a (g.carrier (g.pull q)).1 q.1.2.1 (g.carrier (g.pull q)).2) p‖ ≤
      primitiveCompositionBound N B * A * Real.sqrt ‖(g.carrier (g.pull p)).2‖ := by
  let r := ‖(g.carrier (g.pull p)).2‖
  have hrρ : ρ ≤ r := hg.high_frequency p hp hpK
  have hr : 0 < r := hg.threshold_pos.trans_le hrρ
  have hu : ‖(g.rightArguments (s.normalizedPull r p)).2.2‖ = 1 :=
    s.norm_carrier_normalizedPull p hr
  have he : ((scaledOriginalAmplitude a r ∘ g.rightArguments) ∘ s.normalizedPull r) =
      (fun q ↦ a (g.carrier (g.pull q)).1 q.1.2.1 (g.carrier (g.pull q)).2) :=
    funext (s.scaledOriginalAmplitude_right a hr)
  have hb := norm_iteratedFDeriv_two_compositions_le h s
    (g.rightArguments_contDiff h.coordinates) (h.scaledOriginalAmplitude_contDiff r)
    (mul_nonneg ha.budget_nonneg (Real.sqrt_nonneg r)) (ha.buffered.image_subset hp)
    (fun i hi ↦ ha.mixed_jets r hrρ _ hu i hi)
    (hg.right_jets p hp hpK) (hg.inverse_jets p hp hpK) hj
  simpa only [he, mul_assoc] using hb

/-- Joint jets of the actual complex regularizer, uniformly in its primitive
budget. The inclusion of real scalars in `ℂ` is an isometry, so it causes no
extra loss in `norm_iteratedFDeriv_weightedPair_le`
(`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveJetGeometry.norm_iteratedFDeriv_composedRegularizer_le
    (hg : PrimitiveJetGeometry g s N ρ B c L K) (h : PrimitiveRegularity g a m)
    (hs : BufferedSupport g a L) (hm : PrimitiveRegularizerReserve N ρ M m)
    {p : JointVariables n} (hp : p ∈ g.push '' L) (hpK : p.2 ∈ K)
    {j : ℕ} (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun q ↦ (m (g.carrier (g.pull q)) : ℂ)) p‖ ≤
      primitiveCompositionBound N B * M := by
  let r := ‖(g.carrier (g.pull p)).2‖
  have hrρ : ρ ≤ r := hg.high_frequency p hp hpK
  have hr : 0 < r := hg.threshold_pos.trans_le hrρ
  have hu := s.norm_carrier_normalizedPull p hr
  have he : ((scaledOriginalRegularizer m r ∘ g.carrier) ∘ s.normalizedPull r) =
      (fun q ↦ m (g.carrier (g.pull q))) :=
    funext (s.scaledOriginalRegularizer_carrier m hr)
  have hb := norm_iteratedFDeriv_two_compositions_le h s
    (g.carrier_contDiff h.coordinates) (h.scaledOriginalRegularizer_contDiff r)
    hm.budget_nonneg (hs.image_subset hp)
    (fun i hi ↦ hm.mixed_jets r hrρ _ hu i hi)
    (hg.carrier_jets p hp hpK) (hg.inverse_jets p hp hpK) hj
  rw [he] at hb
  change ‖iteratedFDeriv ℝ j
    (Complex.ofRealLI ∘ (fun q ↦ m (g.carrier (g.pull q)))) p‖ ≤ _
  have hreal : ContDiffAt ℝ ∞ (fun q ↦ m (g.carrier (g.pull q))) p :=
    ((h.regularizer.comp (g.carrier_contDiff h.coordinates)).comp_contDiffOn
      h.pull_contDiffOn).contDiffAt (h.output_open.mem_nhds (hs.image_subset hp))
  exact (Complex.ofRealLI.norm_iteratedFDeriv_comp_left hreal (by simp)).trans_le hb

/-- A common constant is chosen before the arbitrary amplitude, regularizer,
and their budgets. The three conclusions and their smoothness lemmas feed
`norm_iteratedFDeriv_weightedPair_le`; no composed jets are assumed
(`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveJetGeometry.exists_composedAmplitude_regularizer_jet_bound
    (hg : PrimitiveJetGeometry g s N ρ B c L K)
    (X : Set (Euclidean n)) (Z : Set CarrierParameter) (Ω : Set (Euclidean (n - 1))) :
    ∃ T ≥ 0, ∀ (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (A M : ℝ),
      PrimitiveRegularity g a m →
      PrimitiveAmplitudeReserve g N ρ A X K Z Ω L a →
      PrimitiveRegularizerReserve N ρ M m →
      ∀ p ∈ g.push '' L, p.2 ∈ K → ∀ j ≤ N,
        (‖iteratedFDeriv ℝ j (fun q ↦
          a (g.carrier (g.pull q)).1 q.1.1 (g.carrier (g.pull q)).2) p‖ ≤
          T * A * Real.sqrt ‖(g.carrier (g.pull p)).2‖) ∧
        (‖iteratedFDeriv ℝ j (fun q ↦
          a (g.carrier (g.pull q)).1 q.1.2.1 (g.carrier (g.pull q)).2) p‖ ≤
          T * A * Real.sqrt ‖(g.carrier (g.pull p)).2‖) ∧
        (‖iteratedFDeriv ℝ j (fun q ↦ (m (g.carrier (g.pull q)) : ℂ)) p‖ ≤ T * M) := by
  refine ⟨primitiveCompositionBound N B, primitiveCompositionBound_nonneg N B, ?_⟩
  intro a m A M h ha hm p hp hpK j hj
  exact ⟨hg.norm_iteratedFDeriv_composedLeftAmplitude_le h ha hp hpK hj,
    hg.norm_iteratedFDeriv_composedRightAmplitude_le h ha hp hpK hj,
    hg.norm_iteratedFDeriv_composedRegularizer_le h ha.buffered hm hp hpK hj⟩

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
