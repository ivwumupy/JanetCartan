module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.TransverseDetectorMasks

/-!
# A joint refinement preserving the original background mass

The eta-zero background is independent of the angular detector. Dividing a
subset's carrier weight among its labels and multiplying each corresponding
angular mask by the square root of that label count preserves both the
background weight and the original detector normal. This is the finite-copy
specialization needed by `exists_actual_retained_joint_sampling_transport_realization`;
its application must keep the same background atom on the copies.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric NormedSpace
open scoped ContDiff Classical

namespace JanetCartan.Sampling
open SeparatedSampling ContinuumRow.CanonicalConic SamplingKernelBounds
open ActualCarriers FrozenMenu CurrentFullPhase

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Share one carrier subset's weight equally among its labels. The
eta-zero atom has no angular factor, so this division prevents multiplicity
in `app:ch_waves:eq:background-quadrature`. -/
def balancedCarrierSubsetWeight (ψ : Point → ℝ) (b : I → Point → ℝ)
    (s : Finset I) (z : Point) : ℝ := carrierSubsetWeight ψ b s z / s.card

/-- Nonzero balanced weights retain the original subset and every local
plateau (`app:ch_waves:thm:sampling`). -/
theorem balancedCarrierSubsetWeight_support (ψ : Point → ℝ) (b : I → Point → ℝ)
    (s : Finset I) {z : Point} (hz : balancedCarrierSubsetWeight ψ b s z ≠ 0) :
    carrierSubsetWeight ψ b s z ≠ 0 := (div_ne_zero_iff.mp hz).1

/-- The carrier division preserves smoothness and compact support
(`app:ch_waves:eq:background-quadrature`). -/
theorem balancedCarrierSubsetWeight_regular (ψ : Point → ℝ) (b : I → Point → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (s : Finset I) :
    ContDiff ℝ ∞ (balancedCarrierSubsetWeight ψ b s) ∧
      HasCompactSupport (balancedCarrierSubsetWeight ψ b s) := by
  constructor
  · exact (carrierSubsetWeight_contDiff ψ b hψ hb s).div_const _
  · apply HasCompactSupport.intro (carrierSubsetWeight_hasCompactSupport ψ b hψc s).isCompact
    intro z hz
    by_contra hne
    exact hz (subset_tsupport _ (balancedCarrierSubsetWeight_support ψ b s hne))

/-- The original sampling cube and upper bound remain valid after sharing
carrier mass among a subset's labels (`app:ch_waves:thm:sampling`). -/
theorem balancedCarrierSubsetWeight_patchBounds (ψ : Point → ℝ) (b : I → Point → ℝ)
    {B P : ℝ} (hψ : PatchBounds ψ B P) (hb : ∀ i z, b i z ∈ Icc (0 : ℝ) 1)
    (s : Finset I) : PatchBounds (balancedCarrierSubsetWeight ψ b s) B P := by
  have hs := carrierSubsetWeight_patchBounds ψ b hψ hb s
  refine ⟨hs.radius_nonneg, fun z ↦ div_nonneg (hs.nonneg z) (Nat.cast_nonneg _), ?_, ?_⟩
  · intro z
    by_cases hcard : s.card = 0
    · simpa only [balancedCarrierSubsetWeight, hcard, Nat.cast_zero, div_zero] using
        (hs.nonneg z).trans (hs.le_bound z)
    · have hone : (1 : ℝ) ≤ s.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard
      exact (div_le_self (hs.nonneg z) hone).trans (hs.le_bound z)
  · intro z hz
    exact hs.support z (balancedCarrierSubsetWeight_support ψ b s hz)

/-- A covering carrier plateau kills the empty subset. Thus no nonzero
background mass is omitted when each nonempty subset is split among its labels
(`app:ch_waves:eq:background-quadrature`). -/
theorem carrierSubsetWeight_empty_of_plateau (ψ : Point → ℝ) (b : I → Point → ℝ)
    (z : Point) (hcover : ψ z ≠ 0 → ∃ i, b i z = 1) :
    carrierSubsetWeight ψ b ∅ z = 0 := by
  by_contra hs
  obtain ⟨i, hi⟩ := hcover (carrierSubsetWeight_support ψ b ∅ hs).1
  exact Finset.notMem_empty i (mem_of_carrierSubsetWeight_ne_zero ψ b ∅ hs hi)

/-- The original eta-zero carrier weight is preserved exactly on the SAME
finite labels. This identity is separate from angular normal reassembly
(`app:ch_waves:eq:background-quadrature`). -/
theorem sum_balancedCarrierSubsetWeight (ψ : Point → ℝ) (b : I → Point → ℝ)
    (z : Point) (hcover : ψ z ≠ 0 → ∃ i, b i z = 1) :
    ∑ s : Finset I, ∑ _i : s, balancedCarrierSubsetWeight ψ b s z = ψ z := by
  calc
    _ = ∑ s : Finset I, carrierSubsetWeight ψ b s z := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : s = ∅
      · subst s
        simp [carrierSubsetWeight_empty_of_plateau ψ b z hcover]
      · have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
          balancedCarrierSubsetWeight]
        field_simp
    _ = ψ z := sum_carrierSubsetWeight ψ b z

/-- Literal preservation of every eta-zero tensor on the unchanged parent
field; no independently constructed background is identified
(`app:ch_waves:eq:background-quadrature`). -/
theorem sum_balancedCarrierSubsetWeight_smul {V : Type*}
    [AddCommMonoid V] [Module ℝ V]
    (ψ : Point → ℝ) (b : I → Point → ℝ) (z : Point)
    (hcover : ψ z ≠ 0 → ∃ i, b i z = 1) (H : V) :
    (∑ s : Finset I, ∑ _i : s, balancedCarrierSubsetWeight ψ b s z • H) = ψ z • H := by
  simp only [← Finset.sum_smul]
  rw [sum_balancedCarrierSubsetWeight ψ b z hcover]

variable {n : ℕ} (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ i, ηb i ≠ 0) (hr : ∀ i, 0 < r i)

/-- The reciprocal square-root compensation in the detector preserves the
original normal when its carrier mass is shared among the subset's labels
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def balancedSubsetAngularMask (s : Finset I) (i : s) (η : Euclidean (n - 1)) : ℝ :=
  Real.sqrt s.card * subsetAngularMask ηb r hηb hr s i η

omit [Fintype I] [DecidableEq I] in
/-- The compensating angular factors retain smoothness away from zero,
positive homogeneity and the SAME local cone. These are the literal angular
inputs of the retained finite-copy event (`app:ch_waves:thm:sampling`). -/
theorem balancedSubsetAngularMask_spec (s : Finset I) (i : s) :
    (∀ η : Euclidean (n - 1), η ≠ 0 →
      ContDiffAt ℝ ∞ (balancedSubsetAngularMask ηb r hηb hr s i) η) ∧
    (∀ t : ℝ, 0 < t → ∀ η,
      balancedSubsetAngularMask ηb r hηb hr s i (t • η) =
        balancedSubsetAngularMask ηb r hηb hr s i η) ∧
    (∀ η, balancedSubsetAngularMask ηb r hηb hr s i η ≠ 0 →
      normalize η ∈ closedDirections (ηb i.1) (r i.1)) := by
  refine ⟨fun η hη ↦ contDiffAt_const.mul
    (canonicalAngularSquareMask_contDiffAt _ _ _ _ i hη), ?_, ?_⟩
  · intro t ht η
    change Real.sqrt s.card * canonicalAngularSquareMask _ _ _ _ i (t • η) = _
    rw [canonicalAngularSquareMask_homogeneous _ _ _ _ i t ht]
    rfl
  · intro η hη
    exact (canonicalAngularSquareMask_support _ _ _ _ i (mul_ne_zero_iff.mp hη).2).2

/-- One balanced weight and its detector square retain the original
unbalanced term, pointwise in the literal carrier and transverse coordinates
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem balancedCarrierSubsetWeight_mul_angularMask_sq
    (ψ : Point → ℝ) (b : I → Point → ℝ) (s : Finset I) (i : s)
    (z : Point) (η : Euclidean (n - 1)) :
    balancedCarrierSubsetWeight ψ b s z *
        balancedSubsetAngularMask ηb r hηb hr s i η ^ 2 =
      carrierSubsetWeight ψ b s z * subsetAngularMask ηb r hηb hr s i η ^ 2 := by
  have hc : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨i.1, i.2⟩).ne'
  simp only [balancedCarrierSubsetWeight, balancedSubsetAngularMask, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg s.card)]
  field_simp

/-- Simultaneous preservation of background mass and the ORIGINAL weighted
detector normal. The same supplied nonzero detector direction proves that no
empty-subset background is lost; the detector itself is never substituted
(`app:ch_waves:eq:background-quadrature`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem balancedSubsetMasks_preserve_background_and_detector
    (ψ : Point → ℝ) (b : I → Point → ℝ) (a : Euclidean (n - 1) → ℂ)
    (z : Point) (ha : ∃ η, η ≠ 0 ∧ a η ≠ 0)
    (hcover : ψ z ≠ 0 → ∀ η, η ≠ 0 → a η ≠ 0 → ∃ i, b i z = 1 ∧
      normalize η ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4)) :
    (∑ s : Finset I, ∑ _i : s, balancedCarrierSubsetWeight ψ b s z) = ψ z ∧
      ∀ η : Euclidean (n - 1), η ≠ 0 →
        (∑ s : Finset I, ∑ i : s, balancedCarrierSubsetWeight ψ b s z *
          ‖(balancedSubsetAngularMask ηb r hηb hr s i η : ℂ) * a η‖ ^ 2) =
            ψ z * ‖a η‖ ^ 2 := by
  refine ⟨sum_balancedCarrierSubsetWeight ψ b z (fun hz ↦ ?_), ?_⟩
  · obtain ⟨η, hη, haη⟩ := ha
    obtain ⟨i, hi, _⟩ := hcover hz η hη haη
    exact ⟨i, hi⟩
  · intro η hη
    by_cases haη : a η = 0
    · simp [haη]
    · simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        ← mul_assoc, balancedCarrierSubsetWeight_mul_angularMask_sq]
      have he := sum_carrierSubsetWeight_mul_subsetAngularMask_sq
        ηb r hηb hr ψ b z η (fun hz ↦ hcover hz η hη haη)
      have hmul := congrArg (fun x : ℝ ↦ x * ‖a η‖ ^ 2) he
      simpa only [Finset.sum_mul] using hmul

private theorem atomNormal_real_smul {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (t : ℝ) (T : E →L[ℂ] H) : atomNormal (t • T) = t ^ 2 • atomNormal T := by
  have hadj := map_smulₛₗ (ContinuousLinearMap.adjoint (𝕜 := ℂ)) (t : ℂ) T
  rw [show starRingEnd ℂ (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t] at hadj
  have hadj' : (t • T).adjoint = t • T.adjoint := by
    simpa only [Complex.coe_smul] using hadj
  unfold atomNormal
  rw [hadj']
  ext x
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.map_smul_of_tower, smul_smul, pow_two]

/-- Every grouped prefix reassembles the original normal with the SAME
balanced carrier weights that preserve the eta-zero background. The fixed
square-root factor is applied to the actual localized channel; its adjoint
square is proved, with the original Lebesgue spaces and both annular pieces
unchanged (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_balancedCarrierSubsetWeight_jointSubsetKernel_prefix_normal
    {Param : Type*} [TopologicalSpace Param] [FirstCountableTopology Param]
    [LocallyCompactSpace Param] {J : ℕ}
    (D : BandKernelData (Fin J × Param) n)
    (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (ψ : Point → ℝ) (b : I → Point → ℝ) (z : Point)
    (hcover : ψ z ≠ 0 → ∀ η, D.mask η ≠ 0 → ∃ i, b i z = 1 ∧
      normalize η ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    (L : ℕ) (p : Param) :
    (∑ s : Finset I, ∑ i : s, balancedCarrierSubsetWeight ψ b s z •
      atomNormal (Real.sqrt s.card • refinedKernelPrefix
        (jointSubsetKernel ηb r hηb hr D hfloor s i) L p)) =
      ψ z • atomNormal (refinedKernelPrefix D L p) := by
  calc
    _ = ∑ s : Finset I, ∑ i : s, carrierSubsetWeight ψ b s z •
        atomNormal (refinedKernelPrefix
          (jointSubsetKernel ηb r hηb hr D hfloor s i) L p) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      have hc : (s.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr ⟨i.1, i.2⟩).ne'
      rw [atomNormal_real_smul, Real.sq_sqrt (Nat.cast_nonneg s.card), smul_smul]
      congr 1
      exact div_mul_cancel₀ _ hc
    _ = _ := sum_carrierSubsetWeight_jointSubsetKernel_prefix_normal
      ηb r hηb hr D hfloor ψ b z hcover L p

/-- Balanced background weights retain both physical quadratures and the
original factor four in every grouped-prefix normal
(`app:ch_waves:eq:real-normal`). -/
theorem sum_balancedCarrierSubsetWeight_jointSubsetKernel_realPrefix_normal
    {Param : Type*} [TopologicalSpace Param] [FirstCountableTopology Param]
    [LocallyCompactSpace Param] {J : ℕ}
    (D : BandKernelData (Fin J × Param) n)
    (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (ψ : Point → ℝ) (b : I → Point → ℝ) (z : Point)
    (hcover : ψ z ≠ 0 → ∀ η, D.mask η ≠ 0 → ∃ i, b i z = 1 ∧
      normalize η ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    (L : ℕ) (p : Param) :
    (∑ s : Finset I, ∑ i : s, balancedCarrierSubsetWeight ψ b s z •
      ((realQuadratureChannel (Real.sqrt s.card • refinedKernelPrefix
        (jointSubsetKernel ηb r hηb hr D hfloor s i) L p)) ∘L
       (realQuadratureChannel (Real.sqrt s.card • refinedKernelPrefix
        (jointSubsetKernel ηb r hηb hr D hfloor s i) L p)).adjoint)) =
      (4 : ℝ) • realOutputCompression (ψ z • atomNormal (refinedKernelPrefix D L p)) := by
  simp_rw [realQuadratureChannel_normal_eq_four_realPart]
  rw [← sum_balancedCarrierSubsetWeight_jointSubsetKernel_prefix_normal
    ηb r hηb hr D hfloor ψ b z hcover L p]
  ext1 v
  simp [realOutputCompression, atomNormal, Finset.smul_sum, smul_smul, mul_comm, mul_assoc]

/-- A full-support label has nonzero ORIGINAL adapted projection. This
follows from the explicit frozen covector inverse and its unit transverse
input, without another incidence section (`app:ch_waves:thm:sampling`). -/
theorem transverseDetectorIncidenceSupport_adjoint_ne_zero
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {Z : Set (Euclidean 3)}
    {a : Euclidean (n - 1) → ℂ} {w : Euclidean 3 × Euclidean n}
    (hw : w ∈ transverseDetectorIncidenceSupport T Z a) :
    T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2 ≠ 0 := by
  obtain ⟨⟨z, θ⟩, ⟨_hz, hθ⟩, rfl⟩ := hw
  have hn : ‖θ‖ = 1 := mem_sphere_zero_iff_norm.mp hθ.1
  have hθne : θ ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
  have hk := frozenInputCovector_ne_zero T z hθne
  change T.data.adapted.embedding.toContinuousLinearMap.adjoint
    (‖frozenInputCovector T z θ‖⁻¹ • frozenInputCovector T z θ) ≠ 0
  rw [map_smul, frozenInputCovector_adjoint]
  exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hk)) hθne

/-- Construct the actual balanced carrier and detector masks on the finite
cover already returned by the analytic producer. All inputs of the finite-copy
sampling theorem concerning masks are proved. Both original background mass
and the weighted detector square are preserved on the entire original carrier
support, including boundary directions. The original high-pass is untouched
(`app:ch_waves:thm:sampling`, `app:ch_waves:eq:background-quadrature`). -/
theorem exists_transverseDetector_balanced_masks_on_retained_cover
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Z : Set (Euclidean 3)) (a : Euclidean (n - 1) → ℂ)
    (has : ∀ η, η ≠ 0 → ContDiffAt ℝ ∞ a η)
    (ha : ∀ t : ℝ, 0 < t → ∀ η, a (t • η) = a η)
    (hane : ∃ η, η ≠ 0 ∧ a η ≠ 0)
    (r d : transverseDetectorIncidenceSupport T Z a → ℝ)
    (hr : ∀ w, 0 < r w) (hd : ∀ w, 0 < d w)
    (localWeight : transverseDetectorIncidenceSupport T Z a → Point → ℝ)
    (hplateau : ∀ w z, WithLp.toLp 2 z ∈ closedBall w.1.1 (d w) → localWeight w z = 1)
    (labels : Finset (transverseDetectorIncidenceSupport T Z a))
    (hcover : ∀ w ∈ transverseDetectorIncidenceSupport T Z a, ∃ i : labels,
      w.1 ∈ ball i.1.1.1 (d i.1 / 2) ∧
      normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2) ∈
        ball (normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2))
          (angularWidth (n := n)
            (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2) (r i.1) / 4) ∧
      localWeight i.1 w.1.ofLp = 1) :
    let ηb := fun i : labels ↦ T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2
    let r' := fun i : labels ↦ r i.1
    ∃ hηb : ∀ i, ηb i ≠ 0,
    ∃ b : labels → Point → ℝ,
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i)) ∧
      (∀ i z, b i z ∈ Icc (0 : ℝ) 1) ∧
      (∀ i z, b i z ≠ 0 → localWeight i.1 z = 1) ∧
      (∀ z ∈ Z, ∀ η : Euclidean (n - 1), η ≠ 0 → a η ≠ 0 → ∃ i : labels,
        b i z.ofLp = 1 ∧ normalize η ∈
          ball (normalize (ηb i)) (angularWidth (ηb i) (r' i) / 4)) ∧
    ∀ (ψ : Point → ℝ) (B Pψ : ℝ), PatchBounds ψ B Pψ →
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∀ z, ψ z ≠ 0 → WithLp.toLp 2 z ∈ Z) →
    let J := (s : Finset labels) × s
    let weight := fun j : J ↦ balancedCarrierSubsetWeight ψ b j.1
    let angular := fun j : J ↦ fun η : Euclidean (n - 1) ↦
      (balancedSubsetAngularMask ηb r' hηb (fun i ↦ hr i.1) j.1 j.2 η : ℂ) * a η
    ; (∀ j, PatchBounds (weight j) B Pψ ∧ ContDiff ℝ ∞ (weight j) ∧
        HasCompactSupport (weight j)) ∧
      (∀ j z, weight j z ≠ 0 → localWeight j.2.1.1 z = 1) ∧
      (∀ j η, η ≠ 0 → ContDiffAt ℝ ∞ (angular j) η) ∧
      (∀ j (t : ℝ), 0 < t → ∀ η, angular j (t • η) = angular j η) ∧
      (∀ j η, angular j η ≠ 0 → normalize η ∈ closedDirections (ηb j.2.1) (r' j.2.1)) ∧
      (∀ z, ∑ j : J, weight j z = ψ z) ∧
      (∀ z η, η ≠ 0 → ∑ j : J, weight j z * ‖angular j η‖ ^ 2 = ψ z * ‖a η‖ ^ 2) := by
  classical
  intro ηb r'
  have hηb (i : labels) : ηb i ≠ 0 :=
    transverseDetectorIncidenceSupport_adjoint_ne_zero T i.1.2
  obtain ⟨_B, _hB, b, hb, hlocal, hcovered⟩ :=
    exists_transverseDetector_weights_on_retained_cover T Z a ha r d hd localWeight
      hplateau labels hcover
  have hb01 (i : labels) (z : Point) : b i z ∈ Icc (0 : ℝ) 1 :=
    ⟨(hb i).2.2.nonneg z, (hb i).2.2.le_bound z⟩
  refine ⟨hηb, b, fun i ↦ ⟨(hb i).1, (hb i).2.1⟩, hb01, hlocal, hcovered, ?_⟩
  intro ψ B Pψ hψ hψs hψc hψZ J weight angular
  have hs (j : J) := balancedSubsetAngularMask_spec ηb r' hηb (fun i ↦ hr i.1) j.1 j.2
  have hpreserve (z : Point) := balancedSubsetMasks_preserve_background_and_detector
    ηb r' hηb (fun i ↦ hr i.1) ψ b a z hane (fun hz η hη haη ↦
      hcovered (WithLp.toLp 2 z) (hψZ z hz) η hη haη)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨balancedCarrierSubsetWeight_patchBounds ψ b hψ hb01 j.1,
      balancedCarrierSubsetWeight_regular ψ b hψs hψc (fun i ↦ (hb i).1) j.1⟩
  · intro j z hz
    exact hlocal j.2.1 z ((carrierSubsetWeight_support ψ b j.1
      (balancedCarrierSubsetWeight_support ψ b j.1 hz)).2 j.2.1 j.2.2)
  · intro j η hη
    exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp η ((hs j).1 η hη)).mul (has η hη)
  · intro j t ht η
    change (_ : ℂ) * a (t • η) = _
    rw [(hs j).2.1 t ht, ha t ht]
  · intro j η hη
    apply (hs j).2.2 η
    intro hz
    exact hη (by simp only [angular, hz, Complex.ofReal_zero, zero_mul])
  · intro z
    simpa only [J, weight, Fintype.sum_sigma] using (hpreserve z).1
  · intro z η hη
    simpa only [J, weight, angular, Fintype.sum_sigma] using (hpreserve z).2 η hη

end JanetCartan.Sampling
