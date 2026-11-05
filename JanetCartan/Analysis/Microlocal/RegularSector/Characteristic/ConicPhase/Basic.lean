module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhaseHomogeneity
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Conic

/-!
# Fixed radial continuation of the same two-time phase

Only the initial spatial covector is normalized. Both times, the physical
position, and the local inverse chart are retained. The normalization is by
a fixed linear functional positive on the chosen angular patch. Smoothness
is asserted on that chart; no smoothness at zero is asserted.
Source: `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.RegularSector.Characteristic.ConicPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalize the initial covector, keeping both times and position fixed.
Consumer: the conic continuation in `app:ch_regular_base:lem:retarded-kernel`. -/
def normalize (ℓ : E →L[ℝ] ℝ) (q : TwoTimePoint E) : TwoTimePoint E :=
  (q.1, (q.2.1, (q.2.2.1, (ℓ q.2.2.2)⁻¹ • q.2.2.2)))

/-- The positive radial extension of a joint phase on a fixed section.
Consumer: normalized phase jets in `app:ch_regular_base:lem:retarded-kernel`. -/
def extend (ℓ : E →L[ℝ] ℝ) (F : TwoTimePoint E → ℝ) (q : TwoTimePoint E) : ℝ :=
  ℓ q.2.2.2 * F (normalize ℓ q)

/-- Continue the actual inverse-chart phase, without choosing another flow
or root (`app:ch_regular_base:lem:characteristic-kernel`). -/
def phase (ℓ : E →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)) : TwoTimePoint E → ℝ :=
  extend ℓ (twoTimePhase C)

/-- The positive conic chart over a local two-time patch
(`app:ch_regular_base:lem:retarded-kernel`). -/
def domain (ℓ : E →L[ℝ] ℝ) (V : Set (TwoTimePoint E)) : Set (TwoTimePoint E) :=
  {q | 0 < ℓ q.2.2.2 ∧ normalize ℓ q ∈ V}

/-- A product patch in the two times, position, and initial spatial covector
(`app:ch_regular_base:lem:retarded-kernel`). -/
def localPatch (B : Set (ℝ × (ℝ × E))) (P : Set E) : Set (TwoTimePoint E) :=
  {q | (q.1, (q.2.1, q.2.2.1)) ∈ B ∧ q.2.2.2 ∈ P}

omit [InnerProductSpace ℝ E] in
/-- The local product patch is open (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem isOpen_localPatch {B : Set (ℝ × (ℝ × E))} {P : Set E}
    (hB : IsOpen B) (hP : IsOpen P) : IsOpen (localPatch B P) :=
  (hB.preimage (continuous_fst.prodMk
    (continuous_snd.fst.prodMk continuous_snd.snd.fst))).inter
    (hP.preimage continuous_snd.snd.snd)

/-- The fixed radial representative is invariant under positive scaling
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem normalize_smul (ℓ : E →L[ℝ] ℝ) (q : TwoTimePoint E)
    {a : ℝ} (ha : a ≠ 0) :
    normalize ℓ (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))) = normalize ℓ q := by
  have he := CharacteristicRoot.normalize_smul ℓ (q.2.2.1, q.2.2.2) ha
  exact congrArg (fun p : E × E ↦ (q.1, (q.2.1, p))) he

/-- Every normalized representative lies on the fixed section
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem normalization_eq_one (ℓ : E →L[ℝ] ℝ) {q : TwoTimePoint E}
    (hq : ℓ q.2.2.2 ≠ 0) : ℓ (normalize ℓ q).2.2.2 = 1 := by
  simp [normalize, hq]

/-- Normalization fixes its section (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem normalize_of_eq_one (ℓ : E →L[ℝ] ℝ) {q : TwoTimePoint E}
    (hq : ℓ q.2.2.2 = 1) : normalize ℓ q = q := by
  simp [normalize, hq]

/-- The extension has exact degree one at every positive radial scale
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem extend_smul (ℓ : E →L[ℝ] ℝ) (F : TwoTimePoint E → ℝ)
    (q : TwoTimePoint E) {a : ℝ} (ha : 0 < a) :
    extend ℓ F (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))) = a * extend ℓ F q := by
  simp only [extend, normalize_smul ℓ q ha.ne', map_smul, smul_eq_mul, mul_assoc]

/-- Positive scaling preserves the same conic chart
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem mem_domain_smul (ℓ : E →L[ℝ] ℝ) {V : Set (TwoTimePoint E)}
    {q : TwoTimePoint E} (hq : q ∈ domain ℓ V) {a : ℝ} (ha : 0 < a) :
    (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))) ∈ domain ℓ V := by
  refine ⟨by simpa using mul_pos ha hq.1, ?_⟩
  simpa only [normalize_smul ℓ q ha.ne'] using hq.2

/-- The spatial zero covector is excluded by the positive chart
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem covector_ne_zero {ℓ : E →L[ℝ] ℝ} {V : Set (TwoTimePoint E)}
    {q : TwoTimePoint E} (hq : q ∈ domain ℓ V) : q.2.2.2 ≠ 0 := by
  intro he
  simpa [he] using hq.1

/-- The normalization is jointly smooth on its nonzero linear-coordinate
chart (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffAt_normalize (ℓ : E →L[ℝ] ℝ) {q : TwoTimePoint E}
    (hq : ℓ q.2.2.2 ≠ 0) : ContDiffAt ℝ ∞ (normalize ℓ) q :=
  contDiffAt_fst.prodMk (contDiffAt_snd.fst.prodMk (contDiffAt_snd.snd.fst.prodMk
    (((ℓ.contDiff.contDiffAt.comp q contDiffAt_snd.snd.snd).inv hq).smul
      contDiffAt_snd.snd.snd)))

/-- Openness of the continued chart (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem isOpen_domain (ℓ : E →L[ℝ] ℝ) {V : Set (TwoTimePoint E)} (hV : IsOpen V) :
    IsOpen (domain ℓ V) := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  exact inter_mem
    ((isOpen_lt continuous_const (ℓ.continuous.comp continuous_snd.snd.snd)).mem_nhds hq.1)
    ((contDiffAt_normalize ℓ hq.1.ne').continuousAt.preimage_mem_nhds (hV.mem_nhds hq.2))

/-- Smoothness of the actual formula on its conic domain. The local phase
smoothness is supplied by `exists_buffered_physical_pencil_kernel`
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem contDiffOn_extend (ℓ : E →L[ℝ] ℝ) {V : Set (TwoTimePoint E)}
    (hV : IsOpen V) {F : TwoTimePoint E → ℝ} (hF : ContDiffOn ℝ ∞ F V) :
    ContDiffOn ℝ ∞ (extend ℓ F) (domain ℓ V) := by
  intro q hq
  exact ((ℓ.contDiff.contDiffAt.comp q contDiffAt_snd.snd.snd).mul
    ((hF.contDiffAt (hV.mem_nhds hq.2)).comp q
      (contDiffAt_normalize ℓ hq.1.ne'))).contDiffWithinAt

/-- Joint smoothness of the conic continuation of the same chart phase
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_phase (ℓ : E →L[ℝ] ℝ)
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target) :
    ContDiffOn ℝ ∞ (phase ℓ C) (domain ℓ C.target) :=
  contDiffOn_extend ℓ C.open_target hC

/-- The diagonal data continue exactly along every positive ray. The local
data are supplied for this same chart by `exists_buffered_physical_pencil_kernel`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem phase_diagonal (ℓ : E →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E))
    {s : ℝ} {y η : E} (hη : ℓ η ≠ 0)
    (hdiag : twoTimePhase C (s, (s, (y, (ℓ η)⁻¹ • η))) = ⟪y, (ℓ η)⁻¹ • η⟫_ℝ) :
    phase ℓ C (s, (s, (y, η))) = ⟪y, η⟫_ℝ := by
  change ℓ η * twoTimePhase C (s, (s, (y, (ℓ η)⁻¹ • η))) = _
  rw [hdiag, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hη, one_mul]

end JanetCartan.RegularSector.Characteristic.ConicPhase
