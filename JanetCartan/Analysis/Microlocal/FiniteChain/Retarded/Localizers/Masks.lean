module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Smooth buffered retarded masks

Construct the masks in `app:ch_regular:lem:finite-chain`, “Retarded and signed
factors”, using the shared compact-family cutoff construction. All masks are
chosen in normalized phase space, before the frequency and grade parameters.
The input support, including its shoulders, has complete image inside the
output plateau. The prescribed input chart can encode the endpoint buffer.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.FiniteChain.Retarded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The geometric and smooth properties of a proof mask in
`app:ch_regular:lem:finite-chain`. Existence is proved below, with no analytic
off-relation estimate as a field. -/
structure IsBufferedMask (m : CanonicalPhase E → ℝ)
    (K O : Set (CanonicalPhase E)) : Prop where
  smooth : ContDiff ℝ ∞ m
  range : ∀ p, m p ∈ Icc (0 : ℝ) 1
  compactSupport : HasCompactSupport m
  support_subset : tsupport m ⊆ O
  plateau : K ⊆ interior {p | m p = 1}

/-- Open normalized annular neighborhood (`app:ch_regular:lem:finite-chain`). -/
def phaseAnnulus (a b : ℝ) : Set (CanonicalPhase E) :=
  {p | a < frequencySize p.2.1 p.2.2 ∧ frequencySize p.2.1 p.2.2 < b}

omit [NormedSpace ℝ E] in
/-- The radial annular restriction is open (`app:ch_regular:lem:finite-chain`). -/
theorem isOpen_phaseAnnulus (a b : ℝ) : IsOpen (phaseAnnulus (E := E) a b) := by
  have hc : Continuous (fun p : CanonicalPhase E => frequencySize p.2.1 p.2.2) := by
    unfold frequencySize
    fun_prop
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

/-- A compact set in an open chart has a smooth buffered mask
(`app:ch_regular:lem:finite-chain`), reusing the existing cutoff API. -/
theorem exists_bufferedMask [FiniteDimensional ℝ E] {K O : Set (CanonicalPhase E)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ m : CanonicalPhase E → ℝ, IsBufferedMask m K O := by
  obtain ⟨m, hm, hr, hc, hs, hp⟩ := CompatibleResponse.exists_compact_family_cutoff hK hO hKO
  exact ⟨m, hm, hr, hc, hs, hp⟩

/-- The entire closed support of the complementary symbol, including the
identity contribution, misses the protected set
(`app:ch_regular:lem:finite-chain`). -/
theorem IsBufferedMask.disjoint_complement {m : CanonicalPhase E → ℝ}
    {K O : Set (CanonicalPhase E)} (hm : IsBufferedMask m K O) :
    Disjoint K (tsupport (fun p => 1 - m p)) := by
  have he : (fun p => 1 - m p) = fun p => -(m p - 1) := by funext p; ring
  rw [he]
  change Disjoint K (tsupport (-(fun p => m p - 1)))
  rw [tsupport_neg]
  exact CompatibleResponse.disjoint_inactive_tsupport hm.plateau

/-- Compatible input/output masks with positive annular endpoints, for the
lower operator and separately its literal adjoint
(`app:ch_regular:lem:finite-chain`). The complete image of the input mask's
closed support lies in the output plateau, not just the original compact set. -/
theorem exists_compatible_bufferedMasks [FiniteDimensional ℝ E]
    (backward : Bool) {R : Set (ℝ × E)} {K I O : Set (CanonicalPhase E)}
    {a b : ℝ} (hR : IsCompact R) (hK : IsCompact K)
    (hI : IsOpen I) (hKI : K ⊆ I) (hO : IsOpen O)
    (himage : completeImage backward R K ⊆ O) (ha : 0 < a) (hab : a ≤ b)
    (hann : ∀ p ∈ K, frequencySize p.2.1 p.2.2 ∈ Icc a b) :
    ∃ mi mo : CanonicalPhase E → ℝ,
      0 < a / 2 ∧ a / 2 < b + 1 ∧
      IsBufferedMask mi K (I ∩ phaseAnnulus (a / 2) (b + 1)) ∧
      IsBufferedMask mo (completeImage backward R K)
        (O ∩ phaseAnnulus (a / 2) (b + 1)) ∧
      completeImage backward R (tsupport mi) ⊆ interior {p | mo p = 1} := by
  have hKA : K ⊆ phaseAnnulus (a / 2) (b + 1) := by
    intro p hp
    have h := hann p hp
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hIA : completeImage backward R K ⊆ phaseAnnulus (a / 2) (b + 1) := by
    intro q hq
    have h := completeImage_annulus backward hann q hq
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨mo, hmo⟩ := exists_bufferedMask (isCompact_completeImage backward hR hK)
    (hO.inter (isOpen_phaseAnnulus _ _)) (subset_inter himage hIA)
  obtain ⟨U, hU, hKU, hUimage⟩ := exists_open_input_buffer backward hR
    isOpen_interior hmo.plateau
  obtain ⟨mi, hmi⟩ := exists_bufferedMask hK
    ((hI.inter (isOpen_phaseAnnulus _ _)).inter hU)
    (subset_inter (subset_inter hKI hKA) hKU)
  refine ⟨mi, mo, by linarith, by linarith, ?_, hmo, ?_⟩
  · exact ⟨hmi.smooth, hmi.range, hmi.compactSupport,
      fun p hp => (hmi.support_subset hp).1, hmi.plateau⟩
  · rintro q ⟨hq, p, hp, hrel⟩
    exact hUimage ⟨hq, p, (hmi.support_subset hp).2, hrel⟩

/-- The signed proof mask reflects only its covector
(`app:ch_regular:lem:finite-chain`). -/
def signedMask (m : CanonicalPhase E → ℝ) : CanonicalPhase E → ℝ :=
  fun p => m (reflectCovector p)

/-- Covector reflection as a homeomorphism
(`app:ch_regular:lem:finite-chain`). -/
def reflectCovectorHomeomorph : CanonicalPhase E ≃ₜ CanonicalPhase E where
  toFun := reflectCovector
  invFun := reflectCovector
  left_inv := reflectCovector_involutive
  right_inv := reflectCovector_involutive
  continuous_toFun := by unfold reflectCovector; fun_prop
  continuous_invFun := by unfold reflectCovector; fun_prop

omit [NormedSpace ℝ E] in
/-- Reflection acts on the full closed support, including shoulders
(`app:ch_regular:lem:finite-chain`). -/
theorem tsupport_signedMask (m : CanonicalPhase E → ℝ) :
    tsupport (signedMask m) = reflectCovector ⁻¹' tsupport m :=
  tsupport_comp_eq_preimage m reflectCovectorHomeomorph

/-- Signed masks have the reflected compact support and plateau, with no
reversal of time orientation (`app:ch_regular:lem:finite-chain`). -/
theorem IsBufferedMask.signed {m : CanonicalPhase E → ℝ}
    {K O : Set (CanonicalPhase E)} (hm : IsBufferedMask m K O) :
    IsBufferedMask (signedMask m) (reflectCovector ⁻¹' K) (reflectCovector ⁻¹' O) := by
  refine ⟨hm.smooth.comp (by unfold reflectCovector; fun_prop),
    fun p => hm.range _, ?_, ?_, ?_⟩
  · change IsCompact (tsupport (signedMask m))
    rw [tsupport_signedMask]
    exact reflectCovectorHomeomorph.isCompact_preimage.mpr hm.compactSupport
  · rw [tsupport_signedMask]
    exact preimage_mono hm.support_subset
  · apply (preimage_mono hm.plateau).trans
    exact (reflectCovectorHomeomorph.continuous_toFun.isOpen_preimage _ isOpen_interior
      ).subset_interior_iff.mpr (preimage_mono interior_subset)

end JanetCartan.FiniteChain.Retarded
