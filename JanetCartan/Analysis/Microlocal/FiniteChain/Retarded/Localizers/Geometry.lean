module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.FrequencyGaps
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.FunProp

/-!
# Complete retarded images in canonical phase space

The compact geometric images in `app:ch_regular:lem:finite-chain`, subsection
“Retarded and signed factors”. The actual output base rectangle is retained.
The Boolean orientation distinguishes the lower operator from its literal
adjoint; covector reflection does not change this orientation.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.FiniteChain.Retarded

variable {E : Type*} [NormedAddCommGroup E]

/-- Base and normalized joint covector in `app:ch_regular:lem:finite-chain`. -/
abbrev CanonicalPhase (E : Type*) := (ℝ × E) × (ℝ × E)

/-- The complete diagonal plus characteristic relation from
`app:ch_regular:lem:finite-chain`. `true` is the literal-adjoint orientation. -/
def CompleteRelation (backward : Bool) (p q : CanonicalPhase E) : Prop :=
  q = p ∨ if backward then ForwardRelation q.1 p.1 q.2.1 q.2.2 p.2.1 p.2.2
    else ForwardRelation p.1 q.1 p.2.1 p.2.2 q.2.1 q.2.2

/-- The complete image restricted to the actual physical rectangle `R`
(`app:ch_regular:lem:finite-chain`). -/
def completeImage (backward : Bool) (R : Set (ℝ × E))
    (K : Set (CanonicalPhase E)) : Set (CanonicalPhase E) :=
  {q | q.1 ∈ R ∧ ∃ p ∈ K, CompleteRelation backward p q}

omit [NormedAddCommGroup E] in
/-- Both branches preserve the entire joint covector
(`app:ch_regular:lem:finite-chain`). -/
theorem CompleteRelation.covector_eq {backward : Bool} {p q : CanonicalPhase E}
    (h : CompleteRelation backward p q) : q.2 = p.2 := by
  rcases h with h | h
  · exact congrArg Prod.snd h
  · cases backward <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
    · exact Prod.ext (h.2.2.2.1.trans h.2.2.1.symm) h.2.2.2.2
    · exact Prod.ext (h.2.2.1.trans h.2.2.2.1.symm) h.2.2.2.2.symm

omit [NormedAddCommGroup E] in
/-- The literal adjoint exchanges the full relation, including its diagonal
(`app:ch_regular:lem:finite-chain`). -/
theorem completeRelation_backward_iff (p q : CanonicalPhase E) :
    CompleteRelation true p q ↔ CompleteRelation false q p := by
  simp [CompleteRelation, eq_comm]

/-- Closedness of the complete relation, without a frequency truncation
(`app:ch_regular:lem:finite-chain`). -/
theorem isClosed_completeRelation (backward : Bool) :
    IsClosed {z : CanonicalPhase E × CanonicalPhase E |
      CompleteRelation backward z.1 z.2} := by
  have hf : IsClosed {z : CanonicalPhase E × CanonicalPhase E |
      ForwardRelation z.1.1 z.2.1 z.1.2.1 z.1.2.2 z.2.2.1 z.2.2.2} := by
    simp only [ForwardRelation, ofPred_and]
    exact (isClosed_le (by fun_prop) (by fun_prop)).inter
      ((isClosed_eq (by fun_prop) (by fun_prop)).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) (by fun_prop)))))
  cases backward
  · exact (isClosed_eq continuous_snd continuous_fst).union hf
  · exact (isClosed_eq continuous_snd continuous_fst).union
      (hf.preimage (show Continuous (fun z : CanonicalPhase E × CanonicalPhase E =>
        (z.2, z.1)) by fun_prop))

/-- Compact inputs and a compact actual rectangle have a compact complete
image (`app:ch_regular:lem:finite-chain`). Frequency compactness comes from
exact covector preservation, not an assumed output cutoff. -/
theorem isCompact_completeImage (backward : Bool) {R : Set (ℝ × E)}
    {K : Set (CanonicalPhase E)} (hR : IsCompact R) (hK : IsCompact K) :
    IsCompact (completeImage backward R K) := by
  let f : CanonicalPhase E × (ℝ × E) → CanonicalPhase E := fun z => (z.2, z.1.2)
  have hf : Continuous f := by fun_prop
  have hc : IsCompact ((K ×ˢ R) ∩ {z | CompleteRelation backward z.1 (f z)}) :=
    (hK.prod hR).inter_right ((isClosed_completeRelation backward).preimage
      (continuous_fst.prodMk hf))
  have he : f '' ((K ×ˢ R) ∩ {z | CompleteRelation backward z.1 (f z)}) =
      completeImage backward R K := by
    ext q
    constructor
    · rintro ⟨⟨p, x⟩, ⟨⟨hp, hx⟩, hrel⟩, rfl⟩
      exact ⟨hx, p, hp, hrel⟩
    · rintro ⟨hq, p, hp, hrel⟩
      have heq : f (p, q.1) = q := Prod.ext rfl hrel.covector_eq.symm
      have hmem : CompleteRelation backward p (f (p, q.1)) := by rwa [heq]
      exact ⟨(p, q.1), ⟨⟨hp, hq⟩, hmem⟩, heq⟩
  rw [← he]
  exact hc.image hf

/-- The input annulus is preserved on the complete output image, for either
orientation (`app:ch_regular:lem:finite-chain`). -/
theorem completeImage_annulus (backward : Bool) {R : Set (ℝ × E)}
    {K : Set (CanonicalPhase E)} {a b : ℝ}
    (hK : ∀ p ∈ K, frequencySize p.2.1 p.2.2 ∈ Icc a b) :
    ∀ q ∈ completeImage backward R K, frequencySize q.2.1 q.2.2 ∈ Icc a b := by
  rintro q ⟨_, p, hp, hrel⟩
  simpa only [hrel.covector_eq] using hK p hp

/-- An open neighborhood of the complete image still contains the complete
image of an open input neighborhood (`app:ch_regular:lem:finite-chain`).
Compactness of the actual output rectangle controls all input shoulders. -/
theorem exists_open_input_buffer (backward : Bool) {R : Set (ℝ × E)}
    {K O : Set (CanonicalPhase E)} (hR : IsCompact R) (hO : IsOpen O)
    (hKO : completeImage backward R K ⊆ O) :
    ∃ U : Set (CanonicalPhase E), IsOpen U ∧ K ⊆ U ∧
      completeImage backward R U ⊆ O := by
  let : CompactSpace R := isCompact_iff_compactSpace.mp hR
  let f : CanonicalPhase E × R → CanonicalPhase E := fun z => (z.2.1, z.1.2)
  have hf : Continuous f := by fun_prop
  let B : Set (CanonicalPhase E × R) :=
    {z | CompleteRelation backward z.1 (f z)} ∩ f ⁻¹' Oᶜ
  have hB : IsClosed B :=
    ((isClosed_completeRelation backward).preimage (continuous_fst.prodMk hf)).inter
      (hO.isClosed_compl.preimage hf)
  refine ⟨(Prod.fst '' B)ᶜ, (isClosedMap_fst_of_compactSpace B hB).isOpen_compl, ?_, ?_⟩
  · intro p hp
    rintro ⟨⟨p', x⟩, ⟨hrel, hx⟩, he⟩
    change p' = p at he
    subst p'
    exact hx (hKO ⟨x.property, p, hp, hrel⟩)
  · rintro q ⟨hq, p, hp, hrel⟩
    by_contra hnot
    apply hp
    have he : f (p, ⟨q.1, hq⟩) = q := Prod.ext rfl hrel.covector_eq.symm
    refine ⟨(p, ⟨q.1, hq⟩), ?_, rfl⟩
    change CompleteRelation backward p (f (p, ⟨q.1, hq⟩)) ∧
      f (p, ⟨q.1, hq⟩) ∉ O
    simpa only [he] using And.intro hrel hnot

/-- A fixed closed physical rectangle is compact in finite dimension
(`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_physicalRectangle [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (tmin tmax : ℝ) (y : E) (r : ℝ) :
    IsCompact (Icc tmin tmax ×ˢ Metric.closedBall y r) :=
  isCompact_Icc.prod (isCompact_closedBall y r)

/-- Signed conjugation reflects covectors but leaves bases unchanged
(`app:ch_regular:lem:finite-chain`). -/
def reflectCovector (p : CanonicalPhase E) : CanonicalPhase E := (p.1, -p.2)

/-- Signed reflection is involutive (`app:ch_regular:lem:finite-chain`). -/
@[simp] theorem reflectCovector_involutive (p : CanonicalPhase E) :
    reflectCovector (reflectCovector p) = p := by simp [reflectCovector]

/-- Reflection preserves the radial annulus (`app:ch_regular:lem:finite-chain`). -/
@[simp] theorem frequencySize_reflectCovector (p : CanonicalPhase E) :
    frequencySize (reflectCovector p).2.1 (reflectCovector p).2.2 =
      frequencySize p.2.1 p.2.2 := by
  simp [reflectCovector, frequencySize]

/-- Reflection preserves time orientation; it is not the literal adjoint
(`app:ch_regular:lem:finite-chain`). -/
@[simp] theorem completeRelation_reflectCovector (backward : Bool)
    (p q : CanonicalPhase E) :
    CompleteRelation backward (reflectCovector p) (reflectCovector q) ↔
      CompleteRelation backward p q := by
  cases backward <;> simp [CompleteRelation, ForwardRelation, reflectCovector, Prod.ext_iff]

/-- The entire signed image is the covector reflection of the original image
(`app:ch_regular:lem:finite-chain`). -/
theorem completeImage_reflectCovector (backward : Bool) (R : Set (ℝ × E))
    (K : Set (CanonicalPhase E)) :
    completeImage backward R (reflectCovector '' K) =
      reflectCovector '' completeImage backward R K := by
  ext q
  constructor
  · rintro ⟨hq, _, ⟨p, hp, rfl⟩, hrel⟩
    refine ⟨reflectCovector q, ⟨hq, p, hp, ?_⟩, reflectCovector_involutive q⟩
    simpa only [← completeRelation_reflectCovector backward p (reflectCovector q),
      reflectCovector_involutive] using hrel
  · rintro ⟨q, ⟨hq, p, hp, hrel⟩, rfl⟩
    exact ⟨hq, reflectCovector p, mem_image_of_mem _ hp,
      (completeRelation_reflectCovector backward p q).mpr hrel⟩

end JanetCartan.FiniteChain.Retarded
