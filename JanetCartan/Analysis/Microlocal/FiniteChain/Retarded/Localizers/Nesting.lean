module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.Masks

/-!
# Finite nested retarded masks

The compact buffer in `app:ch_regular:lem:finite-chain`, “The protected finite
chain”, permits any prescribed finite depth. The masks are chosen in normalized
phase space, independently of derivative order, frequency, and grade parameters.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.FiniteChain.Retarded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restricting the protected set preserves a buffered mask
(`app:ch_regular:lem:finite-chain`). -/
theorem IsBufferedMask.mono_protected {m : CanonicalPhase E → ℝ}
    {K K' O : Set (CanonicalPhase E)} (hm : IsBufferedMask m K O) (h : K' ⊆ K) :
    IsBufferedMask m K' O :=
  ⟨hm.smooth, hm.range, hm.compactSupport, hm.support_subset, h.trans hm.plateau⟩

omit [NormedSpace ℝ E] in
/-- Covector reflection preserves support-to-plateau nesting
(`app:ch_regular:lem:finite-chain`, “Retarded and signed factors”). -/
theorem signedMask_preserves_nesting {m₁ m₂ : CanonicalPhase E → ℝ}
    (h : tsupport m₁ ⊆ interior {p | m₂ p = 1}) :
    tsupport (signedMask m₁) ⊆ interior {p | signedMask m₂ p = 1} := by
  rw [tsupport_signedMask]
  apply (preimage_mono h).trans
  exact (reflectCovectorHomeomorph.continuous_toFun.isOpen_preimage _ isOpen_interior
    ).subset_interior_iff.mpr (preimage_mono interior_subset)

/-- Arbitrarily long finite families with every earlier closed support in the
interior plateau of every later mask (`app:ch_regular:lem:finite-chain`).
The existential family precedes all analytic parameters. -/
theorem exists_nested_bufferedMasks [FiniteDimensional ℝ E]
    (N : ℕ) {K O : Set (CanonicalPhase E)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ m : Fin N → CanonicalPhase E → ℝ,
      (∀ i, IsBufferedMask (m i) K O) ∧
      ∀ i j, i < j → tsupport (m i) ⊆ interior {p | m j p = 1} := by
  induction N generalizing K with
  | zero => exact ⟨Fin.elim0, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨m, hm⟩ := exists_bufferedMask hK hO hKO
    obtain ⟨ms, hs, hn⟩ := ih (hK.union hm.compactSupport)
      (union_subset hKO hm.support_subset)
    refine ⟨Fin.cons m ms, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hm
      · exact (hs j).mono_protected subset_union_left
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (by simp) (fun j' _ => ?_) j
        exact subset_union_right.trans (hs j').plateau
      · refine Fin.cases (by simp) (fun j' hij => ?_) j
        exact hn i' j' (Fin.succ_lt_succ_iff.mp hij)

end JanetCartan.FiniteChain.Retarded
