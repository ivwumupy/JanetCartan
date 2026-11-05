module

public import JanetCartan.Analysis.Microlocal.NormalizedTerminalProtection.OriginalNoReturn

/-!
# The original signed source in a fixed compact annulus

The original signed-family direction inclusion and beat-normalized bounds
produce the compact source required by the terminal-mask application.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection

open ProtectedFlow SignedPairs

/-- The original signed directions and uniform beat bounds put every actual
normalized signed source in one compact annulus. Its angular inclusion is
derived from the original no-return cover, and its constants precede the
varying current family member. Consumer:
`exists_original_history_terminal_even_proof_masks`
(`app:ch_seed:prop:seed-actual-menu`, `app:ch_regular:thm:no-return`). -/
theorem original_signed_source_annulus {d : ℕ} {X I Z : Type*}
    [NormedAddCommGroup Z] (family : X → I → Z → Euclidean (d+1))
    (S : I → Set Z) {Ω : Set (Euclidean (d+1))} (hΩ : IsCompact Ω)
    {a A : ℝ} (ha : 0 < a)
    (hdirection : closure (directionSet family S) ⊆ interior Ω)
    (hband : ∀ x (q : Pair I Z S),
      a*q.beat ≤ ‖q.vector (family x)‖ ∧ ‖q.vector (family x)‖ ≤ A*q.beat) :
    let Ksource := (fun p : ℝ × Euclidean (d+1) ↦ p.1 • p.2) ''
      (Icc a A ×ˢ (Ω ∩ sphere 0 1))
    IsCompact Ksource ∧
      (∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ Ω) ∧
      ∀ x (q : Pair I Z S), q.beat⁻¹ • q.vector (family x) ∈ Ksource := by
  intro Ksource
  have hcompact : IsCompact Ksource :=
    (isCompact_Icc.prod (hΩ.inter_right isClosed_sphere)).image
      (continuous_fst.smul continuous_snd)
  refine ⟨hcompact, ?_, ?_⟩
  · rintro ξ ⟨⟨t, v⟩, ⟨ht, hvΩ, hv⟩, rfl⟩
    have htpos : 0 < t := ha.trans_le ht.1
    have hvnorm : ‖v‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hv
    have hvne : v ≠ 0 := by intro he; simp [he] at hvnorm
    refine ⟨smul_ne_zero htpos.ne' hvne, ?_⟩
    rw [normalizedCovector_smul_pos htpos]
    simpa only [normalizedCovector, hvnorm, inv_one, one_smul] using hvΩ
  · intro x q
    have hq : 0 < q.beat := q.beat_pos
    have hv : q.vector (family x) ≠ 0 := norm_pos_iff.mp
      ((mul_pos ha hq).trans_le (hband x q).1)
    have hdir : NormedSpace.normalize (q.vector (family x)) ∈ Ω :=
      interior_subset (hdirection (subset_closure ⟨x, q, rfl⟩))
    refine ⟨(‖q.vector (family x)‖ / q.beat,
      NormedSpace.normalize (q.vector (family x))), ?_, ?_⟩
    · refine ⟨⟨(le_div_iff₀ hq).mpr (hband x q).1,
        (div_le_iff₀ hq).mpr (hband x q).2⟩, hdir, ?_⟩
      simpa only [mem_sphere_zero_iff_norm] using NormedSpace.norm_normalize hv
    · dsimp [NormedSpace.normalize]
      rw [smul_smul]
      congr 1
      field_simp

end JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection
