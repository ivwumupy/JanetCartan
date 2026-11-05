module

public import JanetCartan.Analysis.Microlocal.NormalizedTerminalProtection.OriginalSourceAnnulus

/-!
# The source compact inside the original signed cone

The closure of the original family's signed directions stays inside the
protected open cone. Keeping this closure in the source annulus supplies the
interior inclusion required by the observed residual construction.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization

open ProtectedFlow SignedPairs

/-- The same original directions and beat bounds produce a compact annulus
whose directions remain in the interior of the original source cone.
Consumer: `exists_original_signed_residual_decay` and its supplied terminal
mask application (`app:ch_pairs:setup:pairs-lag`,
`app:ch_regular:thm:no-return`, `app:ch_regular:eq:source-tail`). -/
theorem original_supplied_signed_source_annulus_interior
    {d : ℕ} {X I Z : Type*} [NormedAddCommGroup Z]
    (family : X → I → Z → Euclidean (d+1)) (S : I → Set Z)
    {Ω : Set (Euclidean (d+1))} (hΩ : IsCompact Ω) {a A : ℝ} (ha : 0 < a)
    (hdirection : closure (directionSet family S) ⊆ interior Ω)
    (hband : ∀ x (q : Pair I Z S),
      a*q.beat ≤ ‖q.vector (family x)‖ ∧ ‖q.vector (family x)‖ ≤ A*q.beat) :
    let Ksource := (fun p : ℝ × Euclidean (d+1) ↦ p.1 • p.2) ''
      (Icc a A ×ˢ (closure (directionSet family S) ∩ sphere 0 1))
    IsCompact Ksource ∧
      (∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ interior Ω) ∧
      ∀ x (q : Pair I Z S), q.beat⁻¹ • q.vector (family x) ∈ Ksource := by
  intro Ksource
  have hcompact : IsCompact (closure (directionSet family S)) :=
    hΩ.of_isClosed_subset isClosed_closure (hdirection.trans interior_subset)
  refine ⟨(isCompact_Icc.prod (hcompact.inter_right isClosed_sphere)).image
    (continuous_fst.smul continuous_snd), ?_, ?_⟩
  · rintro ξ ⟨⟨t, v⟩, ⟨ht, hvdir, hv⟩, rfl⟩
    have htpos : 0 < t := ha.trans_le ht.1
    have hvnorm : ‖v‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hv
    have hvne : v ≠ 0 := by intro he; simp [he] at hvnorm
    refine ⟨smul_ne_zero htpos.ne' hvne, ?_⟩
    rw [normalizedCovector_smul_pos htpos]
    simpa only [normalizedCovector, hvnorm, inv_one, one_smul] using hdirection hvdir
  · intro x q
    have hq : 0 < q.beat := q.beat_pos
    have hv : q.vector (family x) ≠ 0 := norm_pos_iff.mp
      ((mul_pos ha hq).trans_le (hband x q).1)
    refine ⟨(‖q.vector (family x)‖ / q.beat,
      NormedSpace.normalize (q.vector (family x))), ?_, ?_⟩
    · refine ⟨⟨(le_div_iff₀ hq).mpr (hband x q).1,
        (div_le_iff₀ hq).mpr (hband x q).2⟩, subset_closure ⟨x, q, rfl⟩, ?_⟩
      simpa only [mem_sphere_zero_iff_norm] using NormedSpace.norm_normalize hv
    · dsimp [NormedSpace.normalize]
      rw [smul_smul]
      congr 1
      field_simp

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
