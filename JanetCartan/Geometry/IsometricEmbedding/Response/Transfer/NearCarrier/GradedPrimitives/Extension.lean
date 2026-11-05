module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Calculus
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Fixed cutoff extensions of reserve-graded primitives

For `app:ch_response:eq:direct-envelope-profile`, the local amplitude, `B`,
`B⁻¹`, `C`, and `-C B⁻¹` must have global smooth representatives for
`NearCarrierSymbol.hasFullSourceSymbolBound_of_expression` and
`BranchRealization.exists_modifiedFullGraphL2_of_primitive_jets`.

The cutoff and its derivative constants are constructed from a compact set
`K` inside an open buffered joint domain `U`. They are fixed before the scale,
frequency, and coefficient fields. Multiplication by this cutoff extends
every field smooth on `U`, without assuming any regularity outside `U`.
The total-order Leibniz estimate retains the reserve `L^(j-R)`.

The parent construction must supply the local graded estimates on `U` and
put the **complete** selected support, including every shoulder, in `K`.
Agreement holds on a fixed open neighborhood of all of `K`, for the fields
and their ambient derivatives of every order. This module supplies the
extension implication; it does not assert those geometric or local analytic
inputs, nor an unconditional graph estimate.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.GradedPrimitives

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fixed cutoff and all its finite jet constants, constructed before any
coefficient field or scale in `app:ch_response:eq:direct-envelope-profile`.
The open plateau contains the entire prescribed compact support. -/
theorem exists_fixed_cutoff_jet_profile [FiniteDimensional ℝ X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : X → ℝ) (V : Set X) (H : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn χ (fun _ ↦ 1) V ∧
      (∀ j, 0 ≤ H j) ∧ ∀ j x, ‖iteratedFDeriv ℝ j χ x‖ ≤ H j := by
  obtain ⟨χ, hχ, hrange, hc, hs, hp⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hK hU hKU
  choose H hH hjet using fun j ↦ hc.exists_bound_iteratedFDeriv hχ j
  refine ⟨χ, U ∩ interior {x | χ x = 1}, H, hχ, hrange, hc, hs,
    hU.inter isOpen_interior, ?_, inter_subset_left, ?_, hH, ?_⟩
  · intro x hx
    exact ⟨hKU hx, hp hx⟩
  · intro x hx
    have hx' : x ∈ {y | χ y = 1} := interior_subset hx.2
    exact hx'
  · intro j x
    exact hjet j j le_rfl x

/-- The actual global representative used in
`app:ch_response:eq:direct-envelope-profile`. Its defining formula needs no
regularity of the coefficient field away from the buffered joint domain. -/
def cutoffExtension (χ : X → ℝ) (f : X → E) : X → E :=
  fun x ↦ χ x • f x

/-- Smoothness of the actual cutoff extension from local smoothness alone
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_cutoffExtension {χ : X → ℝ} {f : X → E} {U : Set X}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ (cutoffExtension χ f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hs hx)))
  · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [cutoffExtension, hy]

omit [NormedSpace ℝ X] in
/-- A plateau gives neighborhood agreement, including at boundary points of
the complete selected support (`app:ch_response:eq:direct-envelope-profile`). -/
theorem cutoffExtension_eventuallyEq {χ : X → ℝ} (f : X → E) {V : Set X}
    (hV : IsOpen V) (hχ : EqOn χ (fun _ ↦ 1) V) {x : X} (hx : x ∈ V) :
    cutoffExtension χ f =ᶠ[𝓝 x] f := by
  filter_upwards [hV.mem_nhds hx] with y hy
  simp [cutoffExtension, hχ hy]

/-- Every ambient derivative agrees on a neighborhood of each point of the
plateau, as needed to identify literal coefficient expressions in
`app:ch_response:eq:direct-envelope-profile`. No differentiability premise is
needed for this locality statement. -/
theorem iteratedFDeriv_cutoffExtension_eventuallyEq {χ : X → ℝ} (f : X → E)
    {V : Set X} (hV : IsOpen V) (hχ : EqOn χ (fun _ ↦ 1) V)
    {x : X} (hx : x ∈ V) (j : ℕ) :
    iteratedFDeriv ℝ j (cutoffExtension χ f) =ᶠ[𝓝 x] iteratedFDeriv ℝ j f :=
  (cutoffExtension_eventuallyEq f hV hχ hx).iteratedFDeriv ℝ j

/-- The global jet estimate for the actual cutoff extension. Local jets are
used only on the closed support of the cutoff, including its shoulders.
`norm_jet_bilinear_le` splits one total order between the fixed cutoff and
the coefficient field; it therefore retains the reserve in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_cutoffExtension_le {χ : X → ℝ} {f : X → E} {U : Set X}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (H A : ℕ → ℝ)
    (hH : ∀ j, 0 ≤ H j) (hA : ∀ j, 0 ≤ A j)
    {L : ℝ} (hL : 1 ≤ L) (R N : ℕ)
    (hχjet : ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ H j)
    (hfjet : ∀ j ≤ N, ∀ x ∈ tsupport χ,
      ‖iteratedFDeriv ℝ j f x‖ ≤ A j * L ^ (j - R))
    {k : ℕ} (hk : k ≤ N) (x : X) :
    ‖iteratedFDeriv ℝ k (cutoffExtension χ f) x‖ ≤
      bilinearConstant (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
        H A k * L ^ (k - R) := by
  have hM : 0 ≤ bilinearConstant
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) H A k := by
    rw [bilinearConstant]
    apply mul_nonneg (norm_nonneg
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E))
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hH i)) (hA (k - i))
  by_cases hx : x ∈ tsupport χ
  · apply norm_jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ) hU
      (hχ.of_le (by simp : (N : ℕ∞ω) ≤ ∞)).contDiffOn
      (hf.of_le (by simp : (N : ℕ∞ω) ≤ ∞)) hk (hs hx) H A hH hA hL R
    · intro j hj
      exact (hχjet j (hj.trans hk) x).trans
        (le_mul_of_one_le_right (hH j) (one_le_pow₀ hL))
    · intro j hj
      exact hfjet j (hj.trans hk) x hx
  · have hz : iteratedFDeriv ℝ k (cutoffExtension χ f) x = 0 := by
      apply Function.notMem_support.mp
      intro hmem
      exact hx ((tsupport_smul_subset_left χ f)
        (support_iteratedFDeriv_subset k hmem))
    rw [hz, norm_zero]
    exact mul_nonneg hM (pow_nonneg (zero_le_one.trans hL) _)

/-- Construct reserve-preserving global representatives using a single fixed
cutoff. The cutoff, its plateau, and its finite jet profile precede the local
profile `A`; the resulting global profile `M` precedes the scale, reserve,
finite order, and coefficient field. Thus the same choices apply uniformly
to every frequency and coefficient family with the stated local bounds.

Consumer: the global primitive interface for
`NearCarrierSymbol.hasFullSourceSymbolBound_of_expression` and
`BranchRealization.exists_modifiedFullGraphL2_of_primitive_jets`, from
`app:ch_response:eq:direct-envelope-profile`. The parent must instantiate `K`
with the complete selected support and produce the local bounds on `U`. -/
theorem exists_reserve_preserving_cutoff_extension [FiniteDimensional ℝ X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : X → ℝ) (V : Set X) (H : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn χ (fun _ ↦ 1) V ∧
      (∀ j, 0 ≤ H j) ∧ (∀ j x, ‖iteratedFDeriv ℝ j χ x‖ ≤ H j) ∧
      ∀ A : ℕ → ℝ, (∀ j, 0 ≤ A j) →
        ∃ M : ℕ → ℝ, (∀ j, 0 ≤ M j) ∧
          ∀ (L : ℝ), 1 ≤ L → ∀ (R N : ℕ) (f : X → E),
            ContDiffOn ℝ ∞ f U →
            (∀ j ≤ N, ∀ x ∈ U, ‖iteratedFDeriv ℝ j f x‖ ≤ A j * L ^ (j - R)) →
            ContDiff ℝ ∞ (cutoffExtension χ f) ∧
            HasCompactSupport (cutoffExtension χ f) ∧
            tsupport (cutoffExtension χ f) ⊆ U ∧
            (∀ x ∈ V, cutoffExtension χ f =ᶠ[𝓝 x] f) ∧
            (∀ j x, x ∈ V → iteratedFDeriv ℝ j (cutoffExtension χ f) =ᶠ[𝓝 x]
              iteratedFDeriv ℝ j f) ∧
            (∀ j, EqOn (iteratedFDeriv ℝ j (cutoffExtension χ f))
              (iteratedFDeriv ℝ j f) V) ∧
            ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j (cutoffExtension χ f) x‖ ≤
              M j * L ^ (j - R) := by
  obtain ⟨χ, V, H, hχ, hrange, hc, hs, hV, hKV, hVU, hp, hH, hχjet⟩ :=
    exists_fixed_cutoff_jet_profile hK hU hKU
  refine ⟨χ, V, H, hχ, hrange, hc, hs, hV, hKV, hVU, hp, hH, hχjet, ?_⟩
  intro A hA
  let M := bilinearConstant
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) H A
  refine ⟨M, ?_, ?_⟩
  · intro j
    dsimp [M, bilinearConstant]
    apply mul_nonneg (norm_nonneg
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E))
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hH i)) (hA (j - i))
  · intro L hL R N f hf hfjet
    refine ⟨contDiff_cutoffExtension hU hχ hs hf, hc.smul_right,
      (tsupport_smul_subset_left χ f).trans hs,
      fun x hx ↦ cutoffExtension_eventuallyEq f hV hp hx,
      fun j x hx ↦ iteratedFDeriv_cutoffExtension_eventuallyEq f hV hp hx j,
      fun j x hx ↦ (iteratedFDeriv_cutoffExtension_eventuallyEq f hV hp hx j).eq_of_nhds,
      ?_⟩
    intro j hj x
    exact norm_jet_cutoffExtension_le hU hχ hs hf H A hH hA hL R N
      (fun i _ y ↦ hχjet i y) (fun i hi y hy ↦ hfjet i hi y (hs hy)) hj x

end JanetCartan.ResponseTransfer.GradedPrimitives
