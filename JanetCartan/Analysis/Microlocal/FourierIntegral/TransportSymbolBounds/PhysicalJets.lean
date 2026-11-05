module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.MaskedProfiles

/-!
# Physical mixed derivatives from normalized transport charts

The covector dilation changes only physical covector variables. Every derivative
in such a direction contributes exactly one inverse radius; spatial and source
derivatives contribute none. This is the normalization used for the symbol
seminorms in `app:ch_regular_base:eq:actual-one-high`. Regularity and radial
identities are required only on open buffered charts, not at the zero covector.
The position space may include both source and target positions.
-/

@[expose] public noncomputable section
open scoped BigOperators ContDiff
namespace JanetCartan.FourierIntegral
variable {X Ξ F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Physical frequency dilation, with positions unchanged, for
`app:ch_regular_base:eq:actual-one-high`. -/
def transportCovectorDilation (r : ℝ) : (X × Ξ) →L[ℝ] X × Ξ :=
  (ContinuousLinearMap.id ℝ X).prodMap (r • ContinuousLinearMap.id ℝ Ξ)

/-- The exact radius factor in a mixed derivative: `q` records precisely the
covector slots. This is consumed by the weighted transport seminorm estimate of
`app:ch_regular_base:eq:actual-one-high`. -/
theorem transportMixedJet_dilation (n : ℕ) (r : ℝ) {f : X × Ξ → F}
    {V : Set (X × Ξ)} (hV : IsOpen V) (hf : ContDiffOn ℝ n f V)
    (p : X × Ξ) (hp : (p.1, r • p.2) ∈ V)
    (q : Finset (Fin n)) (v : Fin n → X × Ξ)
    (hv : ∀ i, if i ∈ q then (v i).1 = 0 else (v i).2 = 0) :
    iteratedFDeriv ℝ n (fun z : X × Ξ ↦ f (z.1, r • z.2)) p v =
      r ^ q.card • iteratedFDeriv ℝ n f (p.1, r • p.2) v := by
  let L : (X × Ξ) →L[ℝ] X × Ξ := transportCovectorDilation r
  have hpre : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have hpL : L p ∈ V := hp
  have he := L.iteratedFDerivWithin_comp_right hf hV.uniqueDiffOn hpre.uniqueDiffOn hpL le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ hpre hp,
    iteratedFDerivWithin_of_isOpen _ hV hpL] at he
  have hdir (i : Fin n) : L (v i) = (if i ∈ q then r else 1) • v i := by
    specialize hv i
    by_cases hi : i ∈ q
    · simp only [hi, ite_true] at hv ⊢
      ext <;> simp [L, transportCovectorDilation, hv]
    · simp only [hi, ite_false] at hv ⊢
      ext <;> simp [L, transportCovectorDilation, hv]
  change iteratedFDeriv ℝ n (f ∘ L) p v = _
  rw [he, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp_rw [hdir]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Fintype.prod_ite_mem, Finset.prod_const]
  rfl

/-- Normalized joint bounds control every physical mixed derivative with its
correct covector weight. No order factor is charged to physical positions
(`app:ch_regular_base:eq:actual-one-high`). -/
theorem norm_transportMixedJet_weight_le (n : ℕ) {r : ℝ} (hr : 0 < r)
    {f : X × Ξ → F} {V : Set (X × Ξ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ n f V) (p : X × Ξ) (hp : (p.1, r • p.2) ∈ V)
    (q : Finset (Fin n)) (v : Fin n → X × Ξ)
    (hv : ∀ i, if i ∈ q then (v i).1 = 0 else (v i).2 = 0)
    (hvnorm : ∀ i, ‖v i‖ ≤ 1) :
    r ^ q.card * ‖iteratedFDeriv ℝ n f (p.1, r • p.2) v‖ ≤
      ‖iteratedFDeriv ℝ n (fun z : X × Ξ ↦ f (z.1, r • z.2)) p‖ := by
  have he := congrArg norm (transportMixedJet_dilation n r hV hf p hp q v hv)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _)] at he
  rw [← he]
  exact (ContinuousMultilinearMap.le_opNorm _ v).trans
    (by
      have hprod : (∏ i, ‖v i‖) ≤ 1 :=
        Finset.prod_le_one₀ (fun i _ ↦ norm_nonneg (v i)) (fun i _ ↦ hvnorm i)
      simpa using mul_le_mul_of_nonneg_left hprod
        (norm_nonneg (iteratedFDeriv ℝ n (fun z : X × Ξ ↦ f (z.1, r • z.2)) p)))

/-- Radial degree `-d` and a normalized joint bound imply the physical weighted
bound. For the transport construction, `d = 0` for the leading amplitude and
`d = 1` for the correction and complete remainder. The concrete radial formulas
are proved in `Frequency`; the masked bounds in `MaskedProfiles` supply the
normalized estimates. This is an assembly lemma, not an assumption of symbol
order (`app:ch_regular_base:eq:actual-one-high`). -/
theorem norm_transportMixedJet_of_radial_identity (n d : ℕ) {r : ℝ} (hr : 0 < r)
    {f b : X × Ξ → F} {V U : Set (X × Ξ)} (hV : IsOpen V) (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f V) (hb : ContDiffOn ℝ n b U)
    (hscale : Set.EqOn (fun z : X × Ξ ↦ f (z.1, r • z.2))
      (fun z ↦ (r⁻¹ ^ d) • b z) U)
    (p : X × Ξ) (hp : (p.1, r • p.2) ∈ V) (hpU : p ∈ U)
    (q : Finset (Fin n)) (v : Fin n → X × Ξ)
    (hv : ∀ i, if i ∈ q then (v i).1 = 0 else (v i).2 = 0)
    (hvnorm : ∀ i, ‖v i‖ ≤ 1) :
    r ^ (d + q.card) * ‖iteratedFDeriv ℝ n f (p.1, r • p.2) v‖ ≤
      ‖iteratedFDeriv ℝ n b p‖ := by
  have he := iteratedFDerivWithin_congr (𝕜 := ℝ) hscale hpU n
  rw [iteratedFDerivWithin_of_isOpen _ hU hpU,
    iteratedFDerivWithin_of_isOpen _ hU hpU,
    iteratedFDeriv_const_smul_apply' (hb.contDiffAt (hU.mem_nhds hpU))] at he
  have hbound := mul_le_mul_of_nonneg_left
    (norm_transportMixedJet_weight_le n hr hV hf p hp q v hv hvnorm) (pow_nonneg hr.le d)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.mpr hr) d)] at hbound
  rw [← mul_assoc (r ^ d) (r⁻¹ ^ d), ← mul_pow, mul_inv_cancel₀ hr.ne',
    one_pow, one_mul] at hbound
  simpa only [pow_add, mul_assoc] using hbound

end JanetCartan.FourierIntegral
