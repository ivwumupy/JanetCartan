module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.CompactComposition
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.IntegralComparison
public import JanetCartan.Analysis.ODE.PositiveTransport.FlowSolution

/-!
# Finite-order dependence of the literal scalar formula

These are the integral, exponential and inverse-substitution steps required by
`app:ch_background:prop:bg-frame`. The initial scalar is fixed and smooth on
the original label buffer. Positivity is allowed but unnecessary for these
difference estimates; in particular they apply to the fixed initial scalar one.
No scalar-family continuity is assumed.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
open FullPhaseCharts.InverseEstimates HamiltonPhase.CompositionContinuity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Finite-order continuity of the actual characteristic integral/exponential
formula. The compact coefficient cylinder and threshold precede the varying
coefficient. The fixed initial scalar is smooth on the entire original label
buffer. Consumer: the inverse substitution in
`exists_cNorm_transportFromFootpoint_sub_lt` (`app:ch_waves:thm:leading`). -/
theorem exists_cNorm_characteristicTransport_sub_lt
    {p : E} {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    {K : Set (ℝ × E)} (hK : IsCompact K)
    (hKW : K ⊆ Ioo (-τ) τ ×ˢ ball p r)
    {c₀ : ℝ × E → ℝ} (hc₀ : ContDiffOn ℝ ∞ c₀ (Ioo (-τ) τ ×ˢ ball p r))
    {initial : E → ℝ} (hi : ContDiffOn ℝ ∞ initial (ball p r))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Set (ℝ × E), IsCompact L ∧ L ⊆ Ioo (-τ) τ ×ˢ ball p r ∧
      ∃ δ > 0, ∀ c : ℝ × E → ℝ,
        ContDiffOn ℝ ∞ c (Ioo (-τ) τ ×ˢ ball p r) →
        cNorm L m (c - c₀) < δ →
        cNorm K m (characteristicTransport c 0 initial -
          characteristicTransport c₀ 0 initial) < ε := by
  let W := Ioo (-τ) τ ×ˢ ball p r
  let J (c : ℝ × E → ℝ) (q : ℝ × E) := ∫ s in (0 : ℝ)..q.1, c (s, q.2)
  let f : E × ℝ → ℝ := fun z ↦ Real.exp (-z.2) * initial z.1
  have hf : ContDiffOn ℝ ∞ f (ball p r ×ˢ (univ : Set ℝ)) :=
    contDiffOn_snd.neg.exp.mul (hi.comp contDiffOn_fst (fun _ hz ↦ hz.1))
  have hJ (c : ℝ × E → ℝ) (hc : ContDiffOn ℝ ∞ c W) : ContDiffOn ℝ ∞ (J c) W :=
    contDiffOn_parametricIntervalIntegral isOpen_Ioo ordConnected_Ioo isOpen_ball hc
      ⟨neg_neg_of_pos hτ, hτ⟩
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_ball
  obtain ⟨Lexp, _, _, d, hd, hcomp⟩ := exists_cNorm_comp_sub_lt_with_buffer hK
    (isOpen_ball.prod isOpen_univ) hf
    (fun q hq ↦ (contDiffAt_snd.prodMk ((hJ c₀ hc₀).contDiffAt (hW.mem_nhds (hKW hq)))))
    (fun _ hq ↦ ⟨(hKW hq).2, mem_univ _⟩) m hε
  obtain ⟨L, hL, hLW, C, hC, hb⟩ := exists_cNorm_timeIntegral_sub_le hτ hr hK hKW m
  refine ⟨L, hL, hLW, d / C, div_pos hd hC, ?_⟩
  intro c hc hsmall
  have hpair : cNorm K m ((fun q ↦ (q.2, J c q)) - (fun q ↦ (q.2, J c₀ q))) ≤
      cNorm K m (J c - J c₀) := by
    have he : ((fun q : ℝ × E ↦ (q.2, J c q)) - (fun q ↦ (q.2, J c₀ q))) =
        (fun q ↦ ((0 : E), (J c - J c₀) q)) := by ext q <;> simp
    rw [he]
    have hh := cNorm_prodMk_le_on K hK m
      (fun _ _ ↦ (contDiffAt_const : ContDiffAt ℝ m (fun _ : ℝ × E ↦ (0 : E)) _))
      (fun q hq ↦ (((hJ c hc).sub (hJ c₀ hc₀)).contDiffAt
        (hW.mem_nhds (hKW hq))).of_le (by simp))
    change cNorm K m (fun q ↦ ((0 : E), (J c - J c₀) q)) ≤
      cNorm K m (0 : ℝ × E → E) + cNorm K m (J c - J c₀) at hh
    simpa only [cNorm_zero, zero_add] using hh
  apply hcomp f (fun q ↦ (q.2, J c q)) hf
    (fun q hq ↦ contDiffAt_snd.prodMk ((hJ c hc).contDiffAt (hW.mem_nhds (hKW hq))))
    (by simpa using hd)
  exact (hpair.trans (hb c c₀ hc hc₀)).trans_lt
    (by simpa only [mul_comm] using (lt_div_iff₀ hC).mp hsmall)

/-- The literal inverse-footpoint scalar depends on its characteristic
coefficient and inverse map in finite order. The threshold and compact
coefficient cylinder precede both varying inputs. All scalar comparisons are
proved from the formula, including its exponential; no amplitude continuity
is an input. Consumer: primitive potential and direction assembly for
`app:ch_background:prop:bg-frame`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_cNorm_transportFromFootpoint_sub_lt
    {p : E} {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    {K : Set (ℝ × E)} (hK : IsCompact K)
    {c₀ : ℝ × E → ℝ} (hc₀ : ContDiffOn ℝ ∞ c₀ (Ioo (-τ) τ ×ˢ ball p r))
    {initial : E → ℝ} (hi : ContDiffOn ℝ ∞ initial (ball p r))
    {Y₀ : ℝ × E → E} (hY₀ : ∀ q ∈ K, ContDiffAt ℝ ∞ Y₀ q)
    (hrange₀ : MapsTo (fun q ↦ (q.1, Y₀ q)) K (Ioo (-τ) τ ×ˢ ball p r))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Set (ℝ × E), IsCompact L ∧ L ⊆ Ioo (-τ) τ ×ˢ ball p r ∧
      ∃ δ > 0, ∀ (c : ℝ × E → ℝ) (Y : ℝ × E → E),
        ContDiffOn ℝ ∞ c (Ioo (-τ) τ ×ˢ ball p r) →
        (∀ q ∈ K, ContDiffAt ℝ ∞ Y q) →
        cNorm L m (c - c₀) < δ → cNorm K m (Y - Y₀) < δ →
        cNorm K m (transportFromFootpoint c 0 initial Y -
          transportFromFootpoint c₀ 0 initial Y₀) < ε := by
  have hs (c : ℝ × E → ℝ) (hc : ContDiffOn ℝ ∞ c (Ioo (-τ) τ ×ˢ ball p r)) :=
    contDiffOn_characteristicTransport isOpen_Ioo ordConnected_Ioo isOpen_ball hc hi
      (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨neg_neg_of_pos hτ, hτ⟩)
  obtain ⟨L₀, hL₀, hL₀W, d, hd, hcomp⟩ := exists_cNorm_comp_sub_lt_with_buffer hK
    (isOpen_Ioo.prod isOpen_ball) (hs c₀ hc₀)
    (fun q hq ↦ contDiffAt_fst.prodMk (hY₀ q hq)) hrange₀ m hε
  obtain ⟨L, hL, hLW, dc, hdc, hscalar⟩ := exists_cNorm_characteristicTransport_sub_lt
    hτ hr hL₀ hL₀W hc₀ hi m hd
  refine ⟨L, hL, hLW, min dc d, lt_min hdc hd, ?_⟩
  intro c Y hc hY hclosec hcloseY
  exact hcomp (characteristicTransport c 0 initial) (fun q ↦ (q.1, Y q)) (hs c hc)
    (fun q hq ↦ contDiffAt_fst.prodMk (hY q hq))
    (hscalar c hc (hclosec.trans_le (min_le_left _ _)))
    ((cNorm_timeGraph_sub_le hK m hY hY₀).trans_lt
      (hcloseY.trans_le (min_le_right _ _)))

/-- Primitive potential comparison and the two flow-map comparisons control
the SAME scalar formula. The required forward compact set is chosen before
the varying data and lies inside the original initial-label cylinder. Its
flow-map difference is supplied by the retained ODE comparison, not assumed
in the final coefficient implication. Source: `app:ch_waves:thm:leading` and
`app:ch_background:prop:bg-frame`. -/
theorem exists_cNorm_flowScalar_sub_lt
    {p : E} {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    {Ω L K : Set (ℝ × E)} (hΩ : IsOpen Ω) (hL : IsCompact L) (hLΩ : L ⊆ Ω)
    (hK : IsCompact K)
    {c₀ : ℝ × E → ℝ} (hc₀ : ContDiffOn ℝ ∞ c₀ Ω)
    {initial : E → ℝ} (hi : ContDiffOn ℝ ∞ initial (ball p r))
    {Φ₀ Y₀ : ℝ × E → E}
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀ (Ioo (-τ) τ ×ˢ ball p r))
    (hΦrange₀ : MapsTo (fun q ↦ (q.1, Φ₀ q)) (Ioo (-τ) τ ×ˢ ball p r) L)
    (hY₀ : ∀ q ∈ K, ContDiffAt ℝ ∞ Y₀ q)
    (hYrange₀ : MapsTo (fun q ↦ (q.1, Y₀ q)) K (Ioo (-τ) τ ×ˢ ball p r))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ KΦ : Set (ℝ × E), IsCompact KΦ ∧ KΦ ⊆ Ioo (-τ) τ ×ˢ ball p r ∧
      ∃ δ > 0, ∀ (c : ℝ × E → ℝ) (Φ Y : ℝ × E → E),
        ContDiffOn ℝ ∞ c Ω → ContDiffOn ℝ ∞ Φ (Ioo (-τ) τ ×ˢ ball p r) →
        MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ ball p r) L →
        (∀ q ∈ K, ContDiffAt ℝ ∞ Y q) →
        cNorm L m (c - c₀) < δ → cNorm KΦ m (Φ - Φ₀) < δ →
        cNorm K m (Y - Y₀) < δ →
        cNorm K m (transportFromFootpoint (flowTransportCoefficient c Φ) 0 initial Y -
          transportFromFootpoint (flowTransportCoefficient c₀ Φ₀) 0 initial Y₀) < ε := by
  let W := Ioo (-τ) τ ×ˢ ball p r
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_ball
  have hcoef₀ := contDiffOn_flowTransportCoefficient hc₀ hΦ₀
    (fun q hq ↦ hLΩ (hΦrange₀ hq))
  obtain ⟨KΦ, hKΦ, hKΦW, d, hd, hscalar⟩ := exists_cNorm_transportFromFootpoint_sub_lt
    hτ hr hK hcoef₀ hi hY₀ hYrange₀ m hε
  obtain ⟨dc, hdc, hcomp⟩ := exists_cNorm_comp_sub_lt hKΦ hL
    (fun q hq ↦ (hc₀.contDiffAt (hΩ.mem_nhds (hLΩ hq))).of_le (by simp))
    (fun q hq ↦ (contDiffAt_fst.prodMk
      (hΦ₀.contDiffAt (hW.mem_nhds (hKΦW hq)))).of_le (by simp))
    (hΦrange₀.mono_left hKΦW) hd
  refine ⟨KΦ, hKΦ, hKΦW, min dc d, lt_min hdc hd, ?_⟩
  intro c Φ Y hc hΦ hΦrange hY hcclose hΦclose hYclose
  apply hscalar (flowTransportCoefficient c Φ) Y
    (contDiffOn_flowTransportCoefficient hc hΦ (fun _ hq ↦ hLΩ (hΦrange hq))) hY
    ?_ (hYclose.trans_le (min_le_right _ _))
  apply hcomp c (fun q ↦ (q.1, Φ q))
    (fun q hq ↦ (hc.contDiffAt (hΩ.mem_nhds (hLΩ hq))).of_le (by simp))
    (fun q hq ↦ (contDiffAt_fst.prodMk
      (hΦ.contDiffAt (hW.mem_nhds (hKΦW hq)))).of_le (by simp))
    (hΦrange.mono_left hKΦW) (hcclose.trans_le (min_le_left _ _))
  exact (cNorm_timeGraph_sub_le hKΦ m
    (fun q hq ↦ hΦ.contDiffAt (hW.mem_nhds (hKΦW hq)))
    (fun q hq ↦ hΦ₀.contDiffAt (hW.mem_nhds (hKΦW hq)))).trans_lt
      (hΦclose.trans_le (min_le_left _ _))

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
