module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.GraphBounds

/-!
# Phase budgets for inverse graphs in the actual integration balls

The consumer is the actual full/transverse chart construction of
`app:ch_seed:prop:seed-phase-charts`. The Jacobian gap is needed only at
the inverse graph. The forward integration estimates are exactly those of
`InverseEstimates.PhaseBounds`, with the same sharp phase order `r+3`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.ActualEstimates
open InverseEstimates
variable {R D X E : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [FiniteDimensional ℝ R] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The forward map, inverse and their first epsilon derivatives have one-high joint `C^r`
bounds from primitive phase/carrier order `r+3`, as claimed in the final
paragraph of `app:ch_seed:prop:seed-phase-charts`.

`R` retains all spectators, including time and `z₁` for transverse charts;
`D` is the normalized inverted data space, and `X` is the physical space.
The output map `O` is a fixed coordinate identification. The low bounds are
primitive `C³` bounds, independent of `r`. Both integration segments and the
inverse image have explicit buffered containment. The data gap is required only on the inverse graph. The theorem concerns any
actual smooth inverse satisfying the displayed equation, not its existence. -/
theorem exists_carrierQuotient_inverse_epsilon_oneHigh_on_graph
    (a : ((R × D) × ℝ) × X) (b : ((R × D) × X) × E)
    (d : ((R × D) × ℝ) × X × X) (c : (ℝ × (R × X × X)) × D)
    {ρ σ τ κ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hτ : 0 < τ) (hκ : 0 < κ)
    {V : Set (R × D)} {I W T : Set ℝ} {U B : Set X} {Z : Set E}
    (hV : IsOpen V) (hI : IsOpen I) (hzero : (0 : ℝ) ∈ I)
    (hU : IsOpen U) (hZ : IsOpen Z) (hB : IsOpen B)
    (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (ha : closedBall a ρ ⊆ (V ×ˢ I) ×ˢ U)
    (hp : closedBall a.1.1 ρ ⊆ V)
    (hb : closedBall b σ ⊆ (V ×ˢ U) ×ˢ Z)
    (hd : closedBall d τ ⊆ (V ×ˢ I) ×ˢ B ×ˢ B)
    (hphysical : ∀ x ∈ B, ∀ y ∈ B, ∀ t ∈ T, y + t • (x - y) ∈ U)
    (hsegments : ∀ q ∈ closedBall d τ, ∀ t ∈ Icc (0 : ℝ) 1,
      jointPhysicalSegment t q ∈ closedBall a ρ)
    (hcoord : MapsTo quotientChartReindex (closedBall c κ) (closedBall d τ))
    (O : X →L[ℝ] D) (G : D ≃L[ℝ] D)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (r : ℕ) :
    ∃ C > (0 : ℝ), ∀ (S : ((R × D) × X) → E → ℝ) (z v : R × D → E)
      (g : (ℝ × (R × X × X)) × D → D) (J K : Set ((ℝ × (R × X × X)) × D)),
      ContDiffOn ℝ ∞ (Function.uncurry S) ((V ×ˢ U) ×ˢ Z) →
      ContDiffOn ℝ ∞ z V → ContDiffOn ℝ ∞ v V →
      cNorm (closedBall b σ) 3 (Function.uncurry S) ≤ N →
      cNorm (closedBall a.1.1 ρ) 3 z ≤ M →
      cNorm (closedBall a.1.1 ρ) 3 v ≤ M →
      (∀ p ∈ V, ∀ ε ∈ I, ∀ t ∈ W, z p + (t * ε) • v p ∈ Z) →
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (carrierSubstitution z v t)
        (closedBall a ρ) (closedBall b σ)) →
      IsOpen J → IsCompact K → K ⊆ J → ContDiffOn ℝ ∞ g J →
      MapsTo (inverseGraph g) K (closedBall c κ) →
      (∀ q ∈ K,
        ‖(G.symm : D →L[ℝ] D).comp
          (fderiv ℝ (fun u ↦ carrierQuotientChart O S z v (q.1, u)) (g q)) -
          ContinuousLinearMap.id ℝ D‖ ≤ 1 / 2) →
      (∀ q ∈ J, carrierQuotientChart O S z v (inverseGraph g q) = q.2) →
      (cNorm (closedBall c κ) r (carrierQuotientChart O S z v) +
        cNorm (closedBall c κ) r (fun q : (ℝ × (R × X × X)) × D ↦
          deriv (fun ε ↦ carrierQuotientChart O S z v ((ε,q.1.2),q.2)) q.1.1)) +
      (cNorm K r g + cNorm K r (fun q : (ℝ × (R × X × X)) × D ↦
        deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1)) ≤
        C * (1 + cNorm (closedBall b σ) (r + 3) (Function.uncurry S) +
          cNorm (closedBall a.1.1 ρ) (r + 3) z +
          cNorm (closedBall a.1.1 ρ) (r + 3) v) := by
  let L := quotientChartReindex (R := R) (D := D) (X := X)
  let Q := (V ×ˢ I) ×ˢ B ×ˢ B
  let Q' := L ⁻¹' Q
  have hQ : IsOpen Q := (hV.prod hI).prod (hB.prod hB)
  have hQ' : IsOpen Q' := hQ.preimage L.continuous
  have hc : closedBall c κ ⊆ Q' := fun q hq ↦ hd (hcoord hq)
  choose A hA hforward using fun k ↦ exists_cNorm_carrierQuotient_average_le_oneHigh
    a b d hρ hσ hτ hV hI hzero hU hZ hB hW hIW hT hIT ha hp hb hd
    hphysical hsegments k hM hN
  let H₀ := 1 + N + M + M
  let D₀ := ‖O‖ * 2 * A 1 * H₀
  have hA1 := (hA 1).le
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀, H₀]; positivity
  obtain ⟨C, hC, hinverse⟩ := exists_fiber_inverse_epsilon_cNorm_bound_on_graph
    c hκ hQ' hc G hD₀ r
  let A' := ‖O‖ * (r + 2 : ℝ) * A (r + 1)
  have hAr := (hA (r + 1)).le
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  refine ⟨(C + 2) * (1 + A'), by positivity, ?_⟩
  intro S z v g J K hS hz hv hSN hzM hvM hshift hmap hJ hK hKJ hg hrange hgap heq
  let Ψ : ((R × D) × ℝ) × X × X → X := fun q ↦
    averagedPhaseGradient (fun p x ↦
      phaseShiftQuotient S (p.1, x) (z p.1) (v p.1) p.2) q.1 q.2.1 q.2.2
  have hΨ : ContDiffOn ℝ ∞ Ψ Q :=
    contDiffOn_carrierQuotient_average hV hU hZ hI hW hIW hS hz hv hshift
      hB hT hIT hphysical
  have hΨL : ContDiffOn ℝ ∞ (Ψ ∘ L) Q' :=
    hΨ.comp L.contDiff.contDiffOn (fun _ h ↦ h)
  have hf : ContDiffOn ℝ ∞ (carrierQuotientChart O S z v) Q' :=
    hΨL.continuousLinearMap_comp O
  have hz2 : cNorm (closedBall a.1.1 ρ) 2 z ≤ M :=
    (cNorm_mono_order (by omega : 2 ≤ 3)).trans hzM
  have hv2 : cNorm (closedBall a.1.1 ρ) 2 v ≤ M :=
    (cNorm_mono_order (by omega : 2 ≤ 3)).trans hvM
  have hbnd (k : ℕ) : cNorm (closedBall c κ) k (carrierQuotientChart O S z v) ≤
      (‖O‖ * (k + 1 : ℝ) * A k) *
        (1 + cNorm (closedBall b σ) (k + 2) (Function.uncurry S) +
          cNorm (closedBall a.1.1 ρ) (k + 2) z +
          cNorm (closedBall a.1.1 ρ) (k + 2) v) := by
    have hh := hforward k S z v hS hz hv hSN hz2 hv2 hshift hmap
    have hl := cNorm_comp_contraction_le_on L norm_quotientChartReindex_le
      (isCompact_closedBall d τ) hQ hd hΨ hcoord k
    have ho := cNorm_postLinear_le_on (isCompact_closedBall c κ) k O
      (fun q hq ↦ (hΨL.contDiffAt (hQ'.mem_nhds (hc hq))).of_le (by simp))
    apply ho.trans
    apply (mul_le_mul_of_nonneg_left hl (norm_nonneg O)).trans
    calc
      _ ≤ ‖O‖ * ((k + 1 : ℝ) * (A k *
          (1 + cNorm (closedBall b σ) (k + 2) (Function.uncurry S) +
            cNorm (closedBall a.1.1 ρ) (k + 2) z +
            cNorm (closedBall a.1.1 ρ) (k + 2) v))) := by gcongr
      _ = _ := by ring
  have hlow : cNorm (closedBall c κ) 1 (carrierQuotientChart O S z v) ≤ D₀ := by
    apply (hbnd 1).trans
    dsimp only [D₀]
    norm_num only [Nat.cast_one, Nat.reduceAdd, show (1 : ℝ) + 1 = 2 by norm_num]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (add_le_add (add_le_add (le_refl 1) hSN) hzM) hvM
  have hi := hinverse (carrierQuotientChart O S z v) g J K hJ hK hKJ hf hg
    hlow hrange hgap heq
  have heps := cNorm_deriv_epsilon_le hQ' hf (isCompact_closedBall c κ) hc r
  have hmono := cNorm_mono_order (f := carrierQuotientChart O S z v)
    (s := closedBall c κ) (Nat.le_succ r)
  have hh := hbnd (r + 1)
  simp only [show r + 1 + 2 = r + 3 by omega, Nat.cast_add, Nat.cast_one] at hh
  let H := 1 + cNorm (closedBall b σ) (r + 3) (Function.uncurry S) +
    cNorm (closedBall a.1.1 ρ) (r + 3) z + cNorm (closedBall a.1.1 ρ) (r + 3) v
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg (closedBall b σ) (r + 3) (Function.uncurry S),
      cNorm_nonneg (closedBall a.1.1 ρ) (r + 3) z,
      cNorm_nonneg (closedBall a.1.1 ρ) (r + 3) v]
  have hh' : cNorm (closedBall c κ) (r + 1) (carrierQuotientChart O S z v) ≤ A' * H := by
    convert hh using 1
    dsimp [A', H]
    ring
  have hforward : cNorm (closedBall c κ) r (carrierQuotientChart O S z v) +
      cNorm (closedBall c κ) r (fun q : (ℝ × (R × X × X)) × D ↦
        deriv (fun ε ↦ carrierQuotientChart O S z v ((ε,q.1.2),q.2)) q.1.1) ≤
      2 * (A' * H) := by linarith
  have hinv : cNorm K r g + cNorm K r (fun q : (ℝ × (R × X × X)) × D ↦
      deriv (fun ε ↦ g ((ε,q.1.2),q.2)) q.1.1) ≤ C * ((1 + A') * H) := by
    apply hi.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    nlinarith
  calc
    _ ≤ 2 * (A' * H) + C * ((1 + A') * H) := add_le_add hforward hinv
    _ ≤ (C + 2) * (1 + A') * H := by nlinarith

end JanetCartan.FullPhaseCharts.ActualEstimates
