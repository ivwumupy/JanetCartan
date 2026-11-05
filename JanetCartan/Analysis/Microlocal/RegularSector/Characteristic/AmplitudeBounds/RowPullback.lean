module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.RowPullback.Potential

/-!
# Fixed-shift estimates for the literal two-time chart row

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, apply the
checked characteristic and physical row bounds to `c ∘ C`, deriving its
bounds from `c` and `Φ` under the exact identity `C = twoTimeProjection Φ`.
The initial-label norms are derived from `C.symm`. The common time center is
arbitrary; no orientation of the two times is imposed.

The reserve is two, independently of the differentiating order. Constants
precede all four inputs. These are conditional deductions for the parent
amplitude construction, not an unconditional existence result. The datum
producer is `AmplitudeBounds.RootData.exists_rootMinorData_cNorm_bounds`;
the potential producer is the physical calculus applied to the transported
primitives. The parent retains those instantiations and the final estimates
for `W₀`, `W₁`, and `P W₁`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds.RowPullback

variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

/-- Both characteristic and physical estimates for the existing chart row,
with fixed positive compact balls and open margins. The single-high right
side contains only `c,a₀,Φ,C.symm` at order `m + 2`. All low bounds have the
one fixed order three. No row, integral, exponential, initial-label or
forward-chart derivative bound is assumed.

The actual chart geometry supplies the two forward images, inverse image,
and target containment. The potential and datum producers named in the
module documentation must supply their low/high norms. This implication
is consumed by `jc-direct-characteristic-amplitude-budgets`, for
`app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_twoTimeRowTransport_cNorm_bounds (t₀ : ℝ) (p x : E × E)
    {ρ σ τ Rx R S : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hτ : 0 < τ)
    (hρRx : ρ < Rx) (hσR : σ < R) (hτS : τ < S) {M : ℝ} (hM : 0 ≤ M) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
      ∀ (c : TwoTimePoint E → ℝ) (a₀ : RootState E → ι → ℝ)
        (Φ : RootState E × ℝ → RootState E)
        (C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)),
      (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ →
      ContDiffOn ℝ ∞ c (ball (t₀, (t₀, x)) S) →
      ContDiffOn ℝ ∞ a₀ (ball (t₀, p) R) →
      ContDiffOn ℝ ∞ Φ (ball ((t₀, p), 0) (2 * R)) →
      ContDiffOn ℝ ∞ (C.symm : TwoTimePoint E → TwoTimePoint E)
        (ball (t₀, (t₀, x)) Rx) →
      MapsTo C (closedBall (t₀, (t₀, p)) σ) (closedBall (t₀, (t₀, x)) τ) →
      MapsTo C (ball (t₀, (t₀, p)) R) (ball (t₀, (t₀, x)) S) →
      MapsTo C.symm (closedBall (t₀, (t₀, x)) ρ) (closedBall (t₀, (t₀, p)) σ) →
      closedBall (t₀, (t₀, x)) ρ ⊆ C.target →
      cNorm (closedBall (t₀, (t₀, x)) τ) 3 c ≤ M →
      cNorm (closedBall (t₀, p) σ) 3 a₀ ≤ M →
      cNorm (closedBall ((t₀, p), 0) (2 * σ)) 3 Φ ≤ M →
      cNorm (closedBall (t₀, (t₀, x)) ρ) 3
        (C.symm : TwoTimePoint E → TwoTimePoint E) ≤ M →
      ∀ m,
        let H := 1 + cNorm (closedBall (t₀, (t₀, x)) τ) (m + 2) c +
          cNorm (closedBall (t₀, p) σ) (m + 2) a₀ +
          cNorm (closedBall ((t₀, p), 0) (2 * σ)) (m + 2) Φ +
          cNorm (closedBall (t₀, (t₀, x)) ρ) (m + 2)
            (C.symm : TwoTimePoint E → TwoTimePoint E)
        cNorm (closedBall (t₀, (t₀, p)) σ) m (rowTransport (c ∘ C) a₀) ≤ D m * H ∧
        cNorm (closedBall (t₀, (t₀, x)) ρ) m (twoTimeRowTransport C c a₀) ≤ D m * H := by
  obtain ⟨B, hB, hpot⟩ := exists_chartPotential_cNorm_bounds t₀ p x hσ hτ hσR hτS hM
  let L := ‖initialLabelLinear (E := E)‖
  have hL : 0 ≤ L := norm_nonneg _
  let N := B 1 * (1 + M + M) + M + L * M
  have hN : 0 ≤ N := add_nonneg (add_nonneg
    (mul_nonneg (hB 1).le (by linarith)) hM) (mul_nonneg hL hM)
  obtain ⟨A, hA, hchar⟩ := exists_rowTransport_shifted_cNorm_bounds
    (ι := ι) t₀ p hσ hσR hN
  obtain ⟨F, hF, hphys⟩ := exists_physicalRowTransport_shifted_cNorm_bounds
    (ι := ι) t₀ x p hρ hσ hρRx hσR hN
  refine ⟨fun m ↦ (A m + F m) * (2 + B m + L),
    fun m ↦ mul_pos (add_pos (hA m) (hF m)) (by linarith [hB m]), ?_⟩
  intro c a₀ Φ C hC hc ha hΦ hi hfmap hfopen himap htarget hcl hal hΦl hil m
  have hCf : ContDiffOn ℝ ∞ (C : TwoTimePoint E → TwoTimePoint E)
      (ball (t₀, (t₀, p)) R) := by
    rw [hC]
    exact contDiffOn_twoTimeProjection_ball t₀ p (hσ.trans hσR) hΦ
  have hcc : ContDiffOn ℝ ∞ (c ∘ C) (ball (t₀, (t₀, p)) R) :=
    hc.comp hCf hfopen
  have hY : ContDiffOn ℝ ∞ (twoTimeInitialLabel C) (ball (t₀, (t₀, x)) Rx) := hi.snd.snd
  have hp j := hpot c Φ C hC hc hΦ hfmap
    ((cNorm_mono_order (by omega : 1 ≤ 3)).trans hcl)
    ((cNorm_mono_order (by omega : 1 ≤ 3)).trans hΦl) j
  have hpl : cNorm (closedBall (t₀, (t₀, p)) σ) 1 (c ∘ C) ≤ N := by
    have hh : cNorm (closedBall (t₀, (t₀, p)) σ) 1 (c ∘ C) ≤
        B 1 * (1 + M + M) :=
      (hp 1).trans (mul_le_mul_of_nonneg_left (by dsimp; linarith) (hB 1).le)
    exact hh.trans (by dsimp [N]; nlinarith [mul_nonneg hL hM])
  have hal' : cNorm (closedBall (t₀, p) σ) 1 a₀ ≤ N :=
    ((cNorm_mono_order (by omega : 1 ≤ 3)).trans hal).trans (by
      dsimp [N]; nlinarith [mul_nonneg hL hM, mul_nonneg (hB 1).le (by linarith : 0 ≤ 1 + M + M)])
  have hy j := cNorm_twoTimeInitialLabel_le (t₀, (t₀, x)) hρRx hi j
  have hyl : cNorm (closedBall (t₀, (t₀, x)) ρ) 1 (twoTimeInitialLabel C) ≤ N :=
    (hy 1).trans ((mul_le_mul_of_nonneg_left
      ((cNorm_mono_order (by omega : 1 ≤ 3)).trans hil) hL).trans (by
        dsimp [N]; nlinarith [mul_nonneg (hB 1).le (by linarith : 0 ≤ 1 + M + M)]))
  have hmap : MapsTo (fun q ↦ (q.1, (q.2.1, twoTimeInitialLabel C q)))
      (closedBall (t₀, (t₀, x)) ρ) (closedBall (t₀, (t₀, p)) σ) := by
    intro q hq
    have he := C.right_inv (htarget hq)
    rw [hC] at he
    have ht := congrArg (fun z : TwoTimePoint E ↦ z.1) he
    have hs := congrArg (fun z : TwoTimePoint E ↦ z.2.1) he
    dsimp only [twoTimeProjection] at ht hs
    simpa only [twoTimeInitialLabel, ← ht, ← hs, Prod.mk.eta] using himap hq
  have hr := hchar (c ∘ C) a₀ hcc ha hpl hal' m
  have hf := hphys (c ∘ C) a₀ (twoTimeInitialLabel C) hcc ha hY hmap hpl hal' hyl m
  let H := 1 + cNorm (closedBall (t₀, (t₀, x)) τ) (m + 2) c +
    cNorm (closedBall (t₀, p) σ) (m + 2) a₀ +
    cNorm (closedBall ((t₀, p), 0) (2 * σ)) (m + 2) Φ +
    cNorm (closedBall (t₀, (t₀, x)) ρ) (m + 2)
      (C.symm : TwoTimePoint E → TwoTimePoint E)
  have hc0 := cNorm_nonneg (closedBall (t₀, (t₀, x)) τ) (m + 2) c
  have ha0 := cNorm_nonneg (closedBall (t₀, p) σ) (m + 2) a₀
  have hΦ0 := cNorm_nonneg (closedBall ((t₀, p), 0) (2 * σ)) (m + 2) Φ
  have hi0 := cNorm_nonneg (closedBall (t₀, (t₀, x)) ρ) (m + 2)
    (C.symm : TwoTimePoint E → TwoTimePoint E)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hpa : cNorm (closedBall (t₀, (t₀, p)) σ) m (c ∘ C) ≤ B m * H :=
    (hp m).trans (mul_le_mul_of_nonneg_left (by dsimp [H]; linarith) (hB m).le)
  have haa : cNorm (closedBall (t₀, p) σ) m a₀ ≤ H :=
    (cNorm_mono_order (by omega : m ≤ m + 2)).trans (by dsimp [H]; linarith)
  have hya : cNorm (closedBall (t₀, (t₀, x)) ρ) m (twoTimeInitialLabel C) ≤ L * H :=
    (hy m).trans (mul_le_mul_of_nonneg_left
      ((cNorm_mono_order (by omega : m ≤ m + 2)).trans (by dsimp [H]; linarith)) hL)
  have ht : 1 + cNorm (closedBall (t₀, (t₀, p)) σ) m (c ∘ C) +
      cNorm (closedBall (t₀, p) σ) m a₀ +
      cNorm (closedBall (t₀, (t₀, x)) ρ) m (twoTimeInitialLabel C) ≤
      (2 + B m + L) * H := by nlinarith
  have htn : 0 ≤ (2 + B m + L) * H := mul_nonneg (by linarith [hB m]) (by linarith)
  constructor
  · apply hr.trans
    have ht' : 1 + cNorm (closedBall (t₀, (t₀, p)) σ) m (c ∘ C) +
        cNorm (closedBall (t₀, p) σ) m a₀ ≤ (2 + B m + L) * H := by
      linarith [cNorm_nonneg (closedBall (t₀, (t₀, x)) ρ) m (twoTimeInitialLabel C)]
    exact ((mul_le_mul_of_nonneg_left ht' (hA m).le).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hF m).le) htn)).trans_eq
        (by ring)
  · apply hf.trans
    exact ((mul_le_mul_of_nonneg_left ht (hF m).le).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hA m).le) htn)).trans_eq
        (by ring)

/-- The specialization is exactly the published signed pencil row: the
potential is `lᵀPk` and the datum is `lᵀσ`, with no replacement row or
positivity premise (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem pencilSignedRow_eq_literal_transport {n d : ℕ}
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) :
    pencilSignedRow e Q B h Φ C r c σ =
      twoTimeRowTransport C (pencilTransportPotential e Q B h Φ C r c)
        (pencilSignedDatum e Q h r c σ) := rfl

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds.RowPullback
