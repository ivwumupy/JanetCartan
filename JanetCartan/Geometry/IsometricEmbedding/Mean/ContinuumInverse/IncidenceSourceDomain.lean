module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Nodes
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.IncidenceCover.FiniteDetection
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.IncidenceGeometry

/-!
# The original measurement ball lies in the retained source domain

The global incidence cover has a carrier over a singular cube-pencil direction.
Its original product-cell inclusion places the common measurement ball inside
the supplied working domain. This supplies `SelectedProductSource.h6U` without
shrinking or reselecting the measurement cutoff.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped InnerProductSpace

namespace JanetCartan.ContinuumInverse
open FrozenMenu ActualCarriers FullPhaseCharts.ActualComparison
open ContinuumRow ContinuumRow.CanonicalConic

/-- A finite incidence cover detecting the entire sphere contains a carrier:
the normalized cube node has a nonzero image-channel kernel. This supplies an
actual selected product cell for `SelectedProductSource.h6U`
(`app:ch_seed:prop:seed-frozen-menu`, `app:ch_background:prop:bg-normalized`). -/
theorem retained_incidence_channel_nonempty {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c : ℝ} (hc : 0 < c)
    (centers : Finset (IncidenceCenter D)) (ε : centers → ℝ)
    (hcover : sphere (0 : Euclidean n) 1 ⊆ ⋃ j : centers, ball j.1.1.2 (ε j))
    (hgram : ∀ j : centers, ∀ k ∈ ball j.1.1.2 (ε j), ∀ s : Euclidean n,
      c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil k) s‖ ^ 2 +
        ∑ a, inner ℝ (CubeCarrier.quadratic ((D.patches j.1.1.1 a).toFun
          (D.roots j.1.1.1 a k))) s ^ 2) :
    Nonempty ((j : centers) × Fin (D.patchCount j.1.1.1)) := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  let s := cubeVector a b
  have hs : s ≠ 0 := by
    intro h
    have he := cubeVector_norm_sq hab
    change ‖s‖ ^ 2 = (n : ℝ) at he
    rw [h, norm_zero, zero_pow (by decide)] at he
    have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let k := NormedSpace.normalize s
  have hk : k ∈ sphere (0 : Euclidean n) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize hs
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hk)
  have hkernel : ActualCarriers.imageChannel (cubePencil k) s = 0 := by
    apply (imageChannel_cubePencil_eq_zero_iff k s).2
    exact (cubePencil_node_mulVec_eq_zero_iff hn hab (inv_ne_zero (norm_ne_zero_iff.mpr hs))
      (fun i ↦ s i)).2 ⟨1, by simp [s]⟩
  by_contra hempty
  let : IsEmpty (Fin (D.patchCount j.1.1.1)) := ⟨fun q ↦ hempty ⟨⟨j, q⟩⟩⟩
  have hg := hgram j k hj s
  simp only [hkernel, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hg
  exact (not_le_of_gt (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hs)))) hg

/-- The original coefficient products and measured-radius inequalities imply
`SelectedProductSource.h6U` on the same measurement ball. The nonempty incidence
family is supplied by `retained_incidence_channel_nonempty`; no new radius or
analytic input is chosen (`app:ch_background:prop:bg-normalized`). -/
theorem retained_measured_source_ball_subset
    {n : ℕ} {ι : Type*} [Nonempty ι] {U : Set (Euclidean n)}
    (z : ι → Euclidean 3) {r a am R : ι → ℝ}
    (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 < a i)
    (V : ι → Set CarrierParameter)
    (houter : ∀ i, coefficientDomain (z i) (r i) (6 * a i) ⊆
      ball (0 : Euclidean n) (R i) ×ˢ V i)
    (hRU : ∀ i, ball (0 : Euclidean n) (R i) ⊆ U)
    (ham : ∀ i, am i ≤ a i) {μ : ℝ} (hμ : 0 < μ)
    (hμam : ∀ i, 6 * μ < am i) :
    closedBall (0 : Euclidean n) (6 * μ) ⊆ U := by
  classical
  let i : ι := Classical.choice ‹Nonempty ι›
  intro x hx
  have hx' : x ∈ ball (0 : Euclidean n) (6 * a i) :=
    closedBall_subset_ball (by linarith [ham i, hμam i]) hx
  exact hRU i ((houter i (show (x, (z i 0, spectatorCenter (z i))) ∈
    coefficientDomain (z i) (r i) (6 * a i) from
      ⟨hx', mem_ball_self (hr i), mem_ball_self (by have := ha i; positivity)⟩)).1)

end JanetCartan.ContinuumInverse
