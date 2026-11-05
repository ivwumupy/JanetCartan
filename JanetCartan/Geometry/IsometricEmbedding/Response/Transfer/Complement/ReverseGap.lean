module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ReverseGap.Estimates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ReverseGap.Geometry

/-!
# Uniform reverse-source gap on the complete carrier complement

The complete-complement paragraph of
`app:ch_response:thm:response-literal-transfer` uses the physical source variable
`x` for the reverse graph. This module proves its gap conditional on a supplied
phase and quantitative geometry on the **entire buffered active conic chart**.
The phase-geometry producer must still construct that chart, prove its uniform
annular bounds and full inverse estimate, and place all actual amplitude supports
(including angular/radial shoulders) there. No local determinant condition is
silently promoted to a global estimate.

The constants precede every parameter, source point, carrier, frequency and
perturbation. Physical supports `K` may be arbitrary subsets of the open physical
chart; in particular the conclusion holds uniformly on supplied compact supports.
The compact carrier set is separated from zero. Smoothness is used only through
one spatial derivative. Covectors retain the physical Fourier convention of
`phaseIncrement` and `FourierIntegral.graphOperator`, without a `2π` rescaling.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace JanetCartan.ResponseTransfer

/-- Uniform constants for the full reverse-source gap in
`app:ch_response:thm:response-literal-transfer`. `P` retains all compact-family
parameters; no topology on these labels is needed once the quantitative inputs
are uniform. `D` includes the full conic selector shoulders. The inverse bound
is an input on every pair in `D`, independently of the carrier exclusion.
It can be supplied by `reverseSource_inverse_bound_of_derivative_gap`.

This is a conditional deduction for `jc-response-complement` and
`jc-compatible-phase-geometry`, not construction of the Hamilton phase. -/
theorem reverseSource_gap_uniform {n : ℕ} {I : Type*}
    (S : I → Euclidean n → Euclidean n → ℝ)
    {P : Set I} {K U Z D : Set (Euclidean n)}
    (hU : IsOpen U) (hKU : K ⊆ U) (hZ : IsCompact Z)
    (hZ0 : ∀ ζ ∈ Z, ζ ≠ 0) (hZD : Z ⊆ D)
    (hcone : ∀ η ∈ D, ∀ ρ : ℝ, 0 < ρ → ρ • η ∈ D)
    (hS : ∀ p ∈ P, ∀ η ∈ D, DifferentiableOn ℝ (fun x ↦ S p x η) U)
    (hhom : ∀ p ∈ P, ∀ x ∈ U, ∀ η ∈ D, ∀ ρ : ℝ, 0 < ρ →
      S p x (ρ • η) = ρ * S p x η)
    {m M L c : ℝ} (hm : 0 < m) (hM : 0 < M) (hL : 0 < L) (hc : 0 < c)
    (hannular : ∀ p ∈ P, ∀ x ∈ K, ∀ η ∈ D,
      m * ‖η‖ ≤ ‖gradient (fun y ↦ S p y η) x‖ ∧
      ‖gradient (fun y ↦ S p y η) x‖ ≤ M * ‖η‖)
    (hinverse : ∀ p ∈ P, ∀ x ∈ K, ∀ u ∈ D, ∀ v ∈ D,
      ‖u - v‖ ≤ L * ‖gradient (fun y ↦ S p y u) x -
        gradient (fun y ↦ S p y v) x‖) :
    ∃ d > 0, ∃ ε > 0, ∀ p ∈ P, ∀ x ∈ K, ∀ ζ ∈ Z, ∀ η ∈ D,
      ∀ ρ : ℝ, 0 < ρ → ∀ θ : Euclidean n,
      c * ρ ≤ ‖η - ρ • ζ‖ → ‖θ‖ ≤ ε * ρ →
      d * (ρ + ‖η‖) ≤
        ‖ρ • gradient (fun y ↦ S p y ζ) x - gradient (fun y ↦ S p y η) x + θ‖ := by
  obtain ⟨zlo, hzlo, hlo⟩ : ∃ zlo > 0, ∀ ζ ∈ Z, zlo ≤ ‖ζ‖ := by
    rcases Z.eq_empty_or_nonempty with he | hn
    · exact ⟨1, zero_lt_one, by simp [he]⟩
    · obtain ⟨ζ, hζ, hmin⟩ := hZ.exists_isMinOn hn continuous_norm.continuousOn
      exact ⟨‖ζ‖, norm_pos_iff.mpr (hZ0 ζ hζ), hmin⟩
  obtain ⟨zhi, hzhi, hhi⟩ := hZ.isBounded.exists_pos_norm_le
  let a := m * zlo
  let b := M * zhi
  let R := 1 + 2 * b / m
  have ha : 0 < a := mul_pos hm hzlo
  have hb : 0 < b := mul_pos hM hzhi
  have hR : 1 ≤ R := by
    have : 0 ≤ 2 * b / m := by positivity
    dsimp [R]
    linarith
  have hbR : 2 * b ≤ m * R := by
    have heq : m * R = m + 2 * b := by dsimp [R]; field_simp
    rw [heq]
    linarith
  let d := reverseGapConstant a m L c R / 2
  have hd : 0 < d := div_pos (reverseGapConstant_pos ha hm hL hc hR) (by norm_num)
  refine ⟨d, hd, d, hd, ?_⟩
  intro p hp x hx ζ hζ η hη ρ hρ θ hfar hθ
  have hζD := hZD hζ
  have hcentral : a ≤ ‖gradient (fun y ↦ S p y ζ) x‖ ∧
      ‖gradient (fun y ↦ S p y ζ) x‖ ≤ b := by
    constructor
    · exact (mul_le_mul_of_nonneg_left (hlo ζ hζ) hm.le).trans
        (hannular p hp x hx ζ hζD).1
    · exact (hannular p hp x hx ζ hζD).2.trans
        (mul_le_mul_of_nonneg_left (hhi ζ hζ) hM.le)
  have hhomGrad := sourceGradient_smul_of_phase_homogeneous
    (S := S p) (x := x) (ζ := ζ) (ρ := ρ)
    ((hS p hp ζ hζD x (hKU hx)).differentiableAt (hU.mem_nhds (hKU hx)))
    (Filter.eventually_of_mem (hU.mem_nhds (hKU hx))
      (fun y hy ↦ hhom p hp y hy ζ hζD ρ hρ))
  exact reverseSource_gap_of_chart_bounds
    (F := fun η ↦ gradient (fun y ↦ S p y η) x)
    (D := D) (a := a) (b := b) (m := m) (M := M) (L := L) (c := c) (R := R)
    (ρ := ρ) (ζ := ζ) (η := η) (θ := θ) ha hm hL hc hR hbR hρ
    (hcone ζ hζD ρ hρ) hη hhomGrad hcentral (hannular p hp x hx η hη)
    (hinverse p hp x hx) hfar hθ

end JanetCartan.ResponseTransfer
