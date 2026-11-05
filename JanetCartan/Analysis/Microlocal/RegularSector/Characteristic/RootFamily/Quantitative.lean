module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RootFamily.Domains
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhysicalCoordinates

/-!
# Uniform actual pencil roots with primitive quantitative bounds

For `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`, a fixed regular frozen pencil and
its original adjugate entry produce one actual root family. The coordinate
split is selected from the frozen transverse derivative. The coefficient
neighborhood, physical and frequency domains, root band, root range, gaps,
nested state buffers and seminorm constants all precede the variable field.

The original physical coefficient `Q` supplies every analytic input: joint
root bounds have reserve zero and contain a single high `cNorm` of `Q`.
Finite-low and graded bounds are consequences of the same estimates. The
root solves the perturbed characteristic equation, retains one branch along
positive rays, and preserves the originally selected adjugate entry.

Consumers: the actual two-time flow family, the root and minor inputs of
`AmplitudeBounds.exists_rootMinorData_cNorm_bounds`, and ultimately the
primitive phase/amplitude budgets in `EvolutionIntegral.SymbolBudgets`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.RootFamily

open ActualCarriers AmplitudeBounds

variable {d : ℕ}

/-- Construct the actual uniform family from a regular frozen pencil, retaining
the original minor. The same root has all geometric properties and joint
single-high bounds from the original coefficient on the prescribed physical
ball. The fixed derivative reserve is zero; no root, reciprocal, flow, or
amplitude bound is assumed. The outer state ball contains the nested balls
of radii `ρ` and `2 * ρ` (`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_coordinateSplit_uniform_fieldRoot
    {Ω : Set (Euclidean (d + 1))} (hΩ : IsOpen Ω)
    (x : Euclidean (d + 1)) {R : ℝ} (hR : 0 < R) (hKΩ : closedBall x R ⊆ Ω)
    (A₀ : Fin (d + 1) → MetricTensor (d + 1)) (ξ : Euclidean (d + 1))
    (r c : Fin (d + 1)) (hξ : ξ ≠ 0) (hp : determinant A₀ ξ = 0)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0)
    (hm : (pencil A₀ ξ).adjugate r c ≠ 0) :
    ∃ i : Fin (d + 1),
      let e := coordinateSplit i
      let η₀ := (e ξ).2
      let z : RootState (Euclidean d) := ((e x).1, ((e x).2, η₀))
      ∃ (ℓ : Euclidean d →L[ℝ] ℝ)
        (U : Set ((Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d)) (V : Set ℝ)
        (H : (Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d → ℝ),
        ∃ ε > (0 : ℝ), ∃ κ > 0, ∃ μ > 0, ∃ ν > 0, ∃ G > 0, ∃ δ > 0,
        ∃ ρ > 0, ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
        fderiv ℝ (determinant A₀) ξ (e.symm (1, 0)) ≠ 0 ∧
        ℓ η₀ = 1 ∧ IsOpen U ∧ IsOpen V ∧ H (A₀, η₀) = (e ξ).1 ∧
        ContDiffOn ℝ ∞ H (CharacteristicRoot.conicDomain ℓ U) ∧
        closedBall (A₀, η₀) (3 * ε) ⊆ CharacteristicRoot.conicDomain ℓ U ∧
        cthickening δ ((fun p ↦ (p, H p)) '' closedBall (A₀, η₀) (3 * ε)) ⊆
          CharacteristicRoot.conicBand ℓ U V ∧
        IsOpen (fieldDomain e Ω ℓ η₀ ε) ∧
        (∀ y ∈ Ω, ((e y).1, ((e y).2, η₀)) ∈ fieldDomain e Ω ℓ η₀ ε) ∧
        (∀ w ∈ closedBall z (3 * ρ),
          w ∈ fieldDomain e Ω ℓ η₀ ε ∧
          rootPhysicalPosition e w ∈ closedBall x R ∧
          w.2.2 ∈ closedBall η₀ ε ∧ (1 / 2 : ℝ) ≤ ℓ w.2.2) ∧
        ∀ Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1),
          ContDiffOn ℝ ∞ Q Ω → MapsTo Q Ω (closedBall A₀ ε) →
          let h := fieldRoot e Q H
          let D := fieldDomain e Ω ℓ η₀ ε
          let K := closedBall z (3 * ρ)
          ContDiffOn ℝ ∞ h D ∧
          (∀ w ∈ D, ∀ a : ℝ, 0 < a → h (w.1, (w.2.1, a • w.2.2)) = a * h w) ∧
          (∀ m, cNorm K m h ≤ C m * (1 + cNorm (closedBall x R) m Q)) ∧
          (∀ (R₀ : ℕ) (M : ℝ), cNorm (closedBall x R) R₀ Q ≤ M →
            ∀ j ≤ R₀, cNorm K j h ≤ C R₀ * (1 + M)) ∧
          (∀ (a : ℕ → ℝ) (R₀ : ℕ) (T : ℝ), 1 ≤ T →
            (∀ m, cNorm (closedBall x R) m Q ≤ a m * T ^ (m - R₀)) →
            ∀ m, cNorm K m h ≤ (C m * (1 + a m)) * T ^ (m - R₀)) ∧
          (∀ w ∈ K, (rootPencil e Q h w).det = 0 ∧
            (1 / 2 : ℝ) ^ d * μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
            (1 / 2 : ℝ) ^ (2 * d) * ν ≤
              |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) ∧
          ∀ w ∈ D,
            let p := (Q (e.symm (w.1, w.2.1)), w.2.2)
            let pNorm := normalizedFieldParameter e Q ℓ w
            let PNorm := coefficientRootPencil e H pNorm
            w.2.2 ≠ 0 ∧ (rootPencil e Q h w).det = 0 ∧
            (p, h w) ∈ CharacteristicRoot.conicBand ℓ U V ∧
            (∀ τ, (p, τ) ∈ CharacteristicRoot.conicBand ℓ U V →
              (determinant p.1 (e.symm (τ, p.2)) = 0 ↔ h w = τ)) ∧
            κ ≤ |determinantNormalization (e.symm (h w, w.2.2)) *
              fderiv ℝ (determinant p.1) (e.symm (h w, w.2.2)) (e.symm (1, 0))| ∧
            h w = ℓ w.2.2 * H pNorm ∧ |h w| ≤ ℓ w.2.2 * G ∧
            rootPencil e Q h w = ℓ w.2.2 • PNorm ∧
            μ ≤ |PNorm.adjugate r c| ∧
            ν ≤ |minorTransportCoefficient PNorm (rootTimeCoefficient e Q w) r c| ∧
            (ℓ w.2.2) ^ d * μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
            (ℓ w.2.2) ^ (2 * d) * ν ≤
              |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c| := by
  obtain ⟨i, hi⟩ := exists_coordinateSplit_transverse (fderiv ℝ (determinant A₀) ξ) hreg
  let e := coordinateSplit i
  let η₀ := (e ξ).2
  let z : RootState (Euclidean d) := ((e x).1, ((e x).2, η₀))
  have heξ : e.symm ((e ξ).1, η₀) = ξ := e.symm_apply_apply ξ
  obtain ⟨ℓ, U, V, H, ε, hε, κ, hκ, μ, hμ, ν, hν, G, hG, δ, hδ,
    hℓ, hU, hV, hbase, hH, hsub, hbuffer, hD, hcent, hfields⟩ :=
    exists_uniform_fieldRoot e hΩ A₀ η₀ (e ξ).1 r c
      (by simpa only [heξ] using hξ) (by simpa only [heξ] using hp)
      (by simpa only [heξ] using hi) (by simpa only [heξ] using hm)
  obtain ⟨ρ, hρ, hstate⟩ := exists_fieldRoot_buffers e hΩ x hR hKΩ ℓ η₀ hℓ hε
  obtain ⟨C, hC, hbounds⟩ := exists_fieldRoot_cNorm_bounds e z
    (show 0 < 3 * ρ by positivity) x R A₀ η₀ hε H
    (fun p hp ↦ hH.contDiffAt
      ((CharacteristicRoot.isOpen_conicDomain ℓ hU).mem_nhds (hsub hp)))
    (fun w hw ↦ (hstate w hw).2.1) (fun w hw ↦ (hstate w hw).2.2.1)
  refine ⟨i, ℓ, U, V, H, ε, hε, κ, hκ, μ, hμ, ν, hν, G, hG, δ, hδ,
    ρ, hρ, C, hC, hi, hℓ, hU, hV, hbase, hH, hsub, hbuffer, hD, hcent, hstate, ?_⟩
  intro Q hQ hQrange
  obtain ⟨hh, hhom, hgeometry⟩ := hfields Q hQ hQrange
  have hb := hbounds Ω hΩ hKΩ Q hQ (fun y hy ↦ hQrange (hKΩ hy))
  refine ⟨hh, hhom, hb, ?_, ?_, ?_, ?_⟩
  · intro R₀ M hQM j hj
    exact (cNorm_mono_order hj).trans ((hb R₀).trans
      (mul_le_mul_of_nonneg_left (by linarith) (hC R₀).le))
  · intro a R₀ T hT hgrade m
    apply (hb m).trans
    calc
      C m * (1 + cNorm (closedBall x R) m Q) ≤
          C m * ((1 + a m) * T ^ (m - R₀)) := by
        apply mul_le_mul_of_nonneg_left _ (hC m).le
        nlinarith [hgrade m, one_le_pow₀ hT (n := m - R₀)]
      _ = (C m * (1 + a m)) * T ^ (m - R₀) := by ring
  · intro w hw
    obtain ⟨hwD, _, _, hrad⟩ := hstate w hw
    obtain ⟨_, hdet, _, _, _, _, _, _, _, _, hmrad, htrad⟩ := hgeometry w hwD
    refine ⟨hdet, ?_, ?_⟩
    · have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hrad d
      exact (mul_le_mul_of_nonneg_right hpow hμ.le).trans (by simpa using hmrad)
    · have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hrad (2 * d)
      exact (mul_le_mul_of_nonneg_right hpow hν.le).trans (by simpa using htrad)
  · simpa only [Nat.add_sub_cancel] using hgeometry

end JanetCartan.RegularSector.Characteristic.RootFamily
