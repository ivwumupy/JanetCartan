module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilRoot

/-!
# A characteristic root with the pencil coefficients as parameters

For `app:ch_regular_base:lem:characteristic-kernel`, solve the normalized
determinant jointly in the finite-dimensional coefficient value and spatial
covector. The branch and its conic band are chosen from the frozen pencil,
before choosing a variable coefficient field. In particular, no perturbed
pencil is required to vanish at the frozen covector.

The consumers are the fixed-domain root family and, subsequently, the primitive
root budgets for the two-time flow and `EvolutionIntegral.SymbolBudgets`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.RootFamily

open ActualCarriers

variable {n d : ℕ}

/-- The literal normalized determinant with the entire coefficient value as a
parameter (`app:ch_regular_base:lem:characteristic-kernel`). -/
def coefficientSymbol (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (z : ((Fin n → MetricTensor n) × Euclidean d) × ℝ) : ℝ :=
  determinant z.1.1 (e.symm (z.2, z.1.2)) *
    determinantNormalization (e.symm (z.2, z.1.2))

/-- Joint coefficient/covector smoothness, away from the zero covector
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffAt_coefficientSymbol
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {z : ((Fin n → MetricTensor n) × Euclidean d) × ℝ}
    (hξ : e.symm (z.2, z.1.2) ≠ 0) :
    ContDiffAt ℝ ∞ (coefficientSymbol e) z := by
  have hcoord : ContDiffAt ℝ ∞
      (fun w : ((Fin n → MetricTensor n) × Euclidean d) × ℝ ↦
        e.symm (w.2, w.1.2)) z :=
    e.symm.contDiff.contDiffAt.comp z (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  unfold coefficientSymbol
  apply (contDiff_determinant.contDiffAt.comp z
    (contDiffAt_fst.fst.prodMk hcoord)).mul
  exact (contDiffAt_determinantNormalization hξ).comp z hcoord

/-- The coefficient parameter is unchanged by radial extension; the literal
symbol has degree one (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem coefficientSymbol_homogeneous
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (A : Fin n → MetricTensor n) (η : Euclidean d) (τ : ℝ)
    {a : ℝ} (ha : 0 < a) :
    coefficientSymbol e ((A, a • η), a * τ) =
      a * coefficientSymbol e ((A, η), τ) := by
  exact adaptedNormalizedPencil_homogeneous (fun _ ↦ A) e (0, 0) η τ ha

/-- The transverse derivative is computed from the original determinant. This
is the actual implicit-function hypothesis, not a root assumption on nearby
coefficients (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasDerivAt_coefficientSymbol
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (A : Fin n → MetricTensor n) (η : Euclidean d) (τ : ℝ)
    (hξ : e.symm (τ, η) ≠ 0) (hp : determinant A (e.symm (τ, η)) = 0) :
    HasDerivAt (fun t ↦ coefficientSymbol e ((A, η), t))
      (determinantNormalization (e.symm (τ, η)) *
        fderiv ℝ (determinant A) (e.symm (τ, η)) (e.symm (1, 0))) τ := by
  exact hasDerivAt_adaptedNormalizedPencil (fun _ ↦ A) e (0, 0) η τ hξ hp

/-- Construct one branch for all nearby coefficient values. Its smoothness,
characteristic equation, scalar band, uniqueness, positive homogeneity and
uniform normalized transverse gap refer to the same function. All these
objects precede any variable field `Q`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_coefficientRoot_conic_patch
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (A₀ : Fin n → MetricTensor n) (η₀ : Euclidean d) (τ₀ : ℝ)
    (hξ : e.symm (τ₀, η₀) ≠ 0)
    (hp : determinant A₀ (e.symm (τ₀, η₀)) = 0)
    (ht : fderiv ℝ (determinant A₀) (e.symm (τ₀, η₀)) (e.symm (1, 0)) ≠ 0) :
    ∃ (ℓ : Euclidean d →L[ℝ] ℝ)
      (U : Set ((Fin n → MetricTensor n) × Euclidean d))
      (V : Set ℝ) (κ : ℝ) (H : (Fin n → MetricTensor n) × Euclidean d → ℝ),
      ℓ η₀ = 1 ∧ IsOpen U ∧ IsOpen V ∧ 0 < κ ∧
      (A₀, η₀) ∈ CharacteristicRoot.conicDomain ℓ U ∧ H (A₀, η₀) = τ₀ ∧
      ContDiffOn ℝ ∞ H (CharacteristicRoot.conicDomain ℓ U) ∧
      (∀ p ∈ CharacteristicRoot.conicDomain ℓ U,
        p.2 ≠ 0 ∧ determinant p.1 (e.symm (H p, p.2)) = 0 ∧
        (p, H p) ∈ CharacteristicRoot.conicBand ℓ U V ∧
        κ ≤ |determinantNormalization (e.symm (H p, p.2)) *
          fderiv ℝ (determinant p.1) (e.symm (H p, p.2)) (e.symm (1, 0))|) ∧
      (∀ p ∈ CharacteristicRoot.conicDomain ℓ U, ∀ a : ℝ, 0 < a →
        (p.1, a • p.2) ∈ CharacteristicRoot.conicDomain ℓ U ∧
        H (p.1, a • p.2) = a * H p) ∧
      (∀ z ∈ CharacteristicRoot.conicBand ℓ U V,
        determinant z.1.1 (e.symm (z.2, z.1.2)) = 0 ↔ H z.1 = z.2) ∧
      (∀ K : Set ((Fin n → MetricTensor n) × Euclidean d),
        IsCompact K → K ⊆ CharacteristicRoot.conicDomain ℓ U →
        ∃ δ > (0 : ℝ), cthickening δ ((fun p ↦ (p, H p)) '' K) ⊆
          CharacteristicRoot.conicBand ℓ U V) := by
  let S : Set (((Fin n → MetricTensor n) × Euclidean d) × ℝ) :=
    {z | e.symm (z.2, z.1.2) ≠ 0}
  have hS : IsOpen S := isOpen_ne.preimage
    (e.symm.continuous.comp (continuous_snd.prodMk continuous_fst.snd))
  have hf : ContDiffOn ℝ ∞ (coefficientSymbol e) S :=
    fun _ hz ↦ (contDiffAt_coefficientSymbol e hz).contDiffWithinAt
  let z₀ := ((A₀, η₀), τ₀)
  have hzS : z₀ ∈ S := hξ
  have hz : coefficientSymbol e z₀ = 0 := by simp [coefficientSymbol, z₀, hp]
  have hd : CharacteristicRoot.scalarDerivative (coefficientSymbol e) z₀ ≠ 0 := by
    rw [(CharacteristicRoot.hasDerivAt_scalar
      ((contDiffAt_coefficientSymbol e hξ).differentiableAt (by simp))).unique
        (hasDerivAt_coefficientSymbol e A₀ η₀ τ₀ hξ hp)]
    exact mul_ne_zero (determinantNormalization_pos hξ).ne' ht
  have hcoord : (τ₀, η₀) ≠ 0 := fun he ↦ hξ (by rw [he, map_zero])
  obtain ⟨ℓ, U, V, κ, hℓ, hU, hV, hκ, _, hzD, hbase, hH,
    hroot, hscale, huniq, hgap, hbuffer⟩ :=
    CharacteristicRoot.exists_conicRoot_patch hS hf
      (fun A η τ a ha ↦ coefficientSymbol_homogeneous e A η τ ha) hzS hz hd hcoord
  let H := CharacteristicRoot.conicRoot ℓ (hf.contDiffAt (hS.mem_nhds hzS)) hd
  have nonzero {p} (hp : p ∈ CharacteristicRoot.conicDomain ℓ U) : p.2 ≠ 0 := by
    intro he
    have hpos := hp.1
    simp [he] at hpos
  have coord_nonzero {p} (hp : p ∈ CharacteristicRoot.conicDomain ℓ U) (t : ℝ) :
      e.symm (t, p.2) ≠ 0 := by
    intro he
    have he' : (t, p.2) = 0 := e.symm.injective (by simpa using he)
    exact nonzero hp (congrArg Prod.snd he')
  have zero_iff {p} (hp : p ∈ CharacteristicRoot.conicDomain ℓ U) (t : ℝ) :
      coefficientSymbol e (p, t) = 0 ↔ determinant p.1 (e.symm (t, p.2)) = 0 :=
    mul_eq_zero.trans (or_iff_left (determinantNormalization_pos (coord_nonzero hp t)).ne')
  refine ⟨ℓ, U, V, κ, H, hℓ, hU, hV, hκ, hzD, hbase, hH, ?_, hscale, ?_, hbuffer⟩
  · intro p hp
    have hdet := (zero_iff hp (H p)).mp (hroot p hp).1
    obtain ⟨v, hv, hκv⟩ := hgap p hp
    rw [hv.unique (hasDerivAt_coefficientSymbol e p.1 p.2 (H p)
      (coord_nonzero hp _) hdet)] at hκv
    exact ⟨nonzero hp, hdet, (hroot p hp).2, hκv⟩
  · intro z hz
    exact (zero_iff hz.1 z.2).symm.trans (huniq z hz)

end JanetCartan.RegularSector.Characteristic.RootFamily
