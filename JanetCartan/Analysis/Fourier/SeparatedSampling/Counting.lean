module

public import JanetCartan.Analysis.Fourier.SeparatedSampling.Weights
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Counting shifted samples on a bounded three-parameter patch

Explicit finite sets and constants for `app:ch_waves:thm:sampling`.
The enumerations include exactly the nonzero weights, for every allowed shift.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.SeparatedSampling

/-- Integer coordinate cube used to enumerate the samples of
`app:ch_waves:thm:sampling`. -/
def integerCube (N : ℕ) : Finset Lattice :=
  Finset.Icc (fun _ ↦ -(N : ℤ)) (fun _ ↦ (N : ℤ))

/-- Membership in the integer coordinate cube. -/
theorem mem_integerCube {N : ℕ} {q : Lattice} :
    q ∈ integerCube N ↔ ∀ i, |q i| ≤ (N : ℤ) := by
  simp only [integerCube, Finset.mem_Icc, Pi.le_def, abs_le]
  exact ⟨fun h i ↦ ⟨h.1 i, h.2 i⟩,
    fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

/-- Exact integer cube count in three parameters. -/
theorem card_integerCube (N : ℕ) : (integerCube N).card = (2 * N + 1) ^ 3 := by
  have he : (N : ℤ) + 1 - -(N : ℤ) = (2 * N + 1 : ℕ) := by push_cast; ring
  have hc : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [Int.card_Icc, he, Int.toNat_natCast]
  simp only [integerCube, Pi.card_Icc, hc, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- Uniform number of possible offsets per block in `app:ch_waves:thm:sampling`. -/
def nodesPerBlock (p : ℕ) : ℕ := (2 * (p + 2) + 1) ^ 3

/-- A finite enumeration of the nonzero nodes in a single block. -/
def blockSamples (p : ℕ) (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : Lattice → Point) (q : Lattice) : Finset Lattice :=
  (integerCube (p + 2)).filter fun m ↦ weight ψ w h U (q, m) ≠ 0

/-- The mesh-dependent block enumeration radius. -/
def blockCutoff (p : ℕ) (B h : ℝ) : ℕ := ⌈(B + (p : ℝ) + 2) / h⌉₊

/-- All literal nonzero samples on a patch (`app:ch_waves:thm:sampling`). -/
def samples (p : ℕ) (B : ℝ) (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : Lattice → Point) : Finset Sample :=
  (integerCube (blockCutoff p B h) ×ˢ integerCube (p + 2)).filter
    fun a ↦ weight ψ w h U a ≠ 0

/-- Fixed block-count coefficient; independent of shifts, mesh, and accuracy. -/
def blockCountConstant (p : ℕ) (B : ℝ) : ℝ := (2 * (B + (p : ℝ) + 2) + 3) ^ 3

/-- Fixed sample-count coefficient in `app:ch_waves:thm:sampling`. -/
def countConstant (p : ℕ) (B : ℝ) : ℝ :=
  blockCountConstant p B * nodesPerBlock p

variable {p : ℕ} {w : ℝ → ℝ} {W : ℝ} {ψ : Point → ℝ} {B P : ℝ}
  {h : ℝ} {U : Lattice → Point}

/-- A block enumeration contains exactly the nonzero weights, with no omission. -/
theorem mem_blockSamples_iff (hw : WindowBounds p w W) (hh : 0 < h)
    (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h) {q m : Lattice} :
    m ∈ blockSamples p ψ w h U q ↔ weight ψ w h U (q, m) ≠ 0 := by
  simp only [blockSamples, Finset.mem_filter]
  exact ⟨And.right, fun ha ↦ ⟨mem_integerCube.mpr (by
    intro i
    simpa using offset_bound hw hh hU ha i), ha⟩⟩

/-- Every block has at most a fixed number of samples
(`app:ch_waves:thm:sampling`), even before any estimates on the shifts. -/
theorem card_blockSamples_le (p : ℕ) (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : Lattice → Point) (q : Lattice) :
    (blockSamples p ψ w h U q).card ≤ nodesPerBlock p := by
  exact (Finset.card_filter_le _ _).trans_eq (card_integerCube _)

/-- Every nonzero weight belongs to the finite global enumeration. -/
theorem mem_samples_iff (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 < h) (hh₁ : h ≤ 1) (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h)
    {a : Sample} : a ∈ samples p B ψ w h U ↔ weight ψ w h U a ≠ 0 := by
  simp only [samples, Finset.mem_filter, Finset.mem_product]
  refine ⟨And.right, fun ha ↦ ⟨⟨?_, ?_⟩, ha⟩⟩
  · apply mem_integerCube.mpr
    intro i
    have hi := (block_coordinate_bound hw hψ hh hh₁ ha i).trans
      (Nat.le_ceil ((B + (p : ℝ) + 2) / h))
    exact_mod_cast hi
  · apply mem_integerCube.mpr
    intro i
    simpa using offset_bound hw hh hU ha i

/-- The side length of the enumerating cube has order `h⁻¹`, with a fixed constant. -/
theorem blockCutoff_width_mul_le (hB : 0 ≤ B) (hh : 0 < h) (hh₁ : h ≤ 1) :
    (2 * (blockCutoff p B h : ℝ) + 1) * h ≤ 2 * (B + (p : ℝ) + 2) + 3 := by
  have hn : 0 ≤ (B + (p : ℝ) + 2) / h := by positivity
  have hc := (Nat.ceil_lt_add_one hn).le
  have hc' := mul_le_mul_of_nonneg_right hc hh.le
  dsimp [blockCutoff]
  have he : ((B + (p : ℝ) + 2) / h + 1) * h = B + (p : ℝ) + 2 + h := by
    field_simp
  rw [he] at hc'
  nlinarith

/-- The number of enumerated blocks is at most `C h⁻³`
(`app:ch_waves:thm:sampling`). -/
theorem card_blocks_mul_cube_le (hB : 0 ≤ B) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ((integerCube (blockCutoff p B h)).card : ℝ) * h ^ 3 ≤ blockCountConstant p B := by
  rw [card_integerCube]
  push_cast
  have he := pow_le_pow_left₀ (by positivity :
    0 ≤ (2 * (blockCutoff p B h : ℝ) + 1) * h)
    (blockCutoff_width_mul_le hB hh hh₁ (p := p)) 3
  simpa only [mul_pow, blockCountConstant] using he

/-- The total sample count has the fixed three-dimensional mesh dependence
of `app:ch_waves:thm:sampling`, uniformly in all shifts. -/
theorem card_samples_mul_cube_le (hB : 0 ≤ B) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ((samples p B ψ w h U).card : ℝ) * h ^ 3 ≤ countConstant p B := by
  have hc : (samples p B ψ w h U).card ≤
      (integerCube (blockCutoff p B h)).card * nodesPerBlock p := by
    exact (Finset.card_filter_le _ _).trans_eq (by
      rw [Finset.card_product, card_integerCube (p + 2)]; rfl)
  have hc' : ((samples p B ψ w h U).card : ℝ) ≤
      (integerCube (blockCutoff p B h)).card * (nodesPerBlock p : ℝ) := by
    exact_mod_cast hc
  calc
    _ ≤ ((integerCube (blockCutoff p B h)).card * (nodesPerBlock p : ℝ)) * h ^ 3 :=
      mul_le_mul_of_nonneg_right hc' (by positivity)
    _ = ((integerCube (blockCutoff p B h)).card * h ^ 3) * nodesPerBlock p := by ring
    _ ≤ blockCountConstant p B * nodesPerBlock p := mul_le_mul_of_nonneg_right
      (card_blocks_mul_cube_le hB hh hh₁) (Nat.cast_nonneg _)

/-- The total sample count is at most `C / h³`, with no accuracy dependence. -/
theorem card_samples_le (hB : 0 ≤ B) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ((samples p B ψ w h U).card : ℝ) ≤ countConstant p B / h ^ 3 :=
  (le_div_iff₀ (by positivity)).mpr (card_samples_mul_cube_le hB hh hh₁)

/-- There are only finitely many nonzero literal samples; the enumeration
in `app:ch_waves:thm:sampling` loses no nonzero weights. -/
theorem finite_nonzero_weights (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 < h) (hh₁ : h ≤ 1) (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h) :
    Set.Finite {a : Sample | weight ψ w h U a ≠ 0} := by
  apply (samples p B ψ w h U).finite_toSet.subset
  intro a ha
  exact (mem_samples_iff hw hψ hh hh₁ hU).mpr ha

end JanetCartan.SeparatedSampling
