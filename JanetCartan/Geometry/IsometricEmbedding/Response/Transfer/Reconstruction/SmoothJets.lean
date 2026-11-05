module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.SmoothJets.Classical

/-!
# Smooth envelope jets realized in Euclidean Fourier Sobolev spaces

From a smooth complex envelope representing an actual Lebesgue L² class of
integer Sobolev order `M`, construct all its classical coordinate jets through
length `M`. The same family has distributional derivative recursion and the
Fourier-normalized derivative bounds used in
`app:ch_response:eq:response-graded-displacement` and
`app:ch_response:eq:response-graded-derivative`.

Only root Sobolev membership is assumed. No derivative integrability, compact
support, Schwartz regularity, or temperate growth of the envelope is required.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound

namespace JanetCartan.IsometricEmbedding.Reconstruction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- A classical coordinate word has an actual L² representative of order `s`
when its smooth root has order `s + |w|`. Each coordinate derivative costs `2π`,
with the Fourier normalization needed for
`app:ch_response:eq:response-graded-derivative`. This is the single-word step
in `exists_smoothL2Jets`. -/
theorem exists_smoothCoordinateDerivList {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {u : L2} (huf : u =ᵐ[volume] f) (w : List (Fin d)) {s : ℝ} (hs : 0 ≤ s)
    (hu : MemFourierSobolev (s + w.length) u) :
    ∃ v : L2, v =ᵐ[volume] euclideanCoordinateDerivList w f ∧
      MemFourierSobolev s v ∧
      fourierSobolevNorm s v ≤ (2 * Real.pi) ^ w.length *
        fourierSobolevNorm (s + w.length) u := by
  induction w generalizing s with
  | nil => exact ⟨u, huf, by simpa using hu, by simp⟩
  | cons i w ih =>
    have ho : s + 1 + w.length = s + (i :: w).length := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    obtain ⟨v, hvf, hv, hvbound⟩ := ih (s := s + 1) (by linarith) (by rwa [ho])
    obtain ⟨v', hv', hvs⟩ := hv.exists_coordinateDerivative hs i
    refine ⟨v', coordinateDerivative_ae_eq_classical
      (contDiff_euclideanCoordinateDerivList hf w) hvf hv', hvs, ?_⟩
    calc
      _ ≤ (2 * Real.pi) * fourierSobolevNorm (s + 1) v :=
        hv'.fourierSobolevNorm_le hs hv
      _ ≤ (2 * Real.pi) * ((2 * Real.pi) ^ w.length *
          fourierSobolevNorm (s + 1 + w.length) u) :=
        mul_le_mul_of_nonneg_left hvbound (by positivity)
      _ = _ := by rw [ho, List.length_cons, pow_succ]; ring

/-- Construct a single family of actual classical envelope jets through order
`M` for `app:ch_response:eq:response-graded-displacement` and
`app:ch_response:eq:response-graded-derivative`. The empty word equals the given
L² class, and prepending a coordinate gives its actual distributional derivative.
All memberships and bounds follow from root membership alone. In particular,
taking `s = M - |w|` bounds every jet by `(2π)^|w|` times the root order-`M` norm;
taking `s = 0` gives its L² bound. Entries beyond order `M` are unrestricted. -/
theorem exists_smoothL2Jets {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {M : ℕ} {u : L2} (huf : u =ᵐ[volume] f) (hu : MemFourierSobolev (M : ℝ) u) :
    ∃ v : List (Fin d) → L2,
      v [] = u ∧
      (∀ w, w.length ≤ M → v w =ᵐ[volume] euclideanCoordinateDerivList w f) ∧
      (∀ w, w.length ≤ M → MemFourierSobolev ((M : ℝ) - w.length) (v w)) ∧
      (∀ i w, w.length < M → HasEuclideanL2CoordinateDerivative i (v w) (v (i :: w))) ∧
      (∀ w (s : ℝ), 0 ≤ s → s + w.length ≤ M →
        MemFourierSobolev s (v w) ∧
        fourierSobolevNorm s (v w) ≤ (2 * Real.pi) ^ w.length *
          fourierSobolevNorm (s + w.length) u) := by
  classical
  have hex (w : List (Fin d)) : ∃ v : L2, w.length ≤ M →
      v =ᵐ[volume] euclideanCoordinateDerivList w f ∧
        MemFourierSobolev ((M : ℝ) - w.length) v := by
    by_cases hw : w.length ≤ M
    · obtain ⟨v, hv, hvm, _⟩ := exists_smoothCoordinateDerivList hf huf w
        (s := (M : ℝ) - w.length) (sub_nonneg.mpr (by exact_mod_cast hw))
        (by simpa using hu)
      exact ⟨v, fun _ ↦ ⟨hv, hvm⟩⟩
    · exact ⟨0, fun h ↦ (hw h).elim⟩
  choose v hv using hex
  refine ⟨v, ?_, (fun w hw ↦ (hv w hw).1), (fun w hw ↦ (hv w hw).2), ?_, ?_⟩
  · exact Lp.ext ((hv [] (by simp)).1.trans huf.symm)
  · intro i w hw
    have hwm : w.length ≤ M := Nat.le_of_lt hw
    have hpos : 0 ≤ (M : ℝ) - w.length - 1 := by
      have : (w.length : ℝ) + 1 ≤ M := by exact_mod_cast hw
      linarith
    have hmem : MemFourierSobolev ((M : ℝ) - w.length - 1 + 1) (v w) := by
      simpa using (hv w hwm).2
    obtain ⟨z, hz, _⟩ := hmem.exists_coordinateDerivative hpos i
    have hzf := coordinateDerivative_ae_eq_classical
      (contDiff_euclideanCoordinateDerivList hf w) (hv w hwm).1 hz
    have hzv : z = v (i :: w) := Lp.ext
      (hzf.trans (hv (i :: w) (by simpa using hw)).1.symm)
    rwa [hzv] at hz
  · intro w s hs horder
    have hw : w.length ≤ M := by
      exact_mod_cast (show (w.length : ℝ) ≤ M by linarith)
    obtain ⟨z, hzf, hzm, hzb⟩ := exists_smoothCoordinateDerivList hf huf w hs
      (hu.mono horder)
    have hzv : z = v w := Lp.ext (hzf.trans (hv w hw).1.symm)
    simpa only [hzv] using And.intro hzm hzb

end JanetCartan.IsometricEmbedding.Reconstruction
