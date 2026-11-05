module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.ConicConstruction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.Geometry

/-!
# The source slab fits the retained phase radius

`exists_uniform_supported_conic_pencilAmplitudes_with_retarded_radii` supplies
both radius comparisons on the original amplitude witnesses, before the masks
or varying coefficients. They put the slab of length `3 * src / 4` from
`UniformEvolution.exists_retained_physical_masks` strictly inside the retained
radius. Its lower endpoint is justified for those same amplitudes by
`UniformEvolution.retained_amplitude_zero_before_source_half`.

Consumer: the elapsed-time bound in
`EvolutionIntegral.exists_retardedOperator_signed_integer_bounds_of_primitive_data`,
for `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`.
-/

@[expose] public section

namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes

/-- The actual source-compatible output slab has positive length and fits
strictly inside the same phase/amplitude buffer. The two comparisons are
outputs of `exists_uniform_supported_conic_pencilAmplitudes_with_retarded_radii`;
no radius or amplitude is reselected (`fixed-time-representation`). -/
theorem retained_source_slab_bounds {b ρ src : ℝ}
    (hsrc : 0 < src) (hρb : ρ ≤ b) (hsrcρ : src ≤ ρ / 4) :
    0 < 3 * src / 4 ∧ 3 * src / 4 < UniformEvolution.retainedRadius b ρ := by
  rw [UniformEvolution.retainedRadius, min_eq_right hρb]
  constructor <;> linarith only [hsrc, hsrcρ]

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
