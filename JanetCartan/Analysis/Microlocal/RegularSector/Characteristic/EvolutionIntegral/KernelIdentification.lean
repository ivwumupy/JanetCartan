module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.RetardedLimits
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.FixedTimeLimits

/-!
# Physical retarded kernels and datum-wise strong measurability

For `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`, actual compact frequency
regularizations have proved integrability, physical Fourier splitting and
multiplier-slice inversion. Their fixed-`r` action is precisely the spatial
evolution of the multiplier slice in the order `Mχout U_b B_(χⱼβ) Mχsource`.
The lower-buffer argument identifies the fixed slab with the original retarded
triangle, retaining its endpoints. The literal adjoint has the reversed
triangle and the order `Mχsource* B_(χⱼβ)* E_b* Mχout*`.

`integral_elapsed_regularization_test_representatives` proves that these
pointwise compact kernels represent the actual L² time integrals.
`elapsedGraph_strongLimit_spatialGraphs` identifies the fixed-time uncut graph
as the strong limit of the physical spatial-slice expressions.
`exists_retardedOperator_of_regularizations` constructs the bounded retarded
operator and identifies its forward and adjoint actions as strong L² limits
of the literal compact retarded kernels. It also proves datum-wise strong
measurability, using regularity only near the supported chart.

The uncut results explicitly take the finite test realizations, uniform LOW
bound and forward/adjoint strong limits exported by
`exists_fullGraphFamily_of_wholeImage_phase`. The parent must instantiate that
producer from its geometry and symbol budgets. These checked conditional
kernel deductions do not assert the unconditional retarded-kernel existence
or its Sobolev estimates. No operator-norm continuity or assumed uncut test
action is used.
-/
