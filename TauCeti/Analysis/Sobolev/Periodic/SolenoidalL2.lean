/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.EnergySpace

/-!
# Periodic solenoidal L² closures and orthogonal projections

The periodic solenoidal `L²` space in this file is defined honestly as the norm closure of the
quotient-level values of divergence-free periodic `W¹,²` classes.  A second closed space is the
closure of values of the mean-zero incompressible energy space.  Both definitions stay entirely
inside finite Hilbert products of scalar `L²` quotient classes; no pointwise representative is
chosen.

Each closed subspace has its canonical orthogonal projection.  The contractivity, idempotence,
range, fixed-point, symmetry, and residual-orthogonality statements below are direct Hilbert-space
facts.

Three important identifications are deliberately **not** claimed here:

* equality of the first closure with all distributionally divergence-free `L²` fields;
* a Fourier-multiplier or Helmholtz formula for either projection;
* equality of the mean-zero closure with the intersection of the first closure and an ambient
  vector `L²` mean-zero subspace.

Those require density and multiplier results beyond the closure construction itself.

This advances the periodic solenoidal-space and Leray-projection prerequisites in Layer 0 of the
`IncompressibleFlows` roadmap.

## Main declarations

* `TauCeti.UnitAddTorus.periodicSolenoidalL2Submodule`: closure of divergence-free `W¹,²`
  values.
* `TauCeti.UnitAddTorus.periodicMeanZeroSolenoidalL2Submodule`: closure of mean-zero
  incompressible energy values.
* `TauCeti.UnitAddTorus.periodicLerayProjectionL`: orthogonal projection onto the first closure.
* `TauCeti.UnitAddTorus.periodicMeanZeroLerayProjectionL`: orthogonal projection onto the second.
-/

public section

noncomputable section

namespace TauCeti.UnitAddTorus

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq

/-- The bounded value map from divergence-free periodic `W¹,²` into quotient-native vector
`L²`. -/
def periodicDivergenceFreeValueL :
    PeriodicDivergenceFreeW12 d →L[ℝ] PeriodicVectorL2 d :=
  PeriodicVectorW12.valueL.comp
    (periodicDivergenceFreeW12Submodule d).toSubmodule.subtypeL

@[simp]
theorem periodicDivergenceFreeValueL_apply (u : PeriodicDivergenceFreeW12 d) :
    periodicDivergenceFreeValueL u = PeriodicVectorW12.value (u : PeriodicVectorW12 d) := by
  rw [periodicDivergenceFreeValueL, ContinuousLinearMap.comp_apply,
    PeriodicVectorW12.valueL_apply]
  rfl

/-- The bounded value map from the mean-zero incompressible energy space into quotient-native
vector `L²`. -/
def periodicEnergyValueL :
    PeriodicMeanZeroDivergenceFreeW12 d →L[ℝ] PeriodicVectorL2 d :=
  PeriodicVectorW12.valueL.comp
    (periodicMeanZeroDivergenceFreeW12Submodule d).toSubmodule.subtypeL

@[simp]
theorem periodicEnergyValueL_apply (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicEnergyValueL u = PeriodicVectorW12.value (u : PeriodicVectorW12 d) := by
  rw [periodicEnergyValueL, ContinuousLinearMap.comp_apply,
    PeriodicVectorW12.valueL_apply]
  rfl

/-- The closed periodic solenoidal `L²` space: the norm closure of values of divergence-free
periodic `W¹,²` classes.  No converse distributional characterization is asserted. -/
def periodicSolenoidalL2Submodule (d : Type*) [Fintype d] :
    ClosedSubmodule ℝ (PeriodicVectorL2 d) :=
  periodicDivergenceFreeValueL.range.closure

/-- The closed mean-zero periodic solenoidal `L²` space: the norm closure of values of the
mean-zero incompressible energy space. -/
def periodicMeanZeroSolenoidalL2Submodule (d : Type*) [Fintype d] :
    ClosedSubmodule ℝ (PeriodicVectorL2 d) :=
  periodicEnergyValueL.range.closure

/-- Exact norm-closure membership: a field is solenoidal in the present sense precisely when it
can be approximated arbitrarily well by values of divergence-free periodic `W¹,²` classes. -/
theorem mem_periodicSolenoidalL2Submodule_iff_approx
    (f : PeriodicVectorL2 d) :
    f ∈ periodicSolenoidalL2Submodule d ↔
      ∀ ε > 0, ∃ u : PeriodicDivergenceFreeW12 d,
        dist f (periodicDivergenceFreeValueL u) < ε := by
  change f ∈ closure
    ((periodicDivergenceFreeValueL (d := d)).range : Set (PeriodicVectorL2 d)) ↔ _
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨_, ⟨u, rfl⟩, hu⟩
    exact ⟨u, hu⟩
  · intro h ε hε
    rcases h ε hε with ⟨u, hu⟩
    exact ⟨periodicDivergenceFreeValueL u, ⟨u, rfl⟩, hu⟩

/-- Exact norm-closure membership for the mean-zero solenoidal space. -/
theorem mem_periodicMeanZeroSolenoidalL2Submodule_iff_approx
    (f : PeriodicVectorL2 d) :
    f ∈ periodicMeanZeroSolenoidalL2Submodule d ↔
      ∀ ε > 0, ∃ u : PeriodicMeanZeroDivergenceFreeW12 d,
        dist f (periodicEnergyValueL u) < ε := by
  change f ∈ closure
    ((periodicEnergyValueL (d := d)).range : Set (PeriodicVectorL2 d)) ↔ _
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨_, ⟨u, rfl⟩, hu⟩
    exact ⟨u, hu⟩
  · intro h ε hε
    rcases h ε hε with ⟨u, hu⟩
    exact ⟨periodicEnergyValueL u, ⟨u, rfl⟩, hu⟩

/-- Every divergence-free periodic `W¹,²` value lies in the solenoidal `L²` closure. -/
theorem periodicDivergenceFreeValueL_mem_periodicSolenoidalL2
    (u : PeriodicDivergenceFreeW12 d) :
    periodicDivergenceFreeValueL u ∈ periodicSolenoidalL2Submodule d := by
  exact Submodule.le_topologicalClosure _ ⟨u, rfl⟩

/-- Every root `W¹,²` class satisfying the weak-divergence kernel condition has its value in
the solenoidal `L²` closure. -/
theorem PeriodicVectorW12.value_mem_periodicSolenoidalL2
    (u : PeriodicVectorW12 d) (hu : u ∈ periodicDivergenceFreeW12Submodule d) :
    PeriodicVectorW12.value u ∈ periodicSolenoidalL2Submodule d := by
  simpa only [periodicDivergenceFreeValueL_apply,
    Subtype.coe_eta] using
      periodicDivergenceFreeValueL_mem_periodicSolenoidalL2
        (⟨u, hu⟩ : PeriodicDivergenceFreeW12 d)

/-- Every mean-zero incompressible energy value lies in its corresponding closed `L²` space. -/
theorem periodicEnergyValueL_mem_periodicMeanZeroSolenoidalL2
    (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicEnergyValueL u ∈ periodicMeanZeroSolenoidalL2Submodule d := by
  exact Submodule.le_topologicalClosure _ ⟨u, rfl⟩

/-- Every root `W¹,²` class in the mean-zero incompressible kernel has its value in the
mean-zero solenoidal `L²` closure. -/
theorem PeriodicVectorW12.value_mem_periodicMeanZeroSolenoidalL2
    (u : PeriodicVectorW12 d)
    (hu : u ∈ periodicMeanZeroDivergenceFreeW12Submodule d) :
    PeriodicVectorW12.value u ∈ periodicMeanZeroSolenoidalL2Submodule d := by
  simpa only [periodicEnergyValueL_apply] using
    periodicEnergyValueL_mem_periodicMeanZeroSolenoidalL2
      (⟨u, hu⟩ : PeriodicMeanZeroDivergenceFreeW12 d)

/-- The closure generated by mean-zero incompressible energy values is contained in the closure
generated by all divergence-free `W¹,²` values. -/
theorem periodicMeanZeroSolenoidalL2Submodule_le_periodicSolenoidalL2Submodule :
    periodicMeanZeroSolenoidalL2Submodule d ≤ periodicSolenoidalL2Submodule d := by
  rw [periodicMeanZeroSolenoidalL2Submodule, Submodule.closure_le]
  rintro _ ⟨u, rfl⟩
  change periodicEnergyValueL u ∈ (periodicSolenoidalL2Submodule d).toSubmodule
  rw [periodicEnergyValueL_apply]
  apply PeriodicVectorW12.value_mem_periodicSolenoidalL2
  exact (mem_periodicDivergenceFreeW12Submodule_iff_weaklyDivergenceFree
    (u : PeriodicVectorW12 d)).mpr <|
      (mem_periodicMeanZeroDivergenceFreeW12Submodule_iff
        (u : PeriodicVectorW12 d)).mp u.2 |>.2

/-- The quotient-native periodic Leray projection onto the closure of divergence-free `W¹,²`
values.  This definition does not yet supply a Fourier-multiplier formula. -/
def periodicLerayProjectionL : PeriodicVectorL2 d →L[ℝ] PeriodicVectorL2 d :=
  (periodicSolenoidalL2Submodule d).toSubmodule.starProjection

/-- The orthogonal projection onto the closure generated by mean-zero incompressible energy
values. -/
def periodicMeanZeroLerayProjectionL : PeriodicVectorL2 d →L[ℝ] PeriodicVectorL2 d :=
  (periodicMeanZeroSolenoidalL2Submodule d).toSubmodule.starProjection

theorem periodicLerayProjectionL_mem (f : PeriodicVectorL2 d) :
    periodicLerayProjectionL f ∈ periodicSolenoidalL2Submodule d := by
  exact Submodule.starProjection_apply_mem _ _

theorem periodicMeanZeroLerayProjectionL_mem (f : PeriodicVectorL2 d) :
    periodicMeanZeroLerayProjectionL f ∈ periodicMeanZeroSolenoidalL2Submodule d := by
  exact Submodule.starProjection_apply_mem _ _

theorem periodicLerayProjectionL_eq_self_iff (f : PeriodicVectorL2 d) :
    periodicLerayProjectionL f = f ↔ f ∈ periodicSolenoidalL2Submodule d := by
  exact Submodule.starProjection_eq_self_iff

theorem periodicMeanZeroLerayProjectionL_eq_self_iff (f : PeriodicVectorL2 d) :
    periodicMeanZeroLerayProjectionL f = f ↔
      f ∈ periodicMeanZeroSolenoidalL2Submodule d := by
  exact Submodule.starProjection_eq_self_iff

@[simp]
theorem periodicLerayProjectionL_idem (f : PeriodicVectorL2 d) :
    periodicLerayProjectionL (periodicLerayProjectionL f) = periodicLerayProjectionL f :=
  periodicLerayProjectionL_eq_self_iff _ |>.mpr (periodicLerayProjectionL_mem f)

@[simp]
theorem periodicMeanZeroLerayProjectionL_idem (f : PeriodicVectorL2 d) :
    periodicMeanZeroLerayProjectionL (periodicMeanZeroLerayProjectionL f) =
      periodicMeanZeroLerayProjectionL f :=
  periodicMeanZeroLerayProjectionL_eq_self_iff _ |>.mpr
    (periodicMeanZeroLerayProjectionL_mem f)

theorem norm_periodicLerayProjectionL_apply_le (f : PeriodicVectorL2 d) :
    ‖periodicLerayProjectionL f‖ ≤ ‖f‖ :=
  Submodule.norm_starProjection_apply_le _ f

theorem norm_periodicMeanZeroLerayProjectionL_apply_le (f : PeriodicVectorL2 d) :
    ‖periodicMeanZeroLerayProjectionL f‖ ≤ ‖f‖ :=
  Submodule.norm_starProjection_apply_le _ f

theorem norm_periodicLerayProjectionL_le : ‖periodicLerayProjectionL (d := d)‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

theorem norm_periodicMeanZeroLerayProjectionL_le :
    ‖periodicMeanZeroLerayProjectionL (d := d)‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

theorem range_periodicLerayProjectionL :
    periodicLerayProjectionL (d := d).range =
      (periodicSolenoidalL2Submodule d).toSubmodule := by
  exact Submodule.range_starProjection _

theorem range_periodicMeanZeroLerayProjectionL :
    periodicMeanZeroLerayProjectionL (d := d).range =
      (periodicMeanZeroSolenoidalL2Submodule d).toSubmodule := by
  exact Submodule.range_starProjection _

/-- The Leray residual lies in the orthogonal complement of the solenoidal closure. -/
theorem sub_periodicLerayProjectionL_mem_orthogonal (f : PeriodicVectorL2 d) :
    f - periodicLerayProjectionL f ∈
      (periodicSolenoidalL2Submodule d).toSubmodule.orthogonal := by
  exact Submodule.sub_starProjection_mem_orthogonal f

/-- The mean-zero Leray residual lies in the orthogonal complement of its range closure. -/
theorem sub_periodicMeanZeroLerayProjectionL_mem_orthogonal (f : PeriodicVectorL2 d) :
    f - periodicMeanZeroLerayProjectionL f ∈
      (periodicMeanZeroSolenoidalL2Submodule d).toSubmodule.orthogonal := by
  exact Submodule.sub_starProjection_mem_orthogonal f

/-- Orthogonality of the Leray residual against every field in the solenoidal closure. -/
theorem inner_sub_periodicLerayProjectionL_eq_zero
    (f g : PeriodicVectorL2 d) (hg : g ∈ periodicSolenoidalL2Submodule d) :
    inner ℝ (f - periodicLerayProjectionL f) g = 0 := by
  exact Submodule.starProjection_inner_eq_zero f g hg

/-- The periodic Leray projection is symmetric, hence self-adjoint in the Hilbert-space sense. -/
theorem inner_periodicLerayProjectionL_left_eq_right (f g : PeriodicVectorL2 d) :
    inner ℝ (periodicLerayProjectionL f) g =
      inner ℝ f (periodicLerayProjectionL g) := by
  exact Submodule.inner_starProjection_left_eq_right _ f g

/-- The mean-zero periodic Leray projection is symmetric. -/
theorem inner_periodicMeanZeroLerayProjectionL_left_eq_right
    (f g : PeriodicVectorL2 d) :
    inner ℝ (periodicMeanZeroLerayProjectionL f) g =
      inner ℝ f (periodicMeanZeroLerayProjectionL g) := by
  exact Submodule.inner_starProjection_left_eq_right _ f g

/-- The Leray projection fixes the value of every divergence-free periodic `W¹,²` class. -/
@[simp]
theorem periodicLerayProjectionL_periodicDivergenceFreeValueL
    (u : PeriodicDivergenceFreeW12 d) :
    periodicLerayProjectionL (periodicDivergenceFreeValueL u) =
      periodicDivergenceFreeValueL u :=
  periodicLerayProjectionL_eq_self_iff _ |>.mpr
    (periodicDivergenceFreeValueL_mem_periodicSolenoidalL2 u)

/-- Evaluator form: the Leray projection fixes the underlying quotient-level value class. -/
@[simp]
theorem periodicLerayProjectionL_value_periodicDivergenceFreeW12
    (u : PeriodicDivergenceFreeW12 d) :
    periodicLerayProjectionL (PeriodicVectorW12.value (u : PeriodicVectorW12 d)) =
      PeriodicVectorW12.value (u : PeriodicVectorW12 d) := by
  rw [← periodicDivergenceFreeValueL_apply,
    periodicLerayProjectionL_periodicDivergenceFreeValueL]

/-- The mean-zero Leray projection fixes every mean-zero incompressible energy value. -/
@[simp]
theorem periodicMeanZeroLerayProjectionL_periodicEnergyValueL
    (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicMeanZeroLerayProjectionL (periodicEnergyValueL u) = periodicEnergyValueL u :=
  periodicMeanZeroLerayProjectionL_eq_self_iff _ |>.mpr
    (periodicEnergyValueL_mem_periodicMeanZeroSolenoidalL2 u)

/-- Evaluator form: the mean-zero Leray projection fixes the quotient-level energy value. -/
@[simp]
theorem periodicMeanZeroLerayProjectionL_value_periodicEnergyW12
    (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicMeanZeroLerayProjectionL (PeriodicVectorW12.value (u : PeriodicVectorW12 d)) =
      PeriodicVectorW12.value (u : PeriodicVectorW12 d) := by
  rw [← periodicEnergyValueL_apply,
    periodicMeanZeroLerayProjectionL_periodicEnergyValueL]

end TauCeti.UnitAddTorus
