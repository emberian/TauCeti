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

Two important identifications are deliberately **not** claimed here:

* equality of the first closure with all distributionally divergence-free `L²` fields;
* a Fourier-multiplier or Helmholtz formula for either projection.

The mean-zero closure *is* identified below with the intersection of the first closure and the
kernel of the ambient vector `L²` mean.  This follows constructively by subtracting the constant
mean from every divergence-free `W¹,²` approximant.  The two remaining identifications require
density and multiplier results beyond the closure construction itself.

This advances the periodic solenoidal-space and Leray-projection prerequisites in Layer 0 of the
`IncompressibleFlows` roadmap.

## Main declarations

* `TauCeti.UnitAddTorus.periodicSolenoidalL2Submodule`: closure of divergence-free `W¹,²`
  values.
* `TauCeti.UnitAddTorus.periodicMeanZeroSolenoidalL2Submodule`: closure of mean-zero
  incompressible energy values.
* `TauCeti.UnitAddTorus.periodicMeanZeroSolenoidalL2Submodule_eq_inf`: identification of that
  closure with the zero-mean part of the full solenoidal closure.
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

/- Mathlib keeps the normalized circle probability instance local to its Fourier module. -/
attribute [local instance] unitAddTorusIsProbabilityMeasure

/-- The normalized spatial mean on scalar periodic `L²`, as pairing with the constant one. -/
def periodicScalarL2MeanL :
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) →L[ℝ] ℝ :=
  innerSL ℝ (Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) 1)

@[simp]
theorem periodicScalarL2MeanL_apply
    (f : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) :
    periodicScalarL2MeanL f = mean f := by
  rw [periodicScalarL2MeanL, innerSL_apply_apply, mean_eq_average, average_eq_integral]
  rw [← indicatorConstLp_univ, L2.inner_indicatorConstLp_one]
  simp

@[simp]
theorem periodicScalarL2MeanL_const (c : ℝ) :
    periodicScalarL2MeanL
      (Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) c) = c := by
  rw [periodicScalarL2MeanL_apply, mean_eq_average, average_eq_integral,
    integral_congr_ae (Lp.coeFn_const 2
      (volume : Measure (_root_.UnitAddTorus d)) c)]
  simp

/-- Assemble a finite family of continuous linear maps into an `L²` Hilbert product. -/
private def piLpFamilyL {ι X : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]
    (f : ∀ i, X →L[ℝ] Y i) : X →L[ℝ] PiLp 2 Y :=
  (PiLp.continuousLinearEquiv 2 ℝ Y).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi f)

private theorem piLpFamilyL_apply {ι X : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]
    (f : ∀ i, X →L[ℝ] Y i) (x : X) (i : ι) :
    piLpFamilyL f x i = f i x := by
  rfl

/-- The componentwise normalized spatial mean on quotient-native vector `L²`. -/
def periodicVectorL2MeanL : PeriodicVectorL2 d →L[ℝ] EuclideanSpace ℝ d :=
  piLpFamilyL (ι := d) (X := PeriodicVectorL2 d) fun j ↦
    periodicScalarL2MeanL.comp
      (PiLp.proj (𝕜 := ℝ) 2
        (fun _ : d ↦ Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) j)

@[simp]
theorem periodicVectorL2MeanL_apply (f : PeriodicVectorL2 d) (j : d) :
    periodicVectorL2MeanL f j = mean (f j) := by
  rw [periodicVectorL2MeanL, piLpFamilyL_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, periodicScalarL2MeanL_apply]

/-- Embed a finite constant vector as a quotient-native constant vector `L²` field. -/
def periodicConstantVectorL2L : EuclideanSpace ℝ d →L[ℝ] PeriodicVectorL2 d :=
  piLpFamilyL (ι := d) (X := EuclideanSpace ℝ d) fun j ↦
    (Lp.constL 2 (volume : Measure (_root_.UnitAddTorus d)) ℝ).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) j)

@[simp]
theorem periodicConstantVectorL2L_apply (c : EuclideanSpace ℝ d) (j : d) :
    periodicConstantVectorL2L c j =
      Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) (c j) := by
  rw [periodicConstantVectorL2L, piLpFamilyL_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, Lp.constL_apply]

@[simp]
theorem periodicVectorL2MeanL_periodicConstantVectorL2L (c : EuclideanSpace ℝ d) :
    periodicVectorL2MeanL (periodicConstantVectorL2L c) = c := by
  apply PiLp.ext
  intro j
  rw [periodicVectorL2MeanL_apply, periodicConstantVectorL2L_apply,
    ← periodicScalarL2MeanL_apply, periodicScalarL2MeanL_const]

/-- Subtract the componentwise spatial mean from a quotient-native vector `L²` field. -/
def periodicVectorL2MeanZeroL : PeriodicVectorL2 d →L[ℝ] PeriodicVectorL2 d :=
  ContinuousLinearMap.id ℝ (PeriodicVectorL2 d) -
    periodicConstantVectorL2L.comp periodicVectorL2MeanL

theorem periodicVectorL2MeanZeroL_apply (f : PeriodicVectorL2 d) :
    periodicVectorL2MeanZeroL f =
      f - periodicConstantVectorL2L (periodicVectorL2MeanL f) := by
  rw [periodicVectorL2MeanZeroL, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]

@[simp]
theorem periodicVectorL2MeanL_periodicVectorL2MeanZeroL (f : PeriodicVectorL2 d) :
    periodicVectorL2MeanL (periodicVectorL2MeanZeroL f) = 0 := by
  rw [periodicVectorL2MeanZeroL_apply, map_sub,
    periodicVectorL2MeanL_periodicConstantVectorL2L, sub_self]

/-- The closed ambient vector `L²` subspace with zero componentwise spatial mean. -/
def periodicMeanZeroVectorL2Submodule (d : Type*) [Fintype d] :
    ClosedSubmodule ℝ (PeriodicVectorL2 d) :=
  (⊥ : ClosedSubmodule ℝ (EuclideanSpace ℝ d)).comap periodicVectorL2MeanL

theorem mem_periodicMeanZeroVectorL2Submodule_iff (f : PeriodicVectorL2 d) :
    f ∈ periodicMeanZeroVectorL2Submodule d ↔ periodicVectorL2MeanL f = 0 := by
  simp only [periodicMeanZeroVectorL2Submodule, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot]

/-- The ambient mean-zero correction fixes exactly the mean-zero vector `L²` fields. -/
theorem periodicVectorL2MeanZeroL_eq_self_iff (f : PeriodicVectorL2 d) :
    periodicVectorL2MeanZeroL f = f ↔ periodicVectorL2MeanL f = 0 := by
  constructor
  · intro h
    have := congrArg periodicVectorL2MeanL h
    symm
    simpa only [periodicVectorL2MeanL_periodicVectorL2MeanZeroL, map_zero] using this
  · intro h
    rw [periodicVectorL2MeanZeroL_apply, h, map_zero, sub_zero]

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

@[simp]
theorem periodicVectorL2MeanL_value (u : PeriodicVectorW12 d) :
    periodicVectorL2MeanL (PeriodicVectorW12.value u) = PeriodicVectorW12.mean u := by
  apply PiLp.ext
  intro j
  simp only [periodicVectorL2MeanL_apply, PeriodicVectorW12.value_apply,
    PeriodicVectorW12.mean_apply]

@[simp]
theorem periodicConstantVectorL2L_eq_value_const (c : EuclideanSpace ℝ d) :
    periodicConstantVectorL2L c =
      PeriodicVectorW12.value (PeriodicVectorW12.const c) := by
  apply PiLp.ext
  intro j
  simp only [periodicConstantVectorL2L_apply, PeriodicVectorW12.value_apply,
    PeriodicVectorW12.component_const, PeriodicW12.value_const]

/-- Subtracting the ambient `L²` mean commutes with the quotient-level `W¹,²` value map. -/
theorem periodicVectorL2MeanZeroL_value (u : PeriodicVectorW12 d) :
    periodicVectorL2MeanZeroL (PeriodicVectorW12.value u) =
      PeriodicVectorW12.value
        (u - PeriodicVectorW12.const (PeriodicVectorW12.mean u)) := by
  rw [periodicVectorL2MeanZeroL_apply, periodicVectorL2MeanL_value,
    periodicConstantVectorL2L_eq_value_const]
  rw [← PeriodicVectorW12.valueL_apply u,
    ← PeriodicVectorW12.valueL_apply
      (PeriodicVectorW12.const (PeriodicVectorW12.mean u)),
    ← PeriodicVectorW12.valueL_apply
      (u - PeriodicVectorW12.const (PeriodicVectorW12.mean u))]
  exact (map_sub PeriodicVectorW12.valueL u
    (PeriodicVectorW12.const (PeriodicVectorW12.mean u))).symm

private theorem PeriodicVectorW12.mean_sub_const_mean (u : PeriodicVectorW12 d) :
    PeriodicVectorW12.mean
      (u - PeriodicVectorW12.const (PeriodicVectorW12.mean u)) = 0 := by
  rw [← PeriodicVectorW12.meanL_apply, map_sub,
    PeriodicVectorW12.meanL_apply, PeriodicVectorW12.meanL_apply,
    PeriodicVectorW12.mean_const, sub_self]

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

/-- Every field in the mean-zero solenoidal closure has zero ambient vector `L²` mean. -/
theorem periodicMeanZeroSolenoidalL2Submodule_le_periodicMeanZeroVectorL2Submodule :
    periodicMeanZeroSolenoidalL2Submodule d ≤ periodicMeanZeroVectorL2Submodule d := by
  rw [periodicMeanZeroSolenoidalL2Submodule, Submodule.closure_le]
  rintro _ ⟨u, rfl⟩
  apply (mem_periodicMeanZeroVectorL2Submodule_iff (periodicEnergyValueL u)).mpr
  rw [periodicEnergyValueL_apply, periodicVectorL2MeanL_value]
  exact PeriodicMeanZeroDivergenceFreeW12.mean_eq_zero u

private theorem periodicVectorW12_sub_const_mean_mem_energy
    (u : PeriodicDivergenceFreeW12 d) :
    (u : PeriodicVectorW12 d) -
        PeriodicVectorW12.const (PeriodicVectorW12.mean (u : PeriodicVectorW12 d)) ∈
      periodicMeanZeroDivergenceFreeW12Submodule d := by
  apply (mem_periodicMeanZeroDivergenceFreeW12Submodule_iff _).mpr
  constructor
  · exact (mem_periodicMeanZeroVectorW12Submodule_iff_representative _).mp <|
      (mem_periodicMeanZeroVectorW12Submodule_iff _).mpr
        (PeriodicVectorW12.mean_sub_const_mean (u : PeriodicVectorW12 d))
  · exact (mem_periodicDivergenceFreeW12Submodule_iff_weaklyDivergenceFree _).mp <|
      (periodicDivergenceFreeW12Submodule d).sub_mem u.2
        (periodicVectorW12_const_mem_divergenceFree _)

/-- Mean subtraction carries every divergence-free `W¹,²` value to the range generated by
the mean-zero incompressible energy space. -/
private theorem periodicVectorL2MeanZeroL_mapsTo_valueRanges :
    Set.MapsTo (periodicVectorL2MeanZeroL (d := d))
      ((periodicDivergenceFreeValueL (d := d)).range : Set (PeriodicVectorL2 d))
      ((periodicEnergyValueL (d := d)).range : Set (PeriodicVectorL2 d)) := by
  rintro _ ⟨u, rfl⟩
  let w : PeriodicVectorW12 d :=
    (u : PeriodicVectorW12 d) -
      PeriodicVectorW12.const (PeriodicVectorW12.mean (u : PeriodicVectorW12 d))
  have hw : w ∈ periodicMeanZeroDivergenceFreeW12Submodule d :=
    periodicVectorW12_sub_const_mean_mem_energy u
  refine ⟨⟨w, hw⟩, ?_⟩
  change periodicEnergyValueL ⟨w, hw⟩ =
    periodicVectorL2MeanZeroL (periodicDivergenceFreeValueL u)
  rw [periodicEnergyValueL_apply, periodicDivergenceFreeValueL_apply]
  dsimp only [w]
  exact (periodicVectorL2MeanZeroL_value (u : PeriodicVectorW12 d)).symm

/-- A solenoidal `L²` field with zero ambient mean belongs to the mean-zero solenoidal
closure.  The proof continuously subtracts the mean from the entire generating closure. -/
theorem periodicSolenoidalL2_inf_periodicMeanZeroVectorL2Submodule_le :
    periodicSolenoidalL2Submodule d ⊓ periodicMeanZeroVectorL2Submodule d ≤
      periodicMeanZeroSolenoidalL2Submodule d := by
  intro f hf
  have hsol : f ∈ closure
      ((periodicDivergenceFreeValueL (d := d)).range : Set (PeriodicVectorL2 d)) := hf.1
  have hmean : periodicVectorL2MeanL f = 0 :=
    (mem_periodicMeanZeroVectorL2Submodule_iff f).mp hf.2
  have hcorrected : periodicVectorL2MeanZeroL f ∈ closure
      ((periodicEnergyValueL (d := d)).range : Set (PeriodicVectorL2 d)) :=
    (periodicVectorL2MeanZeroL_mapsTo_valueRanges (d := d)).closure
      (periodicVectorL2MeanZeroL (d := d)).continuous hsol
  rw [(periodicVectorL2MeanZeroL_eq_self_iff f).mpr hmean] at hcorrected
  exact hcorrected

/-- The mean-zero solenoidal closure is exactly the zero-mean part of the full solenoidal
closure. -/
theorem periodicMeanZeroSolenoidalL2Submodule_eq_inf :
    periodicMeanZeroSolenoidalL2Submodule d =
      periodicSolenoidalL2Submodule d ⊓ periodicMeanZeroVectorL2Submodule d := by
  apply le_antisymm
  · exact le_inf periodicMeanZeroSolenoidalL2Submodule_le_periodicSolenoidalL2Submodule
      periodicMeanZeroSolenoidalL2Submodule_le_periodicMeanZeroVectorL2Submodule
  · exact periodicSolenoidalL2_inf_periodicMeanZeroVectorL2Submodule_le

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

/-- Projecting first onto the full solenoidal closure and then onto its mean-zero part is the
mean-zero projection. -/
theorem periodicMeanZeroLerayProjectionL_comp_periodicLerayProjectionL :
    periodicMeanZeroLerayProjectionL (d := d) ∘L periodicLerayProjectionL (d := d) =
      periodicMeanZeroLerayProjectionL (d := d) := by
  rw [periodicMeanZeroLerayProjectionL, periodicLerayProjectionL]
  exact Submodule.starProjection_comp_starProjection_of_le
    periodicMeanZeroSolenoidalL2Submodule_le_periodicSolenoidalL2Submodule

/-- Projecting a mean-zero solenoidal field onto the larger solenoidal closure changes
nothing. -/
theorem periodicLerayProjectionL_comp_periodicMeanZeroLerayProjectionL :
    periodicLerayProjectionL (d := d) ∘L periodicMeanZeroLerayProjectionL (d := d) =
      periodicMeanZeroLerayProjectionL (d := d) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply]
  apply (periodicLerayProjectionL_eq_self_iff _).mpr
  exact periodicMeanZeroSolenoidalL2Submodule_le_periodicSolenoidalL2Submodule
    (periodicMeanZeroLerayProjectionL_mem f)

@[simp]
theorem periodicMeanZeroLerayProjectionL_periodicLerayProjectionL
    (f : PeriodicVectorL2 d) :
    periodicMeanZeroLerayProjectionL (periodicLerayProjectionL f) =
      periodicMeanZeroLerayProjectionL f := by
  exact DFunLike.congr_fun
    periodicMeanZeroLerayProjectionL_comp_periodicLerayProjectionL f

@[simp]
theorem periodicLerayProjectionL_periodicMeanZeroLerayProjectionL
    (f : PeriodicVectorL2 d) :
    periodicLerayProjectionL (periodicMeanZeroLerayProjectionL f) =
      periodicMeanZeroLerayProjectionL f := by
  exact DFunLike.congr_fun
    periodicLerayProjectionL_comp_periodicMeanZeroLerayProjectionL f

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
