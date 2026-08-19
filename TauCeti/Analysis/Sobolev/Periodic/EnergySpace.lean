/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx, Codex
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.VectorW12

/-!
# Mean-zero periodic energy spaces

This file removes the constant Fourier mode from scalar and vector periodic `W¹,²`.  The
spatial mean is packaged as a bounded linear functional on the quotient-native Sobolev space.
Its kernel is therefore a closed subspace.  Componentwise vector means give the corresponding
closed vector subspace, whose intersection with the weak-divergence kernel is the periodic
mean-zero incompressible energy space.

The sharp scalar Poincare theorem is summed over components to control the quotient-level vector
value norm by the weak-Jacobian norm.  Combined with the exact graph-norm identity, this makes the
weak Jacobian coercive on the mean-zero energy space.  The larger divergence-free space is kept
separate: constant vector fields belong to it, and are removed only by the mean-zero condition.

This advances Layer 0, items 3 and 4, and the periodic Poincare acceptance check in the
`IncompressibleFlows` roadmap.

## Main declarations

* `UnitAddTorus.PeriodicW12.meanL`: the normalized scalar spatial mean.
* `UnitAddTorus.periodicMeanZeroW12Submodule`: its closed kernel.
* `UnitAddTorus.PeriodicVectorW12.meanL`: the componentwise vector mean.
* `UnitAddTorus.periodicMeanZeroVectorW12Submodule`: its closed kernel.
* `UnitAddTorus.periodicMeanZeroDivergenceFreeW12Submodule`: the mean-zero incompressible
  energy space as an intersection of closed subspaces.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq

/- Mathlib keeps the normalized circle probability instance local to its Fourier module. -/
attribute [local instance] unitAddTorusIsProbabilityMeasure

namespace PeriodicW12

/-- The normalized spatial mean as a continuous linear functional on periodic `W¹,²`.
It is the `L²` pairing with the normalized constant function, composed with the value map. -/
def meanL : PeriodicW12 d →L[ℝ] ℝ :=
  (innerSL ℝ (Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) 1)).comp valueL

@[simp]
theorem meanL_apply (u : PeriodicW12 d) : meanL u = mean (value u) := by
  rw [meanL, ContinuousLinearMap.comp_apply, valueL_apply, innerSL_apply_apply]
  rw [mean_eq_average, average_eq_integral]
  rw [← indicatorConstLp_univ, L2.inner_indicatorConstLp_one]
  simp

/-- The normalized mean is bounded by the full scalar graph norm. -/
theorem norm_meanL_apply_le (u : PeriodicW12 d) : ‖meanL u‖ ≤ ‖u‖ := by
  rw [meanL, ContinuousLinearMap.comp_apply, valueL_apply, innerSL_apply_apply]
  calc
    ‖inner ℝ (Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) 1) (value u)‖ ≤
        ‖Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) (1 : ℝ)‖ * ‖value u‖ :=
      norm_inner_le_norm _ _
    _ = ‖value u‖ := by simp [Lp.norm_const]
    _ ≤ ‖u‖ := norm_value_le u

theorem norm_meanL_le : ‖meanL (d := d)‖ ≤ 1 := by
  refine (meanL (d := d)).opNorm_le_bound zero_le_one ?_
  intro u
  simpa only [one_mul] using norm_meanL_apply_le u

/-- The quotient-native constant scalar Sobolev class, with zero weak gradient. -/
def const (c : ℝ) : PeriodicW12 d :=
  mk (Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) c) 0 fun i ↦ by
    have h := (hasWeakCoordinateDerivative_const c i).congr_ae
      (Lp.coeFn_const 2 (volume : Measure (_root_.UnitAddTorus d)) c).symm
    apply h.congr_ae_deriv
    have hz : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLp
        (0 : Lp (EuclideanSpace ℝ d) 2
          (volume : Measure (_root_.UnitAddTorus d))) = 0 := by
      rfl
    rw [hz]
    exact (Lp.coeFn_zero ℝ 2 (volume : Measure (_root_.UnitAddTorus d))).symm

@[simp]
theorem value_const (c : ℝ) :
    value (const (d := d) c) =
      Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) c := by
  rw [const, value_mk]

@[simp]
theorem gradient_const (c : ℝ) : gradient (const (d := d) c) = 0 := by
  rw [const, gradient_mk]

@[simp]
theorem weakDeriv_const (c : ℝ) (i : d) : weakDeriv (const (d := d) c) i = 0 := by
  rw [const, weakDeriv_mk]
  rfl

theorem mean_const (c : ℝ) :
    UnitAddTorus.mean (value (const (d := d) c)) = c := by
  rw [value_const, mean_eq_average, average_eq_integral,
    integral_congr_ae (Lp.coeFn_const 2
      (volume : Measure (_root_.UnitAddTorus d)) c)]
  simp

end PeriodicW12

/-- The closed scalar periodic `W¹,²` subspace with vanishing normalized mean. -/
def periodicMeanZeroW12Submodule (d : Type*) [Fintype d] :
    ClosedSubmodule ℝ (PeriodicW12 d) :=
  (⊥ : ClosedSubmodule ℝ ℝ).comap PeriodicW12.meanL

theorem mem_periodicMeanZeroW12Submodule_iff (u : PeriodicW12 d) :
    u ∈ periodicMeanZeroW12Submodule d ↔ mean (PeriodicW12.value u) = 0 := by
  simp only [periodicMeanZeroW12Submodule, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot, PeriodicW12.meanL_apply]

/-- Scalar mean-zero periodic `W¹,²`. -/
abbrev PeriodicMeanZeroW12 (d : Type*) [Fintype d] :=
  (periodicMeanZeroW12Submodule d).toSubmodule

namespace PeriodicMeanZeroW12

instance : CompleteSpace (PeriodicMeanZeroW12 d) :=
  (periodicMeanZeroW12Submodule d).isClosed.completeSpace_coe

end PeriodicMeanZeroW12

private def piLpFamilyL {ι X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]
    (f : ∀ i, X →L[ℝ] Y i) : X →L[ℝ] PiLp 2 Y :=
  (PiLp.continuousLinearEquiv 2 ℝ Y).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi f)

private theorem piLpFamilyL_apply {ι X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]
    (f : ∀ i, X →L[ℝ] Y i) (x : X) (i : ι) :
    piLpFamilyL f x i = f i x := by
  rfl

namespace PeriodicVectorW12

/-- The componentwise normalized mean as a continuous linear map. -/
def meanL : PeriodicVectorW12 d →L[ℝ] EuclideanSpace ℝ d :=
  piLpFamilyL (ι := d) (X := PeriodicVectorW12 d) fun j ↦
    PeriodicW12.meanL.comp (componentL j)

/-- The componentwise normalized mean. -/
def mean (u : PeriodicVectorW12 d) : EuclideanSpace ℝ d :=
  meanL u

@[simp]
theorem meanL_apply (u : PeriodicVectorW12 d) : meanL u = mean u := by
  rw [mean]

@[simp]
theorem mean_apply (u : PeriodicVectorW12 d) (j : d) :
    mean u j = UnitAddTorus.mean (PeriodicW12.value (component u j)) := by
  rw [mean, meanL, piLpFamilyL_apply, ContinuousLinearMap.comp_apply,
    PeriodicW12.meanL_apply, componentL_apply]

private theorem integrable_representative_component (u : PeriodicVectorW12 d) (j : d) :
    Integrable (fun x ↦ representative u x j) := by
  simpa only [representative_apply] using memLp_one_iff_integrable.mp
    ((Lp.memLp (PeriodicW12.value (component u j))).mono_exponent one_le_two)

/-- The quotient-level vector mean agrees coordinatewise with the normalized mean of the
canonical representative. -/
theorem mean_representative_apply (u : PeriodicVectorW12 d) (j : d) :
    UnitAddTorus.mean (representative u) j = mean u j := by
  rw [mean_apply, mean_eq_average, average_eq_integral,
    MeasureTheory.eval_integral (fun i ↦ integrable_representative_component u i) j,
    mean_eq_average, average_eq_integral]
  exact integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ representative_apply u x j

/-- A quotient-native constant vector Sobolev field. -/
def const (c : EuclideanSpace ℝ d) : PeriodicVectorW12 d :=
  ofComponents fun j ↦ PeriodicW12.const (c j)

@[simp]
theorem component_const (c : EuclideanSpace ℝ d) (j : d) :
    component (const c) j = PeriodicW12.const (c j) := by
  rw [const, component_ofComponents]

@[simp]
theorem mean_const (c : EuclideanSpace ℝ d) : mean (const c) = c := by
  apply PiLp.ext
  intro j
  simp only [mean_apply, component_const, PeriodicW12.mean_const]

@[simp]
theorem weakJacobianEntry_const (c : EuclideanSpace ℝ d) (i j : d) :
    weakJacobianEntry (const c) i j = 0 := by
  rw [weakJacobianEntry_eq, component_const, PeriodicW12.weakDeriv_const]

@[simp]
theorem weakJacobian_const (c : EuclideanSpace ℝ d) : weakJacobian (const c) = 0 := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro j
  simp only [weakJacobian_apply, weakJacobianEntry_const, PiLp.zero_apply]

@[simp]
theorem weakDivergence_const (c : EuclideanSpace ℝ d) : weakDivergence (const c) = 0 := by
  rw [weakDivergence_eq_sum]
  simp only [weakJacobianEntry_const, Finset.sum_const_zero]

end PeriodicVectorW12

/-- The closed vector periodic `W¹,²` subspace with vanishing componentwise mean. -/
def periodicMeanZeroVectorW12Submodule (d : Type*) [Fintype d] :
    ClosedSubmodule ℝ (PeriodicVectorW12 d) :=
  (⊥ : ClosedSubmodule ℝ (EuclideanSpace ℝ d)).comap PeriodicVectorW12.meanL

theorem mem_periodicMeanZeroVectorW12Submodule_iff (u : PeriodicVectorW12 d) :
    u ∈ periodicMeanZeroVectorW12Submodule d ↔ PeriodicVectorW12.mean u = 0 := by
  simp only [periodicMeanZeroVectorW12Submodule, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot, PeriodicVectorW12.mean]

theorem mem_periodicMeanZeroVectorW12Submodule_iff_components (u : PeriodicVectorW12 d) :
    u ∈ periodicMeanZeroVectorW12Submodule d ↔
      ∀ j : d, mean (PeriodicW12.value (PeriodicVectorW12.component u j)) = 0 := by
  rw [mem_periodicMeanZeroVectorW12Submodule_iff]
  constructor
  · intro h j
    have hj := congrArg (fun v : EuclideanSpace ℝ d ↦ v j) h
    simpa only [PeriodicVectorW12.mean_apply, PiLp.zero_apply] using hj
  · intro h
    apply PiLp.ext
    intro j
    simpa only [PeriodicVectorW12.mean_apply, PiLp.zero_apply] using h j

theorem mem_periodicMeanZeroVectorW12Submodule_iff_representative (u : PeriodicVectorW12 d) :
    u ∈ periodicMeanZeroVectorW12Submodule d ↔
      mean (PeriodicVectorW12.representative u) = 0 := by
  rw [mem_periodicMeanZeroVectorW12Submodule_iff_components]
  constructor
  · intro h
    funext j
    change mean (PeriodicVectorW12.representative u) j = (0 : ℝ)
    rw [PeriodicVectorW12.mean_representative_apply]
    simpa only [PeriodicVectorW12.mean_apply] using h j
  · intro h j
    rw [← PeriodicVectorW12.mean_apply, ← PeriodicVectorW12.mean_representative_apply]
    have hj := congrFun h j
    simpa using hj

/-- Constant vector fields are removed by the mean-zero condition exactly when their value is
zero. -/
theorem periodicVectorW12_const_mem_meanZero_iff (c : EuclideanSpace ℝ d) :
    PeriodicVectorW12.const c ∈ periodicMeanZeroVectorW12Submodule d ↔ c = 0 := by
  rw [mem_periodicMeanZeroVectorW12Submodule_iff, PeriodicVectorW12.mean_const]

/-- Mean-zero vector-valued periodic `W¹,²`. -/
abbrev PeriodicMeanZeroVectorW12 (d : Type*) [Fintype d] :=
  (periodicMeanZeroVectorW12Submodule d).toSubmodule

/-- The mean-zero incompressible energy space as an intersection of closed subspaces. -/
def periodicMeanZeroDivergenceFreeW12Submodule (d : Type*) [Fintype d] :
    ClosedSubmodule ℝ (PeriodicVectorW12 d) :=
  periodicMeanZeroVectorW12Submodule d ⊓ periodicDivergenceFreeW12Submodule d

theorem mem_periodicMeanZeroDivergenceFreeW12Submodule_iff (u : PeriodicVectorW12 d) :
    u ∈ periodicMeanZeroDivergenceFreeW12Submodule d ↔
      mean (PeriodicVectorW12.representative u) = 0 ∧
        WeaklyDivergenceFree (PeriodicVectorW12.representative u) := by
  rw [periodicMeanZeroDivergenceFreeW12Submodule, ClosedSubmodule.mem_inf,
    mem_periodicMeanZeroVectorW12Submodule_iff_representative,
    mem_periodicDivergenceFreeW12Submodule_iff_weaklyDivergenceFree]

/-- Quotient-native membership in the mean-zero incompressible energy space. -/
theorem mem_periodicMeanZeroDivergenceFreeW12Submodule_iff_mean_weakDivergence
    (u : PeriodicVectorW12 d) :
    u ∈ periodicMeanZeroDivergenceFreeW12Submodule d ↔
      PeriodicVectorW12.mean u = 0 ∧ PeriodicVectorW12.weakDivergence u = 0 := by
  rw [periodicMeanZeroDivergenceFreeW12Submodule, ClosedSubmodule.mem_inf,
    mem_periodicMeanZeroVectorW12Submodule_iff,
    mem_periodicDivergenceFreeW12Submodule_iff]

/-- Every constant vector field belongs to the larger divergence-free space. -/
theorem periodicVectorW12_const_mem_divergenceFree (c : EuclideanSpace ℝ d) :
    PeriodicVectorW12.const c ∈ periodicDivergenceFreeW12Submodule d := by
  rw [mem_periodicDivergenceFreeW12Submodule_iff, PeriodicVectorW12.weakDivergence_const]

/-- A constant belongs to the mean-zero incompressible energy space exactly when it vanishes. -/
theorem periodicVectorW12_const_mem_meanZeroDivergenceFree_iff
    (c : EuclideanSpace ℝ d) :
    PeriodicVectorW12.const c ∈ periodicMeanZeroDivergenceFreeW12Submodule d ↔ c = 0 := by
  rw [periodicMeanZeroDivergenceFreeW12Submodule, ClosedSubmodule.mem_inf,
    periodicVectorW12_const_mem_meanZero_iff]
  simp only [periodicVectorW12_const_mem_divergenceFree, and_true]

/-- The mean-zero weakly incompressible periodic energy space. -/
abbrev PeriodicMeanZeroDivergenceFreeW12 (d : Type*) [Fintype d] :=
  (periodicMeanZeroDivergenceFreeW12Submodule d).toSubmodule

namespace PeriodicVectorW12

/-- The sharp vector Poincare inequality, obtained by summing the scalar inequalities over value
components. -/
theorem norm_value_sq_le_inv_four_pi_sq_mul_norm_weakJacobian_sq
    (u : PeriodicVectorW12 d) (hmean : mean u = 0) :
    ‖value u‖ ^ 2 ≤ ((2 * Real.pi) ^ 2)⁻¹ * ‖weakJacobian u‖ ^ 2 := by
  rw [norm_value_sq_eq_sum_norm_value_component_sq,
    norm_weakJacobian_sq_eq_sum_norm_entry_sq]
  calc
    ∑ j, ‖PeriodicW12.value (component u j)‖ ^ 2 ≤
        ∑ j, ((2 * Real.pi) ^ 2)⁻¹ * ‖PeriodicW12.gradient (component u j)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply PeriodicW12.norm_value_sq_le_inv_four_pi_sq_mul_norm_gradient_sq
      have hj := congrArg (fun v : EuclideanSpace ℝ d ↦ v j) hmean
      simpa only [mean_apply, PiLp.zero_apply] using hj
    _ = ((2 * Real.pi) ^ 2)⁻¹ * ∑ i, ∑ j, ‖weakJacobianEntry u i j‖ ^ 2 := by
      simp_rw [PeriodicW12.norm_gradient_sq_eq_sum_norm_weakDeriv_sq,
        ← weakJacobianEntry_eq]
      rw [← Finset.mul_sum, Finset.sum_comm]

/-- On mean-zero fields, the weak Jacobian controls the full vector `W¹,²` graph norm. -/
theorem norm_sq_le_one_add_inv_four_pi_sq_mul_norm_weakJacobian_sq
    (u : PeriodicVectorW12 d) (hmean : mean u = 0) :
    ‖u‖ ^ 2 ≤ (1 + ((2 * Real.pi) ^ 2)⁻¹) * ‖weakJacobian u‖ ^ 2 := by
  rw [norm_sq_eq_norm_value_sq_add_norm_weakJacobian_sq]
  have hp := norm_value_sq_le_inv_four_pi_sq_mul_norm_weakJacobian_sq u hmean
  nlinarith [sq_nonneg ‖weakJacobian u‖]

end PeriodicVectorW12

namespace PeriodicMeanZeroVectorW12

instance : InnerProductSpace ℝ (PeriodicMeanZeroVectorW12 d) where
  inner u v := ∑ j, inner ℝ ((u : PeriodicVectorW12 d) j) ((v : PeriodicVectorW12 d) j)
  norm_sq_eq_re_inner u := by
    change ‖(u : PeriodicVectorW12 d)‖ ^ 2 = _
    simp only [PiLp.norm_sq_eq_of_L2, map_sum, ← norm_sq_eq_re_inner]
  conj_inner_symm u v := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact inner_conj_symm ((u : PeriodicVectorW12 d) j) ((v : PeriodicVectorW12 d) j)
  add_left u v w := by
    change ∑ j, inner ℝ (((u : PeriodicVectorW12 d) + v) j) ((w : PeriodicVectorW12 d) j) = _
    simp only [PiLp.add_apply, inner_add_left, Finset.sum_add_distrib]
  smul_left u v r := by
    change ∑ j, inner ℝ ((r • (u : PeriodicVectorW12 d)) j) ((v : PeriodicVectorW12 d) j) = _
    simp only [PiLp.smul_apply, inner_smul_left, Finset.mul_sum]

instance : CompleteSpace (PeriodicMeanZeroVectorW12 d) :=
  (periodicMeanZeroVectorW12Submodule d).isClosed.completeSpace_coe

end PeriodicMeanZeroVectorW12

namespace PeriodicMeanZeroDivergenceFreeW12

instance : InnerProductSpace ℝ (PeriodicMeanZeroDivergenceFreeW12 d) where
  inner u v := ∑ j, inner ℝ ((u : PeriodicVectorW12 d) j) ((v : PeriodicVectorW12 d) j)
  norm_sq_eq_re_inner u := by
    change ‖(u : PeriodicVectorW12 d)‖ ^ 2 = _
    simp only [PiLp.norm_sq_eq_of_L2, map_sum, ← norm_sq_eq_re_inner]
  conj_inner_symm u v := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact inner_conj_symm ((u : PeriodicVectorW12 d) j) ((v : PeriodicVectorW12 d) j)
  add_left u v w := by
    change ∑ j, inner ℝ (((u : PeriodicVectorW12 d) + v) j) ((w : PeriodicVectorW12 d) j) = _
    simp only [PiLp.add_apply, inner_add_left, Finset.sum_add_distrib]
  smul_left u v r := by
    change ∑ j, inner ℝ ((r • (u : PeriodicVectorW12 d)) j) ((v : PeriodicVectorW12 d) j) = _
    simp only [PiLp.smul_apply, inner_smul_left, Finset.mul_sum]

instance : CompleteSpace (PeriodicMeanZeroDivergenceFreeW12 d) :=
  (periodicMeanZeroDivergenceFreeW12Submodule d).isClosed.completeSpace_coe

/-- The continuous inclusion of the mean-zero solenoidal energy space into vector-valued
periodic `W¹,²`. -/
def toPeriodicVectorW12L :
    PeriodicMeanZeroDivergenceFreeW12 d →L[ℝ] PeriodicVectorW12 d :=
  (periodicMeanZeroDivergenceFreeW12Submodule d).toSubmodule.subtypeL

/-- The ambient periodic vector `W¹,²` class of an energy-space vector. -/
def toPeriodicVectorW12 (u : PeriodicMeanZeroDivergenceFreeW12 d) : PeriodicVectorW12 d :=
  toPeriodicVectorW12L u

@[simp]
theorem toPeriodicVectorW12L_apply (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    toPeriodicVectorW12L u = toPeriodicVectorW12 u := by
  rw [toPeriodicVectorW12]

theorem toPeriodicVectorW12_eq_coe (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    toPeriodicVectorW12 u = (u : PeriodicVectorW12 d) := by
  rfl

/-- An energy-space element has zero quotient-level componentwise mean. -/
theorem mean_eq_zero (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    PeriodicVectorW12.mean (u : PeriodicVectorW12 d) = 0 :=
  mem_periodicMeanZeroVectorW12Submodule_iff (u : PeriodicVectorW12 d) |>.mp
    (ClosedSubmodule.mem_inf.mp u.2).1

/-- The canonical representative of an energy-space element is weakly divergence-free. -/
theorem weaklyDivergenceFree (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    WeaklyDivergenceFree (PeriodicVectorW12.representative (u : PeriodicVectorW12 d)) :=
  mem_periodicDivergenceFreeW12Submodule_iff_weaklyDivergenceFree
    (u : PeriodicVectorW12 d) |>.mp (ClosedSubmodule.mem_inf.mp u.2).2

/-- Sharp value-norm Poincare inequality on the mean-zero incompressible energy space. -/
theorem norm_value_sq_le_inv_four_pi_sq_mul_norm_weakJacobian_sq
    (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    ‖PeriodicVectorW12.value (u : PeriodicVectorW12 d)‖ ^ 2 ≤
      ((2 * Real.pi) ^ 2)⁻¹ *
        ‖PeriodicVectorW12.weakJacobian (u : PeriodicVectorW12 d)‖ ^ 2 :=
  PeriodicVectorW12.norm_value_sq_le_inv_four_pi_sq_mul_norm_weakJacobian_sq
    (u : PeriodicVectorW12 d) (mean_eq_zero u)

/-- The weak Jacobian controls the full graph norm on the mean-zero incompressible energy
space. -/
theorem norm_sq_le_one_add_inv_four_pi_sq_mul_norm_weakJacobian_sq
    (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    ‖u‖ ^ 2 ≤ (1 + ((2 * Real.pi) ^ 2)⁻¹) *
      ‖PeriodicVectorW12.weakJacobian (u : PeriodicVectorW12 d)‖ ^ 2 := by
  change ‖(u : PeriodicVectorW12 d)‖ ^ 2 ≤ _
  exact PeriodicVectorW12.norm_sq_le_one_add_inv_four_pi_sq_mul_norm_weakJacobian_sq
    (u : PeriodicVectorW12 d) (mean_eq_zero u)

end PeriodicMeanZeroDivergenceFreeW12

end UnitAddTorus
