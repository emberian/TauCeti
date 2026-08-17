/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.EnergySpace
public import TauCeti.Analysis.Sobolev.Periodic.VectorDirichlet
public import TauCeti.Analysis.InnerProductSpace.LaxMilgram

/-!
# Weak periodic Stokes theory on the mean-zero solenoidal energy space

This file restricts the weak periodic vector Dirichlet form to
`PeriodicMeanZeroDivergenceFreeW12 d`.  The sharp periodic Poincare estimate makes that restricted
form coercive with constant

`(1 + ((2 * Real.pi) ^ 2)⁻¹)⁻¹`.

Lax--Milgram then gives the unit-viscosity weak Stokes problem: for every continuous functional
`ℓ` on the energy space, there is a unique `u` such that

`a_E(u,v) = ℓ(v)`

for every energy-space test vector `v`.  The construction remains entirely variational.  In
particular, it does not assert an `L²`-valued strong Stokes operator, recover a pressure, or use a
smooth-density identification.

This advances Layer 4, item 3, of the `IncompressibleFlows` roadmap at the variational
energy-space level.

## Main declarations

* `UnitAddTorus.periodicEnergyDirichletFormL`: the restricted bounded bilinear form.
* `UnitAddTorus.periodicEnergyDirichletForm_isCoercive`: its explicit coercivity.
* `UnitAddTorus.periodicWeakStokesRieszEquiv`: the Lax--Milgram Riesz-side equivalence.
* `UnitAddTorus.periodicWeakStokesSolutionL`: the continuous weak solution operator.
* `UnitAddTorus.periodicWeakStokesSolution_variational`: its variational equation.
* `UnitAddTorus.existsUnique_periodicWeakStokesSolution`: existence and uniqueness.
-/

public section

noncomputable section

namespace UnitAddTorus

open scoped InnerProductSpace

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq

/-- The weak vector Dirichlet form restricted to the concrete mean-zero solenoidal energy
space. -/
def periodicEnergyDirichletFormL :
    PeriodicMeanZeroDivergenceFreeW12 d →L[ℝ]
      PeriodicMeanZeroDivergenceFreeW12 d →L[ℝ] ℝ :=
  let inclusion : PeriodicMeanZeroDivergenceFreeW12 d →L[ℝ] PeriodicVectorW12 d :=
    PeriodicMeanZeroDivergenceFreeW12.toPeriodicVectorW12L
  let restrictRight : PeriodicVectorW12 d →L[ℝ]
      PeriodicMeanZeroDivergenceFreeW12 d →L[ℝ] ℝ :=
    ContinuousLinearMap.flip (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
      (E := PeriodicVectorW12 d)
      (F := PeriodicMeanZeroDivergenceFreeW12 d →L[ℝ] PeriodicVectorW12 d)
      (G := PeriodicMeanZeroDivergenceFreeW12 d →L[ℝ] ℝ)
      (σ₂₃ := RingHom.id ℝ) (σ₁₃ := RingHom.id ℝ)
      (ContinuousLinearMap.precompR (𝕜 := ℝ) (E := PeriodicVectorW12 d)
        (Fₗ := PeriodicVectorW12 d) (Gₗ := ℝ)
        (PeriodicMeanZeroDivergenceFreeW12 d)
        (periodicVectorDirichletFormL (d := d))) inclusion
  restrictRight.comp inclusion

/-- Scalar evaluation of the energy-space Dirichlet form. -/
def periodicEnergyDirichletForm
    (u v : PeriodicMeanZeroDivergenceFreeW12 d) : ℝ :=
  periodicEnergyDirichletFormL (d := d) u v

@[simp]
theorem periodicEnergyDirichletFormL_apply_apply
    (u v : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicEnergyDirichletFormL (d := d) u v =
      periodicEnergyDirichletForm (d := d) u v := by
  rw [periodicEnergyDirichletForm]

/-- Restriction agrees with evaluation of the ambient periodic vector Dirichlet form. -/
theorem periodicEnergyDirichletForm_eq_ambient
    (u v : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicEnergyDirichletForm u v =
      periodicVectorDirichletForm (u : PeriodicVectorW12 d) (v : PeriodicVectorW12 d) := by
  rw [periodicEnergyDirichletForm, periodicEnergyDirichletFormL]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    PeriodicMeanZeroDivergenceFreeW12.toPeriodicVectorW12L_apply,
    PeriodicMeanZeroDivergenceFreeW12.toPeriodicVectorW12_eq_coe]
  change periodicVectorDirichletFormL (d := d) (u : PeriodicVectorW12 d)
    (v : PeriodicVectorW12 d) = periodicVectorDirichletForm (u : PeriodicVectorW12 d) v
  rw [periodicVectorDirichletFormL_apply_apply]

/-- The restricted form is exactly the Hilbert pairing of the two ambient weak Jacobians. -/
theorem periodicEnergyDirichletForm_eq_inner_weakJacobian
    (u v : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicEnergyDirichletForm u v =
      inner ℝ (PeriodicVectorW12.weakJacobian (u : PeriodicVectorW12 d))
        (PeriodicVectorW12.weakJacobian (v : PeriodicVectorW12 d)) := by
  rw [periodicEnergyDirichletForm_eq_ambient, periodicVectorDirichletForm_eq_inner]

/-- The restricted weak Dirichlet form is symmetric. -/
theorem periodicEnergyDirichletForm_comm
    (u v : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicEnergyDirichletForm u v = periodicEnergyDirichletForm v u := by
  rw [periodicEnergyDirichletForm_eq_ambient, periodicEnergyDirichletForm_eq_ambient,
    periodicVectorDirichletForm_comm]

/-- On the diagonal, the restricted form is exactly the ambient weak-Jacobian energy. -/
theorem periodicEnergyDirichletForm_self
    (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicEnergyDirichletForm u u =
      ‖PeriodicVectorW12.weakJacobian (u : PeriodicVectorW12 d)‖ ^ 2 := by
  rw [periodicEnergyDirichletForm_eq_ambient, periodicVectorDirichletForm_self]

/-- The sharp multiplier in the graph-norm estimate on the periodic mean-zero energy space. -/
def periodicStokesGraphConstant : ℝ :=
  1 + ((2 * Real.pi) ^ 2)⁻¹

/-- The reciprocal graph constant used as the explicit weak Stokes coercivity constant. -/
def periodicStokesCoercivityConstant : ℝ :=
  periodicStokesGraphConstant⁻¹

theorem periodicStokesGraphConstant_pos : 0 < periodicStokesGraphConstant := by
  rw [periodicStokesGraphConstant]
  positivity

theorem periodicStokesCoercivityConstant_pos : 0 < periodicStokesCoercivityConstant := by
  rw [periodicStokesCoercivityConstant]
  exact inv_pos.mpr periodicStokesGraphConstant_pos

/-- Explicit coercivity of the restricted Dirichlet form, with the reciprocal of the sharp
graph-norm multiplier. -/
theorem periodicEnergyDirichletForm_coercive
    (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicStokesCoercivityConstant * ‖u‖ * ‖u‖ ≤
      periodicEnergyDirichletForm u u := by
  rw [periodicStokesCoercivityConstant, mul_assoc,
    inv_mul_le_iff₀ periodicStokesGraphConstant_pos,
    periodicEnergyDirichletForm_self]
  simpa only [periodicStokesGraphConstant, pow_two] using
    PeriodicMeanZeroDivergenceFreeW12.norm_sq_le_one_add_inv_four_pi_sq_mul_norm_weakJacobian_sq u

/-- The energy-space weak Dirichlet form satisfies the `IsCoercive` hypothesis used by
Lax--Milgram. -/
theorem periodicEnergyDirichletForm_isCoercive :
    @IsCoercive (PeriodicMeanZeroDivergenceFreeW12 d) inferInstance inferInstance
      (periodicEnergyDirichletFormL (d := d)) :=
  ⟨periodicStokesCoercivityConstant, periodicStokesCoercivityConstant_pos,
    periodicEnergyDirichletForm_coercive⟩

/-- The Riesz-side weak Stokes operator supplied by Lax--Milgram.  It sends `u` to the unique
energy-space vector representing the functional `v ↦ a_E(u,v)`. -/
def periodicWeakStokesRieszEquiv :
    PeriodicMeanZeroDivergenceFreeW12 d ≃L[ℝ]
      PeriodicMeanZeroDivergenceFreeW12 d :=
  @IsCoercive.continuousLinearEquivOfBilin
    (PeriodicMeanZeroDivergenceFreeW12 d) inferInstance inferInstance inferInstance
    (periodicEnergyDirichletFormL (d := d))
    (periodicEnergyDirichletForm_isCoercive (d := d))

/-- Characteristic identity of the Riesz-side weak Stokes equivalence. -/
theorem periodicWeakStokesRieszEquiv_inner
    (u v : PeriodicMeanZeroDivergenceFreeW12 d) :
    inner ℝ (periodicWeakStokesRieszEquiv (d := d) u) v =
      periodicEnergyDirichletForm u v := by
  rw [periodicWeakStokesRieszEquiv,
    IsCoercive.continuousLinearEquivOfBilin_apply,
    periodicEnergyDirichletFormL_apply_apply]

/-- The continuous weak Stokes solution operator from the energy-space dual. -/
def periodicWeakStokesSolutionL :
    StrongDual ℝ (PeriodicMeanZeroDivergenceFreeW12 d) →L[ℝ]
      PeriodicMeanZeroDivergenceFreeW12 d :=
  @IsCoercive.solutionOfFunctionalL
    (PeriodicMeanZeroDivergenceFreeW12 d) inferInstance inferInstance inferInstance
    (periodicEnergyDirichletFormL (d := d))
    (periodicEnergyDirichletForm_isCoercive (d := d))

/-- The weak Stokes solution for a continuous functional. -/
def periodicWeakStokesSolution
    (ℓ : StrongDual ℝ (PeriodicMeanZeroDivergenceFreeW12 d)) :
    PeriodicMeanZeroDivergenceFreeW12 d :=
  periodicWeakStokesSolutionL (d := d) ℓ

@[simp]
theorem periodicWeakStokesSolutionL_apply
    (ℓ : StrongDual ℝ (PeriodicMeanZeroDivergenceFreeW12 d)) :
    periodicWeakStokesSolutionL (d := d) ℓ = periodicWeakStokesSolution (d := d) ℓ := by
  rw [periodicWeakStokesSolution]

/-- The named solution agrees with Tau Ceti's functional form of the Lax--Milgram solution. -/
theorem periodicWeakStokesSolution_eq_solutionOfFunctional
    (ℓ : StrongDual ℝ (PeriodicMeanZeroDivergenceFreeW12 d)) :
    periodicWeakStokesSolution ℓ =
      @IsCoercive.solutionOfFunctional
        (PeriodicMeanZeroDivergenceFreeW12 d) inferInstance inferInstance inferInstance
        (periodicEnergyDirichletFormL (d := d))
        (periodicEnergyDirichletForm_isCoercive (d := d)) ℓ := by
  unfold periodicWeakStokesSolution periodicWeakStokesSolutionL
  exact @IsCoercive.solutionOfFunctionalL_apply
    (PeriodicMeanZeroDivergenceFreeW12 d) inferInstance inferInstance inferInstance
    (periodicEnergyDirichletFormL (d := d))
    (periodicEnergyDirichletForm_isCoercive (d := d)) ℓ

/-- The weak Stokes solution satisfies `a_E(u,v) = ℓ(v)` for every energy-space test vector. -/
@[simp]
theorem periodicWeakStokesSolution_variational
    (ℓ : StrongDual ℝ (PeriodicMeanZeroDivergenceFreeW12 d))
    (v : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicEnergyDirichletForm (periodicWeakStokesSolution ℓ) v = ℓ v := by
  rw [periodicWeakStokesSolution_eq_solutionOfFunctional, ←
    periodicEnergyDirichletFormL_apply_apply]
  exact @IsCoercive.apply_solutionOfFunctional_eq
    (PeriodicMeanZeroDivergenceFreeW12 d) inferInstance inferInstance inferInstance
    (periodicEnergyDirichletFormL (d := d))
    (periodicEnergyDirichletForm_isCoercive (d := d)) ℓ v

/-- A vector satisfying the weak Stokes variational equation is the named solution. -/
theorem eq_periodicWeakStokesSolution
    {ℓ : StrongDual ℝ (PeriodicMeanZeroDivergenceFreeW12 d)}
    {u : PeriodicMeanZeroDivergenceFreeW12 d}
    (hu : ∀ v, periodicEnergyDirichletForm u v = ℓ v) :
    u = periodicWeakStokesSolution ℓ := by
  rw [periodicWeakStokesSolution_eq_solutionOfFunctional]
  apply @IsCoercive.eq_solutionOfFunctional
    (PeriodicMeanZeroDivergenceFreeW12 d) inferInstance inferInstance inferInstance
    (periodicEnergyDirichletFormL (d := d))
    (periodicEnergyDirichletForm_isCoercive (d := d)) ℓ u
  intro v
  simpa only [periodicEnergyDirichletFormL_apply_apply] using hu v

/-- Existence and uniqueness of the unit-viscosity weak periodic Stokes solution for every
continuous functional on the mean-zero solenoidal energy space. -/
theorem existsUnique_periodicWeakStokesSolution
    (ℓ : StrongDual ℝ (PeriodicMeanZeroDivergenceFreeW12 d)) :
    ∃! u : PeriodicMeanZeroDivergenceFreeW12 d,
      ∀ v, periodicEnergyDirichletForm u v = ℓ v :=
  ⟨periodicWeakStokesSolution ℓ, periodicWeakStokesSolution_variational ℓ,
    fun _ hu ↦ eq_periodicWeakStokesSolution hu⟩

/-- A priori energy-space estimate for the weak Stokes solution. -/
theorem norm_periodicWeakStokesSolution_le
    (ℓ : StrongDual ℝ (PeriodicMeanZeroDivergenceFreeW12 d)) :
    ‖periodicWeakStokesSolution ℓ‖ ≤ periodicStokesGraphConstant * ‖ℓ‖ := by
  let u : PeriodicMeanZeroDivergenceFreeW12 d := periodicWeakStokesSolution ℓ
  have henergy : periodicStokesCoercivityConstant * ‖u‖ * ‖u‖ ≤
      ‖ℓ‖ * ‖u‖ := by
    calc
      periodicStokesCoercivityConstant * ‖u‖ * ‖u‖ ≤
          periodicEnergyDirichletForm u u := periodicEnergyDirichletForm_coercive u
      _ = ℓ u := periodicWeakStokesSolution_variational ℓ u
      _ ≤ ‖ℓ u‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ ‖ℓ‖ * ‖u‖ :=
        @ContinuousLinearMap.le_opNorm ℝ ℝ
          (PeriodicMeanZeroDivergenceFreeW12 d) ℝ
          inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          (RingHom.id ℝ) inferInstance ℓ u
  by_cases hu : ‖u‖ = 0
  · rw [hu]
    exact mul_nonneg periodicStokesGraphConstant_pos.le (norm_nonneg ℓ)
  · have hu_pos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
    have hcancel : periodicStokesCoercivityConstant * ‖u‖ ≤ ‖ℓ‖ := by
      exact le_of_mul_le_mul_right (by simpa only [mul_assoc] using henergy) hu_pos
    rw [periodicStokesCoercivityConstant] at hcancel
    exact (inv_mul_le_iff₀ periodicStokesGraphConstant_pos).mp hcancel

end UnitAddTorus
