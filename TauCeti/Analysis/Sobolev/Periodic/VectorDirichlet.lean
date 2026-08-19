/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx, Codex
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.VectorW12
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The weak periodic vector Dirichlet form

This file packages the weak-Jacobian energy on vector-valued periodic `W¹,²` as a bounded
continuous bilinear form.  For `u` and `v` in `PeriodicVectorW12 d`,

`a(u,v) = ⟪weakJacobian u, weakJacobian v⟫ = ∑ i, ∑ j, ⟪∂ᵢuⱼ, ∂ᵢvⱼ⟫_{L²}`.

The same curried continuous linear map is named `variationalNegativeLaplacianL` when it is read
as the variational negative Laplacian: by definition its sign convention is
`⟨-Δu,v⟩ = a(u,v)`.  Its codomain is the continuous dual of `PeriodicVectorW12 d`; no
`L²`-valued Laplacian or smooth-density identification is asserted here.

## Main declarations

* `UnitAddTorus.periodicVectorDirichletFormL`: the bounded curried bilinear form.
* `UnitAddTorus.periodicVectorDirichletForm_eq_sum_inner`: its componentwise formula.
* `UnitAddTorus.periodicVectorDirichletForm_self`: the weak-Jacobian energy identity.
* `UnitAddTorus.variationalNegativeLaplacianL`: the variational operator `-Δ`.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory
open scoped ENNReal

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq

namespace PeriodicVectorW12

/-- The weak-Jacobian projection is contractive for the periodic vector `W¹,²` graph norm. -/
theorem norm_weakJacobian_le (u : PeriodicVectorW12 d) :
    ‖weakJacobian u‖ ≤ ‖u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    norm_sq_eq_norm_value_sq_add_norm_weakJacobian_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

end PeriodicVectorW12

/-- The algebraic weak vector Dirichlet form before it is upgraded with its sharp graph-norm
bound. -/
private def periodicVectorDirichletFormLinear :
    PeriodicVectorW12 d →ₗ[ℝ] PeriodicVectorW12 d →ₗ[ℝ] ℝ :=
  (innerₗ (PeriodicWeakJacobianL2 d)).compl₁₂
    PeriodicVectorW12.weakJacobianL.toLinearMap
    PeriodicVectorW12.weakJacobianL.toLinearMap

private theorem periodicVectorDirichletFormLinear_bound
    (u v : PeriodicVectorW12 d) :
    ‖periodicVectorDirichletFormLinear u v‖ ≤ 1 * ‖u‖ * ‖v‖ := by
  simp only [periodicVectorDirichletFormLinear, LinearMap.compl₁₂_apply,
    innerₗ_apply_apply, one_mul, Real.norm_eq_abs]
  have hu : PeriodicVectorW12.weakJacobianL.toLinearMap u =
      PeriodicVectorW12.weakJacobian u :=
    PeriodicVectorW12.weakJacobianL_apply u
  have hv : PeriodicVectorW12.weakJacobianL.toLinearMap v =
      PeriodicVectorW12.weakJacobian v :=
    PeriodicVectorW12.weakJacobianL_apply v
  rw [hu, hv]
  exact (abs_real_inner_le_norm
      (PeriodicVectorW12.weakJacobian u) (PeriodicVectorW12.weakJacobian v)).trans
    (mul_le_mul (PeriodicVectorW12.norm_weakJacobian_le u)
      (PeriodicVectorW12.norm_weakJacobian_le v) (norm_nonneg _) (norm_nonneg _))

/-- The weak vector Dirichlet form as a genuinely bounded, curried continuous bilinear map.
Its continuity constant with respect to the full periodic vector `W¹,²` graph norm is one. -/
def periodicVectorDirichletFormL :
    PeriodicVectorW12 d →L[ℝ] PeriodicVectorW12 d →L[ℝ] ℝ :=
  periodicVectorDirichletFormLinear.mkContinuous₂ 1
    periodicVectorDirichletFormLinear_bound

/-- Scalar evaluation of the weak vector Dirichlet form. -/
def periodicVectorDirichletForm (u v : PeriodicVectorW12 d) : ℝ :=
  periodicVectorDirichletFormL u v

@[simp]
theorem periodicVectorDirichletFormL_apply_apply (u v : PeriodicVectorW12 d) :
    periodicVectorDirichletFormL u v = periodicVectorDirichletForm u v := by
  rw [periodicVectorDirichletForm]

/-- The canonical formula for the Dirichlet form is the Hilbert pairing of the two quotient-level
weak Jacobians. -/
theorem periodicVectorDirichletForm_eq_inner (u v : PeriodicVectorW12 d) :
    periodicVectorDirichletForm u v = inner ℝ
      (PeriodicVectorW12.weakJacobian u) (PeriodicVectorW12.weakJacobian v) := by
  simp only [periodicVectorDirichletForm, periodicVectorDirichletFormL,
    LinearMap.mkContinuous₂_apply, periodicVectorDirichletFormLinear,
    LinearMap.compl₁₂_apply, innerₗ_apply_apply]
  have hu : PeriodicVectorW12.weakJacobianL.toLinearMap u =
      PeriodicVectorW12.weakJacobian u :=
    PeriodicVectorW12.weakJacobianL_apply u
  have hv : PeriodicVectorW12.weakJacobianL.toLinearMap v =
      PeriodicVectorW12.weakJacobian v :=
    PeriodicVectorW12.weakJacobianL_apply v
  rw [hu, hv]

/-- Componentwise expansion of the weak vector Dirichlet form. -/
theorem periodicVectorDirichletForm_eq_sum_inner (u v : PeriodicVectorW12 d) :
    periodicVectorDirichletForm u v =
      ∑ i, ∑ j, inner ℝ (PeriodicVectorW12.weakJacobianEntry u i j)
        (PeriodicVectorW12.weakJacobianEntry v i j) := by
  rw [periodicVectorDirichletForm_eq_inner, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [PiLp.inner_apply]
  simp only [PeriodicVectorW12.weakJacobian_apply]

/-- Integral expansion of the weak vector Dirichlet form using the canonical `L²`
representatives of every weak-Jacobian entry. -/
theorem periodicVectorDirichletForm_eq_sum_integral (u v : PeriodicVectorW12 d) :
    periodicVectorDirichletForm u v =
      ∑ i, ∑ j, ∫ x, PeriodicVectorW12.weakJacobianEntry u i j x *
        PeriodicVectorW12.weakJacobianEntry v i j x := by
  rw [periodicVectorDirichletForm_eq_sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def]
  simp only [Real.inner_apply]

/-- The weak vector Dirichlet form is symmetric. -/
theorem periodicVectorDirichletForm_comm (u v : PeriodicVectorW12 d) :
    periodicVectorDirichletForm u v = periodicVectorDirichletForm v u := by
  rw [periodicVectorDirichletForm_eq_inner, periodicVectorDirichletForm_eq_inner,
    real_inner_comm]

/-- Sharp Cauchy--Schwarz estimate in terms of the two weak Jacobians. -/
theorem norm_periodicVectorDirichletForm_le_weakJacobian (u v : PeriodicVectorW12 d) :
    ‖periodicVectorDirichletForm u v‖ ≤
      ‖PeriodicVectorW12.weakJacobian u‖ * ‖PeriodicVectorW12.weakJacobian v‖ := by
  rw [periodicVectorDirichletForm_eq_inner, Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

/-- Cauchy--Schwarz estimate in the full periodic vector `W¹,²` graph norm. -/
theorem norm_periodicVectorDirichletForm_le (u v : PeriodicVectorW12 d) :
    ‖periodicVectorDirichletForm u v‖ ≤ ‖u‖ * ‖v‖ :=
  (norm_periodicVectorDirichletForm_le_weakJacobian u v).trans
    (mul_le_mul (PeriodicVectorW12.norm_weakJacobian_le u)
      (PeriodicVectorW12.norm_weakJacobian_le v) (norm_nonneg _) (norm_nonneg _))

/-- On the diagonal, the Dirichlet form is exactly the squared weak-Jacobian norm. -/
theorem periodicVectorDirichletForm_self (u : PeriodicVectorW12 d) :
    periodicVectorDirichletForm u u = ‖PeriodicVectorW12.weakJacobian u‖ ^ 2 := by
  rw [periodicVectorDirichletForm_eq_inner, real_inner_self_eq_norm_sq]

/-- The weak vector Dirichlet form is nonnegative on the diagonal. -/
theorem periodicVectorDirichletForm_nonneg (u : PeriodicVectorW12 d) :
    0 ≤ periodicVectorDirichletForm u u := by
  rw [periodicVectorDirichletForm_self]
  positivity

/-- A curried slice has operator norm at most the weak-Jacobian norm of its first argument. -/
theorem norm_periodicVectorDirichletFormL_apply_le_weakJacobian (u : PeriodicVectorW12 d) :
    ‖periodicVectorDirichletFormL u‖ ≤ ‖PeriodicVectorW12.weakJacobian u‖ := by
  apply (periodicVectorDirichletFormL u).opNorm_le_bound (norm_nonneg _)
  intro v
  rw [periodicVectorDirichletFormL_apply_apply]
  exact (norm_periodicVectorDirichletForm_le_weakJacobian u v).trans
    (mul_le_mul_of_nonneg_left (PeriodicVectorW12.norm_weakJacobian_le v) (norm_nonneg _))

/-- A curried slice has operator norm at most the full graph norm of its first argument. -/
theorem norm_periodicVectorDirichletFormL_apply_le (u : PeriodicVectorW12 d) :
    ‖periodicVectorDirichletFormL u‖ ≤ ‖u‖ :=
  (norm_periodicVectorDirichletFormL_apply_le_weakJacobian u).trans
    (PeriodicVectorW12.norm_weakJacobian_le u)

/-- The variational negative Laplacian.  This is a bounded map from periodic vector `W¹,²` into
its continuous dual, with the pinned convention `⟨-Δu,v⟩ = a(u,v)`. -/
def variationalNegativeLaplacianL :
    PeriodicVectorW12 d →L[ℝ] PeriodicVectorW12 d →L[ℝ] ℝ :=
  periodicVectorDirichletFormL

/-- Evaluation of the variational negative Laplacian is the weak vector Dirichlet form. -/
@[simp]
theorem variationalNegativeLaplacianL_apply_apply (u v : PeriodicVectorW12 d) :
    variationalNegativeLaplacianL u v = periodicVectorDirichletForm u v := by
  rfl

/-- The variational negative Laplacian obeys the unit graph-norm continuity estimate. -/
theorem norm_variationalNegativeLaplacianL_apply_le (u : PeriodicVectorW12 d) :
    ‖variationalNegativeLaplacianL u‖ ≤ ‖u‖ :=
  norm_periodicVectorDirichletFormL_apply_le u

end UnitAddTorus
