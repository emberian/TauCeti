/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.VectorField.Flat.Basic

/-!
# Smooth flat Laplacians and Green identities on finite unit tori

This file defines scalar and vector Laplacians on `UnitAddTorus d` for an arbitrary finite
coordinate type.  The sign convention is pinned intrinsically by

`scalarLaplacian f = divergence (gradient f)`

and, componentwise, by `vectorLaplacian u = tensorDivergence (jacobian u)`.  Thus a Fourier mode
of frequency `k` has Laplacian eigenvalue `-4π² |k|²`: `Δ` is nonpositive in the `L²` pairing,
while `-Δ` (and the corresponding Stokes operator) is positive.

The regularity predicates below require only the pure-coordinate second derivatives used by the
Laplacian.  They do not assert existence, continuity, or commutation of mixed partials.  Green's
identities retain explicit integrability hypotheses for every summand, avoiding the totalized
value of the Bochner integral on non-integrable fields.

This is a classical smooth substrate.  No weak `W¹,²` Green identity or viscous cancellation is
claimed here; that extension still requires the bounded-operator and density bridge.

## Main declarations

* `UnitAddTorus.scalarLaplacian`: scalar `Δ = div grad`.
* `UnitAddTorus.vectorLaplacian`: componentwise vector `Δ = div jacobian`.
* `UnitAddTorus.integral_scalarLaplacian_eq_zero`: periodic scalar Laplacian has mean zero.
* `UnitAddTorus.integral_mul_scalarLaplacian_eq_neg_integral_pairing_gradient`: scalar
  Green identity.
* `UnitAddTorus.integral_pairing_vectorLaplacian_eq_neg_sum_integral_jacobian`: vector
  Green identity.
* `UnitAddTorus.integral_pairing_vectorLaplacian_self_eq_neg_sum_integral_sq`: diagonal
  viscous dissipation identity.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory
open scoped BigOperators

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The scalar flat Laplacian with sign convention `Δ = div grad`. -/
def scalarLaplacian (f : ScalarField d) : ScalarField d :=
  divergence (gradient f)

/-- The componentwise vector flat Laplacian, equivalently divergence of the flat Jacobian. -/
def vectorLaplacian (u : VectorField d) : VectorField d :=
  tensorDivergence (jacobian u)

/-- Pure-coordinate classical regularity sufficient to interpret the scalar Laplacian.

The first clause says that every `∂ᵢ f` is a genuine classical derivative.  The second says that
this first derivative is itself `C¹` in the same direction.  No mixed regularity is included. -/
def ContDiffForScalarLaplacian (f : ScalarField d) : Prop :=
  (∀ i, ContDiffAlongCoordinate f i) ∧
    ∀ i, ContDiffAlongCoordinate (coordinateDerivative f i) i

omit [Fintype d] in
/-- Constructor-and-eliminator form of pure-coordinate scalar Laplacian regularity. -/
theorem contDiffForScalarLaplacian_iff {f : ScalarField d} :
    ContDiffForScalarLaplacian f ↔
      (∀ i, ContDiffAlongCoordinate f i) ∧
        ∀ i, ContDiffAlongCoordinate (coordinateDerivative f i) i :=
  Iff.rfl

/-- Pure-coordinate classical regularity sufficient to interpret the vector Laplacian.

No mixed derivative of a component is required. -/
def ContDiffForVectorLaplacian (u : VectorField d) : Prop :=
  ContDiffVectorField u ∧
    ∀ i j, ContDiffAlongCoordinate (componentDerivative u i j) i

omit [Fintype d] in
/-- Constructor-and-eliminator form of pure-coordinate vector Laplacian regularity. -/
theorem contDiffForVectorLaplacian_iff {u : VectorField d} :
    ContDiffForVectorLaplacian u ↔
      ContDiffVectorField u ∧
        ∀ i j, ContDiffAlongCoordinate (componentDerivative u i j) i :=
  Iff.rfl

omit [Fintype d] in
/-- First-order coordinate regularity contained in scalar Laplacian regularity. -/
theorem ContDiffForScalarLaplacian.firstOrder {f : ScalarField d}
    (hf : ContDiffForScalarLaplacian f) (i : d) :
    ContDiffAlongCoordinate f i := by
  exact hf.1 i

omit [Fintype d] in
/-- Pure second-coordinate regularity contained in scalar Laplacian regularity. -/
theorem ContDiffForScalarLaplacian.pureSecondOrder {f : ScalarField d}
    (hf : ContDiffForScalarLaplacian f) (i : d) :
    ContDiffAlongCoordinate (coordinateDerivative f i) i := by
  exact hf.2 i

omit [Fintype d] in
/-- First-order component regularity contained in vector Laplacian regularity. -/
theorem ContDiffForVectorLaplacian.firstOrder {u : VectorField d}
    (hu : ContDiffForVectorLaplacian u) :
    ContDiffVectorField u := by
  exact hu.1

omit [Fintype d] in
/-- Pure second-coordinate component regularity contained in vector Laplacian regularity. -/
theorem ContDiffForVectorLaplacian.pureSecondOrder {u : VectorField d}
    (hu : ContDiffForVectorLaplacian u) (i j : d) :
    ContDiffAlongCoordinate (componentDerivative u i j) i := by
  exact hu.2 i j

/-- The scalar Laplacian is definitionally pinned to divergence of the gradient. -/
theorem scalarLaplacian_eq_divergence_gradient (f : ScalarField d) :
    scalarLaplacian f = divergence (gradient f) := by
  rfl

/-- The vector Laplacian is definitionally pinned to tensor divergence of the Jacobian. -/
theorem vectorLaplacian_eq_tensorDivergence_jacobian (u : VectorField d) :
    vectorLaplacian u = tensorDivergence (jacobian u) := by
  rfl

@[simp]
theorem scalarLaplacian_apply (f : ScalarField d) (x : _root_.UnitAddTorus d) :
    scalarLaplacian f x =
      ∑ i, coordinateDerivative (coordinateDerivative f i) i x := by
  simp only [scalarLaplacian, divergence_apply, jacobian_apply, componentDerivative_apply,
    gradient_apply]

@[simp]
theorem vectorLaplacian_apply (u : VectorField d) (x : _root_.UnitAddTorus d) (j : d) :
    vectorLaplacian u x j =
      ∑ i, coordinateDerivative (componentDerivative u i j) i x := by
  simp only [vectorLaplacian, tensorDivergence_apply, jacobian_apply]

/-- Fully expanded coordinate formula for the componentwise vector Laplacian. -/
theorem vectorLaplacian_apply_coordinate (u : VectorField d) (x : _root_.UnitAddTorus d)
    (j : d) :
    vectorLaplacian u x j =
      ∑ i, coordinateDerivative (coordinateDerivative (fun z ↦ u z j) i) i x := by
  rw [vectorLaplacian_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [componentDerivative_eq]

/-- The vector Laplacian acts componentwise by the scalar Laplacian. -/
theorem vectorLaplacian_apply_eq_scalarLaplacian_component (u : VectorField d)
    (x : _root_.UnitAddTorus d) (j : d) :
    vectorLaplacian u x j = scalarLaplacian (fun z ↦ u z j) x := by
  simp only [vectorLaplacian_apply_coordinate, scalarLaplacian_apply]

theorem scalarLaplacian_const (c : ℝ) (x : _root_.UnitAddTorus d) :
    scalarLaplacian (fun _ ↦ c) x = 0 := by
  simp only [scalarLaplacian_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  have hzero : coordinateDerivative (fun _ : _root_.UnitAddTorus d ↦ c) i = fun _ ↦ 0 := by
    funext y
    exact coordinateDerivative_const c i y
  rw [hzero]
  exact coordinateDerivative_const 0 i x

theorem vectorLaplacian_const (c : d → ℝ) (x : _root_.UnitAddTorus d) (j : d) :
    vectorLaplacian (fun _ ↦ c) x j = 0 := by
  rw [vectorLaplacian_apply_eq_scalarLaplacian_component]
  exact scalarLaplacian_const (c j) x

/-- The integral of a sufficiently regular scalar Laplacian is zero on a periodic unit torus. -/
theorem integral_scalarLaplacian_eq_zero (g : ScalarField d)
    (hg : ContDiffForScalarLaplacian g)
    (hsecond : ∀ i,
      Integrable (coordinateDerivative (coordinateDerivative g i) i)) :
    (∫ x, scalarLaplacian g x) = 0 := by
  change (∫ x, divergence (gradient g) x) = 0
  apply integral_divergence_eq_zero (gradient g)
  · intro i
    simpa only [gradient_apply] using hg.pureSecondOrder i
  · intro i
    rw [componentDerivative_eq]
    simpa only [gradient_apply] using hsecond i

/-- Scalar Green identity on a finite unit torus:
`∫ f Δg = -∫ ∇f · ∇g`.

The two integrability families are exactly the summands on the left and right. -/
theorem integral_mul_scalarLaplacian_eq_neg_integral_pairing_gradient
    (f g : ScalarField d)
    (hf : ∀ i, ContDiffAlongCoordinate f i)
    (hg : ContDiffForScalarLaplacian g)
    (hleft : ∀ i, Integrable (fun x ↦
      f x * coordinateDerivative (coordinateDerivative g i) i x))
    (hright : ∀ i, Integrable (fun x ↦
      coordinateDerivative f i x * coordinateDerivative g i x)) :
    (∫ x, f x * scalarLaplacian g x) =
      -(∫ x, pairing (gradient f) (gradient g) x) := by
  have hcomponent : ∀ i,
      (∫ x, f x * coordinateDerivative (coordinateDerivative g i) i x) =
        -(∫ x, coordinateDerivative f i x * coordinateDerivative g i x) := by
    intro i
    exact integral_mul_coordinateDerivative_eq_neg f (coordinateDerivative g i) i
      (hf i) (hg.pureSecondOrder i) (hleft i) (hright i)
  calc
    (∫ x, f x * scalarLaplacian g x) =
        ∫ x, ∑ i, f x * coordinateDerivative (coordinateDerivative g i) i x := by
      congr 1
      funext x
      simp only [scalarLaplacian_apply, Finset.mul_sum]
    _ = ∑ i, ∫ x, f x * coordinateDerivative (coordinateDerivative g i) i x := by
      exact integral_finsetSum Finset.univ fun i _hi ↦ hleft i
    _ = ∑ i, -(∫ x, coordinateDerivative f i x * coordinateDerivative g i x) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcomponent i
    _ = -(∑ i, ∫ x, coordinateDerivative f i x * coordinateDerivative g i x) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i, coordinateDerivative f i x * coordinateDerivative g i x) := by
      rw [integral_finsetSum Finset.univ fun i _hi ↦ hright i]
    _ = -(∫ x, pairing (gradient f) (gradient g) x) := by
      congr 2
      funext x
      simp only [pairing_apply, gradient_apply]

/-- Vector Green identity on a finite unit torus:
`∫ u · Δv = -∑ᵢⱼ ∫ (∂ᵢuⱼ)(∂ᵢvⱼ)`.

Only pure-coordinate second regularity of `v` is used; no mixed derivative is formed. -/
theorem integral_pairing_vectorLaplacian_eq_neg_sum_integral_jacobian
    (u v : VectorField d)
    (hu : ContDiffVectorField u)
    (hv : ContDiffForVectorLaplacian v)
    (hleft : ∀ i j, Integrable (fun x ↦
      u x j * coordinateDerivative (componentDerivative v i j) i x))
    (hright : ∀ i j, Integrable (fun x ↦
      componentDerivative u i j x * componentDerivative v i j x)) :
    (∫ x, pairing u (vectorLaplacian v) x) =
      -(∑ i, ∑ j, ∫ x,
        componentDerivative u i j x * componentDerivative v i j x) := by
  have hcomponent : ∀ i j,
      (∫ x, u x j * coordinateDerivative (componentDerivative v i j) i x) =
        -(∫ x, componentDerivative u i j x * componentDerivative v i j x) := by
    intro i j
    have hright' : Integrable (fun x ↦
        coordinateDerivative (fun z ↦ u z j) i x * componentDerivative v i j x) := by
      rw [← componentDerivative_eq u i j]
      exact hright i j
    have hparts := integral_mul_coordinateDerivative_eq_neg (fun x ↦ u x j)
      (componentDerivative v i j) i (hu.component i j) (hv.pureSecondOrder i j)
      (hleft i j) hright'
    rw [← componentDerivative_eq u i j] at hparts
    exact hparts
  have hleftSum : ∀ j, Integrable (fun x ↦
      ∑ i, u x j * coordinateDerivative (componentDerivative v i j) i x) := by
    intro j
    exact integrable_finsetSum Finset.univ fun i _hi ↦ hleft i j
  calc
    (∫ x, pairing u (vectorLaplacian v) x) =
        ∫ x, ∑ j, ∑ i,
          u x j * coordinateDerivative (componentDerivative v i j) i x := by
      congr 1
      funext x
      simp only [pairing_apply, vectorLaplacian_apply, Finset.mul_sum]
    _ = ∑ j, ∫ x, ∑ i,
        u x j * coordinateDerivative (componentDerivative v i j) i x := by
      exact integral_finsetSum Finset.univ fun j _hi ↦ hleftSum j
    _ = ∑ j, ∑ i, ∫ x,
        u x j * coordinateDerivative (componentDerivative v i j) i x := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact integral_finsetSum Finset.univ fun i _hi ↦ hleft i j
    _ = ∑ j, ∑ i, -(∫ x,
        componentDerivative u i j x * componentDerivative v i j x) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcomponent i j
    _ = -(∑ j, ∑ i, ∫ x,
        componentDerivative u i j x * componentDerivative v i j x) := by
      simp only [Finset.sum_neg_distrib]
    _ = -(∑ i, ∑ j, ∫ x,
        componentDerivative u i j x * componentDerivative v i j x) := by
      congr 1
      rw [Finset.sum_comm]

/-- Diagonal vector Green identity, exhibiting the nonpositive viscous Laplacian:
`∫ u · Δu = -∑ᵢⱼ ∫ (∂ᵢuⱼ)²`. -/
theorem integral_pairing_vectorLaplacian_self_eq_neg_sum_integral_sq
    (u : VectorField d)
    (hu : ContDiffForVectorLaplacian u)
    (hleft : ∀ i j, Integrable (fun x ↦
      u x j * coordinateDerivative (componentDerivative u i j) i x))
    (hsquare : ∀ i j, Integrable (fun x ↦ (componentDerivative u i j x) ^ 2)) :
    (∫ x, pairing u (vectorLaplacian u) x) =
      -(∑ i, ∑ j, ∫ x, (componentDerivative u i j x) ^ 2) := by
  have hgreen := integral_pairing_vectorLaplacian_eq_neg_sum_integral_jacobian
    u u hu.firstOrder hu hleft
      (fun i j ↦ by simpa only [pow_two] using hsquare i j)
  simpa only [pow_two] using hgreen

end UnitAddTorus
