/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.WeakDerivUniqueness
public import TauCeti.Analysis.VectorField.Flat.Basic

/-!
# Representative-level weak flat vector calculus on finite unit tori

This file lifts the scalar periodic weak-coordinate derivative to scalar and vector fields on
`UnitAddTorus d`, for an arbitrary finite coordinate type `d`.  A weak gradient or Jacobian here
is an explicit family of integrable representatives satisfying the scalar distributional
relations componentwise.  Scalar uniqueness, combined over the finite coordinate type, makes
these candidates unique almost everywhere.

The diagonal trace of a weak-Jacobian candidate defines its weak divergence.  The relation
`HasWeakDivergence u q` records a representative `q` only up to almost-everywhere equality, and
`WeaklyDivergenceFree u` is consequently independent of the chosen Jacobian and divergence
representatives.  Scalar representative congruence also makes the weak gradient, Jacobian,
divergence, and incompressibility predicates invariant under replacing the original field almost
everywhere.  An all-coordinate bounded scalar test class packages the distributional adjoint
identity `∫ φ div u = -∫ ∇φ · u`.

The final results identify these representative-level operators with the smooth operators from
`Flat.Basic`.  No nonlinear weak product, Sobolev-class transport, or energy cancellation is
asserted here; those require separate multiplication, integrability, and density bridges.

## Main declarations

* `TauCeti.UnitAddTorus.HasWeakGradient`: a componentwise weak-gradient candidate.
* `TauCeti.UnitAddTorus.HasWeakJacobian`: a componentwise weak-Jacobian candidate.
* `TauCeti.UnitAddTorus.weakDivergence`: diagonal trace of a weak-Jacobian candidate.
* `TauCeti.UnitAddTorus.HasWeakDivergence`: candidate-independent weak divergence relation.
* `TauCeti.UnitAddTorus.WeaklyDivergenceFree`: weak incompressibility.
* `TauCeti.UnitAddTorus.HasWeakDivergence.integral_test_mul_eq_neg_integral_pairing_gradient`:
  the smooth-test divergence/gradient adjoint identity.
* `TauCeti.UnitAddTorus.hasWeakJacobian_jacobian`: agreement with the classical Jacobian.
-/

public section

noncomputable section

namespace TauCeti.UnitAddTorus

open MeasureTheory
open scoped BigOperators ENNReal

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `G` is a representative-level weak gradient of the scalar field `f`. -/
def HasWeakGradient (f : ScalarField d) (G : VectorField d) : Prop :=
  ∀ i, HasWeakCoordinateDerivative f (fun x ↦ G x i) i

/-- Constructor-and-eliminator form of the componentwise weak-gradient relation. -/
theorem hasWeakGradient_iff {f : ScalarField d} {G : VectorField d} :
    HasWeakGradient f G ↔
      ∀ i, HasWeakCoordinateDerivative f (fun x ↦ G x i) i :=
  Iff.rfl

/-- Extract one scalar weak-coordinate derivative from a weak-gradient candidate. -/
theorem HasWeakGradient.coordinate {f : ScalarField d} {G : VectorField d}
    (hG : HasWeakGradient f G) (i : d) :
    HasWeakCoordinateDerivative f (fun x ↦ G x i) i := by
  exact hG i

/-- `J` is a representative-level weak Jacobian of the vector field `u`, with the convention
`J x i j = ∂ᵢ uⱼ`. -/
def HasWeakJacobian (u : VectorField d) (J : TensorField d) : Prop :=
  ∀ i j, HasWeakCoordinateDerivative (fun x ↦ u x j) (fun x ↦ J x i j) i

/-- Constructor-and-eliminator form of the componentwise weak-Jacobian relation. -/
theorem hasWeakJacobian_iff {u : VectorField d} {J : TensorField d} :
    HasWeakJacobian u J ↔
      ∀ i j, HasWeakCoordinateDerivative (fun x ↦ u x j) (fun x ↦ J x i j) i :=
  Iff.rfl

/-- Extract one scalar weak-coordinate derivative from a weak-Jacobian candidate. -/
theorem HasWeakJacobian.coordinate {u : VectorField d} {J : TensorField d}
    (hJ : HasWeakJacobian u J) (i j : d) :
    HasWeakCoordinateDerivative (fun x ↦ u x j) (fun x ↦ J x i j) i := by
  exact hJ i j

/-- The weak-gradient relation depends only on the almost-everywhere class of the scalar field. -/
theorem HasWeakGradient.congr_ae {f g : ScalarField d} {G : VectorField d}
    (hG : HasWeakGradient f G) (hfg : f =ᵐ[volume] g) :
    HasWeakGradient g G := by
  intro i
  exact (hG i).congr_ae hfg

/-- The weak-Jacobian relation depends only on the almost-everywhere class of the vector field. -/
theorem HasWeakJacobian.congr_ae {u v : VectorField d} {J : TensorField d}
    (hJ : HasWeakJacobian u J) (huv : u =ᵐ[volume] v) :
    HasWeakJacobian v J := by
  intro i j
  apply (hJ i j).congr_ae
  filter_upwards [huv] with x hx
  rw [hx]

/-- The diagonal trace of a representative-level weak-Jacobian candidate. -/
def weakDivergence (J : TensorField d) : ScalarField d :=
  fun x ↦ ∑ i, J x i i

omit [DecidableEq d] in
@[simp]
theorem weakDivergence_apply (J : TensorField d) (x : _root_.UnitAddTorus d) :
    weakDivergence J x = ∑ i, J x i i := by
  rfl

/-- `q` represents the weak divergence of `u` if some componentwise weak Jacobian has diagonal
trace equal to `q` almost everywhere.  The existential Jacobian is unique almost everywhere, so
this relation is independent of the Jacobian and divergence candidate choices for fixed `u`. -/
def HasWeakDivergence (u : VectorField d) (q : ScalarField d) : Prop :=
  ∃ J, HasWeakJacobian u J ∧ q =ᵐ[volume] weakDivergence J

/-- Constructor-and-eliminator form of the representative-level weak-divergence relation. -/
theorem hasWeakDivergence_iff {u : VectorField d} {q : ScalarField d} :
    HasWeakDivergence u q ↔
      ∃ J, HasWeakJacobian u J ∧ q =ᵐ[volume] weakDivergence J :=
  Iff.rfl

/-- A vector field is weakly divergence-free when its weak divergence is represented by zero. -/
def WeaklyDivergenceFree (u : VectorField d) : Prop :=
  HasWeakDivergence u 0

/-- Weak incompressibility is the assertion that zero represents the weak divergence. -/
theorem weaklyDivergenceFree_iff {u : VectorField d} :
    WeaklyDivergenceFree u ↔ HasWeakDivergence u 0 :=
  Iff.rfl

/-- The weak-divergence relation depends only on the almost-everywhere class of the vector
field. -/
theorem HasWeakDivergence.congr_ae {u v : VectorField d} {q : ScalarField d}
    (hq : HasWeakDivergence u q) (huv : u =ᵐ[volume] v) :
    HasWeakDivergence v q := by
  rcases hq with ⟨J, hJ, hqJ⟩
  exact ⟨J, hJ.congr_ae huv, hqJ⟩

/-- Weak incompressibility depends only on the almost-everywhere class of the vector field. -/
theorem WeaklyDivergenceFree.congr_ae {u v : VectorField d}
    (hu : WeaklyDivergenceFree u) (huv : u =ᵐ[volume] v) :
    WeaklyDivergenceFree v :=
  HasWeakDivergence.congr_ae hu huv

/-- A scalar test field that is an admissible coordinate test in every direction. -/
structure FlatScalarTestFunction (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The scalar field underlying the test function. -/
  toFun : ScalarField d
  /-- The test field is classically `C¹` in every coordinate. -/
  contDiffAlongCoordinate : ∀ i, ContDiffAlongCoordinate toFun i
  /-- The test field is essentially bounded. -/
  memLp_top : MemLp toFun ∞
  /-- Every classical coordinate derivative is essentially bounded. -/
  coordinateDerivative_memLp_top : ∀ i, MemLp (coordinateDerivative toFun i) ∞

instance : CoeFun (FlatScalarTestFunction d) (fun _ ↦ ScalarField d) :=
  ⟨FlatScalarTestFunction.toFun⟩

/-- Regard an all-coordinate scalar test field as a test in one selected coordinate. -/
abbrev FlatScalarTestFunction.coordinateTest (φ : FlatScalarTestFunction d) (i : d) :
    CoordinateTestFunction d i where
  toFun := φ
  contDiffAlongCoordinate := φ.contDiffAlongCoordinate i
  memLp_top := φ.memLp_top
  coordinateDerivative_memLp_top := φ.coordinateDerivative_memLp_top i

@[simp]
theorem FlatScalarTestFunction.coordinateTest_apply (φ : FlatScalarTestFunction d) (i : d)
    (x : _root_.UnitAddTorus d) :
    φ.coordinateTest i x = φ x := rfl

/-- Two representative-level weak gradients of the same field agree almost everywhere. -/
theorem HasWeakGradient.ae_eq {f : ScalarField d} {G H : VectorField d}
    (hG : HasWeakGradient f G) (hH : HasWeakGradient f H) :
    G =ᵐ[volume] H := by
  have hcoord : ∀ i, (fun x ↦ G x i) =ᵐ[volume] fun x ↦ H x i :=
    fun i ↦ (hG i).ae_eq_deriv (hH i)
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  funext i
  exact hx i

/-- Two representative-level weak Jacobians of the same field agree almost everywhere. -/
theorem HasWeakJacobian.ae_eq {u : VectorField d} {J K : TensorField d}
    (hJ : HasWeakJacobian u J) (hK : HasWeakJacobian u K) :
    J =ᵐ[volume] K := by
  have hcoord : ∀ i j, (fun x ↦ J x i j) =ᵐ[volume] fun x ↦ K x i j :=
    fun i j ↦ (hJ i j).ae_eq_deriv (hK i j)
  filter_upwards [ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hcoord i)] with x hx
  funext i j
  exact hx i j

/-- The diagonal trace of a weak-Jacobian candidate is integrable. -/
theorem HasWeakJacobian.integrable_weakDivergence {u : VectorField d} {J : TensorField d}
    (hJ : HasWeakJacobian u J) :
    Integrable (weakDivergence J) := by
  change Integrable (fun x ↦ ∑ i, J x i i)
  exact integrable_finsetSum Finset.univ fun i _hi ↦ (hJ i i).integrable_deriv

/-- Almost-everywhere uniqueness of weak Jacobians descends to their diagonal traces. -/
theorem HasWeakJacobian.weakDivergence_ae_eq {u : VectorField d} {J K : TensorField d}
    (hJ : HasWeakJacobian u J) (hK : HasWeakJacobian u K) :
    weakDivergence J =ᵐ[volume] weakDivergence K := by
  filter_upwards [hJ.ae_eq hK] with x hx
  change (∑ i, J x i i) = ∑ i, K x i i
  rw [hx]

/-- Every representative of a weak divergence is integrable. -/
theorem HasWeakDivergence.integrable {u : VectorField d} {q : ScalarField d}
    (hq : HasWeakDivergence u q) :
    Integrable q := by
  rcases hq with ⟨J, hJ, hqJ⟩
  exact hJ.integrable_weakDivergence.congr hqJ.symm

/-- A vector field has at most one weak divergence representative, up to almost-everywhere
equality. -/
theorem HasWeakDivergence.ae_eq {u : VectorField d} {q r : ScalarField d}
    (hq : HasWeakDivergence u q) (hr : HasWeakDivergence u r) :
    q =ᵐ[volume] r := by
  rcases hq with ⟨J, hJ, hqJ⟩
  rcases hr with ⟨K, hK, hrK⟩
  exact hqJ.trans ((hJ.weakDivergence_ae_eq hK).trans hrK.symm)

/-- Candidate-level divergence/gradient adjointness against an all-coordinate bounded smooth
scalar test field. -/
theorem HasWeakJacobian.integral_test_mul_weakDivergence_eq_neg_integral_pairing_gradient
    {u : VectorField d} {J : TensorField d} (hJ : HasWeakJacobian u J)
    (φ : FlatScalarTestFunction d) :
    (∫ x, φ x * weakDivergence J x) =
      -(∫ x, pairing (gradient φ) u x) := by
  have hleft : ∀ i, Integrable (fun x ↦ φ x * J x i i) := by
    intro i
    exact (φ.coordinateTest i).integrable_mul (hJ i i).integrable_deriv
  have hright : ∀ i, Integrable (fun x ↦ coordinateDerivative φ i x * u x i) := by
    intro i
    exact (φ.coordinateTest i).integrable_coordinateDerivative_mul (hJ i i).integrable
  have hcomponent : ∀ i,
      (∫ x, φ x * J x i i) =
        -(∫ x, coordinateDerivative φ i x * u x i) := by
    intro i
    have hrel := (hJ i i).integral_coordinateDerivative_mul_eq_neg_integral_mul
      (φ.coordinateTest i)
    change (∫ x, coordinateDerivative φ i x * u x i) =
      -(∫ x, φ x * J x i i) at hrel
    linarith
  calc
    (∫ x, φ x * weakDivergence J x) =
        ∫ x, ∑ i, φ x * J x i i := by
      congr 1
      funext x
      simp only [weakDivergence, Finset.mul_sum]
    _ = ∑ i, ∫ x, φ x * J x i i := by
      exact integral_finsetSum Finset.univ fun i _hi ↦ hleft i
    _ = ∑ i, -(∫ x, coordinateDerivative φ i x * u x i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcomponent i
    _ = -(∑ i, ∫ x, coordinateDerivative φ i x * u x i) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i, coordinateDerivative φ i x * u x i) := by
      rw [integral_finsetSum Finset.univ fun i _hi ↦ hright i]
    _ = -(∫ x, pairing (gradient φ) u x) := by
      congr 2
      funext x
      simp only [pairing_apply, gradient_apply]

/-- The divergence/gradient adjoint identity stated for an arbitrary weak-divergence
representative. -/
theorem HasWeakDivergence.integral_test_mul_eq_neg_integral_pairing_gradient
    {u : VectorField d} {q : ScalarField d} (hq : HasWeakDivergence u q)
    (φ : FlatScalarTestFunction d) :
    (∫ x, φ x * q x) = -(∫ x, pairing (gradient φ) u x) := by
  rcases hq with ⟨J, hJ, hqJ⟩
  calc
    (∫ x, φ x * q x) = ∫ x, φ x * weakDivergence J x := by
      apply integral_congr_ae
      filter_upwards [hqJ] with x hx
      rw [hx]
    _ = -(∫ x, pairing (gradient φ) u x) :=
      hJ.integral_test_mul_weakDivergence_eq_neg_integral_pairing_gradient φ

/-- The classical gradient is a representative-level weak gradient under explicit smoothness
and integrability hypotheses. -/
theorem hasWeakGradient_gradient (f : ScalarField d)
    (hf : ∀ i, ContDiffAlongCoordinate f i) (hf_int : Integrable f)
    (hgrad_int : ∀ i, Integrable (fun x ↦ gradient f x i)) :
    HasWeakGradient f (gradient f) := by
  intro i
  simpa only [gradient_apply] using
    hasWeakCoordinateDerivative_coordinateDerivative f i (hf i) hf_int
      (by simpa only [gradient_apply] using hgrad_int i)

/-- Any weak-gradient candidate agrees almost everywhere with the integrable classical gradient. -/
theorem HasWeakGradient.ae_eq_gradient {f : ScalarField d} {G : VectorField d}
    (hG : HasWeakGradient f G) (hf : ∀ i, ContDiffAlongCoordinate f i)
    (hgrad_int : ∀ i, Integrable (fun x ↦ gradient f x i)) :
    G =ᵐ[volume] gradient f := by
  have hclassical : HasWeakGradient f (gradient f) := by
    intro i
    simpa only [gradient_apply] using
      hasWeakCoordinateDerivative_coordinateDerivative f i (hf i) (hG i).integrable
        (by simpa only [gradient_apply] using hgrad_int i)
  exact hG.ae_eq hclassical

/-- The classical Jacobian is a representative-level weak Jacobian under explicit componentwise
smoothness and integrability hypotheses. -/
theorem hasWeakJacobian_jacobian (u : VectorField d)
    (hu : ContDiffVectorField u)
    (hu_int : ∀ j, Integrable (fun x ↦ u x j))
    (hjac_int : ∀ i j, Integrable (fun x ↦ jacobian u x i j)) :
    HasWeakJacobian u (jacobian u) := by
  intro i j
  simpa only [jacobian_apply, componentDerivative_apply] using
    hasWeakCoordinateDerivative_coordinateDerivative (fun x ↦ u x j) i
      (hu.component i j) (hu_int j)
      (by simpa only [jacobian_apply, componentDerivative_apply] using hjac_int i j)

/-- Any weak-Jacobian candidate agrees almost everywhere with the integrable classical Jacobian. -/
theorem HasWeakJacobian.ae_eq_jacobian {u : VectorField d} {J : TensorField d}
    (hJ : HasWeakJacobian u J) (hu : ContDiffVectorField u)
    (hjac_int : ∀ i j, Integrable (fun x ↦ jacobian u x i j)) :
    J =ᵐ[volume] jacobian u := by
  have hu_int : ∀ j, Integrable (fun x ↦ u x j) :=
    fun j ↦ (hJ j j).integrable
  exact hJ.ae_eq <| hasWeakJacobian_jacobian u hu hu_int hjac_int

/-- The classical divergence represents the weak divergence whenever the full classical Jacobian
is integrable componentwise. -/
theorem hasWeakDivergence_divergence (u : VectorField d)
    (hu : ContDiffVectorField u)
    (hu_int : ∀ j, Integrable (fun x ↦ u x j))
    (hjac_int : ∀ i j, Integrable (fun x ↦ jacobian u x i j)) :
    HasWeakDivergence u (divergence u) := by
  refine ⟨jacobian u, hasWeakJacobian_jacobian u hu hu_int hjac_int, ?_⟩
  filter_upwards with x
  change divergence u x = ∑ i, jacobian u x i i
  exact divergence_apply u x

/-- A classically divergence-free smooth field with integrable components and Jacobian is weakly
divergence-free. -/
theorem weaklyDivergenceFree_of_divergence_eq_zero (u : VectorField d)
    (hu : ContDiffVectorField u)
    (hu_int : ∀ j, Integrable (fun x ↦ u x j))
    (hjac_int : ∀ i j, Integrable (fun x ↦ jacobian u x i j))
    (hdiv : ∀ x, divergence u x = 0) :
    WeaklyDivergenceFree u := by
  refine ⟨jacobian u, hasWeakJacobian_jacobian u hu hu_int hjac_int, ?_⟩
  filter_upwards with x
  change 0 = ∑ i, jacobian u x i i
  rw [← divergence_apply]
  exact (hdiv x).symm

end TauCeti.UnitAddTorus
