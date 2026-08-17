/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.Integration

/-!
# Smooth flat vector calculus on finite unit tori

This file defines scalar, vector, and two-tensor fields on `UnitAddTorus d` for an arbitrary
finite coordinate type `d`.  The differential operators are built from the intrinsic classical
`UnitAddTorus.coordinateDerivative`; no fundamental-domain representative occurs in their public
definitions or theorem statements.

The analytic endpoint is smooth periodic transport calculus.  In particular, divergence
integrates to zero, transport satisfies integration by parts, divergence-free transport is
skew-adjoint, and the nonlinear kinetic-energy production has integral zero.  Every theorem
states the coordinate regularity and integrability used by its proof.  No weak or Sobolev
extension is asserted here.

This advances Layers 1.1, 1.3, and 1.4 and supplies the smooth cancellation required by Layer 5.1
of `TauCetiRoadmap/IncompressibleFlows/README.md`.

The transport proof is ported and generalized from `emberian/navier-stokes-proof`, commit
`787377f`, by Ember Arlynx.  That source treated `Fin (n + 1)`; this module uses an arbitrary
finite index type.

## Main declarations

* `UnitAddTorus.gradient`, `jacobian`, and `divergence`: smooth flat differential
  operators.
* `UnitAddTorus.scalarTransport` and `vectorTransport`: advective derivatives.
* `UnitAddTorus.integral_divergence_eq_zero`: periodic divergence theorem.
* `UnitAddTorus.transport_integration_by_parts`: smooth transport integration by parts.
* `UnitAddTorus.divergenceFree_transport_skew`: skew-adjointness of incompressible
  transport.
* `UnitAddTorus.transportTrilinear_swap`: skew-symmetry of the transport trilinear form.
* `UnitAddTorus.integral_selfTransportEnergyDensity_eq_zero`: nonlinear kinetic-energy
  cancellation.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory
open scoped BigOperators

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Real scalar fields on a finite normalized unit torus. -/
abbrev ScalarField (d : Type*) := _root_.UnitAddTorus d → ℝ

/-- Real flat vector fields, with value coordinates indexed by the torus coordinate type. -/
abbrev VectorField (d : Type*) := _root_.UnitAddTorus d → d → ℝ

/-- Real two-tensor fields with both indices in the torus coordinate type. -/
abbrev TensorField (d : Type*) := _root_.UnitAddTorus d → d → d → ℝ

/-- The derivative of component `j` of a vector field in coordinate direction `i`. -/
def componentDerivative (u : VectorField d) (i j : d) : ScalarField d :=
  coordinateDerivative (fun x ↦ u x j) i

/-- Gradient of a scalar field on a finite unit torus. -/
def gradient (f : ScalarField d) : VectorField d :=
  fun x i ↦ coordinateDerivative f i x

/-- Jacobian of a flat vector field.  The index convention is
`jacobian u x i j = ∂ᵢ uⱼ`. -/
def jacobian (u : VectorField d) : TensorField d :=
  fun x i j ↦ componentDerivative u i j x

/-- Euclidean coordinate pairing of flat vector fields. -/
def pairing (u v : VectorField d) : ScalarField d :=
  fun x ↦ ∑ i, u x i * v x i

/-- Coordinate divergence, the trace of the flat Jacobian. -/
def divergence (u : VectorField d) : ScalarField d :=
  fun x ↦ ∑ i, jacobian u x i i

/-- Transport of a scalar field by a flat vector field. -/
def scalarTransport (u : VectorField d) (f : ScalarField d) : ScalarField d :=
  pairing u (gradient f)

/-- Transport of a vector field by a flat vector field, componentwise. -/
def vectorTransport (u v : VectorField d) : VectorField d :=
  fun x j ↦ ∑ i, u x i * jacobian v x i j

/-- Pointwise tensor product, with `(u ⊗ v)ᵢⱼ = uᵢ vⱼ`. -/
def tensorProduct (u v : VectorField d) : TensorField d :=
  fun x i j ↦ u x i * v x j

/-- Divergence in the first index of a two-tensor field. -/
def tensorDivergence (T : TensorField d) : VectorField d :=
  fun x j ↦ ∑ i, coordinateDerivative (fun z ↦ T z i j) i x

/-- Self-transport `(u · ∇)u`. -/
def selfTransport (u : VectorField d) : VectorField d :=
  vectorTransport u u

/-- The nonlinear kinetic-energy production density `u · ((u · ∇)u)`. -/
def selfTransportEnergyDensity (u : VectorField d) : ScalarField d :=
  pairing u (selfTransport u)

/-- The smooth transport trilinear form `b(u,v,w) = ∫ ((u · ∇)v) · w`. -/
def transportTrilinear (u v w : VectorField d) : ℝ :=
  ∫ x, pairing (vectorTransport u v) w x

/-- Every component of a vector field is `C¹` along every torus coordinate. -/
def ContDiffVectorField (u : VectorField d) : Prop :=
  ∀ i j, ContDiffAlongCoordinate (fun x ↦ u x j) i

omit [Fintype d] in
@[simp]
theorem componentDerivative_apply (u : VectorField d) (x : _root_.UnitAddTorus d) (i j : d) :
    componentDerivative u i j x = coordinateDerivative (fun z ↦ u z j) i x := by
  rfl

omit [Fintype d] in
/-- A component derivative is the coordinate derivative of the selected scalar component. -/
theorem componentDerivative_eq (u : VectorField d) (i j : d) :
    componentDerivative u i j = coordinateDerivative (fun z ↦ u z j) i := by
  funext x
  exact componentDerivative_apply u x i j

omit [Fintype d] in
@[simp]
theorem gradient_apply (f : ScalarField d) (x : _root_.UnitAddTorus d) (i : d) :
    gradient f x i = coordinateDerivative f i x := by
  simp only [gradient]

omit [Fintype d] in
@[simp]
theorem jacobian_apply (u : VectorField d) (x : _root_.UnitAddTorus d) (i j : d) :
    jacobian u x i j = componentDerivative u i j x := by
  simp only [jacobian]

omit [DecidableEq d] in
@[simp]
theorem pairing_apply (u v : VectorField d) (x : _root_.UnitAddTorus d) :
    pairing u v x = ∑ i, u x i * v x i := by
  rfl

@[simp]
theorem divergence_apply (u : VectorField d) (x : _root_.UnitAddTorus d) :
    divergence u x = ∑ i, jacobian u x i i := by
  rfl

@[simp]
theorem tensorDivergence_apply (T : TensorField d) (x : _root_.UnitAddTorus d) (j : d) :
    tensorDivergence T x j = ∑ i, coordinateDerivative (fun z ↦ T z i j) i x := by
  rfl

omit [Fintype d] in
/-- Extract coordinatewise smoothness from a smooth flat vector field. -/
theorem ContDiffVectorField.component {u : VectorField d} (hu : ContDiffVectorField u)
    (i j : d) :
    ContDiffAlongCoordinate (fun x ↦ u x j) i := by
  exact hu i j

omit [Fintype d] in
/-- Build a coordinatewise smooth vector field from smoothness of all scalar components in all
coordinate directions. -/
theorem contDiffVectorField_of_components {u : VectorField d}
    (hu : ∀ i j, ContDiffAlongCoordinate (fun x ↦ u x j) i) :
    ContDiffVectorField u := by
  exact hu

omit [Fintype d] in
theorem componentDerivative_const (c : d → ℝ) (i j : d)
    (x : _root_.UnitAddTorus d) :
    componentDerivative (fun _ ↦ c) i j x = 0 := by
  exact coordinateDerivative_const (c j) i x

theorem divergence_const (c : d → ℝ) (x : _root_.UnitAddTorus d) :
    divergence (fun _ ↦ c) x = 0 := by
  simp [divergence]

@[simp]
theorem selfTransport_const (c : d → ℝ) (x : _root_.UnitAddTorus d) (j : d) :
    selfTransport (fun _ ↦ c) x j = 0 := by
  simp [selfTransport, vectorTransport]

@[simp]
theorem selfTransportEnergyDensity_const (c : d → ℝ) (x : _root_.UnitAddTorus d) :
    selfTransportEnergyDensity (fun _ ↦ c) x = 0 := by
  simp [selfTransportEnergyDensity, pairing]

@[simp]
theorem vectorTransport_apply (u v : VectorField d) (x : _root_.UnitAddTorus d) (j : d) :
    vectorTransport u v x j = scalarTransport u (fun z ↦ v z j) x := by
  simp only [vectorTransport, scalarTransport, pairing, gradient, jacobian, componentDerivative]

/-- The tensor product rule
`div (u ⊗ v) = (div u) v + (u · ∇)v` for coordinatewise `C¹` fields. -/
theorem tensorDivergence_tensorProduct (u v : VectorField d)
    (hu : ContDiffVectorField u) (hv : ContDiffVectorField v) :
    tensorDivergence (tensorProduct u v) =
      fun x j ↦ divergence u x * v x j + vectorTransport u v x j := by
  funext x j
  simp only [tensorDivergence, tensorProduct]
  simp_rw [coordinateDerivative_mul (fun z ↦ u z _) (fun z ↦ v z _) _ x
    (hu _ _) (hv _ _)]
  rw [Finset.sum_add_distrib]
  simp only [divergence, jacobian, componentDerivative, vectorTransport]
  rw [Finset.sum_mul]

/-- Every diagonal derivative has zero integral, so the integral of a smooth periodic
divergence vanishes.  Only diagonal coordinate regularity and integrability are required. -/
theorem integral_divergence_eq_zero (u : VectorField d)
    (hu : ∀ i, ContDiffAlongCoordinate (fun x ↦ u x i) i)
    (hint : ∀ i, Integrable (componentDerivative u i i)) :
    (∫ x, divergence u x) = 0 := by
  rw [show (∫ x, divergence u x) = ∑ i, ∫ x, componentDerivative u i i x by
    simp only [divergence, jacobian]
    exact integral_finsetSum Finset.univ fun i _ ↦ hint i]
  apply Finset.sum_eq_zero
  intro i _hi
  have hparts := integral_mul_coordinateDerivative_eq_neg
    (fun _ : _root_.UnitAddTorus d ↦ (1 : ℝ)) (fun x ↦ u x i) i
    (contDiffAlongCoordinate_const 1 i) (hu i)
    (by simpa only [one_mul, componentDerivative] using hint i)
    (by simp)
  simpa only [one_mul, coordinateDerivative_const, zero_mul, integral_zero,
    neg_zero, componentDerivative] using hparts

/-- One coordinate of transport integration by parts.  The derivative of the transporting
component is retained explicitly; summing these terms produces `div u`. -/
theorem transportComponent_integration_by_parts (b f g : ScalarField d) (i : d)
    (hb : ContDiffAlongCoordinate b i) (hf : ContDiffAlongCoordinate f i)
    (hg : ContDiffAlongCoordinate g i)
    (hleft : Integrable (fun x ↦ (f x * b x) * coordinateDerivative g i x))
    (hright : Integrable (fun x ↦
      coordinateDerivative (fun z ↦ f z * b z) i x * g x)) :
    (∫ x, (f x * b x) * coordinateDerivative g i x) =
      -(∫ x, (coordinateDerivative f i x * b x +
        f x * coordinateDerivative b i x) * g x) := by
  have hparts := integral_mul_coordinateDerivative_eq_neg
    (fun x ↦ f x * b x) g i (hf.mul hb) hg hleft hright
  calc
    (∫ x, (f x * b x) * coordinateDerivative g i x) =
        -(∫ x, coordinateDerivative (fun z ↦ f z * b z) i x * g x) := hparts
    _ = -(∫ x, (coordinateDerivative f i x * b x +
        f x * coordinateDerivative b i x) * g x) := by
      congr 2
      funext x
      rw [coordinateDerivative_mul f b i x hf hb]

/-- Smooth transport integration by parts on a finite unit torus:
`∫ f (u · ∇g) = -∫ ((u · ∇f) + f div u) g`. -/
theorem transport_integration_by_parts (u : VectorField d) (f g : ScalarField d)
    (hu : ∀ i, ContDiffAlongCoordinate (fun x ↦ u x i) i)
    (hf : ∀ i, ContDiffAlongCoordinate f i)
    (hg : ∀ i, ContDiffAlongCoordinate g i)
    (hleft : ∀ i, Integrable (fun x ↦
      (f x * u x i) * coordinateDerivative g i x))
    (hright : ∀ i, Integrable (fun x ↦
      coordinateDerivative (fun z ↦ f z * u z i) i x * g x)) :
    (∫ x, f x * scalarTransport u g x) =
      -(∫ x, (scalarTransport u f x + f x * divergence u x) * g x) := by
  have hcomponent : ∀ i,
      (∫ x, (f x * u x i) * coordinateDerivative g i x) =
        -(∫ x, coordinateDerivative (fun z ↦ f z * u z i) i x * g x) := by
    intro i
    exact integral_mul_coordinateDerivative_eq_neg
      (fun x ↦ f x * u x i) g i ((hf i).mul (hu i)) (hg i)
        (hleft i) (hright i)
  calc
    (∫ x, f x * scalarTransport u g x) =
        ∫ x, ∑ i, (f x * u x i) * coordinateDerivative g i x := by
      congr 1
      funext x
      simp only [scalarTransport, pairing, gradient, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i, ∫ x, (f x * u x i) * coordinateDerivative g i x := by
      exact integral_finsetSum Finset.univ fun i _hi ↦ hleft i
    _ = ∑ i, -(∫ x,
        coordinateDerivative (fun z ↦ f z * u z i) i x * g x) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcomponent i
    _ = -(∑ i, ∫ x,
        coordinateDerivative (fun z ↦ f z * u z i) i x * g x) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i,
        coordinateDerivative (fun z ↦ f z * u z i) i x * g x) := by
      rw [integral_finsetSum Finset.univ fun i _hi ↦ hright i]
    _ = -(∫ x, (scalarTransport u f x + f x * divergence u x) * g x) := by
      congr 2
      funext x
      calc
        (∑ i, coordinateDerivative (fun z ↦ f z * u z i) i x * g x) =
            ∑ i, (coordinateDerivative f i x * u x i +
              f x * coordinateDerivative (fun z ↦ u z i) i x) * g x := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [coordinateDerivative_mul f (fun z ↦ u z i) i x (hf i) (hu i)]
        _ = (scalarTransport u f x + f x * divergence u x) * g x := by
          simp only [scalarTransport, pairing, gradient, divergence, jacobian,
            componentDerivative]
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [← Finset.sum_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          · rw [← Finset.sum_mul, Finset.mul_sum]

/-- For a divergence-free transporting field, smooth scalar transport is skew-adjoint in the
Haar-volume pairing. -/
theorem divergenceFree_transport_skew (u : VectorField d) (f g : ScalarField d)
    (hu : ∀ i, ContDiffAlongCoordinate (fun x ↦ u x i) i)
    (hf : ∀ i, ContDiffAlongCoordinate f i)
    (hg : ∀ i, ContDiffAlongCoordinate g i)
    (hleft : ∀ i, Integrable (fun x ↦
      (f x * u x i) * coordinateDerivative g i x))
    (hright : ∀ i, Integrable (fun x ↦
      coordinateDerivative (fun z ↦ f z * u z i) i x * g x))
    (hdiv : ∀ x, divergence u x = 0) :
    (∫ x, f x * scalarTransport u g x) =
      -(∫ x, scalarTransport u f x * g x) := by
  rw [transport_integration_by_parts u f g hu hf hg hleft hright]
  congr 2
  funext x
  rw [hdiv]
  ring

/-- The smooth transport trilinear form is skew in its final two arguments when the transporting
field is divergence-free: `b(u,v,w) = -b(u,w,v)`.  The three integrability families respectively
justify scalar integration by parts and exchanging the two finite component sums with the
integral. -/
theorem transportTrilinear_swap (u v w : VectorField d)
    (hu : ∀ i, ContDiffAlongCoordinate (fun x ↦ u x i) i)
    (hv : ContDiffVectorField v) (hw : ContDiffVectorField w)
    (hvuw : ∀ i j, Integrable (fun x ↦
      (w x j * u x i) * coordinateDerivative (fun z ↦ v z j) i x))
    (hproduct : ∀ i j, Integrable (fun x ↦
      coordinateDerivative (fun z ↦ w z j * u z i) i x * v x j))
    (hwuv : ∀ i j, Integrable (fun x ↦
      (v x j * u x i) * coordinateDerivative (fun z ↦ w z j) i x))
    (hdiv : ∀ x, divergence u x = 0) :
    transportTrilinear u v w = -transportTrilinear u w v := by
  have hvwIntegrable : ∀ j, Integrable (fun x ↦
      scalarTransport u (fun z ↦ v z j) x * w x j) := by
    intro j
    simp only [scalarTransport, pairing, gradient, Finset.sum_mul]
    exact integrable_finsetSum Finset.univ fun i _hi ↦ by
      exact (hvuw i j).congr (Filter.Eventually.of_forall fun x ↦ by ring)
  have hwvIntegrable : ∀ j, Integrable (fun x ↦
      scalarTransport u (fun z ↦ w z j) x * v x j) := by
    intro j
    simp only [scalarTransport, pairing, gradient, Finset.sum_mul]
    exact integrable_finsetSum Finset.univ fun i _hi ↦ by
      exact (hwuv i j).congr (Filter.Eventually.of_forall fun x ↦ by ring)
  have hcomponent : ∀ j,
      (∫ x, scalarTransport u (fun z ↦ v z j) x * w x j) =
        -(∫ x, scalarTransport u (fun z ↦ w z j) x * v x j) := by
    intro j
    have hskew := divergenceFree_transport_skew
      u (fun x ↦ w x j) (fun x ↦ v x j) hu
      (fun i ↦ hw i j) (fun i ↦ hv i j)
      (fun i ↦ hvuw i j) (fun i ↦ hproduct i j) hdiv
    calc
      (∫ x, scalarTransport u (fun z ↦ v z j) x * w x j) =
          ∫ x, w x j * scalarTransport u (fun z ↦ v z j) x := by
        congr 1
        funext x
        ring
      _ = -(∫ x, scalarTransport u (fun z ↦ w z j) x * v x j) := hskew
  calc
    transportTrilinear u v w =
        ∫ x, ∑ j, scalarTransport u (fun z ↦ v z j) x * w x j := by
      simp only [transportTrilinear, pairing, vectorTransport_apply]
    _ = ∑ j, ∫ x, scalarTransport u (fun z ↦ v z j) x * w x j := by
      exact integral_finsetSum Finset.univ fun j _hi ↦ hvwIntegrable j
    _ = ∑ j, -(∫ x, scalarTransport u (fun z ↦ w z j) x * v x j) := by
      apply Finset.sum_congr rfl
      intro j _hi
      exact hcomponent j
    _ = -(∑ j, ∫ x, scalarTransport u (fun z ↦ w z j) x * v x j) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ j, scalarTransport u (fun z ↦ w z j) x * v x j) := by
      rw [integral_finsetSum Finset.univ fun j _hi ↦ hwvIntegrable j]
    _ = -transportTrilinear u w v := by
      congr 1

/-- The smooth transport trilinear form vanishes on its repeated final arguments when the
transporting field is divergence-free. -/
theorem transportTrilinear_self_eq_zero (u v : VectorField d)
    (hu : ∀ i, ContDiffAlongCoordinate (fun x ↦ u x i) i)
    (hv : ContDiffVectorField v)
    (hleft : ∀ i j, Integrable (fun x ↦
      (v x j * u x i) * coordinateDerivative (fun z ↦ v z j) i x))
    (hright : ∀ i j, Integrable (fun x ↦
      coordinateDerivative (fun z ↦ v z j * u z i) i x * v x j))
    (hdiv : ∀ x, divergence u x = 0) :
    transportTrilinear u v v = 0 := by
  have hskew := transportTrilinear_swap
    u v v hu hv hv hleft hright hleft hdiv
  linarith

/-- A divergence-free field does no net work against its own advective derivative:
`∫ u · ((u · ∇)u) = 0`.  This is the smooth periodic nonlinear kinetic-energy cancellation in
arbitrary finite dimension. -/
theorem integral_selfTransportEnergyDensity_eq_zero (u : VectorField d)
    (hu : ContDiffVectorField u)
    (hleft : ∀ i j, Integrable (fun x ↦
      (u x j * u x i) * coordinateDerivative (fun z ↦ u z j) i x))
    (hright : ∀ i j, Integrable (fun x ↦
      coordinateDerivative (fun z ↦ u z j * u z i) i x * u x j))
    (hdiv : ∀ x, divergence u x = 0) :
    (∫ x, selfTransportEnergyDensity u x) = 0 := by
  have htri := transportTrilinear_self_eq_zero
    u u (fun i ↦ hu i i) hu hleft hright hdiv
  calc
    (∫ x, selfTransportEnergyDensity u x) = transportTrilinear u u u := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      simp only [selfTransportEnergyDensity, pairing, selfTransport]
      apply Finset.sum_congr rfl
      intro j _hi
      ring
    _ = 0 := htri

end UnitAddTorus
