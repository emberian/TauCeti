/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.Integration
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Weak coordinate derivatives on a finite flat torus

This file defines the distributional derivative in one coordinate of a normalized finite unit
torus. A test field is `C¹` along the selected coordinate and both it and its classical coordinate
derivative are essentially bounded. The latter two hypotheses make its products with any
integrable field integrable, so every integral in the weak relation is an honest Bochner integral.

`TauCeti.UnitAddTorus.HasWeakCoordinateDerivative f f' i` requires `f` and `f'` themselves to be
integrable and asserts

`∫ x, (∂ᵢ φ) x * f x = -∫ x, φ x * f' x`

for every coordinate test field `φ`. The explicit `L¹` hypotheses prevent the convention that the
Bochner integral of a non-integrable function is zero from making the relation vacuous.

The checked smooth integration-by-parts theorem in
`TauCeti.Analysis.Sobolev.Periodic.Integration` proves that the intrinsic classical
`coordinateDerivative` realizes this weak relation. Constants are available as test fields, so
every periodic weak coordinate derivative has integral zero. This is the first basic obstruction
that distinguishes periodic weak derivatives from weak derivatives on a domain with boundary.

## Main declarations

* `TauCeti.UnitAddTorus.CoordinateTestFunction`: bounded `C¹` coordinate test fields with bounded
  coordinate derivative.
* `TauCeti.UnitAddTorus.HasWeakCoordinateDerivative`: the periodic weak coordinate derivative
  relation, including explicit integrability of the field and candidate derivative.
* `TauCeti.UnitAddTorus.hasWeakCoordinateDerivative_coordinateDerivative`: a smooth classical
  coordinate derivative is a weak coordinate derivative.
* `TauCeti.UnitAddTorus.HasWeakCoordinateDerivative.integral_deriv_eq_zero`: every periodic weak
  coordinate derivative has mean zero.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

namespace UnitAddTorus

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A test field for the weak derivative in coordinate `i`.

Besides being `C¹` in the selected coordinate, the field and its coordinate derivative belong to
`L∞`. Consequently both may be multiplied by an arbitrary `L¹` field without losing
integrability. No regularity in the transverse variables is needed for a single-coordinate weak
relation. -/
structure CoordinateTestFunction (d : Type*) [Fintype d] [DecidableEq d] (i : d) where
  /-- The scalar field underlying the test function. -/
  toFun : _root_.UnitAddTorus d → ℝ
  /-- The test field is classically `C¹` along the tested coordinate. -/
  contDiffAlongCoordinate : ContDiffAlongCoordinate toFun i
  /-- The test field is essentially bounded. -/
  memLp_top : MemLp toFun ∞
  /-- Its classical coordinate derivative is essentially bounded. -/
  coordinateDerivative_memLp_top : MemLp (coordinateDerivative toFun i) ∞

instance (i : d) : CoeFun (CoordinateTestFunction d i)
    (fun _ => _root_.UnitAddTorus d → ℝ) :=
  ⟨CoordinateTestFunction.toFun⟩

@[ext]
theorem CoordinateTestFunction.ext {i : d} {φ ψ : CoordinateTestFunction d i}
    (h : (φ : _root_.UnitAddTorus d → ℝ) = ψ) : φ = ψ := by
  cases φ
  cases ψ
  simp_all

/-- Multiplying an integrable field by a coordinate test field is integrable. -/
theorem CoordinateTestFunction.integrable_mul {i : d} (φ : CoordinateTestFunction d i)
    {f : _root_.UnitAddTorus d → ℝ} (hf : Integrable f) :
    Integrable (fun x => φ x * f x) := by
  change Integrable (φ.toFun * f)
  exact hf.mul_of_top_right φ.memLp_top

/-- Multiplying an integrable field by the classical derivative of a coordinate test field is
integrable. -/
theorem CoordinateTestFunction.integrable_coordinateDerivative_mul {i : d}
    (φ : CoordinateTestFunction d i) {f : _root_.UnitAddTorus d → ℝ} (hf : Integrable f) :
    Integrable (fun x => coordinateDerivative φ i x * f x) := by
  change Integrable (coordinateDerivative φ.toFun i * f)
  exact hf.mul_of_top_right φ.coordinateDerivative_memLp_top

/-- A constant is a coordinate test field. In particular, the test class is inhabited for every
finite torus and coordinate. -/
abbrev CoordinateTestFunction.const (i : d) (c : ℝ) : CoordinateTestFunction d i where
  toFun := fun _ => c
  contDiffAlongCoordinate := contDiffAlongCoordinate_const c i
  memLp_top := memLp_top_const c
  coordinateDerivative_memLp_top := by
    have heq : coordinateDerivative (fun _ : _root_.UnitAddTorus d => c) i = fun _ => 0 := by
      funext x
      exact coordinateDerivative_const c i x
    rw [heq]
    exact memLp_top_const 0

@[simp]
theorem CoordinateTestFunction.const_apply (i : d) (c : ℝ) (x : _root_.UnitAddTorus d) :
    CoordinateTestFunction.const i c x = c := rfl

/-- `f'` is the weak derivative of `f` in coordinate `i` on the finite unit torus.

Both functions must be integrable. The two products in the defining identity are integrable for
every `CoordinateTestFunction`, by its `L∞` hypotheses. -/
def HasWeakCoordinateDerivative (f f' : _root_.UnitAddTorus d → ℝ) (i : d) : Prop :=
  Integrable f ∧ Integrable f' ∧
    ∀ φ : CoordinateTestFunction d i,
      (∫ x, coordinateDerivative φ i x * f x) = -∫ x, φ x * f' x

/-- Constructor-and-eliminator form of the periodic weak coordinate derivative relation. -/
theorem hasWeakCoordinateDerivative_iff {f f' : _root_.UnitAddTorus d → ℝ} {i : d} :
    HasWeakCoordinateDerivative f f' i ↔
      Integrable f ∧ Integrable f' ∧
        ∀ φ : CoordinateTestFunction d i,
          (∫ x, coordinateDerivative φ i x * f x) = -∫ x, φ x * f' x :=
  Iff.rfl

/-- A weakly coordinate-differentiable field is integrable. -/
theorem HasWeakCoordinateDerivative.integrable {f f' : _root_.UnitAddTorus d → ℝ} {i : d}
    (h : HasWeakCoordinateDerivative f f' i) : Integrable f := h.1

/-- A periodic weak coordinate derivative is integrable. -/
theorem HasWeakCoordinateDerivative.integrable_deriv
    {f f' : _root_.UnitAddTorus d → ℝ} {i : d} (h : HasWeakCoordinateDerivative f f' i) :
    Integrable f' := h.2.1

/-- The integration-by-parts identity defining a periodic weak coordinate derivative. -/
theorem HasWeakCoordinateDerivative.integral_coordinateDerivative_mul_eq_neg_integral_mul
    {f f' : _root_.UnitAddTorus d → ℝ} {i : d} (h : HasWeakCoordinateDerivative f f' i)
    (φ : CoordinateTestFunction d i) :
    (∫ x, coordinateDerivative φ i x * f x) = -∫ x, φ x * f' x := h.2.2 φ

/-- The classical coordinate derivative of a coordinatewise `C¹` integrable field is its weak
coordinate derivative, provided the classical derivative is integrable. -/
theorem hasWeakCoordinateDerivative_coordinateDerivative
    (f : _root_.UnitAddTorus d → ℝ) (i : d)
    (hf : ContDiffAlongCoordinate f i) (hf_int : Integrable f)
    (hdf_int : Integrable (coordinateDerivative f i)) :
    HasWeakCoordinateDerivative f (coordinateDerivative f i) i := by
  rw [hasWeakCoordinateDerivative_iff]
  refine ⟨hf_int, hdf_int, ?_⟩
  intro φ
  have hφf := φ.integrable_coordinateDerivative_mul hf_int
  have hφdf := φ.integrable_mul hdf_int
  have hibp := integral_mul_coordinateDerivative_eq_neg
    (φ : _root_.UnitAddTorus d → ℝ) f i φ.contDiffAlongCoordinate hf hφdf hφf
  simpa only [neg_neg] using (congrArg Neg.neg hibp).symm

/-- The zero field has weak coordinate derivative zero. -/
@[simp]
theorem hasWeakCoordinateDerivative_zero (i : d) :
    HasWeakCoordinateDerivative (0 : _root_.UnitAddTorus d → ℝ) 0 i := by
  rw [hasWeakCoordinateDerivative_iff]
  refine ⟨integrable_zero _ _ _, integrable_zero _ _ _, ?_⟩
  intro φ
  simp

/-- Periodic weak coordinate differentiation is additive. -/
theorem HasWeakCoordinateDerivative.add
    {f g f' g' : _root_.UnitAddTorus d → ℝ} {i : d}
    (hf : HasWeakCoordinateDerivative f f' i) (hg : HasWeakCoordinateDerivative g g' i) :
    HasWeakCoordinateDerivative (f + g) (f' + g') i := by
  rw [hasWeakCoordinateDerivative_iff]
  refine ⟨hf.integrable.add hg.integrable, hf.integrable_deriv.add hg.integrable_deriv, ?_⟩
  intro φ
  have hDφf := φ.integrable_coordinateDerivative_mul hf.integrable
  have hDφg := φ.integrable_coordinateDerivative_mul hg.integrable
  have hφf' := φ.integrable_mul hf.integrable_deriv
  have hφg' := φ.integrable_mul hg.integrable_deriv
  simp only [Pi.add_apply, mul_add]
  rw [integral_add hDφf hDφg, integral_add hφf' hφg',
    hf.integral_coordinateDerivative_mul_eq_neg_integral_mul φ,
    hg.integral_coordinateDerivative_mul_eq_neg_integral_mul φ]
  ring

/-- Periodic weak coordinate differentiation commutes with negation. -/
theorem HasWeakCoordinateDerivative.neg
    {f f' : _root_.UnitAddTorus d → ℝ} {i : d}
    (h : HasWeakCoordinateDerivative f f' i) :
    HasWeakCoordinateDerivative (-f) (-f') i := by
  rw [hasWeakCoordinateDerivative_iff]
  refine ⟨h.integrable.neg, h.integrable_deriv.neg, ?_⟩
  intro φ
  simp only [Pi.neg_apply, mul_neg, integral_neg]
  rw [h.integral_coordinateDerivative_mul_eq_neg_integral_mul φ]

/-- Periodic weak coordinate differentiation is subtractive. -/
theorem HasWeakCoordinateDerivative.sub
    {f g f' g' : _root_.UnitAddTorus d → ℝ} {i : d}
    (hf : HasWeakCoordinateDerivative f f' i) (hg : HasWeakCoordinateDerivative g g' i) :
    HasWeakCoordinateDerivative (f - g) (f' - g') i := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Periodic weak coordinate differentiation commutes with multiplication by a real scalar. -/
theorem HasWeakCoordinateDerivative.const_smul
    {f f' : _root_.UnitAddTorus d → ℝ} {i : d}
    (h : HasWeakCoordinateDerivative f f' i) (c : ℝ) :
    HasWeakCoordinateDerivative (c • f) (c • f') i := by
  rw [hasWeakCoordinateDerivative_iff]
  refine ⟨h.integrable.smul c, h.integrable_deriv.smul c, ?_⟩
  intro φ
  have hleft :
      (fun x => coordinateDerivative φ i x * (c • f) x) =
        fun x => c * (coordinateDerivative φ i x * f x) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hright :
      (fun x => φ x * (c • f') x) = fun x => c * (φ x * f' x) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hleft, hright, integral_const_mul, integral_const_mul,
    h.integral_coordinateDerivative_mul_eq_neg_integral_mul φ]
  ring

/-- A constant scalar field has weak coordinate derivative zero. -/
theorem hasWeakCoordinateDerivative_const (c : ℝ) (i : d) :
    HasWeakCoordinateDerivative (fun _ : _root_.UnitAddTorus d => c) 0 i := by
  have hzero :
      coordinateDerivative (fun _ : _root_.UnitAddTorus d => c) i =
        (0 : _root_.UnitAddTorus d → ℝ) := by
    funext x
    exact coordinateDerivative_const c i x
  have h := hasWeakCoordinateDerivative_coordinateDerivative
    (fun _ : _root_.UnitAddTorus d => c) i (contDiffAlongCoordinate_const c i)
      (integrable_const c) (by rw [hzero]; exact integrable_zero _ _ _)
  rw [hzero] at h
  exact h

/-- Every periodic weak coordinate derivative has integral zero. This follows by testing against
the constant function `1` and is the basic compatibility condition for solving `∂ᵢ f = g` on a
torus. -/
theorem HasWeakCoordinateDerivative.integral_deriv_eq_zero
    {f f' : _root_.UnitAddTorus d → ℝ} {i : d}
    (h : HasWeakCoordinateDerivative f f' i) : ∫ x, f' x = 0 := by
  have htest := h.integral_coordinateDerivative_mul_eq_neg_integral_mul
    (CoordinateTestFunction.const i 1)
  have hzero :
      coordinateDerivative (CoordinateTestFunction.const i 1) i =
        (0 : _root_.UnitAddTorus d → ℝ) := by
    funext x
    exact coordinateDerivative_const 1 i x
  rw [hzero] at htest
  have hneg : 0 = -(∫ x, f' x) := by
    simpa only [Pi.zero_apply, zero_mul, integral_zero,
      CoordinateTestFunction.const_apply, one_mul] using htest
  exact neg_eq_zero.mp hneg.symm

end UnitAddTorus

end TauCeti
