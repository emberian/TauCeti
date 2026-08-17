/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.WeakDerivUniqueness
public import TauCeti.Analysis.Sobolev.Periodic.FourierWeakDeriv
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The scalar periodic Sobolev space W¹,²

This file packages the scalar first-order weak Sobolev space on a finite unit torus as a closed
graph in `L²`.  Its ambient jet is the Euclidean product of an `L²` value class and an
`L²` Euclidean-gradient class.  For every coordinate and every bounded coordinate test function,
the graph is cut out by the continuous functional

`⟪∂ᵢ φ, u⟫ + ⟪φ, Gᵢ⟫`.

Membership is therefore exactly the componentwise periodic weak-derivative relation, rather than
a proof field asserting closedness.  The closed-submodule presentation makes completeness
structural, while almost-everywhere uniqueness of periodic weak coordinate derivatives makes an
element determined by its `L²` value class.

This is the scalar `p = 2`, order-one graph-space part of Layer 0, item 3 in the
`IncompressibleFlows` roadmap.

## Main declarations

* `TauCeti.UnitAddTorus.periodicW12Submodule`: the closed graph in the value-gradient jet space.
* `TauCeti.UnitAddTorus.PeriodicW12`: the resulting complete Hilbert space.
* `TauCeti.UnitAddTorus.mem_periodicW12Submodule_iff_hasWeakCoordinateDerivative`: membership is
  componentwise weak coordinate differentiability.
* `TauCeti.UnitAddTorus.PeriodicW12.ext_value`: a periodic Sobolev class is determined by its
  value class.
-/

public section

noncomputable section

namespace TauCeti.UnitAddTorus

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq

/-- The ambient value-gradient graph space for scalar periodic `W¹,²`. -/
abbrev PeriodicSobolev1JetLp (d : Type*) [Fintype d] :=
  WithLp 2
    (Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) ×
      Lp (EuclideanSpace ℝ d) 2 (volume : Measure (_root_.UnitAddTorus d)))

/-- The continuous projection from a periodic Sobolev jet to its value class. -/
def PeriodicSobolev1JetLp.valueL :
    PeriodicSobolev1JetLp d →L[ℝ]
      Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  WithLp.fstL 2 ℝ _ _

/-- The value class of a periodic Sobolev jet. -/
def PeriodicSobolev1JetLp.value (J : PeriodicSobolev1JetLp d) :
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  PeriodicSobolev1JetLp.valueL J

/-- The continuous projection from a periodic Sobolev jet to its Euclidean weak gradient. -/
def PeriodicSobolev1JetLp.gradientL :
    PeriodicSobolev1JetLp d →L[ℝ]
      Lp (EuclideanSpace ℝ d) 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  WithLp.sndL 2 ℝ _ _

/-- The Euclidean weak-gradient class of a periodic Sobolev jet. -/
def PeriodicSobolev1JetLp.gradient (J : PeriodicSobolev1JetLp d) :
    Lp (EuclideanSpace ℝ d) 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  PeriodicSobolev1JetLp.gradientL J

/-- The continuous projection to coordinate `i` of the candidate weak gradient. -/
def PeriodicSobolev1JetLp.weakDerivL (i : d) :
    PeriodicSobolev1JetLp d →L[ℝ]
      Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLpL 2
      (volume : Measure (_root_.UnitAddTorus d))).comp
    PeriodicSobolev1JetLp.gradientL

/-- Coordinate `i` of the candidate weak gradient. -/
def PeriodicSobolev1JetLp.weakDeriv (J : PeriodicSobolev1JetLp d) (i : d) :
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  PeriodicSobolev1JetLp.weakDerivL i J

@[simp]
theorem PeriodicSobolev1JetLp.valueL_apply (J : PeriodicSobolev1JetLp d) :
    PeriodicSobolev1JetLp.valueL J = PeriodicSobolev1JetLp.value J := by
  rw [PeriodicSobolev1JetLp.value]

@[simp]
theorem PeriodicSobolev1JetLp.gradientL_apply (J : PeriodicSobolev1JetLp d) :
    PeriodicSobolev1JetLp.gradientL J = PeriodicSobolev1JetLp.gradient J := by
  rw [PeriodicSobolev1JetLp.gradient]

@[simp]
theorem PeriodicSobolev1JetLp.weakDerivL_apply (J : PeriodicSobolev1JetLp d) (i : d) :
    PeriodicSobolev1JetLp.weakDerivL i J = PeriodicSobolev1JetLp.weakDeriv J i := by
  rw [PeriodicSobolev1JetLp.weakDeriv]

/-- A bounded periodic coordinate test function, regarded as an `L²` class. -/
private def CoordinateTestFunction.toL2 {i : d} (φ : CoordinateTestFunction d i) :
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  (φ.memLp_top.mono_exponent (by simp)).toLp φ

/-- The coordinate derivative of a periodic test function, regarded as an `L²` class. -/
private def CoordinateTestFunction.coordinateDerivativeToL2 {i : d}
    (φ : CoordinateTestFunction d i) :
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  (φ.coordinateDerivative_memLp_top.mono_exponent (by simp)).toLp
    (coordinateDerivative φ i)

private theorem CoordinateTestFunction.toL2_apply_ae {i : d}
    (φ : CoordinateTestFunction d i) :
    CoordinateTestFunction.toL2 φ =ᵐ[volume] φ :=
  MemLp.coeFn_toLp (φ.memLp_top.mono_exponent (by simp))

private theorem CoordinateTestFunction.coordinateDerivativeToL2_apply_ae {i : d}
    (φ : CoordinateTestFunction d i) :
    CoordinateTestFunction.coordinateDerivativeToL2 φ =ᵐ[volume]
      coordinateDerivative φ i :=
  MemLp.coeFn_toLp (φ.coordinateDerivative_memLp_top.mono_exponent (by simp))

/-- The continuous `L²` functional expressing the weak derivative identity in coordinate `i`
against the bounded coordinate test function `φ`. -/
private def periodicWeakDerivativeTestFunctional {i : d}
    (φ : CoordinateTestFunction d i) : PeriodicSobolev1JetLp d →L[ℝ] ℝ :=
  (innerSL ℝ (CoordinateTestFunction.coordinateDerivativeToL2 φ)).comp
      PeriodicSobolev1JetLp.valueL +
    (innerSL ℝ (CoordinateTestFunction.toL2 φ)).comp
      (PeriodicSobolev1JetLp.weakDerivL i)

private theorem periodicWeakDerivativeTestFunctional_apply {i : d}
    (J : PeriodicSobolev1JetLp d) (φ : CoordinateTestFunction d i) :
    periodicWeakDerivativeTestFunctional φ J =
      (∫ x, coordinateDerivative φ i x * PeriodicSobolev1JetLp.value J x) +
        ∫ x, φ x * PeriodicSobolev1JetLp.weakDeriv J i x := by
  rw [periodicWeakDerivativeTestFunctional]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    PeriodicSobolev1JetLp.valueL_apply, PeriodicSobolev1JetLp.weakDerivL_apply]
  rw [innerSL_apply_apply, innerSL_apply_apply, L2.inner_def, L2.inner_def]
  congr 1
  · apply integral_congr_ae
    filter_upwards [CoordinateTestFunction.coordinateDerivativeToL2_apply_ae φ] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  · apply integral_congr_ae
    filter_upwards [CoordinateTestFunction.toL2_apply_ae φ] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- The closed graph of scalar periodic `W¹,²`: every coordinate weak-derivative test functional
vanishes. -/
def periodicW12Submodule (d : Type*) [Fintype d] :
    ClosedSubmodule ℝ (PeriodicSobolev1JetLp d) :=
  ⨅ i : d, ⨅ φ : CoordinateTestFunction d i,
    (⊥ : ClosedSubmodule ℝ ℝ).comap (periodicWeakDerivativeTestFunctional φ)

/-- Membership in the periodic graph is exactly the family of weak integration-by-parts
identities. -/
theorem mem_periodicW12Submodule_iff (J : PeriodicSobolev1JetLp d) :
    J ∈ periodicW12Submodule d ↔
      ∀ (i : d) (φ : CoordinateTestFunction d i),
        (∫ x, coordinateDerivative φ i x * PeriodicSobolev1JetLp.value J x) =
          -∫ x, φ x * PeriodicSobolev1JetLp.weakDeriv J i x := by
  rw [show J ∈ periodicW12Submodule d ↔
      ∀ (i : d) (φ : CoordinateTestFunction d i),
        periodicWeakDerivativeTestFunctional φ J = 0 by
    simp [periodicW12Submodule]]
  simp only [periodicWeakDerivativeTestFunctional_apply, add_eq_zero_iff_eq_neg]

private theorem integrable_periodicSobolev1JetLp_value (J : PeriodicSobolev1JetLp d) :
    Integrable (PeriodicSobolev1JetLp.value J) :=
  memLp_one_iff_integrable.mp <| (Lp.memLp _).mono_exponent one_le_two

private theorem integrable_periodicSobolev1JetLp_weakDeriv
    (J : PeriodicSobolev1JetLp d) (i : d) :
    Integrable (PeriodicSobolev1JetLp.weakDeriv J i) :=
  memLp_one_iff_integrable.mp <| (Lp.memLp _).mono_exponent one_le_two

/-- A jet lies in the closed graph exactly when every gradient coordinate is the periodic weak
coordinate derivative of its value class. -/
theorem mem_periodicW12Submodule_iff_hasWeakCoordinateDerivative
    (J : PeriodicSobolev1JetLp d) :
    J ∈ periodicW12Submodule d ↔
      ∀ i : d, HasWeakCoordinateDerivative (PeriodicSobolev1JetLp.value J)
        (PeriodicSobolev1JetLp.weakDeriv J i) i := by
  rw [mem_periodicW12Submodule_iff]
  constructor
  · intro h i
    rw [hasWeakCoordinateDerivative_iff]
    exact ⟨integrable_periodicSobolev1JetLp_value J,
      integrable_periodicSobolev1JetLp_weakDeriv J i, h i⟩
  · intro h i
    exact (h i).integral_coordinateDerivative_mul_eq_neg_integral_mul

/-- The scalar periodic first-order Sobolev space `W¹,²(UnitAddTorus d)`. -/
abbrev PeriodicW12 (d : Type*) [Fintype d] :=
  (periodicW12Submodule d).toSubmodule

namespace PeriodicW12

/-- The continuous projection to the `L²` value class. -/
def valueL : PeriodicW12 d →L[ℝ]
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  PeriodicSobolev1JetLp.valueL.comp (periodicW12Submodule d).toSubmodule.subtypeL

/-- The `L²` value class. -/
def value (u : PeriodicW12 d) :
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  valueL u

@[simp]
theorem valueL_apply (u : PeriodicW12 d) : valueL u = value u := by
  rw [value]

/-- The continuous projection to the `L²` Euclidean weak gradient. -/
def gradientL : PeriodicW12 d →L[ℝ]
    Lp (EuclideanSpace ℝ d) 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  PeriodicSobolev1JetLp.gradientL.comp (periodicW12Submodule d).toSubmodule.subtypeL

/-- The `L²` Euclidean weak gradient. -/
def gradient (u : PeriodicW12 d) :
    Lp (EuclideanSpace ℝ d) 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  gradientL u

@[simp]
theorem gradientL_apply (u : PeriodicW12 d) : gradientL u = gradient u := by
  rw [gradient]

/-- The continuous projection to coordinate `i` of the `L²` weak gradient. -/
def weakDerivL (i : d) : PeriodicW12 d →L[ℝ]
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  PeriodicSobolev1JetLp.weakDerivL i |>.comp
    (periodicW12Submodule d).toSubmodule.subtypeL

/-- Coordinate `i` of the `L²` weak gradient. -/
def weakDeriv (u : PeriodicW12 d) (i : d) :
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  weakDerivL i u

@[simp]
theorem weakDerivL_apply (u : PeriodicW12 d) (i : d) :
    weakDerivL i u = weakDeriv u i := by
  rw [weakDeriv]

/-- Construct a periodic Sobolev class from an `L²` value, an `L²` Euclidean gradient, and the
componentwise weak-derivative identities on their canonical representatives. -/
def mk (u : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)))
    (G : Lp (EuclideanSpace ℝ d) 2 (volume : Measure (_root_.UnitAddTorus d)))
    (h : ∀ i : d, HasWeakCoordinateDerivative u
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLp G) i) :
    PeriodicW12 d :=
  ⟨WithLp.toLp 2 (u, G),
    (mem_periodicW12Submodule_iff_hasWeakCoordinateDerivative _).mpr h⟩

@[simp]
theorem value_mk (u : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)))
    (G : Lp (EuclideanSpace ℝ d) 2 (volume : Measure (_root_.UnitAddTorus d)))
    (h : ∀ i : d, HasWeakCoordinateDerivative u
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLp G) i) :
    value (mk u G h) = u := by
  rfl

@[simp]
theorem gradient_mk (u : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)))
    (G : Lp (EuclideanSpace ℝ d) 2 (volume : Measure (_root_.UnitAddTorus d)))
    (h : ∀ i : d, HasWeakCoordinateDerivative u
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLp G) i) :
    gradient (mk u G h) = G := by
  rfl

@[simp]
theorem weakDeriv_mk (u : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)))
    (G : Lp (EuclideanSpace ℝ d) 2 (volume : Measure (_root_.UnitAddTorus d)))
    (h : ∀ i : d, HasWeakCoordinateDerivative u
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLp G) i) (i : d) :
    weakDeriv (mk u G h) i =
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLp G := by
  rfl

/-- Every periodic `W¹,²` class carries the componentwise weak-derivative relation. -/
theorem hasWeakCoordinateDerivative (u : PeriodicW12 d) (i : d) :
    HasWeakCoordinateDerivative (value u) (weakDeriv u i) i :=
  (mem_periodicW12Submodule_iff_hasWeakCoordinateDerivative u.1).mp u.2 i

/-- Coordinate projection of the weak-gradient class agrees almost everywhere with pointwise
evaluation of the Euclidean gradient representative. -/
theorem weakDeriv_apply_ae (u : PeriodicW12 d) (i : d) :
    weakDeriv u i =ᵐ[volume] fun x ↦ gradient u x i := by
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLp (gradient u) =ᵐ[volume]
    fun x ↦ gradient u x i
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).coeFn_compLp (gradient u)

/-- Two periodic Sobolev classes agree when their value and gradient classes agree. -/
theorem ext_value_gradient {u v : PeriodicW12 d}
    (hvalue : value u = value v) (hgradient : gradient u = gradient v) : u = v := by
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  exact Prod.ext hvalue hgradient

/-- Two periodic Sobolev classes agree when their value classes agree; weak-derivative uniqueness
determines every coordinate of the gradient. -/
@[ext]
theorem ext_value {u v : PeriodicW12 d} (hvalue : value u = value v) : u = v := by
  apply ext_value_gradient hvalue
  apply Lp.ext
  have hcoord (i : d) : weakDeriv u i = weakDeriv v i := by
    apply Lp.ext
    exact (hasWeakCoordinateDerivative u i).ae_eq_deriv <| by
      simpa only [hvalue] using hasWeakCoordinateDerivative v i
  have hgradient_ae : gradient u =ᵐ[volume] gradient v := by
    have hu : ∀ᵐ x ∂volume, ∀ i : d, weakDeriv u i x = gradient u x i :=
      by
        simpa only [Set.mem_univ, forall_const] using
          (Filter.eventually_all_finite Set.finite_univ).2 fun i _ ↦ weakDeriv_apply_ae u i
    have hv : ∀ᵐ x ∂volume, ∀ i : d, weakDeriv v i x = gradient v x i :=
      by
        simpa only [Set.mem_univ, forall_const] using
          (Filter.eventually_all_finite Set.finite_univ).2 fun i _ ↦ weakDeriv_apply_ae v i
    have huv : ∀ᵐ x ∂volume, ∀ i : d, weakDeriv u i x = weakDeriv v i x :=
      by
        simpa only [Set.mem_univ, forall_const] using
          (Filter.eventually_all_finite Set.finite_univ).2 fun i _ ↦ by
            have hi : weakDeriv u i =ᵐ[volume] weakDeriv v i := by rw [hcoord i]
            exact hi
    filter_upwards [hu, hv, huv] with x hxu hxv hxuv
    apply PiLp.ext
    intro i
    exact (hxu i).symm.trans ((hxuv i).trans (hxv i))
  exact hgradient_ae

/-- The graph norm controls the value-class norm. -/
theorem norm_value_le (u : PeriodicW12 d) : ‖value u‖ ≤ ‖u‖ := by
  exact WithLp.norm_fst_le _ u.1

/-- The graph norm controls the weak-gradient norm. -/
theorem norm_gradient_le (u : PeriodicW12 d) : ‖gradient u‖ ≤ ‖u‖ := by
  exact WithLp.norm_snd_le _ u.1

/-- The periodic `W¹,²` norm is the Hilbert graph norm of the value and gradient classes. -/
theorem norm_sq_eq_norm_value_sq_add_norm_gradient_sq (u : PeriodicW12 d) :
    ‖u‖ ^ 2 = ‖value u‖ ^ 2 + ‖gradient u‖ ^ 2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 u.1

/-- The squared `L²` norm of the weak gradient is the sum of the squared norms of its coordinate
weak derivatives. -/
theorem norm_gradient_sq_eq_sum_norm_weakDeriv_sq (u : PeriodicW12 d) :
    ‖gradient u‖ ^ 2 = ∑ i, ‖weakDeriv u i‖ ^ 2 := by
  have hcoord : ∀ᵐ x ∂volume, ∀ i : d, weakDeriv u i x = gradient u x i := by
    simpa only [Set.mem_univ, forall_const] using
      (Filter.eventually_all_finite Set.finite_univ).2 fun i _ ↦ weakDeriv_apply_ae u i
  calc
    ‖gradient u‖ ^ 2 = ∫ x, ⟪gradient u x, gradient u x⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    _ = ∫ x, ∑ i, weakDeriv u i x * weakDeriv u i x := by
      apply integral_congr_ae
      filter_upwards [hcoord] with x hx
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      apply Finset.sum_congr rfl
      intro i _
      rw [hx i]
    _ = ∑ i, ∫ x, weakDeriv u i x * weakDeriv u i x := by
      apply integral_finsetSum
      intro i _
      simpa only [RCLike.inner_apply, conj_trivial] using
        L2.integrable_inner (𝕜 := ℝ) (weakDeriv u i) (weakDeriv u i)
    _ = ∑ i, ‖weakDeriv u i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [RCLike.inner_apply, conj_trivial]

/-- The full periodic `W¹,²` graph norm splits into the value energy and all coordinate
weak-derivative energies. -/
theorem norm_sq_eq_norm_value_sq_add_sum_norm_weakDeriv_sq (u : PeriodicW12 d) :
    ‖u‖ ^ 2 = ‖value u‖ ^ 2 + ∑ i, ‖weakDeriv u i‖ ^ 2 := by
  rw [norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
    norm_gradient_sq_eq_sum_norm_weakDeriv_sq]

/-- The sharp mean-zero Poincare inequality on periodic `W¹,²`, with the first nonzero unit-torus
frequency constant. -/
theorem norm_value_sq_le_inv_four_pi_sq_mul_norm_gradient_sq
    (u : PeriodicW12 d) (hmean : mean (value u) = 0) :
    ‖value u‖ ^ 2 ≤ ((2 * Real.pi) ^ 2)⁻¹ * ‖gradient u‖ ^ 2 := by
  let D : d → _root_.UnitAddTorus d → ℝ := fun i x ↦ weakDeriv u i x
  have hD (i : d) : MemLp (D i) 2 := Lp.memLp (weakDeriv u i)
  have hweak (i : d) : HasWeakCoordinateDerivative (value u) (D i) i :=
    hasWeakCoordinateDerivative u i
  have hp := norm_sq_toLp_le_inv_four_pi_sq_mul_sum_weakGradient
    (value u) D (Lp.memLp (value u)) hD hweak hmean
  simpa only [D, Lp.toLp_coeFn, norm_gradient_sq_eq_sum_norm_weakDeriv_sq] using hp

/-- Periodic scalar `W¹,²` is complete because it is a closed subspace of its Hilbert graph
space. -/
instance : CompleteSpace (PeriodicW12 d) :=
  (periodicW12Submodule d).isClosed.completeSpace_coe

end PeriodicW12

end TauCeti.UnitAddTorus
