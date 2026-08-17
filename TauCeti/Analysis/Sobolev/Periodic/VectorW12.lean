/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.W12
public import TauCeti.Analysis.VectorField.Flat.Weak

/-!
# Vector-valued periodic W¹,² and weak incompressibility

A vector-valued periodic Sobolev class is defined as the finite Hilbert product of the scalar
spaces `PeriodicW12`.  Thus membership is componentwise by construction, without choosing a tuple
of pointwise representatives.  The continuous value and weak-Jacobian maps take values in finite
Hilbert products of scalar `L²` classes, and their squared norms give the exact vector graph norm.

The diagonal of the quotient-level weak Jacobian defines a bounded linear weak-divergence map to
real `L²`.  Its kernel is a closed Hilbert subspace.  Explicit canonical representatives are used
only to bridge this quotient-native construction to the representative-level predicates
`HasWeakJacobian`, `HasWeakDivergence`, and `WeaklyDivergenceFree` from flat weak vector calculus.

This advances the finite-product and periodic parts of Layer 0, items 1 and 3, in the
`IncompressibleFlows` roadmap.

## Main declarations

* `TauCeti.UnitAddTorus.PeriodicVectorW12`: the finite Hilbert product of scalar periodic
  `W¹,²` spaces.
* `TauCeti.UnitAddTorus.PeriodicVectorW12.valueL` and `.weakJacobianL`: continuous quotient-level
  value and weak-Jacobian maps.
* `TauCeti.UnitAddTorus.PeriodicVectorW12.weakDivergenceL`: bounded linear weak divergence.
* `TauCeti.UnitAddTorus.periodicDivergenceFreeW12Submodule`: its closed kernel.
* `TauCeti.UnitAddTorus.mem_periodicDivergenceFreeW12Submodule_iff_weaklyDivergenceFree`:
  equivalence with representative-level weak incompressibility.
-/

public section

noncomputable section

namespace TauCeti.UnitAddTorus

open MeasureTheory
open scoped ENNReal

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq

/-- The quotient-native `L²` space of finite real vector fields, represented as the Hilbert
product of scalar `L²` classes. -/
abbrev PeriodicVectorL2 (d : Type*) [Fintype d] :=
  PiLp 2 fun _ : d ↦ Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))

/-- The quotient-native `L²` space of weak Jacobians.  The first index is the derivative
coordinate and the second is the value coordinate. -/
abbrev PeriodicWeakJacobianL2 (d : Type*) [Fintype d] :=
  PiLp 2 fun _ : d ↦ PiLp 2 fun _ : d ↦
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))

/-- Vector-valued periodic `W¹,²`, as the finite Hilbert product of its scalar components. -/
abbrev PeriodicVectorW12 (d : Type*) [Fintype d] :=
  PiLp 2 fun _ : d ↦ PeriodicW12 d

/-- Assemble a finite family of continuous linear maps into a Hilbert-product-valued map.
This is the local bridge needed because Mathlib's `lpPiLpₗᵢ` concerns discrete `lp`, not Bochner
`Lp` over a measure space. -/
private def piLpFamilyL {ι X : Type*} [Fintype ι] [NormedAddCommGroup X] [NormedSpace ℝ X]
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

namespace PeriodicVectorW12

/-- The continuous projection to scalar component `j`. -/
def componentL (j : d) : PeriodicVectorW12 d →L[ℝ] PeriodicW12 d :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ PeriodicW12 d) j

/-- Scalar component `j` of a vector-valued periodic Sobolev class. -/
def component (u : PeriodicVectorW12 d) (j : d) : PeriodicW12 d :=
  componentL j u

@[simp]
theorem componentL_apply (u : PeriodicVectorW12 d) (j : d) :
    componentL j u = component u j := by
  rw [component]

/-- Assemble a vector-valued periodic Sobolev class from its scalar quotient classes. -/
def ofComponents (u : d → PeriodicW12 d) : PeriodicVectorW12 d :=
  WithLp.toLp 2 u

@[simp]
theorem component_ofComponents (u : d → PeriodicW12 d) (j : d) :
    component (ofComponents u) j = u j := by
  rw [component, componentL]
  rfl

/-- Two vector-valued periodic Sobolev classes are equal when all scalar components are equal. -/
@[ext]
theorem ext_component {u v : PeriodicVectorW12 d}
    (h : ∀ j : d, component u j = component v j) : u = v := by
  apply PiLp.ext
  intro j
  exact h j

/-- The continuous projection to the Hilbert product of scalar `L²` value classes. -/
def valueL : PeriodicVectorW12 d →L[ℝ] PeriodicVectorL2 d :=
  piLpFamilyL (ι := d) (X := PeriodicVectorW12 d)
    fun j ↦ PeriodicW12.valueL.comp (componentL j)

/-- The Hilbert product of scalar `L²` value classes. -/
def value (u : PeriodicVectorW12 d) : PeriodicVectorL2 d :=
  valueL u

@[simp]
theorem valueL_apply (u : PeriodicVectorW12 d) : valueL u = value u := by
  rw [value]

@[simp]
theorem value_apply (u : PeriodicVectorW12 d) (j : d) :
    value u j = PeriodicW12.value (component u j) := by
  rw [value, valueL, piLpFamilyL_apply]
  rw [ContinuousLinearMap.comp_apply, PeriodicW12.valueL_apply, componentL_apply]

/-- The continuous projection to weak-Jacobian entry `∂ᵢuⱼ`. -/
def weakJacobianEntryL (i j : d) : PeriodicVectorW12 d →L[ℝ]
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  (PeriodicW12.weakDerivL i).comp (componentL j)

/-- Weak-Jacobian entry `∂ᵢuⱼ`. -/
def weakJacobianEntry (u : PeriodicVectorW12 d) (i j : d) :
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  weakJacobianEntryL i j u

@[simp]
theorem weakJacobianEntryL_apply (u : PeriodicVectorW12 d) (i j : d) :
    weakJacobianEntryL i j u = weakJacobianEntry u i j := by
  rw [weakJacobianEntry]

theorem weakJacobianEntry_eq (u : PeriodicVectorW12 d) (i j : d) :
    weakJacobianEntry u i j = PeriodicW12.weakDeriv (component u j) i := by
  rw [weakJacobianEntry, weakJacobianEntryL, ContinuousLinearMap.comp_apply,
    PeriodicW12.weakDerivL_apply, componentL_apply]

/-- The continuous projection to the full quotient-level weak Jacobian.  Its first index is the
derivative coordinate and its second index is the value coordinate. -/
def weakJacobianL : PeriodicVectorW12 d →L[ℝ] PeriodicWeakJacobianL2 d :=
  piLpFamilyL (ι := d) (X := PeriodicVectorW12 d) fun i ↦
    piLpFamilyL (ι := d) (X := PeriodicVectorW12 d) fun j ↦ weakJacobianEntryL i j

/-- The full quotient-level weak Jacobian. -/
def weakJacobian (u : PeriodicVectorW12 d) : PeriodicWeakJacobianL2 d :=
  weakJacobianL u

@[simp]
theorem weakJacobianL_apply (u : PeriodicVectorW12 d) :
    weakJacobianL u = weakJacobian u := by
  rw [weakJacobian]

@[simp]
theorem weakJacobian_apply (u : PeriodicVectorW12 d) (i j : d) :
    weakJacobian u i j = weakJacobianEntry u i j := by
  rw [weakJacobian, weakJacobianL, piLpFamilyL_apply, piLpFamilyL_apply,
    weakJacobianEntryL_apply]

/-- The vector graph norm is the sum of the squared scalar graph norms. -/
theorem norm_sq_eq_sum_norm_component_sq (u : PeriodicVectorW12 d) :
    ‖u‖ ^ 2 = ∑ j, ‖component u j‖ ^ 2 := by
  simpa only [component, componentL, PiLp.proj_apply] using
    PiLp.norm_sq_eq_of_L2 (fun _ : d ↦ PeriodicW12 d) u

/-- The squared vector-value norm is the sum of the squared scalar-value norms. -/
theorem norm_value_sq_eq_sum_norm_value_component_sq (u : PeriodicVectorW12 d) :
    ‖value u‖ ^ 2 = ∑ j, ‖PeriodicW12.value (component u j)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [value_apply]

/-- The squared weak-Jacobian norm is the sum of the squared norms of all entries. -/
theorem norm_weakJacobian_sq_eq_sum_norm_entry_sq (u : PeriodicVectorW12 d) :
    ‖weakJacobian u‖ ^ 2 = ∑ i, ∑ j, ‖weakJacobianEntry u i j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [weakJacobian_apply]

/-- The vector-valued `W¹,²` norm is exactly the `L²` value norm plus the full weak-Jacobian
norm. -/
theorem norm_sq_eq_norm_value_sq_add_norm_weakJacobian_sq (u : PeriodicVectorW12 d) :
    ‖u‖ ^ 2 = ‖value u‖ ^ 2 + ‖weakJacobian u‖ ^ 2 := by
  rw [norm_sq_eq_sum_norm_component_sq, norm_value_sq_eq_sum_norm_value_component_sq,
    norm_weakJacobian_sq_eq_sum_norm_entry_sq]
  simp_rw [PeriodicW12.norm_sq_eq_norm_value_sq_add_sum_norm_weakDeriv_sq]
  simp only [weakJacobianEntry_eq]
  rw [Finset.sum_add_distrib, Finset.sum_comm]

/-- Weak divergence as the bounded linear diagonal trace of the quotient-level weak Jacobian. -/
def weakDivergenceL : PeriodicVectorW12 d →L[ℝ]
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  ∑ i, weakJacobianEntryL i i

/-- The quotient-level weak divergence. -/
def weakDivergence (u : PeriodicVectorW12 d) :
    Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
  weakDivergenceL u

@[simp]
theorem weakDivergenceL_apply (u : PeriodicVectorW12 d) :
    weakDivergenceL u = weakDivergence u := by
  rw [weakDivergence]

theorem weakDivergence_eq_sum (u : PeriodicVectorW12 d) :
    weakDivergence u = ∑ i, weakJacobianEntry u i i := by
  rw [weakDivergence, weakDivergenceL]
  have hsum (s : Finset d) :
      (∑ i ∈ s, weakJacobianEntryL i i) u =
        ∑ i ∈ s, weakJacobianEntry u i i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert, ha, not_false_eq_true, add_apply,
          weakJacobianEntryL_apply, ih]
  simpa only [Finset.sum_const_zero, Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
    hsum Finset.univ

/-- The canonical pointwise representative selected from the component `L²` classes. -/
def representative (u : PeriodicVectorW12 d) : VectorField d :=
  fun x j ↦ PeriodicW12.value (component u j) x

/-- The canonical pointwise representative of the quotient-level weak Jacobian. -/
def weakJacobianRepresentative (u : PeriodicVectorW12 d) : TensorField d :=
  fun x i j ↦ weakJacobianEntry u i j x

/-- The canonical representatives satisfy the componentwise weak-Jacobian relation. -/
theorem hasWeakJacobian (u : PeriodicVectorW12 d) :
    HasWeakJacobian (representative u) (weakJacobianRepresentative u) := by
  rw [hasWeakJacobian_iff]
  intro i j
  simpa only [representative, weakJacobianRepresentative, weakJacobianEntry_eq] using
    PeriodicW12.hasWeakCoordinateDerivative (component u j) i

/-- The quotient-level weak divergence agrees almost everywhere with the diagonal trace of the
canonical weak-Jacobian representative. -/
theorem weakDivergence_ae_eq_representative (u : PeriodicVectorW12 d) :
    weakDivergence u =ᵐ[volume]
      TauCeti.UnitAddTorus.weakDivergence (weakJacobianRepresentative u) := by
  rw [weakDivergence_eq_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i ↦ weakJacobianEntry u i i)] with x hx
  rw [TauCeti.UnitAddTorus.weakDivergence_apply]
  simpa only [weakJacobianRepresentative] using hx

/-- The quotient-level weak divergence represents the weak divergence of the canonical vector
representative. -/
theorem hasWeakDivergence (u : PeriodicVectorW12 d) :
    HasWeakDivergence (representative u) (weakDivergence u) :=
  hasWeakDivergence_iff.mpr
    ⟨weakJacobianRepresentative u, hasWeakJacobian u,
      weakDivergence_ae_eq_representative u⟩

end PeriodicVectorW12

/-- The closed divergence-free subspace of vector-valued periodic `W¹,²`. -/
def periodicDivergenceFreeW12Submodule (d : Type*) [Fintype d] :
    ClosedSubmodule ℝ (PeriodicVectorW12 d) :=
  (⊥ : ClosedSubmodule ℝ
    (Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d)))).comap
      PeriodicVectorW12.weakDivergenceL

/-- Membership in the closed divergence-free subspace is vanishing of the quotient-level weak
divergence. -/
theorem mem_periodicDivergenceFreeW12Submodule_iff (u : PeriodicVectorW12 d) :
    u ∈ periodicDivergenceFreeW12Submodule d ↔
      PeriodicVectorW12.weakDivergence u = 0 := by
  simp only [periodicDivergenceFreeW12Submodule, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot, PeriodicVectorW12.weakDivergence]

/-- Kernel membership is equivalent to representative-level weak incompressibility. -/
theorem mem_periodicDivergenceFreeW12Submodule_iff_weaklyDivergenceFree
    (u : PeriodicVectorW12 d) :
    u ∈ periodicDivergenceFreeW12Submodule d ↔
      WeaklyDivergenceFree (PeriodicVectorW12.representative u) := by
  rw [mem_periodicDivergenceFreeW12Submodule_iff, weaklyDivergenceFree_iff]
  constructor
  · intro hdiv
    rcases hasWeakDivergence_iff.mp (PeriodicVectorW12.hasWeakDivergence u) with ⟨J, hJ, hqJ⟩
    apply hasWeakDivergence_iff.mpr
    refine ⟨J, hJ, ?_⟩
    have hzero : PeriodicVectorW12.weakDivergence u =ᵐ[volume]
        (0 : _root_.UnitAddTorus d → ℝ) := by
      rw [hdiv]
      exact Lp.coeFn_zero ℝ 2 volume
    exact hzero.symm.trans hqJ
  · intro hdiv
    have hzero : PeriodicVectorW12.weakDivergence u =ᵐ[volume]
        (0 : _root_.UnitAddTorus d → ℝ) :=
      (PeriodicVectorW12.hasWeakDivergence u).ae_eq hdiv
    apply Lp.ext
    exact hzero.trans (Lp.coeFn_zero ℝ 2 volume).symm

/-- The complete Hilbert space of weakly divergence-free periodic vector `W¹,²` classes. -/
abbrev PeriodicDivergenceFreeW12 (d : Type*) [Fintype d] :=
  (periodicDivergenceFreeW12Submodule d).toSubmodule

namespace PeriodicDivergenceFreeW12

/-- The inner product inherited from vector-valued periodic `W¹,²`.  This is stated
explicitly because the `PiLp` inner-product instance and its pre-existing module instance are not
definitionally aligned closely enough for `Submodule.innerProductSpace` to synthesize here. -/
instance : InnerProductSpace ℝ (PeriodicDivergenceFreeW12 d) where
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

/-- The continuous inclusion into vector-valued periodic `W¹,²`. -/
def toPeriodicVectorW12L :
    PeriodicDivergenceFreeW12 d →L[ℝ] PeriodicVectorW12 d :=
  (periodicDivergenceFreeW12Submodule d).toSubmodule.subtypeL

/-- The underlying vector-valued periodic `W¹,²` class. -/
def toPeriodicVectorW12 (u : PeriodicDivergenceFreeW12 d) : PeriodicVectorW12 d :=
  toPeriodicVectorW12L u

@[simp]
theorem toPeriodicVectorW12L_apply (u : PeriodicDivergenceFreeW12 d) :
    toPeriodicVectorW12L u = toPeriodicVectorW12 u := by
  rw [toPeriodicVectorW12]

/-- The canonical representative of a divergence-free quotient class is weakly
divergence-free. -/
theorem weaklyDivergenceFree (u : PeriodicDivergenceFreeW12 d) :
    WeaklyDivergenceFree
      (PeriodicVectorW12.representative (toPeriodicVectorW12 u)) :=
  (mem_periodicDivergenceFreeW12Submodule_iff_weaklyDivergenceFree u.1).mp u.2

/-- The divergence-free periodic vector `W¹,²` subspace is complete. -/
instance : CompleteSpace (PeriodicDivergenceFreeW12 d) :=
  (periodicDivergenceFreeW12Submodule d).isClosed.completeSpace_coe

end PeriodicDivergenceFreeW12

end TauCeti.UnitAddTorus
