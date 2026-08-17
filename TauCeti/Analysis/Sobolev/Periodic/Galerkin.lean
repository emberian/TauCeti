/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.VectorFourier
public import TauCeti.Analysis.Sobolev.Periodic.VectorW12Density

/-!
# Finite Fourier--Galerkin spaces for periodic incompressible flow

This file proves that finite Fourier truncation preserves both constraints defining the periodic
energy space: zero mean and weak incompressibility.  The essential calculation is quotient-native.
For a weakly divergence-free vector field, the diagonal weak derivatives of one real Fourier term
sum to the real part of

`(2 * π * I) * (sum i, k i * uHat k i) * mFourier k`,

which vanishes by the previously proved Fourier characterization of weak divergence.

For a finite frequency set `S`, real coefficient synthesis has finite-dimensional range in
`PeriodicVectorW12`.  Pulling that range back to the mean-zero incompressible energy space gives a
finite-dimensional closed Galerkin subspace.  The explicit Fourier truncations belong to these
subspaces and converge in the full energy graph norm, so their union is dense.

The closed finite-dimensional spaces admit canonical orthogonal projections in the energy graph
inner product.  These maps are contractive, symmetric, idempotent, and converge strongly to the
identity along the directed net of finite frequency sets.  The proof of convergence deliberately
does not identify the projection with the raw real Fourier truncation: arbitrary finite frequency
sets need not be symmetric under negation, so those truncations are used only as convergent
competitors in the same Galerkin space.  Zero-extension of real Fourier coefficients proves that
the Galerkin spaces are monotone in the frequency set, and the associated nested orthogonal
projectors absorb in both composition orders.

This advances Layer 7, item 1, of the `IncompressibleFlows` roadmap.  It does **not** yet prove
commutation with the Leray or Stokes operators or extend nonlinear cancellation to the
finite-dimensional evolution system.

## Main declarations

* `PeriodicVectorW12.weakDivergence_fourierTerm_eq_zero`: one Fourier term preserves weak
  incompressibility.
* `PeriodicMeanZeroDivergenceFreeW12.fourierTruncation`: constraint-preserving energy truncation.
* `periodicGalerkinSubmodule`: a finite-dimensional energy subspace at finite frequency support.
* `periodicGalerkinSubmodule_mono`: directedness under enlargement of the frequency set.
* `periodicGalerkinProjectionL`: its canonical energy-orthogonal projection.
* `periodicGalerkinProjectionL_comp_of_subset`: nested-projector absorption.
* `tendsto_periodicGalerkinProjectionL`: strong graph-norm convergence to the identity.
* `dense_isFiniteGalerkinField`: graph-norm density of finite incompressible Fourier fields.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory Filter Topology

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq
attribute [local instance] unitAddTorusIsProbabilityMeasure

namespace PeriodicVectorW12

/-- The weak divergence of one Fourier term of a weakly divergence-free field vanishes. -/
theorem weakDivergence_fourierTerm_eq_zero
    (u : PeriodicVectorW12 d)
    (hu : u ∈ periodicDivergenceFreeW12Submodule d) (k : d → ℤ) :
    weakDivergence (fourierTerm u k) = 0 := by
  have hpair : fourierDivergencePairing u k = 0 :=
    (mem_periodicDivergenceFreeW12Submodule_iff_forall_fourierDivergencePairing_eq_zero u).mp
      hu k
  apply Lp.ext
  have hall : ∀ᵐ x ∂volume, ∀ i : d,
      weakJacobianEntry (fourierTerm u k) i i x =
        (2 * Real.pi * Complex.I * (k i) *
          mFourierCoeff u k i * _root_.UnitAddTorus.mFourier k x).re := by
    simpa only [Set.mem_univ, forall_const] using
      (Filter.eventually_all_finite Set.finite_univ).2 fun i _ ↦ by
        rw [weakJacobianEntry_fourierTerm, PeriodicW12.fourierTerm_eq_realMFourierAtom]
        have h := PeriodicW12.weakDeriv_realMFourierAtom_ae
          (mFourierCoeff u k i) k i
        filter_upwards [h] with x hx
        simpa only [mFourierCoeff_apply_eq_mFourierCoeff] using hx
  filter_upwards [hall,
    Lp.coeFn_finsetSum Finset.univ
      (fun i ↦ weakJacobianEntry (fourierTerm u k) i i),
    Lp.coeFn_zero ℝ 2 volume] with x hx hsum hzero
  rw [weakDivergence_eq_sum, hsum, hzero]
  simp only [Finset.sum_apply, Pi.zero_apply]
  simp_rw [hx]
  calc
    (∑ i, (2 * Real.pi * Complex.I * (k i) *
        mFourierCoeff u k i * _root_.UnitAddTorus.mFourier k x).re) =
        (∑ i, 2 * Real.pi * Complex.I * (k i) *
          mFourierCoeff u k i * _root_.UnitAddTorus.mFourier k x).re := by
      rw [Complex.re_sum]
    _ = ((2 * Real.pi * Complex.I) * fourierDivergencePairing u k *
        _root_.UnitAddTorus.mFourier k x).re := by
      apply congrArg Complex.re
      rw [fourierDivergencePairing_eq_sum, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [hpair]; norm_num

/-- Real finite Fourier synthesis with one coefficient per component and selected frequency. -/
def realTrigonometricSynthesis (S : Finset (d → ℤ)) :
    (d → S → ℂ) →ₗ[ℝ] PeriodicVectorW12 d where
  toFun a := ofComponents fun j ↦
    ∑ k : S, PeriodicW12.realMFourierAtom (a j k) k.1
  map_add' a b := by
    apply ext_component
    intro j
    rw [component_ofComponents, ← componentL_apply, map_add]
    simp only [Pi.add_apply, PeriodicW12.realMFourierAtom_add, Finset.sum_add_distrib,
      componentL_apply, component_ofComponents]
  map_smul' r a := by
    apply ext_component
    intro j
    rw [component_ofComponents, ← componentL_apply, map_smul]
    simp only [Pi.smul_apply, Complex.real_smul, PeriodicW12.realMFourierAtom_smul,
      componentL_apply, component_ofComponents]
    rw [Finset.smul_sum]
    rfl

/-- A component of real finite Fourier synthesis is the corresponding finite mode sum. -/
@[simp]
theorem component_realTrigonometricSynthesis (S : Finset (d → ℤ))
    (a : d → S → ℂ) (j : d) :
    component (realTrigonometricSynthesis S a) j =
      ∑ k : S, PeriodicW12.realMFourierAtom (a j k) k.1 := by
  change component (ofComponents fun j ↦
    ∑ k : S, PeriodicW12.realMFourierAtom (a j k) k.1) j = _
  rw [component_ofComponents]

/-- The finite-dimensional ambient vector trigonometric subspace supported in `S`. -/
def realTrigonometricSubmodule (S : Finset (d → ℤ)) :
    Submodule ℝ (PeriodicVectorW12 d) :=
  (realTrigonometricSynthesis S).range

/-- Enlarging the frequency set enlarges the ambient real trigonometric subspace. -/
theorem realTrigonometricSubmodule_mono {S T : Finset (d → ℤ)}
    (hST : S ⊆ T) : realTrigonometricSubmodule S ≤ realTrigonometricSubmodule T := by
  rintro _ ⟨a, rfl⟩
  let b : d → T → ℂ := fun j k ↦ if hk : k.1 ∈ S then a j ⟨k.1, hk⟩ else 0
  refine ⟨b, ?_⟩
  apply ext_component
  intro j
  rw [component_realTrigonometricSynthesis, component_realTrigonometricSynthesis]
  let g : (d → ℤ) → PeriodicW12 d := fun k ↦
    if hk : k ∈ S then PeriodicW12.realMFourierAtom (a j ⟨k, hk⟩) k else 0
  calc
    (∑ k : T, PeriodicW12.realMFourierAtom (b j k) k.1) = ∑ k ∈ T, g k := by
      rw [Finset.sum_subtype T (fun _ ↦ Iff.rfl) g]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.1 ∈ S <;> simp [b, g, hk]
    _ = ∑ k ∈ S, g k := by
      symm
      apply Finset.sum_subset hST
      intro k hkT hkS
      simp [g, hkS]
    _ = ∑ k : S, PeriodicW12.realMFourierAtom (a j k) k.1 := by
      rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl) g]
      apply Finset.sum_congr rfl
      intro k hk
      simp [g]

noncomputable instance finiteDimensional_realTrigonometricSubmodule
    (S : Finset (d → ℤ)) :
    FiniteDimensional ℝ (realTrigonometricSubmodule S) :=
  FiniteDimensional.of_surjective (realTrigonometricSynthesis S).rangeRestrict
    (LinearMap.surjective_rangeRestrict _)

/-- A finite Fourier truncation belongs to its corresponding ambient trigonometric subspace. -/
theorem fourierTruncation_mem_realTrigonometricSubmodule
    (u : PeriodicVectorW12 d) (S : Finset (d → ℤ)) :
    fourierTruncation u S ∈ realTrigonometricSubmodule S := by
  let a : d → S → ℂ := fun j k ↦
    _root_.UnitAddTorus.mFourierCoeff
      (fun x ↦ (PeriodicW12.value (component u j) x : ℂ)) k.1
  refine ⟨a, ?_⟩
  apply ext_component
  intro j
  rw [component_fourierTruncation]
  change (ofComponents (fun j ↦
    ∑ k : S, PeriodicW12.realMFourierAtom (a j k) k.1)).component j = _
  rw [component_ofComponents]
  rw [PeriodicW12.fourierTruncation_eq_sum]
  simp only [PeriodicW12.fourierTerm_eq_realMFourierAtom, a]
  exact Finset.sum_coe_sort S (fun k : d → ℤ ↦
    PeriodicW12.realMFourierAtom
      (_root_.UnitAddTorus.mFourierCoeff
        (fun x ↦ (PeriodicW12.value (component u j) x : ℂ)) k) k)

/-- One Fourier term of a weakly divergence-free field is weakly divergence-free. -/
theorem fourierTerm_mem_periodicDivergenceFreeW12Submodule
    (u : PeriodicVectorW12 d)
    (hu : u ∈ periodicDivergenceFreeW12Submodule d) (k : d → ℤ) :
    fourierTerm u k ∈ periodicDivergenceFreeW12Submodule d := by
  rw [mem_periodicDivergenceFreeW12Submodule_iff]
  exact weakDivergence_fourierTerm_eq_zero u hu k

/-- Every finite Fourier truncation preserves weak incompressibility. -/
theorem fourierTruncation_mem_periodicDivergenceFreeW12Submodule
    (u : PeriodicVectorW12 d)
    (hu : u ∈ periodicDivergenceFreeW12Submodule d) (S : Finset (d → ℤ)) :
    fourierTruncation u S ∈ periodicDivergenceFreeW12Submodule d := by
  rw [fourierTruncation_eq_sum]
  exact Submodule.sum_mem _ fun k hk ↦
    fourierTerm_mem_periodicDivergenceFreeW12Submodule u hu k

end PeriodicVectorW12

namespace PeriodicMeanZeroDivergenceFreeW12

/-- One Fourier term, bundled in the mean-zero incompressible energy space. -/
def fourierTerm (u : PeriodicMeanZeroDivergenceFreeW12 d) (k : d → ℤ) :
    PeriodicMeanZeroDivergenceFreeW12 d :=
  ⟨PeriodicVectorW12.fourierTerm (u : PeriodicVectorW12 d) k, by
    apply (mem_periodicMeanZeroDivergenceFreeW12Submodule_iff_mean_weakDivergence _).mpr
    exact ⟨PeriodicVectorW12.mean_fourierTerm_eq_zero _ (mean_eq_zero u) k,
      PeriodicVectorW12.weakDivergence_fourierTerm_eq_zero
        (u : PeriodicVectorW12 d)
        ((mem_periodicDivergenceFreeW12Submodule_iff _).mpr
          ((mem_periodicMeanZeroDivergenceFreeW12Submodule_iff_mean_weakDivergence _).mp
            u.2).2) k⟩⟩

@[simp]
theorem coe_fourierTerm (u : PeriodicMeanZeroDivergenceFreeW12 d) (k : d → ℤ) :
    (fourierTerm u k : PeriodicVectorW12 d) =
      PeriodicVectorW12.fourierTerm (u : PeriodicVectorW12 d) k := by
  rfl

/-- Finite Fourier truncation in the mean-zero incompressible energy space. -/
def fourierTruncation (u : PeriodicMeanZeroDivergenceFreeW12 d)
    (S : Finset (d → ℤ)) : PeriodicMeanZeroDivergenceFreeW12 d :=
  ∑ k ∈ S, fourierTerm u k

@[simp]
theorem coe_fourierTruncation (u : PeriodicMeanZeroDivergenceFreeW12 d)
    (S : Finset (d → ℤ)) :
    (fourierTruncation u S : PeriodicVectorW12 d) =
      PeriodicVectorW12.fourierTruncation (u : PeriodicVectorW12 d) S := by
  rw [← toPeriodicVectorW12_eq_coe, ← toPeriodicVectorW12L_apply]
  rw [fourierTruncation, map_sum, PeriodicVectorW12.fourierTruncation_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [toPeriodicVectorW12L_apply, toPeriodicVectorW12_eq_coe, coe_fourierTerm]

/-- Energy-space Fourier terms sum unconditionally in the full graph norm. -/
theorem hasSum_fourierTerm (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    HasSum (fourierTerm u) u := by
  change Tendsto (fourierTruncation u) atTop (nhds u)
  apply tendsto_subtype_rng.mpr
  simpa only [coe_fourierTruncation] using
    PeriodicVectorW12.tendsto_fourierTruncation (u : PeriodicVectorW12 d)

/-- The finite energy-space Fourier truncations converge in the full graph norm. -/
theorem tendsto_fourierTruncation (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    Tendsto (fourierTruncation u) atTop (nhds u) :=
  hasSum_fourierTerm u

end PeriodicMeanZeroDivergenceFreeW12

/-- The finite-frequency Galerkin subspace of the mean-zero incompressible energy space. -/
def periodicGalerkinSubmodule (S : Finset (d → ℤ)) :
    Submodule ℝ (PeriodicMeanZeroDivergenceFreeW12 d) :=
  (PeriodicVectorW12.realTrigonometricSubmodule S).comap
    (periodicMeanZeroDivergenceFreeW12Submodule d).toSubmodule.subtype

theorem mem_periodicGalerkinSubmodule_iff
    (u : PeriodicMeanZeroDivergenceFreeW12 d) (S : Finset (d → ℤ)) :
    u ∈ periodicGalerkinSubmodule S ↔
      (u : PeriodicVectorW12 d) ∈ PeriodicVectorW12.realTrigonometricSubmodule S := by
  rfl

/-- The finite-frequency Galerkin subspaces are monotone in their frequency sets. -/
theorem periodicGalerkinSubmodule_mono {S T : Finset (d → ℤ)} (hST : S ⊆ T) :
    periodicGalerkinSubmodule S ≤ periodicGalerkinSubmodule T := by
  intro u hu
  rw [mem_periodicGalerkinSubmodule_iff] at hu ⊢
  exact PeriodicVectorW12.realTrigonometricSubmodule_mono hST hu

private def periodicGalerkinToRealTrigonometricSubmodule
    (S : Finset (d → ℤ)) :
    periodicGalerkinSubmodule S →ₗ[ℝ]
      PeriodicVectorW12.realTrigonometricSubmodule S where
  toFun u := ⟨((u : PeriodicMeanZeroDivergenceFreeW12 d) : PeriodicVectorW12 d), u.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem periodicGalerkinToRealTrigonometricSubmodule_injective
    (S : Finset (d → ℤ)) :
    Function.Injective (periodicGalerkinToRealTrigonometricSubmodule S) := by
  intro u v huv
  rcases u with ⟨⟨u, huE⟩, huG⟩
  rcases v with ⟨⟨v, hvE⟩, hvG⟩
  change (⟨u, _⟩ : PeriodicVectorW12.realTrigonometricSubmodule S) = ⟨v, _⟩ at huv
  have huv' : u = v := congrArg Subtype.val huv
  subst v
  rfl

noncomputable instance finiteDimensional_periodicGalerkinSubmodule
    (S : Finset (d → ℤ)) :
    FiniteDimensional ℝ (periodicGalerkinSubmodule S) :=
  FiniteDimensional.of_injective
    (periodicGalerkinToRealTrigonometricSubmodule S)
    (periodicGalerkinToRealTrigonometricSubmodule_injective S)

/-- A finite-frequency truncation belongs to its corresponding Galerkin subspace. -/
theorem PeriodicMeanZeroDivergenceFreeW12.fourierTruncation_mem_periodicGalerkinSubmodule
    (u : PeriodicMeanZeroDivergenceFreeW12 d) (S : Finset (d → ℤ)) :
    fourierTruncation u S ∈ periodicGalerkinSubmodule S := by
  rw [mem_periodicGalerkinSubmodule_iff, coe_fourierTruncation]
  exact PeriodicVectorW12.fourierTruncation_mem_realTrigonometricSubmodule
    (u : PeriodicVectorW12 d) S

/-- The finite-frequency Galerkin subspace, bundled as a closed subspace. -/
def periodicGalerkinClosedSubmodule (S : Finset (d → ℤ)) :
    ClosedSubmodule ℝ (PeriodicMeanZeroDivergenceFreeW12 d) where
  toSubmodule := periodicGalerkinSubmodule S
  isClosed' := Submodule.closed_of_finiteDimensional _

/-- Forgetting closedness recovers the algebraic finite-frequency Galerkin subspace. -/
@[simp]
theorem periodicGalerkinClosedSubmodule_toSubmodule (S : Finset (d → ℤ)) :
    (periodicGalerkinClosedSubmodule S).toSubmodule = periodicGalerkinSubmodule S := by
  rfl

/-- The orthogonal projection onto a finite-frequency Galerkin subspace, using the energy-space
graph inner product. -/
def periodicGalerkinProjectionL (S : Finset (d → ℤ)) :
    PeriodicMeanZeroDivergenceFreeW12 d →L[ℝ]
      PeriodicMeanZeroDivergenceFreeW12 d :=
  Submodule.starProjection (𝕜 := ℝ)
    (E := PeriodicMeanZeroDivergenceFreeW12 d)
    (periodicGalerkinClosedSubmodule S).toSubmodule

/-- Every Galerkin projection lies in its finite-frequency subspace. -/
theorem periodicGalerkinProjectionL_mem
    (S : Finset (d → ℤ)) (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicGalerkinProjectionL S u ∈ periodicGalerkinSubmodule S := by
  exact Submodule.starProjection_apply_mem
    (periodicGalerkinClosedSubmodule S).toSubmodule u

/-- A Galerkin projection fixes exactly its Galerkin subspace. -/
theorem periodicGalerkinProjectionL_eq_self_iff
    (S : Finset (d → ℤ)) (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicGalerkinProjectionL S u = u ↔ u ∈ periodicGalerkinSubmodule S := by
  exact Submodule.starProjection_eq_self_iff

/-- The range of the Galerkin projector is exactly the finite-frequency Galerkin subspace. -/
theorem range_periodicGalerkinProjectionL (S : Finset (d → ℤ)) :
    (periodicGalerkinProjectionL S).range = periodicGalerkinSubmodule S := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact periodicGalerkinProjectionL_mem S u
  · intro u hu
    exact ⟨u, (periodicGalerkinProjectionL_eq_self_iff S u).mpr hu⟩

/-- The range of each Galerkin projector is finite-dimensional. -/
theorem finiteDimensional_range_periodicGalerkinProjectionL (S : Finset (d → ℤ)) :
    FiniteDimensional ℝ (periodicGalerkinProjectionL S).range := by
  rw [range_periodicGalerkinProjectionL]
  infer_instance

/-- Finite-frequency orthogonal Galerkin projection is idempotent. -/
@[simp]
theorem periodicGalerkinProjectionL_idem
    (S : Finset (d → ℤ)) (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicGalerkinProjectionL S (periodicGalerkinProjectionL S u) =
      periodicGalerkinProjectionL S u :=
  (periodicGalerkinProjectionL_eq_self_iff S _).mpr (periodicGalerkinProjectionL_mem S u)

/-- Projecting first onto a larger frequency space and then onto a contained one is the same as
projecting directly onto the smaller space. -/
theorem periodicGalerkinProjectionL_subset_apply_superset {S T : Finset (d → ℤ)}
    (hST : S ⊆ T) (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicGalerkinProjectionL S (periodicGalerkinProjectionL T u) =
      periodicGalerkinProjectionL S u := by
  let nag : NormedAddCommGroup (PeriodicMeanZeroDivergenceFreeW12 d) := inferInstance
  let ips : InnerProductSpace ℝ (PeriodicMeanZeroDivergenceFreeW12 d) := inferInstance
  let U : @Submodule ℝ (PeriodicMeanZeroDivergenceFreeW12 d) Real.semiring
      nag.toAddCommGroup.toAddCommMonoid ips.toNormedSpace.toModule :=
    (periodicGalerkinClosedSubmodule S).toSubmodule
  let V : @Submodule ℝ (PeriodicMeanZeroDivergenceFreeW12 d) Real.semiring
      nag.toAddCommGroup.toAddCommMonoid ips.toNormedSpace.toModule :=
    (periodicGalerkinClosedSubmodule T).toSubmodule
  have hUV : U ≤ V := periodicGalerkinSubmodule_mono hST
  have hcomp := @Submodule.starProjection_comp_starProjection_of_le ℝ
    (PeriodicMeanZeroDivergenceFreeW12 d) _ nag ips U V inferInstance inferInstance hUV
  have happ := DFunLike.congr_fun hcomp u
  simpa only [ContinuousLinearMap.comp_apply, periodicGalerkinProjectionL, U, V] using happ

/-- Projecting a smaller-frequency field onto any containing Galerkin space fixes it. -/
theorem periodicGalerkinProjectionL_superset_apply_subset {S T : Finset (d → ℤ)}
    (hST : S ⊆ T) (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicGalerkinProjectionL T (periodicGalerkinProjectionL S u) =
      periodicGalerkinProjectionL S u := by
  apply (periodicGalerkinProjectionL_eq_self_iff T _).mpr
  exact periodicGalerkinSubmodule_mono hST (periodicGalerkinProjectionL_mem S u)

/-- Nested Galerkin projections absorb in the order smaller-after-larger. -/
theorem periodicGalerkinProjectionL_comp_of_subset {S T : Finset (d → ℤ)}
    (hST : S ⊆ T) :
    (periodicGalerkinProjectionL S).comp (periodicGalerkinProjectionL T) =
      periodicGalerkinProjectionL S := by
  apply ContinuousLinearMap.ext
  intro u
  exact periodicGalerkinProjectionL_subset_apply_superset hST u

/-- Nested Galerkin projections also absorb in the order larger-after-smaller. -/
theorem periodicGalerkinProjectionL_comp_rev_of_subset {S T : Finset (d → ℤ)}
    (hST : S ⊆ T) :
    (periodicGalerkinProjectionL T).comp (periodicGalerkinProjectionL S) =
      periodicGalerkinProjectionL S := by
  apply ContinuousLinearMap.ext
  intro u
  exact periodicGalerkinProjectionL_superset_apply_subset hST u

/-- Orthogonal Galerkin projection is `1`-Lipschitz in the energy graph metric. -/
theorem periodicGalerkinProjectionL_lipschitzWith
    (S : Finset (d → ℤ)) :
    LipschitzWith 1 (periodicGalerkinProjectionL S) :=
  by
    let nag : NormedAddCommGroup (PeriodicMeanZeroDivergenceFreeW12 d) := inferInstance
    let ips : InnerProductSpace ℝ (PeriodicMeanZeroDivergenceFreeW12 d) := inferInstance
    let K : @Submodule ℝ (PeriodicMeanZeroDivergenceFreeW12 d) Real.semiring
        nag.toAddCommGroup.toAddCommMonoid ips.toNormedSpace.toModule :=
      (periodicGalerkinClosedSubmodule S).toSubmodule
    have h : LipschitzWith 1 K.starProjection :=
      @Submodule.lipschitzWith_starProjection ℝ
        (PeriodicMeanZeroDivergenceFreeW12 d) _ nag ips K inferInstance
    simpa only [periodicGalerkinProjectionL, K] using h

/-- Orthogonal Galerkin projection is symmetric in the energy-space inner product. -/
theorem inner_periodicGalerkinProjectionL_left_eq_right
    (S : Finset (d → ℤ)) (u v : PeriodicMeanZeroDivergenceFreeW12 d) :
    inner ℝ (periodicGalerkinProjectionL S u) v =
      inner ℝ u (periodicGalerkinProjectionL S v) := by
  let nag : NormedAddCommGroup (PeriodicMeanZeroDivergenceFreeW12 d) := inferInstance
  let ips : InnerProductSpace ℝ (PeriodicMeanZeroDivergenceFreeW12 d) := inferInstance
  let K : @Submodule ℝ (PeriodicMeanZeroDivergenceFreeW12 d) Real.semiring
      nag.toAddCommGroup.toAddCommMonoid ips.toNormedSpace.toModule :=
    (periodicGalerkinClosedSubmodule S).toSubmodule
  have h := @Submodule.inner_starProjection_left_eq_right ℝ
    (PeriodicMeanZeroDivergenceFreeW12 d) _ nag ips K inferInstance u v
  simpa only [periodicGalerkinProjectionL, K] using h

/-- The residual of an orthogonal Galerkin projection is orthogonal to every vector in the
finite-frequency Galerkin subspace. -/
theorem inner_sub_periodicGalerkinProjectionL_eq_zero
    (S : Finset (d → ℤ)) (u v : PeriodicMeanZeroDivergenceFreeW12 d)
    (hv : v ∈ periodicGalerkinSubmodule S) :
    inner ℝ (u - periodicGalerkinProjectionL S u) v = 0 := by
  let nag : NormedAddCommGroup (PeriodicMeanZeroDivergenceFreeW12 d) := inferInstance
  let ips : InnerProductSpace ℝ (PeriodicMeanZeroDivergenceFreeW12 d) := inferInstance
  let K : @Submodule ℝ (PeriodicMeanZeroDivergenceFreeW12 d) Real.semiring
      nag.toAddCommGroup.toAddCommMonoid ips.toNormedSpace.toModule :=
    (periodicGalerkinClosedSubmodule S).toSubmodule
  have h := @Submodule.starProjection_inner_eq_zero ℝ
    (PeriodicMeanZeroDivergenceFreeW12 d) _ nag ips K inferInstance u v (by exact hv)
  simpa only [periodicGalerkinProjectionL, K] using h

/-- Orthogonal Galerkin projection is norm-contracting in the energy graph norm. -/
theorem norm_periodicGalerkinProjectionL_le
    (S : Finset (d → ℤ)) (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    ‖periodicGalerkinProjectionL S u‖ ≤ ‖u‖ := by
  let nag : NormedAddCommGroup (PeriodicMeanZeroDivergenceFreeW12 d) := inferInstance
  let ips : InnerProductSpace ℝ (PeriodicMeanZeroDivergenceFreeW12 d) := inferInstance
  let K : @Submodule ℝ (PeriodicMeanZeroDivergenceFreeW12 d) Real.semiring
      nag.toAddCommGroup.toAddCommMonoid ips.toNormedSpace.toModule :=
    (periodicGalerkinClosedSubmodule S).toSubmodule
  have h := @Submodule.norm_starProjection_apply_le ℝ
    (PeriodicMeanZeroDivergenceFreeW12 d) _ nag ips K inferInstance u
  simpa only [periodicGalerkinProjectionL, K] using h

/-- The Galerkin projector fixes the explicit constraint-preserving Fourier truncation. -/
@[simp]
theorem periodicGalerkinProjectionL_fourierTruncation
    (S : Finset (d → ℤ)) (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    periodicGalerkinProjectionL S (PeriodicMeanZeroDivergenceFreeW12.fourierTruncation u S) =
      PeriodicMeanZeroDivergenceFreeW12.fourierTruncation u S :=
  (periodicGalerkinProjectionL_eq_self_iff S _).mpr
    (PeriodicMeanZeroDivergenceFreeW12.fourierTruncation_mem_periodicGalerkinSubmodule u S)

/-- The orthogonal projection error is controlled by twice the error of the explicit Fourier
truncation in the same finite-frequency space. -/
theorem dist_periodicGalerkinProjectionL_le_two_mul_dist_fourierTruncation
    (S : Finset (d → ℤ)) (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    dist (periodicGalerkinProjectionL S u) u ≤
      2 * dist (PeriodicMeanZeroDivergenceFreeW12.fourierTruncation u S) u := by
  let q := PeriodicMeanZeroDivergenceFreeW12.fourierTruncation u S
  calc
    dist (periodicGalerkinProjectionL S u) u ≤
        dist (periodicGalerkinProjectionL S u) q + dist q u :=
      dist_triangle _ _ _
    _ = dist (periodicGalerkinProjectionL S u) (periodicGalerkinProjectionL S q) +
        dist q u := by rw [periodicGalerkinProjectionL_fourierTruncation]
    _ ≤ 1 * dist u q + dist q u := by
      gcongr
      exact (periodicGalerkinProjectionL_lipschitzWith S).dist_le_mul u q
    _ = 2 * dist q u := by rw [one_mul, dist_comm u q]; ring

/-- Finite-frequency orthogonal Galerkin projections converge strongly to the identity in the
full energy graph norm. -/
theorem tendsto_periodicGalerkinProjectionL
    (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    Tendsto (fun S : Finset (d → ℤ) ↦ periodicGalerkinProjectionL S u) atTop (nhds u) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun S ↦
    dist_periodicGalerkinProjectionL_le_two_mul_dist_fourierTruncation S u) ?_
  have hdist := tendsto_iff_dist_tendsto_zero.mp
    (PeriodicMeanZeroDivergenceFreeW12.tendsto_fourierTruncation u)
  simpa only [mul_zero] using tendsto_const_nhds.mul hdist

/-- An energy field with finite Galerkin support. -/
def IsFiniteGalerkinField (u : PeriodicMeanZeroDivergenceFreeW12 d) : Prop :=
  ∃ S : Finset (d → ℤ), u ∈ periodicGalerkinSubmodule S

/-- Finite-frequency mean-zero incompressible fields are dense in the full energy graph norm. -/
theorem dense_isFiniteGalerkinField :
    Dense {u : PeriodicMeanZeroDivergenceFreeW12 d | IsFiniteGalerkinField u} := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro u
  exact mem_closure_of_tendsto
    (PeriodicMeanZeroDivergenceFreeW12.tendsto_fourierTruncation u)
    (Filter.Eventually.of_forall fun S ↦
      ⟨S, PeriodicMeanZeroDivergenceFreeW12.fourierTruncation_mem_periodicGalerkinSubmodule
        u S⟩)

/-- Explicit graph-metric approximation by a field in one finite-dimensional Galerkin space. -/
theorem exists_periodicGalerkinSubmodule_dist_lt
    (u : PeriodicMeanZeroDivergenceFreeW12 d) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset (d → ℤ)) (v : PeriodicMeanZeroDivergenceFreeW12 d),
      v ∈ periodicGalerkinSubmodule S ∧ dist u v < ε := by
  obtain ⟨v, ⟨S, hvS⟩, hv⟩ :=
    (dense_isFiniteGalerkinField (d := d)).exists_dist_lt u hε
  exact ⟨S, v, hvS, hv⟩

end UnitAddTorus
