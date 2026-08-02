/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveLine.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.FiniteType

/-!
# The structure morphism of the projective line

This file equips `ProjectiveLine.scheme K` with its structure morphism to `Spec K`. It identifies
the degree-zero part of `K[X₀, X₁]` with `K`, verifies finite generation over that degree-zero
part, and records that the structure morphism is locally of finite type and proper.

These are prerequisites for spreading a function-field point out to a rational map and then
extending it on a proper regular curve, as required by the product formula in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve".
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace ProjectiveLine

noncomputable section

/-- The homogeneous coordinate ring of the projective line is finitely generated over its
degree-zero part. -/
noncomputable instance (K : Type u) [Field K] :
    Algebra.FiniteType (homogeneousPieces K 0) (MvPolynomial (Fin 2) K) := by
  letI : IsScalarTower K (homogeneousPieces K 0) (MvPolynomial (Fin 2) K) :=
    IsScalarTower.of_algebraMap_eq
      (R := K) (S := homogeneousPieces K 0) (A := MvPolynomial (Fin 2) K)
      (fun r ↦ by rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    K (homogeneousPieces K 0) (MvPolynomial (Fin 2) K)

/-- The structure morphism `ℙ¹_K ⟶ Spec K`. -/
noncomputable def structureMap (K : Type u) [Field K] : scheme K ⟶ Spec (.of K) :=
  Proj.toSpecZero (homogeneousPieces K) ≫
    Spec.map (degreeZeroRingEquiv K).toCommRingCatIso.hom

/-- The point `[g : 1]` lies over the base-field map `K → F`. -/
@[reassoc]
lemma ofElement_comp_structureMap (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofElement K F ι g ≫ structureMap K =
      Spec.map (CommRingCat.ofHom ι) := by
  rw [structureMap, ← Category.assoc, ofElement_toSpecZero]
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp

noncomputable instance (K : Type u) [Field K] :
    LocallyOfFiniteType (structureMap K) := by
  dsimp only [structureMap]
  infer_instance

noncomputable instance (K : Type u) [Field K] : IsProper (structureMap K) := by
  dsimp only [structureMap]
  infer_instance

/-- The structure morphism of the projective line satisfies the valuative criterion. -/
lemma structureMap_valuativeCriterion (K : Type u) [Field K] :
    ValuativeCriterion (structureMap K) := by
  have h : IsProper (structureMap K) := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1

end

end ProjectiveLine

end AlgebraicGeometry

end TauCeti
