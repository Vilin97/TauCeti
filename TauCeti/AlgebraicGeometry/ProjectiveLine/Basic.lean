/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The projective line and its generic points

This file realizes the projective line over a field `K` as the projective spectrum of the
standard grading on `K[X₀, X₁]`. A field extension map `K → F` and an element `g : F` determine
the `F`-valued point `[g : 1]`.

For an integral curve with function field `F`, this is the generic-point morphism attached to a
rational function. It is the first geometric input to the product formula in
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

/-- The standard grading of the homogeneous coordinate ring `K[X₀, X₁]`. -/
abbrev homogeneousPieces (K : Type u) [Field K] :=
  MvPolynomial.homogeneousSubmodule (Fin 2) K

/-- The standard graded-algebra structure on the homogeneous coordinate ring of the projective
line. Mathlib intentionally does not install this instance globally because multivariate
polynomials admit other weighted gradings. -/
noncomputable instance (K : Type u) [Field K] : GradedAlgebra (homogeneousPieces K) :=
  MvPolynomial.gradedAlgebra

/-- The projective line over `K`, realized as `Proj K[X₀, X₁]`. -/
abbrev scheme (K : Type u) [Field K] : Scheme.{u} :=
  Proj (homogeneousPieces K)

/-- The constant-polynomial equivalence from `K` to the degree-zero part of `K[X₀, X₁]`. -/
@[expose]
noncomputable def degreeZeroRingEquiv (K : Type u) [Field K] :
    K ≃+* homogeneousPieces K 0 :=
  RingEquiv.ofBijective (algebraMap K (homogeneousPieces K 0)) <| by
    constructor
    · intro r s hrs
      exact MvPolynomial.C_injective (Fin 2) K (congrArg Subtype.val hrs)
    · intro p
      have hp : (p : MvPolynomial (Fin 2) K) ∈
          (1 : Submodule K (MvPolynomial (Fin 2) K)) := by
        simpa [homogeneousPieces, MvPolynomial.homogeneousSubmodule_zero] using p.property
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
      refine ⟨r, Subtype.ext ?_⟩
      exact hr

@[simp]
lemma coe_degreeZeroRingEquiv_apply (K : Type u) [Field K] (r : K) :
    ((degreeZeroRingEquiv K r : homogeneousPieces K 0) : MvPolynomial (Fin 2) K) =
      MvPolynomial.C r := rfl

private def coordinateRingHom (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    MvPolynomial (Fin 2) K →+* Γ(Spec (.of F), ⊤) :=
  MvPolynomial.eval₂Hom
    ((Scheme.ΓSpecIso (.of F)).inv.hom.comp ι)
    (fun i ↦ (Scheme.ΓSpecIso (.of F)).inv (if i = 0 then g else 1))

private lemma coordinateRingHom_X_one (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    coordinateRingHom K F ι g (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [coordinateRingHom]

private lemma X_mem_irrelevant (K : Type u) [Field K] (i : Fin 2) :
    MvPolynomial.X i ∈ HomogeneousIdeal.irrelevant (homogeneousPieces K) := by
  rw [HomogeneousIdeal.mem_irrelevant_iff]
  change ((MvPolynomial.decomposition.decompose' (MvPolynomial.X i) 0 :
    MvPolynomial.homogeneousSubmodule (Fin 2) K 0) :
      MvPolynomial (Fin 2) K) = 0
  rw [MvPolynomial.decomposition.decompose'_apply]
  rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_X K i)]
  simp

private lemma map_irrelevant_eq_top (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    Ideal.map (coordinateRingHom K F ι g)
      (HomogeneousIdeal.irrelevant (homogeneousPieces K)).toIdeal = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  rw [← coordinateRingHom_X_one K F ι g]
  exact Ideal.mem_map_of_mem (coordinateRingHom K F ι g) (X_mem_irrelevant K 1)

/-- The `F`-valued point `[g : 1]` of the projective line associated to a field map `K → F`
and an element `g : F`.

For a curve function field, this is the generic-point morphism defined by the corresponding
rational function. The explicit field map makes the base-field structure part of the data and
avoids choosing a global `Algebra K F` instance. -/
noncomputable def ofElement (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : Spec (.of F) ⟶ scheme K :=
  Proj.fromOfGlobalSections (homogeneousPieces K) (coordinateRingHom K F ι g)
    (map_irrelevant_eq_top K F ι g)

/-- Before identifying the degree-zero homogeneous coordinate ring with `K`, the point `[g : 1]`
lies over the field map from that degree-zero ring to `F`. -/
lemma ofElement_toSpecZero (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofElement K F ι g ≫ Proj.toSpecZero (homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        (ι.comp (degreeZeroRingEquiv K).symm.toRingHom)) := by
  rw [ofElement, Proj.fromOfGlobalSections_toSpecZero]
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, Category.assoc, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  change (Scheme.ΓSpecIso (.of F)).hom
    (coordinateRingHom K F ι g
      (((degreeZeroRingEquiv K r : homogeneousPieces K 0) :
        MvPolynomial (Fin 2) K))) = ι r
  rw [coe_degreeZeroRingEquiv_apply]
  dsimp [coordinateRingHom, degreeZeroRingEquiv]
  simp

end

end ProjectiveLine

end AlgebraicGeometry

end TauCeti
