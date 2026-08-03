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

/-- The standard affine chart `D₊(X₁)` of the projective line. -/
abbrev standardAffineOpen (K : Type u) [Field K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))

private lemma X_one_mem_degree_one (K : Type u) [Field K] :
    MvPolynomial.X (1 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (1 : Fin 2)

private lemma X_zero_mem_degree_one (K : Type u) [Field K] :
    MvPolynomial.X (0 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (0 : Fin 2)

private lemma zero_lt_one : 0 < (1 : ℕ) := Nat.zero_lt_succ 0

/-- The degree-zero homogeneous fraction `X₀ / X₁` on the standard affine chart. -/
private noncomputable def affineCoordinateAway (K : Type u) [Field K] :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_one_mem_degree_one K) 1
    (MvPolynomial.X (0 : Fin 2)) (by simpa using X_zero_mem_degree_one K)

/-- The regular function `X₀ / X₁` on the standard affine chart `D₊(X₁)`. -/
noncomputable def affineCoordinate (K : Type u) [Field K] :
  Γ(scheme K, standardAffineOpen K) :=
  (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one).hom (affineCoordinateAway K)

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

private def coordinatePolynomialHom (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : MvPolynomial (Fin 2) K →+* F :=
  MvPolynomial.eval₂Hom ι fun i ↦ if i = 0 then g else 1

private lemma coordinatePolynomialHom_X_zero (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    coordinatePolynomialHom K F ι g (MvPolynomial.X (0 : Fin 2)) = g := by
  simp [coordinatePolynomialHom]

private lemma coordinatePolynomialHom_X_one (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    coordinatePolynomialHom K F ι g (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [coordinatePolynomialHom]

/-- The affine-chart coordinate homomorphism sending `X₀ / X₁` to `g`. -/
private noncomputable def affineCoordinateRingHom
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) →+* F :=
  (Localization.awayLift (coordinatePolynomialHom K F ι g)
      (MvPolynomial.X (1 : Fin 2)) (by
        rw [coordinatePolynomialHom_X_one]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))
      (Localization.Away (MvPolynomial.X (1 : Fin 2))))

private lemma affineCoordinateRingHom_affineCoordinateAway
    (K F : Type u) [Field K] [Field F] (ι : K →+* F) (g : F) :
    affineCoordinateRingHom K F ι g (affineCoordinateAway K) = g := by
  simp only [affineCoordinateRingHom, RingHom.comp_apply, affineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk (coordinatePolynomialHom K F ι g)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.X (0 : Fin 2)) 1
    (by rw [coordinatePolynomialHom_X_one]; simp) 1
  simpa [coordinatePolynomialHom] using h

private lemma basicOpenIsoSpec_hom_appTop_affineCoordinateAway
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one).hom.appTop
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K)) =
      (standardAffineOpen K).topIso.inv (affineCoordinate K) := by
  rw [Proj.basicOpenIsoSpec_hom]
  change (Proj.basicOpenToSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))).app ⊤
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K)) = _
  rw [Proj.basicOpenToSpec_app_top]
  change (((Scheme.ΓSpecIso (.of <|
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).hom ≫
      Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) ≫
      (standardAffineOpen K).topIso.inv)
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K))) =
    (standardAffineOpen K).topIso.inv
      (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (affineCoordinateAway K))
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

private lemma basicOpenIsoSpec_inv_appTop_affineCoordinate
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one).inv.appTop
      ((standardAffineOpen K).topIso.inv (affineCoordinate K)) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K) := by
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one
  change e.inv.appTop ((standardAffineOpen K).topIso.inv (affineCoordinate K)) = _
  have hinj : Function.Injective e.hom.appTop := by
    intro x y hxy
    have h := congrArg (fun z ↦ e.inv.appTop z) hxy
    simpa only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply] using h
  apply hinj
  change (e.inv.appTop ≫ e.hom.appTop)
      ((standardAffineOpen K).topIso.inv (affineCoordinate K)) = _
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  exact (basicOpenIsoSpec_hom_appTop_affineCoordinateAway K).symm

private lemma awayι_preimage_standardAffineOpen (K : Type u) [Field K] :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one ⁻¹ᵁ standardAffineOpen K = ⊤ := by
  change Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) = ⊤
  rw [← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one]
  exact Scheme.Hom.preimage_opensRange _

private lemma awayι_appLE_affineCoordinate (K : Type u) [Field K] :
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one).appLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge (affineCoordinate K) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K) := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one
  have hres : φ.resLE (standardAffineOpen K) ⊤
      (awayι_preimage_standardAffineOpen K).ge =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv := by
    apply (cancel_mono (standardAffineOpen K).ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    change (⊤ : (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens).ι ≫ φ =
      ((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv) ≫
        (standardAffineOpen K).ι
    simp only [Category.assoc, Scheme.topIso_hom, e, φ,
      Proj.basicOpenIsoSpec_inv_ι]
  have happ := congrArg Scheme.Hom.appTop hres
  have heval := congrArg
    (fun h ↦ h ((standardAffineOpen K).topIso.inv (affineCoordinate K))) happ
  let V : (Spec (.of <| HomogeneousLocalization.Away
    (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens := ⊤
  apply V.topIso.symm.commRingCatIsoToRingEquiv.injective
  convert heval using 1
  · change V.topIso.inv
      ((φ.appLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge) (affineCoordinate K)) =
      (φ.resLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge).app ⊤
        ((standardAffineOpen K).topIso.inv (affineCoordinate K))
    rw [Scheme.Hom.resLE_app_top]
    change V.topIso.inv
        ((φ.appLE (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen K).ge) (affineCoordinate K)) =
      (⊤ : (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens).topIso.inv
        ((φ.appLE (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen K).ge)
            ((standardAffineOpen K).topIso.hom
              ((standardAffineOpen K).topIso.inv (affineCoordinate K))))
    rw [Iso.inv_hom_id_apply]
  · change V.topIso.inv
        ((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
            (affineCoordinateAway K)) =
        (((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv).appTop)
          ((standardAffineOpen K).topIso.inv (affineCoordinate K))
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [basicOpenIsoSpec_inv_appTop_affineCoordinate]
    dsimp [V]
    simp only [Scheme.topIso_hom, Scheme.Opens.ι_appTop]
    rfl

/-- The `F`-valued point `[g : 1]` of the projective line associated to a field map `K → F`
and an element `g : F`.

For a curve function field, this is the generic-point morphism defined by the corresponding
rational function. The explicit field map makes the base-field structure part of the data and
avoids choosing a global `Algebra K F` instance. -/
noncomputable def ofElement (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) : Spec (.of F) ⟶ scheme K :=
  Spec.map (CommRingCat.ofHom (affineCoordinateRingHom K F ι g)) ≫
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one

/-- The point `[g : 1]` lies in the standard affine chart where the second homogeneous
coordinate is nonzero. -/
@[simp]
lemma ofElement_preimage_basicOpen_X_one (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofElement K F ι g ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) = ⊤ := by
  rw [ofElement, Scheme.Hom.comp_preimage,
    ← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one]
  simp

/-- Pulling the standard affine coordinate `X₀ / X₁` back along `[g : 1]` gives `g`.

This is the computational interface needed to distinguish the rational-function morphism of a
non-global function from a constant morphism. -/
lemma ofElement_appLE_affineCoordinate (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    (ofElement K F ι g).appLE (standardAffineOpen K) ⊤
        (ofElement_preimage_basicOpen_X_one K F ι g).ge (affineCoordinate K) =
      (Scheme.ΓSpecIso (.of F)).inv g := by
  change ((Spec.map (CommRingCat.ofHom (affineCoordinateRingHom K F ι g)) ≫
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) zero_lt_one).appLE
      (standardAffineOpen K) ⊤ (ofElement_preimage_basicOpen_X_one K F ι g).ge)
        (affineCoordinate K) = _
  rw [← Scheme.Hom.appLE_comp_appLE
    (Spec.map (CommRingCat.ofHom (affineCoordinateRingHom K F ι g)))
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) zero_lt_one)
    (standardAffineOpen K) ⊤ ⊤ (awayι_preimage_standardAffineOpen K).ge le_rfl]
  simp only [CommRingCat.comp_apply, awayι_appLE_affineCoordinate]
  change (((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv ≫
        (Spec.map (CommRingCat.ofHom
          (affineCoordinateRingHom K F ι g))).appTop) (affineCoordinateAway K)) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (Scheme.ΓSpecIso (.of F)).inv
    (affineCoordinateRingHom_affineCoordinateAway K F ι g)

/-- Before identifying the degree-zero homogeneous coordinate ring with `K`, the point `[g : 1]`
lies over the field map from that degree-zero ring to `F`. -/
lemma ofElement_toSpecZero (K F : Type u) [Field K] [Field F]
    (ι : K →+* F) (g : F) :
    ofElement K F ι g ≫ Proj.toSpecZero (homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        (ι.comp (degreeZeroRingEquiv K).symm.toRingHom)) := by
  rw [ofElement, Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  change affineCoordinateRingHom K F ι g
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (1 : Fin 2))) (degreeZeroRingEquiv K r)) = ι r
  simp only [affineCoordinateRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk (coordinatePolynomialHom K F ι g)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [coordinatePolynomialHom_X_one]; simp) 0
  convert h using 1
  · congr 1
  · simp [coordinatePolynomialHom]

end

end ProjectiveLine

end AlgebraicGeometry

end TauCeti
