/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness of the rational-function morphism

A non-global rational function on an integral proper smooth relative curve gives a dominant
morphism to the projective line. Its maps on stalks are injective: dominance over the reduced
target makes the morphism scheme-theoretically dominant, while integrality of the source makes
germs injective. The target stalk is either the function field or a discrete valuation ring, so
the source stalk is a torsion-free, hence flat, module over it.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

private theorem stalkMap_injective_of_isDominant_of_isIntegral
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : X ⟶ Y) [IsDominant φ] [QuasiCompact φ] (x : X) :
    Function.Injective (φ.stalkMap x) := by
  letI : IsSchemeTheoreticallyDominant φ :=
    IsSchemeTheoreticallyDominant.of_isDominant φ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (φ x)) isOpen_univ
  apply hU.stalkMap_injective φ x hxU
  intro g hg
  rw [Scheme.Hom.germ_stalkMap_apply] at hg
  letI : Nonempty (φ ⁻¹ᵁ U) := ⟨⟨x, hxU⟩⟩
  have happ : φ.app U g = 0 := by
    apply germ_injective_of_isIntegral X x hxU
    simpa using hg
  have hgzero : g = 0 := φ.app_injective U (by simpa using happ)
  rw [hgzero, map_zero]

/-- The projective-line morphism associated to a non-global rational function is flat. -/
theorem flat_rationalFunctionMorphism_of_nonGlobal
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ a : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ a) :
    Flat (rationalFunctionMorphism K X f g) := by
  let φ := rationalFunctionMorphism K X f g
  letI : IsDominant φ :=
    isDominant_rationalFunctionMorphism_of_nonGlobal K X f g hg
  letI : IsProper φ := isProper_rationalFunctionMorphism K X f g
  change Flat φ
  apply Flat.of_stalkMap
  intro x
  have hinj : Function.Injective (φ.stalkMap x) :=
    stalkMap_injective_of_isDominant_of_isIntegral φ x
  let R := (ProjectiveLine.scheme K).presheaf.stalk (φ x)
  letI : ValuationRing R :=
    valuationRing_stalk_of_smoothRelativeDimension_one
      K (ProjectiveLine.scheme K) (ProjectiveLine.structureMap K) (φ x)
  letI : IsNoetherianRing R := inferInstance
  letI : IsLocalRing R := inferInstance
  letI : IsDomain R := inferInstance
  letI : IsDedekindDomain R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 1 2).mp
      (show ValuationRing R from inferInstance)
  algebraize [(φ.stalkMap x).hom]
  letI : Module.IsTorsionFree R (X.presheaf.stalk x) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, RingHom.algebraMap_toAlgebra]
    exact hinj
  change Module.Flat R (X.presheaf.stalk x)
  infer_instance

/-- The finite-flat degree of the projective-line morphism attached to a non-global rational
function is independent of the point of the projective line. -/
theorem finrank_rationalFunctionMorphism_eq_of_nonGlobal
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ a : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ a)
    (y z : ProjectiveLine.scheme K) :
    (rationalFunctionMorphism K X f g).finrank y =
      (rationalFunctionMorphism K X f g).finrank z := by
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ :=
    isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg
  letI : Flat φ :=
    flat_rationalFunctionMorphism_of_nonGlobal K X f g hg
  change φ.finrank y = φ.finrank z
  exact φ.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y z

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
