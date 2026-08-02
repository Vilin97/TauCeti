/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Local rings of standard-smooth relative curves

A standard-smooth algebra of relative dimension one is étale over a one-variable polynomial
ring. After localizing at a prime, formal unramifiedness identifies the target maximal ideal with
the image of the source maximal ideal. The source is a localization of a principal ideal domain,
so the target maximal ideal is principal. The Noetherian-local-domain characterization of
valuation rings then applies.

This gives the local commutative-algebra input needed to extend rational functions on a smooth
curve to projective-line-valued morphisms.
-/

public section

namespace TauCeti

namespace RingTheory

noncomputable section

universe u v w

/-- A local ring of a standard-smooth relative curve over a field is a valuation ring. -/
theorem valuationRing_localizationAtPrime_of_isStandardSmoothOfRelativeDimension_one
    (K : Type u) (A : Type v) [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A]
    (q : Ideal A) [q.IsPrime] : ValuationRing (Localization.AtPrime q) := by
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 K A
  let P := MvPolynomial (Fin 1) K
  letI : IsPrincipalIdealRing P := IsPrincipalIdealRing.of_surjective
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm.toRingHom
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm.surjective
  letI : Algebra P A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale P A := by
    rw [← RingHom.etale_algebraMap]
    exact hg
  let p : Ideal P := q.under P
  letI : p.IsPrime := Ideal.IsPrime.comap g.toRingHom
  have hpq : q.LiesOver p := by
    rw [Ideal.liesOver_iff]
  letI : q.LiesOver p := hpq
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  letI : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  haveI : Algebra.IsUnramifiedAt P q := inferInstance
  haveI : Algebra.FormallyUnramified
      (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
  haveI : Algebra.EssFiniteType
      (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp P _ _
  have hm : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).IsPrincipal := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p]
    exact (IsPrincipalIdealRing.principal p).map_ringHom _
  have hq : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).IsPrincipal := by
    rw [← hm]
    exact hp.map_ringHom _
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (Localization.AtPrime q)).out 4 1).mp hq

/-- Any chosen localization at a prime of a standard-smooth relative curve over a field is a
valuation ring. This form applies directly to scheme stalks. -/
theorem valuationRing_of_isLocalizationAtPrime_of_isStandardSmoothOfRelativeDimension_one
    (K : Type u) (A : Type v) (Aq : Type w)
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A]
    [CommRing Aq] [IsDomain Aq] [Algebra A Aq]
    (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime Aq q] : ValuationRing Aq := by
  letI : ValuationRing (Localization.AtPrime q) :=
    valuationRing_localizationAtPrime_of_isStandardSmoothOfRelativeDimension_one K A q
  let e : Localization.AtPrime q ≃ₐ[A] Aq :=
    IsLocalization.algEquiv q.primeCompl _ _
  exact Function.Surjective.valuationRing e.toRingEquiv.toRingHom e.surjective

end

end RingTheory

end TauCeti
