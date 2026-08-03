/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveLine.Smooth

/-!
# Distinguished points and sections of the projective line

This file packages the zero and infinity sections and separates their closed points from the
generic point.  It is downstream of the affine-chart, smoothness, and integrality calculations.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti.AlgebraicGeometry.ProjectiveLine

noncomputable section

universe u

/-- The zero point as a section of the projective-line structure morphism. -/
noncomputable def zeroSection (K : Type u) [Field K] :
    Spec (.of K) ⟶ scheme K :=
  ofElement K K (RingHom.id K) 0

@[simp]
lemma zeroSection_comp_structureMap (K : Type u) [Field K] :
    zeroSection K ≫ structureMap K = 𝟙 _ := by
  rw [zeroSection, ofElement_comp_structureMap]
  exact Spec.map_id (CommRingCat.of K)

/-- The section `zeroSection` sends the unique point of `Spec K` to `[0 : 1]`. -/
@[simp]
lemma zeroSection_closedPoint (K : Type u) [Field K] :
    zeroSection K (IsLocalRing.closedPoint K) = zeroPoint K := by
  let s := zeroSection K
  let z : Spec (.of K) := IsLocalRing.closedPoint K
  let U := standardAffineOpen K
  let hU := isAffineOpen_standardAffineOpen K
  have hpre : s ⁻¹ᵁ U = ⊤ :=
    ofElement_preimage_basicOpen_X_one K K (RingHom.id K) 0
  have hzU : s z ∈ U := by
    change z ∈ s ⁻¹ᵁ U
    rw [hpre]
    trivial
  apply (affineCoordinate_mem_primeIdealOf_iff_eq_zeroPoint K (s z) hzU).mp
  let htop := isAffineOpen_top (Spec (.of K))
  have hcomap := IsAffineOpen.comap_primeIdealOf_appLE U hU ⊤ htop
    (f := s) hpre.ge (x := z) trivial
  have hideal := congrArg PrimeSpectrum.asIdeal hcomap
  rw [PrimeSpectrum.comap_asIdeal] at hideal
  rw [← hideal]
  change s.appLE U ⊤ hpre.ge (affineCoordinate K) ∈
    (htop.primeIdealOf ⟨z, trivial⟩).asIdeal
  rw [show s.appLE U ⊤ hpre.ge (affineCoordinate K) = 0 by
    simpa [s, zeroSection] using
      ofElement_appLE_affineCoordinate K K (RingHom.id K) 0]
  exact Ideal.zero_mem _

/-- The point at infinity as a section of the projective-line structure morphism. -/
noncomputable def infinitySection (K : Type u) [Field K] :
    Spec (.of K) ⟶ scheme K :=
  ofInverseElement K K (RingHom.id K) 0

@[simp]
lemma infinitySection_comp_structureMap (K : Type u) [Field K] :
    infinitySection K ≫ structureMap K = 𝟙 _ := by
  rw [infinitySection, ofInverseElement_comp_structureMap]
  exact Spec.map_id (CommRingCat.of K)

/-- The section `infinitySection` sends the unique point of `Spec K` to `[1 : 0]`. -/
@[simp]
lemma infinitySection_closedPoint (K : Type u) [Field K] :
    infinitySection K (IsLocalRing.closedPoint K) = infinityPoint K := by
  let s := infinitySection K
  let z : Spec (.of K) := IsLocalRing.closedPoint K
  let U := infinityAffineOpen K
  let hU := isAffineOpen_infinityAffineOpen K
  have hpre : s ⁻¹ᵁ U = ⊤ :=
    ofInverseElement_preimage_basicOpen_X_zero K K (RingHom.id K) 0
  have hzU : s z ∈ U := by
    change z ∈ s ⁻¹ᵁ U
    rw [hpre]
    trivial
  apply (inverseAffineCoordinate_mem_primeIdealOf_iff_eq_infinityPoint
    K (s z) hzU).mp
  let htop := isAffineOpen_top (Spec (.of K))
  have hcomap := IsAffineOpen.comap_primeIdealOf_appLE U hU ⊤ htop
    (f := s) hpre.ge (x := z) trivial
  have hideal := congrArg PrimeSpectrum.asIdeal hcomap
  rw [PrimeSpectrum.comap_asIdeal] at hideal
  rw [← hideal]
  change s.appLE U ⊤ hpre.ge (inverseAffineCoordinate K) ∈
    (htop.primeIdealOf ⟨z, trivial⟩).asIdeal
  rw [show s.appLE U ⊤ hpre.ge (inverseAffineCoordinate K) = 0 by
    simpa [s, infinitySection] using
      ofInverseElement_appLE_inverseAffineCoordinate K K (RingHom.id K) 0]
  exact Ideal.zero_mem _

/-- The point `[0 : 1]` is not the generic point of the projective line. -/
lemma zeroPoint_ne_genericPoint (K : Type u) [Field K] :
    zeroPoint K ≠ genericPoint (scheme K) := by
  intro h
  let U := standardAffineOpen K
  let hU := isAffineOpen_standardAffineOpen K
  let hz : zeroPoint K ∈ U := zeroPoint_mem_standardAffineOpen K
  letI : Nonempty U := ⟨⟨zeroPoint K, hz⟩⟩
  have hη : genericPoint (scheme K) ∈ U :=
    ((genericPoint_spec (scheme K)).mem_open_set_iff U.isOpen).mpr
      ⟨zeroPoint K, trivial, hz⟩
  have heq : hU.primeIdealOf ⟨zeroPoint K, hz⟩ =
      hU.primeIdealOf ⟨genericPoint (scheme K), hη⟩ := by
    congr 1
    exact Subtype.ext h
  have hηIdeal : (hU.primeIdealOf ⟨genericPoint (scheme K), hη⟩).asIdeal = ⊥ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  have heqIdeal := congrArg PrimeSpectrum.asIdeal heq
  rw [primeIdealOf_zeroPoint_asIdeal_of_mem K hz, hηIdeal] at heqIdeal
  exact affineCoordinate_ne_zero K (Ideal.span_singleton_eq_bot.mp heqIdeal)

/-- The point `[1 : 0]` is not the generic point of the projective line. -/
lemma infinityPoint_ne_genericPoint (K : Type u) [Field K] :
    infinityPoint K ≠ genericPoint (scheme K) := by
  intro h
  let U := infinityAffineOpen K
  let hU := isAffineOpen_infinityAffineOpen K
  let hinf : infinityPoint K ∈ U := infinityPoint_mem_infinityAffineOpen K
  letI : Nonempty U := ⟨⟨infinityPoint K, hinf⟩⟩
  have hη : genericPoint (scheme K) ∈ U :=
    ((genericPoint_spec (scheme K)).mem_open_set_iff U.isOpen).mpr
      ⟨infinityPoint K, trivial, hinf⟩
  have heq : hU.primeIdealOf ⟨infinityPoint K, hinf⟩ =
      hU.primeIdealOf ⟨genericPoint (scheme K), hη⟩ := by
    congr 1
    exact Subtype.ext h
  have hηIdeal : (hU.primeIdealOf ⟨genericPoint (scheme K), hη⟩).asIdeal = ⊥ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  have heqIdeal := congrArg PrimeSpectrum.asIdeal heq
  rw [primeIdealOf_infinityPoint_asIdeal_of_mem K hinf, hηIdeal] at heqIdeal
  exact inverseAffineCoordinate_ne_zero K (Ideal.span_singleton_eq_bot.mp heqIdeal)

end

end TauCeti.AlgebraicGeometry.ProjectiveLine
