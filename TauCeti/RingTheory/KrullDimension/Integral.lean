/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Krull dimension and integral extensions

This file proves that a faithful integral extension of commutative rings preserves Krull
dimension.  The main ingredient is a chain form of going-up: a finite strict chain of primes in
the base lifts, with the same length, after choosing a prime above its first term.

The result supplies the integral-extension step in the Noether-normalization route to dimension
computations.  In particular, it is a prerequisite for dimension additivity of products of
abelian varieties in Layer E of `TauCetiRoadmap/JacobianChallenge/README.md`.
-/

public section

open Order

namespace RingHom.IsIntegral

universe u

variable {K P Q A B : Type u} [CommRing K] [CommRing P] [CommRing Q] [CommRing A]
  [CommRing B] [Algebra K P] [Algebra K Q] [Algebra K A] [Algebra K B]

/-- The tensor product of two integral algebra homomorphisms is integral. -/
theorem tensorProductMap (g : P →ₐ[K] A) (h : Q →ₐ[K] B)
    (hg : g.IsIntegral) (hh : h.IsIntegral) :
    (Algebra.TensorProduct.map g h).IsIntegral := by
  intro x
  induction x with
  | zero => exact RingHom.isIntegralElem_zero _
  | tmul a b =>
    have ha := (hg a).map
      (Algebra.TensorProduct.includeLeft : A →ₐ[K] TensorProduct K A B).toRingHom
    have hb := (hh b).map
      (Algebra.TensorProduct.includeRight : B →ₐ[K] TensorProduct K A B).toRingHom
    have hleft :
        (Algebra.TensorProduct.map g h).toRingHom.comp
            (Algebra.TensorProduct.includeLeft : P →ₐ[K] TensorProduct K P Q).toRingHom =
          (Algebra.TensorProduct.includeLeft : A →ₐ[K] TensorProduct K A B).toRingHom.comp
            g.toRingHom := by
      ext
      simp
    have hright :
        (Algebra.TensorProduct.map g h).toRingHom.comp
            (Algebra.TensorProduct.includeRight : Q →ₐ[K] TensorProduct K P Q).toRingHom =
          (Algebra.TensorProduct.includeRight : B →ₐ[K] TensorProduct K A B).toRingHom.comp
            h.toRingHom := by
      ext
      simp
    rw [← hleft] at ha
    rw [← hright] at hb
    have ha' := RingHom.isIntegralElem.of_comp
      (Algebra.TensorProduct.includeLeft : P →ₐ[K] TensorProduct K P Q).toRingHom
      (Algebra.TensorProduct.map g h).toRingHom ha
    have hb' := RingHom.isIntegralElem.of_comp
      (Algebra.TensorProduct.includeRight : Q →ₐ[K] TensorProduct K P Q).toRingHom
      (Algebra.TensorProduct.map g h).toRingHom hb
    simpa [Algebra.TensorProduct.one_def] using
      ha'.mul (Algebra.TensorProduct.map g h).toRingHom hb'
  | add x y hx hy => exact hx.add _ hy

end RingHom.IsIntegral

namespace Ideal

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

private theorem exists_ltSeries_liesOver_of_isIntegral_aux [Algebra.IsIntegral R S]
    (l : LTSeries (PrimeSpectrum R)) (P : Ideal S) [P.IsPrime]
    (hPover : l.head.asIdeal = P.under R) :
    ∃ L : LTSeries (PrimeSpectrum S),
      L.length = l.length ∧
      L.head = ⟨P, inferInstance⟩ ∧
      List.map (PrimeSpectrum.comap (algebraMap R S)) L.toList = l.toList := by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton p =>
    use RelSeries.singleton _ ⟨P, inferInstance⟩
    simp only [RelSeries.singleton_length, RelSeries.head_singleton, RelSeries.toList_singleton,
      List.map_cons, List.map_nil, List.cons.injEq, and_true, true_and]
    ext : 1
    exact hPover.symm
  | cons l p hpl ih =>
    simp only [RelSeries.head_cons] at hPover
    have hIP : P.comap (algebraMap R S) ≤ l.head.asIdeal := by
      change P.under R ≤ l.head.asIdeal
      rw [← hPover]
      exact hpl.le
    obtain ⟨Q, hPQ, hQ, hQover⟩ :=
      exists_ideal_over_prime_of_isIntegral_of_isPrime l.head.asIdeal P hIP
    have hPQ' : P < Q := by
      refine hPQ.lt_of_ne fun hEq ↦ ?_
      subst hEq
      have hEq' : p.asIdeal = l.head.asIdeal := hPover.trans hQover
      exact hpl.ne (PrimeSpectrum.ext_iff.mpr hEq')
    letI : Q.IsPrime := hQ
    obtain ⟨L, hlen, hhead, hmap⟩ := ih Q hQover.symm
    have hPL : (⟨P, inferInstance⟩ : PrimeSpectrum S) < L.head := by
      rw [hhead]
      exact hPQ'
    use L.cons ⟨P, inferInstance⟩ hPL
    constructor
    · simpa using hlen
    constructor
    · rfl
    simpa [hmap] using
      PrimeSpectrum.ext_iff.mpr hPover.symm

/-- A finite strict chain of prime ideals lifts along an integral extension after choosing a
prime above the first member of the chain. -/
theorem exists_ltSeries_liesOver_of_isIntegral [Algebra.IsIntegral R S]
    (l : LTSeries (PrimeSpectrum R)) (P : Ideal S) [P.IsPrime]
    [P.LiesOver l.head.asIdeal] :
    ∃ L : LTSeries (PrimeSpectrum S),
      L.length = l.length ∧
      L.head = ⟨P, inferInstance⟩ ∧
      List.map (PrimeSpectrum.comap (algebraMap R S)) L.toList = l.toList :=
  exists_ltSeries_liesOver_of_isIntegral_aux l P Ideal.LiesOver.over

end Ideal

namespace Algebra.IsIntegral

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- A faithful integral extension of commutative rings preserves Krull dimension. -/
theorem ringKrullDim_eq [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · rw [ringKrullDim, ringKrullDim]
    apply krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro P Q hPQ
    exact Ideal.IsIntegral.comap_lt_comap hPQ
  · rw [ringKrullDim, ringKrullDim, krullDim]
    refine iSup_le fun l ↦ ?_
    let P : l.head.asIdeal.primesOver S := Classical.choice inferInstance
    obtain ⟨L, hlen, -, -⟩ :=
      Ideal.exists_ltSeries_liesOver_of_isIntegral l P.1
    rw [← hlen]
    exact le_iSup (fun L : LTSeries (PrimeSpectrum S) ↦ (L.length : WithBot ℕ∞)) L

end Algebra.IsIntegral
