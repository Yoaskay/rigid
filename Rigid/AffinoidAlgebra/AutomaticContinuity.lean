import Mathlib
import Rigid.AffinoidAlgebra.Basic
import Rigid.TateAlgebra.Complete

set_option linter.style.header false

/-!
# Automatic continuity for affinoid algebras

This file isolates the proof of automatic continuity used by the Development comparator.  It
follows Proposition 1.4.11: first handle finite-dimensional targets, and then apply the closed
graph theorem together with the finite-dimensional quotients by powers of maximal ideals.
-/

universe u v w

open Filter
open scoped Topology

namespace Rigid

section

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [CommRing A] [Algebra K A]

private theorem residueTopology_eq (P Q : AffinoidPresentation K A) :
    P.residueTopology = Q.residueTopology := sorry

private theorem affinoidTopology_eq_residueTopology (hA : IsAffinoidAlgebra K A)
    (P : AffinoidPresentation K A) : affinoidTopology K A hA = P.residueTopology :=
  residueTopology_eq K A hA.presentation P

private theorem continuous_for_affinoidTopology_of_surjective
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) :
    @Continuous A B (affinoidTopology K A hA) (affinoidTopology K B hB) f := by
  let P := hA.presentation
  let g : TateAlgebra K (Fin P.n) →ₐ[K] B := f.comp P.toAlgHom
  have hg : Function.Surjective g := hf.comp P.toAlgHom_surjective
  let Q : AffinoidPresentation K B :=
    { n := P.n
      ideal := RingHom.ker g
      equiv := Ideal.quotientKerAlgEquivOfSurjective hg }
  have hQg : Q.toAlgHom = g := by
    ext x
    simp [AffinoidPresentation.toAlgHom, Q]
  rw [affinoidTopology_eq_residueTopology K A hA P,
    affinoidTopology_eq_residueTopology K B hB Q]
  letI : TopologicalSpace A := P.residueTopology
  letI : TopologicalSpace B := Q.residueTopology
  change Continuous f
  have hP : IsOpenQuotientMap P.toAlgHom :=
    isOpenQuotientMap_coinduced P.toAlgHom P.toAlgHom_surjective
  apply hP.continuous_comp_iff.mp
  simpa [Function.comp_def, g, hQg] using
    (continuous_coinduced_rng : Continuous Q.toAlgHom)

private theorem isAffinoidAlgebra_of_surjective
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (f : A →ₐ[K] B) (hf : Function.Surjective f) :
    IsAffinoidAlgebra K B := by
  let P := hA.presentation
  let g : TateAlgebra K (Fin P.n) →ₐ[K] B := f.comp P.toAlgHom
  have hg : Function.Surjective g := hf.comp P.toAlgHom_surjective
  exact ⟨
    { n := P.n
      ideal := RingHom.ker g
      equiv := Ideal.quotientKerAlgEquivOfSurjective hg }⟩

@[reducible]
private noncomputable def compatibleResidueNormedAddCommGroup
    (P : AffinoidPresentation K A) : NormedAddCommGroup A where
  toNorm := sorry
  toAddCommGroup := inferInstance
  toMetricSpace := sorry
  dist_eq := by sorry

@[reducible]
private noncomputable def compatibleResidueNormedSpace (P : AffinoidPresentation K A) :
    letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
    NormedSpace K A := by
  letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
  exact
    { toModule := inferInstance
      norm_smul_le := by sorry }

private theorem compatibleResidueCompleteSpace (P : AffinoidPresentation K A) :
    letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
    CompleteSpace A := sorry

private theorem compatibleResidueTopology_eq (P : AffinoidPresentation K A) :
    (letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
     inferInstance : TopologicalSpace A) = P.residueTopology := sorry

private theorem residueT2Space (P : AffinoidPresentation K A) :
    @T2Space A P.residueTopology := by
  rw [← compatibleResidueTopology_eq K A P]
  letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
  infer_instance

private theorem continuous_for_affinoidTopology_of_finite_codomain
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B] [Module.Finite K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    @Continuous A B (affinoidTopology K A hA) (affinoidTopology K B hB) f := by
  let C := f.range
  let q : A →ₐ[K] C := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hC : IsAffinoidAlgebra K C := isAffinoidAlgebra_of_surjective K hA q hq
  have hqcont : @Continuous A C (affinoidTopology K A hA) (affinoidTopology K C hC) q :=
    continuous_for_affinoidTopology_of_surjective K hA hC q hq
  let PC := hC.presentation
  let PB := hB.presentation
  letI : NormedAddCommGroup C := compatibleResidueNormedAddCommGroup K C PC
  letI : NormedSpace K C := compatibleResidueNormedSpace K C PC
  letI : NormedAddCommGroup B := compatibleResidueNormedAddCommGroup K B PB
  letI : NormedSpace K B := compatibleResidueNormedSpace K B PB
  letI : TopologicalSpace C := PC.residueTopology
  letI : IsTopologicalRing C := PC.residueIsTopologicalRing
  letI : ContinuousSMul K C := PC.residueContinuousSMul
  letI : T2Space C := residueT2Space K C PC
  letI : TopologicalSpace B := PB.residueTopology
  letI : IsTopologicalRing B := PB.residueIsTopologicalRing
  letI : ContinuousSMul K B := PB.residueContinuousSMul
  have hval : Continuous (f.range.val : C →ₐ[K] B) :=
    f.range.val.toLinearMap.continuous_of_finiteDimensional
  have hval' : @Continuous C B (affinoidTopology K C hC) (affinoidTopology K B hB)
      f.range.val := by
    rw [affinoidTopology_eq_residueTopology K C hC PC,
      affinoidTopology_eq_residueTopology K B hB PB]
    exact hval
  letI : TopologicalSpace A := affinoidTopology K A hA
  letI : TopologicalSpace C := affinoidTopology K C hC
  letI : TopologicalSpace B := affinoidTopology K B hB
  exact hval'.comp hqcont

private theorem continuous_linearMap_of_seq_closed_graph
    {A : Type v} [NormedAddCommGroup A] [NormedSpace K A] [CompleteSpace A]
    {B : Type w} [NormedAddCommGroup B] [NormedSpace K B] [CompleteSpace B]
    (f : A →ₗ[K] B)
    (hgraph : ∀ (u : ℕ → A) (x : A) (y : B), Tendsto u atTop (𝓝 x) →
      Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) : Continuous f :=
  f.continuous_of_seq_closed_graph hgraph

/-- The Noether-normalization consequence used in Proposition 1.4.11: powers of maximal ideals
have finite-dimensional quotient. -/
private theorem finite_quotient_maximal_pow_of_isAffinoidAlgebra
    {B : Type w} [CommRing B] [Algebra K B] (hB : IsAffinoidAlgebra K B)
    (m : Ideal B) (hm : m.IsMaximal) (l : ℕ) (hl : 1 ≤ l) :
    Module.Finite K (B ⧸ m ^ l) := sorry

/-- The Krull-intersection consequence used in Proposition 1.4.11. -/
private theorem eq_zero_of_mem_all_maximal_powers_of_isAffinoidAlgebra
    {B : Type w} [CommRing B] [Algebra K B] (hB : IsAffinoidAlgebra K B) (b : B)
    (hb : ∀ (m : Ideal B), m.IsMaximal → ∀ l : ℕ, 1 ≤ l → b ∈ m ^ l) : b = 0 := sorry

private theorem continuous_for_affinoidTopology_of_isAffinoidAlgebra
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    @Continuous A B (affinoidTopology K A hA) (affinoidTopology K B hB) f := by
  let fLinear : A →ₗ[K] B := f.toLinearMap
  let PA := hA.presentation
  let PB := hB.presentation
  letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A PA
  letI : NormedSpace K A := compatibleResidueNormedSpace K A PA
  letI : CompleteSpace A := compatibleResidueCompleteSpace K A PA
  letI : NormedAddCommGroup B := compatibleResidueNormedAddCommGroup K B PB
  letI : NormedSpace K B := compatibleResidueNormedSpace K B PB
  letI : CompleteSpace B := compatibleResidueCompleteSpace K B PB
  have hAtop : (inferInstance : TopologicalSpace A) = affinoidTopology K A hA :=
    (compatibleResidueTopology_eq K A PA).trans
      (affinoidTopology_eq_residueTopology K A hA PA).symm
  have hBtop : (inferInstance : TopologicalSpace B) = affinoidTopology K B hB :=
    (compatibleResidueTopology_eq K B PB).trans
      (affinoidTopology_eq_residueTopology K B hB PB).symm
  have hfmetric := continuous_linearMap_of_seq_closed_graph K fLinear (by
    intro u x y hu hfu
    suffices y - f x = 0 by simpa [fLinear] using (sub_eq_zero.mp this)
    apply eq_zero_of_mem_all_maximal_powers_of_isAffinoidAlgebra K hB
    intro m hm l hl
    let q : B →ₐ[K] B ⧸ m ^ l := Ideal.Quotient.mkₐ K (m ^ l)
    let hQ : IsAffinoidAlgebra K (B ⧸ m ^ l) :=
      isAffinoidAlgebra_of_surjective K hB q (Ideal.Quotient.mkₐ_surjective K (m ^ l))
    letI : Module.Finite K (B ⧸ m ^ l) :=
      finite_quotient_maximal_pow_of_isAffinoidAlgebra K hB m hm l hl
    have hqf := continuous_for_affinoidTopology_of_finite_codomain K hA hQ (q.comp f)
    have hq := continuous_for_affinoidTopology_of_finite_codomain K hB hQ q
    let PQ := hQ.presentation
    rw [← hAtop] at hqf
    rw [← hBtop] at hq
    letI : TopologicalSpace (B ⧸ m ^ l) := affinoidTopology K (B ⧸ m ^ l) hQ
    have hT2Q : @T2Space (B ⧸ m ^ l) (affinoidTopology K (B ⧸ m ^ l) hQ) := by
      rw [affinoidTopology_eq_residueTopology K (B ⧸ m ^ l) hQ PQ]
      exact residueT2Space K (B ⧸ m ^ l) PQ
    letI : T2Space (B ⧸ m ^ l) := hT2Q
    have hlim₁ : Tendsto (fun n ↦ q (f (u n))) atTop (𝓝 (q (f x))) :=
      (hqf.tendsto x).comp hu
    have hlim₂ : Tendsto (fun n ↦ q (f (u n))) atTop (𝓝 (q y)) :=
      (hq.tendsto y).comp hfu
    have heq : q (f x) = q y := tendsto_nhds_unique hlim₁ hlim₂
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q (y - f x) = 0
    rw [map_sub, heq, sub_self])
  change @Continuous A B (inferInstance : TopologicalSpace A)
    (inferInstance : TopologicalSpace B) f at hfmetric
  rwa [hAtop, hBtop] at hfmetric

/-- Automatic continuity written directly in terms of two quotient presentations. -/
theorem continuous_for_affinoidPresentationData
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B]
    {nA nB : ℕ} (IA : Ideal (TateAlgebra K (Fin nA)))
    (eA : (TateAlgebra K (Fin nA) ⧸ IA) ≃ₐ[K] A)
    (IB : Ideal (TateAlgebra K (Fin nB)))
    (eB : (TateAlgebra K (Fin nB) ⧸ IB) ≃ₐ[K] B) (f : A →ₐ[K] B) :
    @Continuous A B
      (TopologicalSpace.coinduced
        (eA.toAlgHom.comp (Ideal.Quotient.mkₐ K IA)) inferInstance)
      (TopologicalSpace.coinduced
        (eB.toAlgHom.comp (Ideal.Quotient.mkₐ K IB)) inferInstance) f := by
  let PA : AffinoidPresentation K A := { n := nA, ideal := IA, equiv := eA }
  let PB : AffinoidPresentation K B := { n := nB, ideal := IB, equiv := eB }
  have h := continuous_for_affinoidTopology_of_isAffinoidAlgebra K
    (show IsAffinoidAlgebra K A from ⟨PA⟩) (show IsAffinoidAlgebra K B from ⟨PB⟩) f
  rw [affinoidTopology_eq_residueTopology K A ⟨PA⟩ PA,
    affinoidTopology_eq_residueTopology K B ⟨PB⟩ PB] at h
  change @Continuous A B PA.residueTopology PB.residueTopology f
  exact h

end

end Rigid
