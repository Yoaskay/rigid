import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Rigid.AffinoidAlgebra.LaurentIntersectionMaps
import Rigid.AffinoidSpectrum.Cech

set_option linter.style.header false

/-!
# The normalized Čech complex of a Laurent cover

This file identifies the first three terms of the normalized Čech complex of the two-member
Laurent cover with the short exact sequence constructed in `LaurentIntersectionMaps`.
-/

open CategoryTheory

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain

/-- A rational datum for the Laurent overlap `|f| = 1` whose section algebra is the direct
Laurent intersection used by the established short exact sequence. -/
noncomputable def laurentIntersectionDomain (f : A) :
    AffinoidRationalSubdomain K A where
  n := 2
  g := f
  f := CompletedLaurent.laurentIntersectionNumerator A f
  isRational := by
    rw [IsRationalDatum]
    apply (Ideal.eq_top_iff_one _).mpr
    apply Ideal.subset_span
    apply Set.mem_insert_of_mem
    refine ⟨1, ?_⟩
    simp [CompletedLaurent.laurentIntersectionNumerator]

@[simp]
theorem mem_laurentIntersectionDomain_carrier (f : A) (x : BerkovichSpectrumOver K A) :
    x ∈ (laurentIntersectionDomain K A f).carrier ↔ x f = 1 := by
  change
    (∀ i : Fin 2,
      x (CompletedLaurent.laurentIntersectionNumerator A f i) ≤ x f) ↔
        x f = 1
  constructor
  · intro hx
    have h0 := hx 0
    have h1 := hx 1
    have hnonneg := BerkovichSpectrumOver.nonneg K A x f
    simp only [CompletedLaurent.laurentIntersectionNumerator, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_pow, BerkovichSpectrumOver.map_one] at h0 h1
    nlinarith
  · intro hx
    intro i
    fin_cases i <;>
      simp [CompletedLaurent.laurentIntersectionNumerator, hx]

/-- The product rational datum for the intersection of the two Laurent charts and the direct
Laurent-intersection datum cut out the same point set. -/
theorem carrier_inter_laurent_eq_laurentIntersectionDomain (f : A) :
    (inter K A (laurentLE K A f) (laurentGE K A f)).carrier =
      (laurentIntersectionDomain K A f).carrier := by
  ext x
  rw [carrier_inter]
  simp only [Set.mem_inter_iff, mem_carrier_laurentLE, mem_carrier_laurentGE,
    mem_laurentIntersectionDomain_carrier]
  exact (le_antisymm_iff).symm

namespace Cover

private noncomputable def standardOverlapToDirect (hA : IsAffinoidAlgebra K A) (f : A) :
    ContinuousAlgHom K
      (inter K A (laurentLE K A f) (laurentGE K A f)).Sections
      (laurentIntersectionDomain K A f).Sections :=
  restriction K A hA
    (carrier_inter_laurent_eq_laurentIntersectionDomain K A f).ge

private theorem plusRestriction_comp_plusMap
    (hA : IsAffinoidAlgebra K A) (f : A) :
    (restriction K A hA
        (inter_subset_left K A (laurentLE K A f) (laurentGE K A f))).comp
          (LaurentCharts.plusMap K A f) =
      RationalLocalization.baseMap K A
        (inter K A (laurentLE K A f) (laurentGE K A f)).n
        (inter K A (laurentLE K A f) (laurentGE K A f)).g
        (inter K A (laurentLE K A f) (laurentGE K A f)).f := by
  simpa only [LaurentCharts.plusMap, laurentLE] using
    restriction_comp_baseMap K A hA
      (inter_subset_left K A (laurentLE K A f) (laurentGE K A f))

private theorem minusRestriction_comp_minusMap
    (hA : IsAffinoidAlgebra K A) (f : A) :
    (restriction K A hA
        (inter_subset_right K A (laurentLE K A f) (laurentGE K A f))).comp
          (LaurentCharts.minusMap K A f) =
      RationalLocalization.baseMap K A
        (inter K A (laurentLE K A f) (laurentGE K A f)).n
        (inter K A (laurentLE K A f) (laurentGE K A f)).g
        (inter K A (laurentLE K A f) (laurentGE K A f)).f := by
  simpa only [LaurentCharts.minusMap, laurentGE] using
    restriction_comp_baseMap K A hA
      (inter_subset_right K A (laurentLE K A f) (laurentGE K A f))

private theorem standardOverlapToDirect_comp_baseMap
    (hA : IsAffinoidAlgebra K A) (f : A) :
    (standardOverlapToDirect K A hA f).comp
        (RationalLocalization.baseMap K A
          (inter K A (laurentLE K A f) (laurentGE K A f)).n
          (inter K A (laurentLE K A f) (laurentGE K A f)).g
          (inter K A (laurentLE K A f) (laurentGE K A f)).f) =
      RationalLocalization.baseMap K A 2 f
        (CompletedLaurent.laurentIntersectionNumerator A f) := by
  simpa only [standardOverlapToDirect, laurentIntersectionDomain] using
    restriction_comp_baseMap K A hA
      (carrier_inter_laurent_eq_laurentIntersectionDomain K A f).ge

private theorem standardOverlapToDirect_comp_plusRestriction
    (hA : IsAffinoidAlgebra K A) (f : A) :
    (standardOverlapToDirect K A hA f).comp
        (restriction K A hA
          (inter_subset_left K A (laurentLE K A f) (laurentGE K A f))) =
      CompletedLaurent.plusToLaurentIntersection K A f := by
  change
    ((standardOverlapToDirect K A hA f).comp
      (restriction K A hA
        (inter_subset_left K A (laurentLE K A f) (laurentGE K A f))) :
        ContinuousAlgHom K (LaurentCharts.Plus K A f)
          (CompletedLaurent.LaurentIntersection K A f)) =
      CompletedLaurent.plusToLaurentIntersection K A f
  apply RationalLocalization.hom_ext_of_isUnit K A
  · have hunit : IsUnit (1 : (laurentIntersectionDomain K A f).Sections) :=
      isUnit_one
    simpa only [map_one] using hunit
  · calc
      ((standardOverlapToDirect K A hA f).comp
          (restriction K A hA
            (inter_subset_left K A (laurentLE K A f) (laurentGE K A f)))).comp
            (LaurentCharts.plusMap K A f) =
          (standardOverlapToDirect K A hA f).comp
            ((restriction K A hA
              (inter_subset_left K A (laurentLE K A f) (laurentGE K A f))).comp
                (LaurentCharts.plusMap K A f)) :=
        ContinuousAlgHom.comp_assoc _ _ _
      _ = (standardOverlapToDirect K A hA f).comp
          (RationalLocalization.baseMap K A
            (inter K A (laurentLE K A f) (laurentGE K A f)).n
            (inter K A (laurentLE K A f) (laurentGE K A f)).g
            (inter K A (laurentLE K A f) (laurentGE K A f)).f) := by
        rw [plusRestriction_comp_plusMap K A hA f]
      _ = RationalLocalization.baseMap K A 2 f
          (CompletedLaurent.laurentIntersectionNumerator A f) :=
        standardOverlapToDirect_comp_baseMap K A hA f
      _ = (CompletedLaurent.plusToLaurentIntersection K A f).comp
          (LaurentCharts.plusMap K A f) :=
        (CompletedLaurent.plusToLaurentIntersection_comp_plusMap K A f).symm

private theorem standardOverlapToDirect_comp_minusRestriction
    (hA : IsAffinoidAlgebra K A) (f : A) :
    (standardOverlapToDirect K A hA f).comp
        (restriction K A hA
          (inter_subset_right K A (laurentLE K A f) (laurentGE K A f))) =
      CompletedLaurent.minusToLaurentIntersection K A f := by
  change
    ((standardOverlapToDirect K A hA f).comp
      (restriction K A hA
        (inter_subset_right K A (laurentLE K A f) (laurentGE K A f))) :
        ContinuousAlgHom K (LaurentCharts.Minus K A f)
          (CompletedLaurent.LaurentIntersection K A f)) =
      CompletedLaurent.minusToLaurentIntersection K A f
  apply RationalLocalization.hom_ext_of_isUnit K A
  · have hbase :
        ((standardOverlapToDirect K A hA f).comp
            (restriction K A hA
              (inter_subset_right K A (laurentLE K A f) (laurentGE K A f)))).comp
              (LaurentCharts.minusMap K A f) =
          RationalLocalization.baseMap K A 2 f
            (CompletedLaurent.laurentIntersectionNumerator A f) := by
        calc
          _ = (standardOverlapToDirect K A hA f).comp
              ((restriction K A hA
                (inter_subset_right K A (laurentLE K A f) (laurentGE K A f))).comp
                  (LaurentCharts.minusMap K A f)) :=
            ContinuousAlgHom.comp_assoc _ _ _
          _ = (standardOverlapToDirect K A hA f).comp
              (RationalLocalization.baseMap K A
                (inter K A (laurentLE K A f) (laurentGE K A f)).n
                (inter K A (laurentLE K A f) (laurentGE K A f)).g
                (inter K A (laurentLE K A f) (laurentGE K A f)).f) := by
            rw [minusRestriction_comp_minusMap K A hA f]
          _ = _ := standardOverlapToDirect_comp_baseMap K A hA f
    change IsUnit
      (((standardOverlapToDirect K A hA f).comp
          (restriction K A hA
            (inter_subset_right K A (laurentLE K A f) (laurentGE K A f)))).comp
          (LaurentCharts.minusMap K A f) f)
    rw [hbase]
    exact RationalLocalization.isUnit_baseMap_denominator K A 2 f
      (CompletedLaurent.laurentIntersectionNumerator A f)
      (laurentIntersectionDomain K A f).isRational
  · calc
      ((standardOverlapToDirect K A hA f).comp
          (restriction K A hA
            (inter_subset_right K A (laurentLE K A f) (laurentGE K A f)))).comp
            (LaurentCharts.minusMap K A f) =
          (standardOverlapToDirect K A hA f).comp
            ((restriction K A hA
              (inter_subset_right K A (laurentLE K A f) (laurentGE K A f))).comp
                (LaurentCharts.minusMap K A f)) :=
        ContinuousAlgHom.comp_assoc _ _ _
      _ = (standardOverlapToDirect K A hA f).comp
          (RationalLocalization.baseMap K A
            (inter K A (laurentLE K A f) (laurentGE K A f)).n
            (inter K A (laurentLE K A f) (laurentGE K A f)).g
            (inter K A (laurentLE K A f) (laurentGE K A f)).f) := by
        rw [minusRestriction_comp_minusMap K A hA f]
      _ = RationalLocalization.baseMap K A 2 f
          (CompletedLaurent.laurentIntersectionNumerator A f) :=
        standardOverlapToDirect_comp_baseMap K A hA f
      _ = (CompletedLaurent.minusToLaurentIntersection K A f).comp
          (LaurentCharts.minusMap K A f) :=
        (CompletedLaurent.minusToLaurentIntersection_comp_minusMap K A f).symm

/-! ## The three terms of the normalized complex -/

private noncomputable def laurentLeftIndex (f : A) : Fin (laurent K A f).m := by
  change Fin 2
  exact 0

private noncomputable def laurentRightIndex (f : A) : Fin (laurent K A f).m := by
  change Fin 2
  exact 1

@[simp]
private theorem laurent_domain_leftIndex (f : A) :
    (laurent K A f).domain (laurentLeftIndex K A f) = laurentLE K A f := by
  change (![laurentLE K A f, laurentGE K A f] : Fin 2 →
    AffinoidRationalSubdomain K A) 0 = laurentLE K A f
  rfl

@[simp]
private theorem laurent_domain_rightIndex (f : A) :
    (laurent K A f).domain (laurentRightIndex K A f) = laurentGE K A f := by
  change (![laurentLE K A f, laurentGE K A f] : Fin 2 →
    AffinoidRationalSubdomain K A) 1 = laurentGE K A f
  rfl

/-- The unique increasing pair of indices in the two-member Laurent cover. -/
private noncomputable def laurentPairTuple (hA : IsAffinoidAlgebra K A) (f : A) :
    ((laurent K A f).cechFamily K A hA).StrictTuple 1 := by
  change Fin 2 ↪o Fin 2
  exact OrderEmbedding.id _

private noncomputable def laurentLeftTuple (hA : IsAffinoidAlgebra K A) (f : A) :
    ((laurent K A f).cechFamily K A hA).StrictTuple 0 :=
  ((laurent K A f).cechFamily K A hA).strictDelete 1
    (laurentPairTuple K A hA f)

private noncomputable def laurentRightTuple (hA : IsAffinoidAlgebra K A) (f : A) :
    ((laurent K A f).cechFamily K A hA).StrictTuple 0 :=
  ((laurent K A f).cechFamily K A hA).strictDelete 0
    (laurentPairTuple K A hA f)

@[simp]
private theorem laurentLeftTuple_apply (hA : IsAffinoidAlgebra K A) (f : A) :
    laurentLeftTuple K A hA f 0 = laurentLeftIndex K A f :=
  rfl

@[simp]
private theorem laurentRightTuple_apply (hA : IsAffinoidAlgebra K A) (f : A) :
    laurentRightTuple K A hA f 0 = laurentRightIndex K A f :=
  rfl

private theorem wholeToLeftRestriction_comp_baseMap
    (hA : IsAffinoidAlgebra K A) (f : A) :
    (restriction K A hA
        ((laurent K A f).subset (laurentLeftTuple K A hA f 0))).comp
          (RationalLocalization.baseMap K A (whole K A).n (whole K A).g
            (whole K A).f) =
      LaurentCharts.plusMap K A f := by
  calc
    _ = RationalLocalization.baseMap K A
        ((laurent K A f).domain (laurentLeftTuple K A hA f 0)).n
        ((laurent K A f).domain (laurentLeftTuple K A hA f 0)).g
        ((laurent K A f).domain (laurentLeftTuple K A hA f 0)).f :=
      restriction_comp_baseMap K A hA
        ((laurent K A f).subset (laurentLeftTuple K A hA f 0))
    _ = LaurentCharts.plusMap K A f := by rfl

private theorem wholeToRightRestriction_comp_baseMap
    (hA : IsAffinoidAlgebra K A) (f : A) :
    (restriction K A hA
        ((laurent K A f).subset (laurentRightTuple K A hA f 0))).comp
          (RationalLocalization.baseMap K A (whole K A).n (whole K A).g
            (whole K A).f) =
      LaurentCharts.minusMap K A f := by
  calc
    _ = RationalLocalization.baseMap K A
        ((laurent K A f).domain (laurentRightTuple K A hA f 0)).n
        ((laurent K A f).domain (laurentRightTuple K A hA f 0)).g
        ((laurent K A f).domain (laurentRightTuple K A hA f 0)).f :=
      restriction_comp_baseMap K A hA
        ((laurent K A f).subset (laurentRightTuple K A hA f 0))
    _ = LaurentCharts.minusMap K A f := by rfl

private theorem laurentStrictTuple_zero_eq_left_or_right
    (hA : IsAffinoidAlgebra K A) (f : A)
    (σ : ((laurent K A f).cechFamily K A hA).StrictTuple 0) :
    σ = laurentLeftTuple K A hA f ∨ σ = laurentRightTuple K A hA f := by
  change Fin 1 ↪o Fin 2 at σ
  have hval : (σ 0).val = 0 ∨ (σ 0).val = 1 := by omega
  rcases hval with hval | hval
  · have h : σ 0 = 0 := Fin.ext hval
    left
    ext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact congrArg Fin.val h
  · have h : σ 0 = 1 := Fin.ext hval
    right
    ext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact congrArg Fin.val h

private noncomputable def laurentChartCochainsEquiv
    (hA : IsAffinoidAlgebra K A) (f : A) :
    ((laurent K A f).cechFamily K A hA).NormalizedCochains 0 ≃ₗ[K]
      LaurentCharts.Plus K A f × LaurentCharts.Minus K A f where
  toFun s :=
    (s (laurentLeftTuple K A hA f), s (laurentRightTuple K A hA f))
  invFun pq := by
    intro σ
    by_cases hσ : σ = laurentLeftTuple K A hA f
    · subst σ
      exact pq.1
    · have hσ' :=
        (laurentStrictTuple_zero_eq_left_or_right K A hA f σ).resolve_left hσ
      subst σ
      exact pq.2
  left_inv s := by
    funext σ
    rcases laurentStrictTuple_zero_eq_left_or_right K A hA f σ with hσ | hσ
    · subst σ
      rfl
    · subst σ
      rfl
  right_inv pq := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem laurentStrictTuple_one_eq_pair
    (hA : IsAffinoidAlgebra K A) (f : A)
    (σ : ((laurent K A f).cechFamily K A hA).StrictTuple 1) :
    σ = laurentPairTuple K A hA f := by
  change (σ : Fin 2 ↪o Fin 2) = OrderEmbedding.id _
  change Fin 2 ↪o Fin 2 at σ
  have hlt : σ 0 < σ 1 := σ.strictMono (by decide)
  have h0 : (σ 0).val = 0 := by omega
  have h1 : (σ 1).val = 1 := by omega
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

private theorem laurentPair_delete_zero
    (hA : IsAffinoidAlgebra K A) (f : A) :
    ((laurent K A f).cechFamily K A hA).strictDelete 0
        (laurentPairTuple K A hA f) =
      laurentRightTuple K A hA f := by
  rfl

private theorem laurentPair_delete_one
    (hA : IsAffinoidAlgebra K A) (f : A) :
    ((laurent K A f).cechFamily K A hA).strictDelete 1
        (laurentPairTuple K A hA f) =
      laurentLeftTuple K A hA f := by
  rfl

private theorem laurent_normalizedCoface_zero_at_pair
    (hA : IsAffinoidAlgebra K A) (f : A)
    (s : ((laurent K A f).cechFamily K A hA).NormalizedCochains 0) :
    ((laurent K A f).cechFamily K A hA).normalizedCoface 0 0 s
        (laurentPairTuple K A hA f) =
      restriction K A hA
        (inter_subset_right K A (laurentLE K A f) (laurentGE K A f))
        (s (laurentRightTuple K A hA f)) := by
  change
    (rationalPresheaf K A hA).restriction _
        (s (((laurent K A f).cechFamily K A hA).strictDelete 0
          (laurentPairTuple K A hA f))) =
      _
  cases laurentPair_delete_zero K A hA f
  rfl

private theorem laurent_normalizedCoface_one_at_pair
    (hA : IsAffinoidAlgebra K A) (f : A)
    (s : ((laurent K A f).cechFamily K A hA).NormalizedCochains 0) :
    ((laurent K A f).cechFamily K A hA).normalizedCoface 0 1 s
        (laurentPairTuple K A hA f) =
      restriction K A hA
        (inter_subset_left K A (laurentLE K A f) (laurentGE K A f))
        (s (laurentLeftTuple K A hA f)) := by
  change
    (rationalPresheaf K A hA).restriction _
        (s (((laurent K A f).cechFamily K A hA).strictDelete 1
          (laurentPairTuple K A hA f))) =
      _
  cases laurentPair_delete_one K A hA f
  rfl

private noncomputable def laurentStandardOverlapCochainsEquiv
    (hA : IsAffinoidAlgebra K A) (f : A) :
    ((laurent K A f).cechFamily K A hA).NormalizedCochains 1 ≃ₗ[K]
      (inter K A (laurentLE K A f) (laurentGE K A f)).Sections where
  toFun s := s (laurentPairTuple K A hA f)
  invFun x := by
    intro σ
    have hσ := laurentStrictTuple_one_eq_pair K A hA f σ
    subst σ
    exact x
  left_inv s := by
    funext σ
    have hσ := laurentStrictTuple_one_eq_pair K A hA f σ
    subst σ
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def laurentOverlapCochainsEquiv
    (hA : IsAffinoidAlgebra K A) (f : A) :
    ((laurent K A f).cechFamily K A hA).NormalizedCochains 1 ≃ₗ[K]
      CompletedLaurent.LaurentIntersection K A f := by
  change
    ((laurent K A f).cechFamily K A hA).NormalizedCochains 1 ≃ₗ[K]
      RationalLocalization K A 2 f
        (CompletedLaurent.laurentIntersectionNumerator A f)
  exact (laurentStandardOverlapCochainsEquiv K A hA f).trans
    (sectionsLinearEquivOfCarrierEq K A hA
      (inter K A (laurentLE K A f) (laurentGE K A f))
      (laurentIntersectionDomain K A f)
      (carrier_inter_laurent_eq_laurentIntersectionDomain K A f))

private theorem laurent_normalizedAugmentation_comm
    (hA : IsAffinoidAlgebra K A) (f : A)
    (s : (whole K A).Sections) :
    laurentChartCochainsEquiv K A hA f
        (((laurent K A f).cechFamily K A hA).normalizedAugmentation s) =
      LaurentCharts.diagonal K A f (wholeSectionsLinearEquiv K A hA s) := by
  apply Prod.ext
  · change
      restriction K A hA
          ((laurent K A f).subset (laurentLeftTuple K A hA f 0)) s =
        LaurentCharts.plusMap K A f (wholeSectionsLinearEquiv K A hA s)
    calc
      _ = restriction K A hA
          ((laurent K A f).subset (laurentLeftTuple K A hA f 0))
          ((wholeSectionsLinearEquiv K A hA).symm
            (wholeSectionsLinearEquiv K A hA s)) := congrArg _ <|
        (wholeSectionsLinearEquiv K A hA).symm_apply_apply s |>.symm
      _ = _ := by
        rw [wholeSectionsLinearEquiv_symm_apply]
        exact congrArg
            (fun φ : ContinuousAlgHom K A (laurentLE K A f).Sections ↦
              φ (wholeSectionsLinearEquiv K A hA s))
            (wholeToLeftRestriction_comp_baseMap K A hA f)
  · change
      restriction K A hA
          ((laurent K A f).subset (laurentRightTuple K A hA f 0)) s =
        LaurentCharts.minusMap K A f (wholeSectionsLinearEquiv K A hA s)
    calc
      _ = restriction K A hA
          ((laurent K A f).subset (laurentRightTuple K A hA f 0))
          ((wholeSectionsLinearEquiv K A hA).symm
            (wholeSectionsLinearEquiv K A hA s)) := congrArg _ <|
        (wholeSectionsLinearEquiv K A hA).symm_apply_apply s |>.symm
      _ = _ := by
        rw [wholeSectionsLinearEquiv_symm_apply]
        exact congrArg
            (fun φ : ContinuousAlgHom K A (laurentGE K A f).Sections ↦
              φ (wholeSectionsLinearEquiv K A hA s))
            (wholeToRightRestriction_comp_baseMap K A hA f)

private theorem laurent_normalizedDifferential_comm
    (hA : IsAffinoidAlgebra K A) (f : A)
    (s : ((laurent K A f).cechFamily K A hA).NormalizedCochains 0) :
    laurentOverlapCochainsEquiv K A hA f
        (((laurent K A f).cechFamily K A hA).normalizedCofaceModule.differential 0 s) =
      -CompletedLaurent.directDifference K A f
        (laurentChartCochainsEquiv K A hA f s) := by
  rw [Cech.CofaceModule.differential, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_zsmul,
    one_zsmul, ModuleCat.hom_add, ModuleCat.hom_neg, ModuleCat.hom_ofHom,
    LinearMap.add_apply, LinearMap.neg_apply]
  change
    standardOverlapToDirect K A hA f
      ((((laurent K A f).cechFamily K A hA).normalizedCoface 0 0 s)
          (laurentPairTuple K A hA f) +
        -(((laurent K A f).cechFamily K A hA).normalizedCoface 0 1 s)
          (laurentPairTuple K A hA f)) =
      -CompletedLaurent.directDifference K A f
        (laurentChartCochainsEquiv K A hA f s)
  rw [laurent_normalizedCoface_zero_at_pair K A hA f,
    laurent_normalizedCoface_one_at_pair K A hA f]
  change
    standardOverlapToDirect K A hA f
        (restriction K A hA
          (inter_subset_right K A (laurentLE K A f) (laurentGE K A f))
          (s (laurentRightTuple K A hA f)) +
        -restriction K A hA
          (inter_subset_left K A (laurentLE K A f) (laurentGE K A f))
          (s (laurentLeftTuple K A hA f))) =
      -CompletedLaurent.directDifference K A f
        (s (laurentLeftTuple K A hA f), s (laurentRightTuple K A hA f))
  rw [CompletedLaurent.directDifference_apply, map_add, map_neg]
  have hminus :
      standardOverlapToDirect K A hA f
          (restriction K A hA
            (inter_subset_right K A (laurentLE K A f) (laurentGE K A f))
            (s (laurentRightTuple K A hA f))) =
        CompletedLaurent.minusToLaurentIntersection K A f
          (s (laurentRightTuple K A hA f)) := by
    have h := congrArg
      (fun φ : ContinuousAlgHom K (LaurentCharts.Minus K A f)
          (CompletedLaurent.LaurentIntersection K A f) ↦
        φ (s (laurentRightTuple K A hA f)))
      (standardOverlapToDirect_comp_minusRestriction K A hA f)
    change
      standardOverlapToDirect K A hA f
          (restriction K A hA
            (inter_subset_right K A (laurentLE K A f) (laurentGE K A f))
            (s (laurentRightTuple K A hA f))) =
        CompletedLaurent.minusToLaurentIntersection K A f
          (s (laurentRightTuple K A hA f)) at h
    exact h
  have hplus :
      standardOverlapToDirect K A hA f
          (restriction K A hA
            (inter_subset_left K A (laurentLE K A f) (laurentGE K A f))
            (s (laurentLeftTuple K A hA f))) =
        CompletedLaurent.plusToLaurentIntersection K A f
          (s (laurentLeftTuple K A hA f)) := by
    have h := congrArg
      (fun φ : ContinuousAlgHom K (LaurentCharts.Plus K A f)
          (CompletedLaurent.LaurentIntersection K A f) ↦
        φ (s (laurentLeftTuple K A hA f)))
      (standardOverlapToDirect_comp_plusRestriction K A hA f)
    change
      standardOverlapToDirect K A hA f
          (restriction K A hA
            (inter_subset_left K A (laurentLE K A f) (laurentGE K A f))
            (s (laurentLeftTuple K A hA f))) =
        CompletedLaurent.plusToLaurentIntersection K A f
          (s (laurentLeftTuple K A hA f)) at h
    exact h
  rw [hminus, hplus]
  abel

private theorem isEmpty_laurentStrictTuple
    (hA : IsAffinoidAlgebra K A) (f : A) (n : ℕ) (hn : 2 ≤ n) :
    IsEmpty (((laurent K A f).cechFamily K A hA).StrictTuple n) := by
  constructor
  intro σ
  change Fin (n + 1) ↪o Fin 2 at σ
  have hcard : n + 1 ≤ 2 := by
    simpa using Fintype.card_le_of_injective σ σ.injective
  omega

/-- The normalized Čech complex of a two-member Laurent cover is acyclic. -/
theorem laurent_normalizedCechComplex_acyclic
    (hA : IsAffinoidAlgebra K A) (f : A) :
    (laurent K A f).normalizedCechComplex K A hA |>.Acyclic := by
  intro n
  rcases n with _ | _ | _ | n
  · rw [((laurent K A f).normalizedCechComplex K A hA).exactAt_iff'
      0 0 1 (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    change
      ∀ x : (whole K A).Sections,
        ((laurent K A f).cechFamily K A hA).normalizedAugmentation x = 0 →
          ∃ y : (whole K A).Sections, 0 = x
    intro x hx
    have hdiag :
        LaurentCharts.diagonal K A f (wholeSectionsLinearEquiv K A hA x) = 0 := by
      have h := congrArg (laurentChartCochainsEquiv K A hA f) hx
      rw [laurent_normalizedAugmentation_comm K A hA f] at h
      simpa only [map_zero] using h
    have hx0 : x = 0 := by
      apply (wholeSectionsLinearEquiv K A hA).injective
      apply (CompletedLaurent.direct_shortExact K A hA f).1
      exact hdiag.trans (by simp only [map_zero])
    subst x
    exact ⟨0, by simp⟩
  · rw [((laurent K A f).normalizedCechComplex K A hA).exactAt_iff'
      0 1 2 (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    change
      ∀ x : ((laurent K A f).cechFamily K A hA).NormalizedCochains 0,
        ((laurent K A f).cechFamily K A hA).normalizedCofaceModule.differential 0 x =
            0 →
          ∃ y : (whole K A).Sections,
            ((laurent K A f).cechFamily K A hA).normalizedAugmentation y = x
    intro x hx
    change
      ((laurent K A f).cechFamily K A hA).normalizedCofaceModule.differential 0 x =
        (0 : ((laurent K A f).cechFamily K A hA).NormalizedCochains 1) at hx
    have hdiff :
        CompletedLaurent.directDifference K A f
          (laurentChartCochainsEquiv K A hA f x) = 0 := by
      have h := congrArg (laurentOverlapCochainsEquiv K A hA f) hx
      rw [laurent_normalizedDifferential_comm K A hA f] at h
      have hzero :
          laurentOverlapCochainsEquiv K A hA f 0 = 0 :=
        map_zero (laurentOverlapCochainsEquiv K A hA f)
      rw [hzero] at h
      exact neg_eq_zero.mp h
    obtain ⟨a, ha⟩ :=
      ((CompletedLaurent.direct_shortExact K A hA f).2.1
        (laurentChartCochainsEquiv K A hA f x)).mp hdiff
    refine ⟨(wholeSectionsLinearEquiv K A hA).symm a, ?_⟩
    apply (laurentChartCochainsEquiv K A hA f).injective
    rw [laurent_normalizedAugmentation_comm K A hA f]
    simpa only [LinearEquiv.apply_symm_apply] using ha
  · rw [((laurent K A f).normalizedCechComplex K A hA).exactAt_iff'
      1 2 3 (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    change
      ∀ x : ((laurent K A f).cechFamily K A hA).NormalizedCochains 1,
        _ → ∃ y : ((laurent K A f).cechFamily K A hA).NormalizedCochains 0,
          ((laurent K A f).cechFamily K A hA).normalizedCofaceModule.differential 0 y =
            x
    intro x _
    obtain ⟨pq, hpq⟩ :=
      (CompletedLaurent.direct_shortExact K A hA f).2.2
        (laurentOverlapCochainsEquiv K A hA f x)
    refine ⟨(laurentChartCochainsEquiv K A hA f).symm (-pq), ?_⟩
    apply (laurentOverlapCochainsEquiv K A hA f).injective
    rw [laurent_normalizedDifferential_comm K A hA f]
    simp only [LinearEquiv.apply_symm_apply, map_neg, neg_neg]
    exact hpq
  · apply HomologicalComplex.ExactAt.of_isZero
    change CategoryTheory.Limits.IsZero
      (ModuleCat.of K
        (((laurent K A f).cechFamily K A hA).NormalizedCochains (n + 2)))
    letI : IsEmpty
        (((laurent K A f).cechFamily K A hA).StrictTuple (n + 2)) :=
      isEmpty_laurentStrictTuple K A hA f (n + 2) (by omega)
    letI : Subsingleton
        (((laurent K A f).cechFamily K A hA).NormalizedCochains (n + 2)) :=
      inferInstance
    exact ModuleCat.isZero_of_subsingleton _

end Cover

end AffinoidRationalSubdomain

end Rigid
