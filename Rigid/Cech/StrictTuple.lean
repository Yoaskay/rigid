import Mathlib.Order.Hom.PowersetCard
import Rigid.Cech.Normalized

set_option linter.style.header false

/-!
# Inserting an index into a normalized Čech tuple

Normalized Čech cochains are indexed by increasing tuples.  The contracting homotopy for a
family with a distinguished member inserts that member into a tuple, unless it is already
present.  This file isolates the finite-order bookkeeping for that operation.
-/

universe u v w

namespace Rigid.Cech

variable {R : Type u} [Ring R]
variable {P : Presheaf.{u, v, w} R}

namespace Presheaf.Family

variable (𝒰 : P.Family)

/-- The unique increasing one-term tuple with prescribed value. -/
noncomputable def strictSingleton (i : Fin 𝒰.card) : 𝒰.StrictTuple 0 :=
  ({i} : Finset (Fin 𝒰.card)).orderEmbOfFin (by simp)

@[simp]
theorem strictSingleton_apply (i : Fin 𝒰.card) (j : Fin 1) :
    𝒰.strictSingleton i j = i := by
  unfold strictSingleton
  exact Finset.orderEmbOfFin_singleton i j

/-- Every one-term strict tuple is the canonical singleton determined by its value. -/
theorem strictTuple_zero_eq_singleton (σ : 𝒰.StrictTuple 0) :
    σ = 𝒰.strictSingleton (σ 0) := by
  ext j
  rw [Fin.eq_zero j, strictSingleton_apply]

/-- The finite set underlying a strictly increasing Čech tuple. -/
noncomputable def strictSupport {n : ℕ} (σ : 𝒰.StrictTuple n) :
    Finset (Fin 𝒰.card) :=
  Finset.univ.image σ

@[simp]
theorem mem_strictSupport_iff {n : ℕ} (σ : 𝒰.StrictTuple n) (i : Fin 𝒰.card) :
    i ∈ 𝒰.strictSupport σ ↔ i ∈ Set.range σ := by
  simp [strictSupport]

@[simp]
theorem card_strictSupport {n : ℕ} (σ : 𝒰.StrictTuple n) :
    (𝒰.strictSupport σ).card = n + 1 := by
  simp [strictSupport, Finset.card_image_of_injective _ σ.injective]

/-- The canonical increasing tuple obtained by inserting a new index. -/
noncomputable def strictInsert {n : ℕ} (σ : 𝒰.StrictTuple n)
    (i : Fin 𝒰.card) (hi : i ∉ 𝒰.strictSupport σ) :
    𝒰.StrictTuple (n + 1) :=
  (insert i (𝒰.strictSupport σ)).orderEmbOfFin (by
    rw [Finset.card_insert_of_notMem hi, card_strictSupport])

/-- The position occupied by the newly inserted index. -/
noncomputable def strictInsertPosition {n : ℕ} (σ : 𝒰.StrictTuple n)
    (i : Fin 𝒰.card) (hi : i ∉ 𝒰.strictSupport σ) :
    Fin (n + 2) :=
  let hcard : (insert i (𝒰.strictSupport σ)).card = n + 2 := by
    rw [Finset.card_insert_of_notMem hi, card_strictSupport]
  ((insert i (𝒰.strictSupport σ)).orderIsoOfFin hcard).symm
    ⟨i, Finset.mem_insert_self i _⟩

@[simp]
theorem strictInsert_apply_position {n : ℕ} (σ : 𝒰.StrictTuple n)
    (i : Fin 𝒰.card) (hi : i ∉ 𝒰.strictSupport σ) :
    𝒰.strictInsert σ i hi (𝒰.strictInsertPosition σ i hi) = i := by
  unfold strictInsert strictInsertPosition
  exact congrArg Subtype.val
    ((insert i (𝒰.strictSupport σ)).orderIsoOfFin _ |>.apply_symm_apply
      ⟨i, Finset.mem_insert_self i _⟩)

private theorem strictTuple_eq_orderEmbOfSupport {n : ℕ} (σ : 𝒰.StrictTuple n) :
    σ = (𝒰.strictSupport σ).orderEmbOfFin (𝒰.card_strictSupport σ) := by
  apply Finset.orderEmbOfFin_unique'
  intro j
  exact (𝒰.mem_strictSupport_iff σ (σ j)).2 ⟨j, rfl⟩

/-- Deleting the newly inserted position recovers the original tuple. -/
@[simp]
theorem strictDelete_strictInsert {n : ℕ} (σ : 𝒰.StrictTuple n)
    (i : Fin 𝒰.card) (hi : i ∉ 𝒰.strictSupport σ) :
    𝒰.strictDelete (𝒰.strictInsertPosition σ i hi) (𝒰.strictInsert σ i hi) = σ := by
  let ρ := 𝒰.strictInsert σ i hi
  let k := 𝒰.strictInsertPosition σ i hi
  have hdel :
      𝒰.strictDelete k ρ =
        (𝒰.strictSupport σ).orderEmbOfFin (𝒰.card_strictSupport σ) := by
    apply Finset.orderEmbOfFin_unique'
    intro j
    have hmem :
        ρ (k.succAbove j) ∈ insert i (𝒰.strictSupport σ) := by
      exact Finset.orderEmbOfFin_mem _ _ _
    have hne : ρ (k.succAbove j) ≠ i := by
      intro heq
      have hki : ρ k = i := by
        exact strictInsert_apply_position 𝒰 σ i hi
      have hindex : k.succAbove j = k :=
        ρ.injective (heq.trans hki.symm)
      exact (Fin.succAbove_ne k j) hindex
    change ρ (k.succAbove j) ∈ 𝒰.strictSupport σ
    simpa [hne] using hmem
  exact hdel.trans (strictTuple_eq_orderEmbOfSupport 𝒰 σ).symm

/-- The canonical insertion is `Fin.insertNth` at its canonical position. -/
theorem strictInsert_coe {n : ℕ} (σ : 𝒰.StrictTuple n)
    (i : Fin 𝒰.card) (hi : i ∉ 𝒰.strictSupport σ) :
    (𝒰.strictInsert σ i hi : Fin (n + 2) → Fin 𝒰.card) =
      Fin.insertNth (𝒰.strictInsertPosition σ i hi) i σ := by
  apply Fin.eq_insertNth_iff.2
  constructor
  · exact 𝒰.strictInsert_apply_position σ i hi
  · funext j
    have h := congrArg
      (fun ρ : 𝒰.StrictTuple n ↦ ρ j)
      (𝒰.strictDelete_strictInsert σ i hi)
    simpa only [Fin.removeNth_apply, strictDelete, OrderEmbedding.coe_comp,
      Function.comp_apply, Fin.succAboveOrderEmb_apply] using h

/-- Deleting one entry removes its value from the support. -/
theorem not_mem_strictSupport_strictDelete {n : ℕ} (ρ : 𝒰.StrictTuple (n + 1))
    (k : Fin (n + 2)) :
    ρ k ∉ 𝒰.strictSupport (𝒰.strictDelete k ρ) := by
  rw [𝒰.mem_strictSupport_iff]
  rintro ⟨j, hj⟩
  have hindex : k.succAbove j = k := ρ.injective hj
  exact (Fin.succAbove_ne k j) hindex

/-- A value absent from a tuple remains absent after deleting an entry. -/
theorem not_mem_strictSupport_strictDelete_of_not_mem {n : ℕ}
    (ρ : 𝒰.StrictTuple (n + 1)) (i : Fin 𝒰.card)
    (hi : i ∉ 𝒰.strictSupport ρ) (k : Fin (n + 2)) :
    i ∉ 𝒰.strictSupport (𝒰.strictDelete k ρ) := by
  intro hmem
  rw [𝒰.mem_strictSupport_iff] at hmem
  obtain ⟨j, hj⟩ := hmem
  apply hi
  rw [𝒰.mem_strictSupport_iff]
  exact ⟨k.succAbove j, hj⟩

/-- Deleting an entry and canonically reinserting its value recovers the tuple. -/
@[simp]
theorem strictInsert_strictDelete {n : ℕ} (ρ : 𝒰.StrictTuple (n + 1))
    (k : Fin (n + 2)) :
    𝒰.strictInsert (𝒰.strictDelete k ρ) (ρ k)
        (𝒰.not_mem_strictSupport_strictDelete ρ k) = ρ := by
  let hcard :
      (insert (ρ k) (𝒰.strictSupport (𝒰.strictDelete k ρ))).card = n + 2 := by
    rw [Finset.card_insert_of_notMem
      (𝒰.not_mem_strictSupport_strictDelete ρ k), 𝒰.card_strictSupport]
  calc
    𝒰.strictInsert (𝒰.strictDelete k ρ) (ρ k)
        (𝒰.not_mem_strictSupport_strictDelete ρ k) =
        (𝒰.strictSupport ρ).orderEmbOfFin (𝒰.card_strictSupport ρ) := by
      change
        (insert (ρ k) (𝒰.strictSupport (𝒰.strictDelete k ρ))).orderEmbOfFin hcard =
          (𝒰.strictSupport ρ).orderEmbOfFin (𝒰.card_strictSupport ρ)
      apply Finset.orderEmbOfFin_unique'
      intro j
      have hj :
          (insert (ρ k) (𝒰.strictSupport (𝒰.strictDelete k ρ))).orderEmbOfFin
              hcard j ∈
            insert (ρ k) (𝒰.strictSupport (𝒰.strictDelete k ρ)) :=
        Finset.orderEmbOfFin_mem
          (insert (ρ k) (𝒰.strictSupport (𝒰.strictDelete k ρ))) hcard j
      rcases Finset.mem_insert.mp hj with hj | hj
      · rw [hj]
        exact (𝒰.mem_strictSupport_iff ρ (ρ k)).2 ⟨k, rfl⟩
      · rw [𝒰.mem_strictSupport_iff] at hj ⊢
        obtain ⟨l, hl⟩ := hj
        exact ⟨k.succAbove l, hl⟩
    _ = ρ := (strictTuple_eq_orderEmbOfSupport 𝒰 ρ).symm

/-- The canonical position after deleting and reinserting an entry is the deleted position. -/
@[simp]
theorem strictInsertPosition_strictDelete {n : ℕ} (ρ : 𝒰.StrictTuple (n + 1))
    (k : Fin (n + 2)) :
    𝒰.strictInsertPosition (𝒰.strictDelete k ρ) (ρ k)
        (𝒰.not_mem_strictSupport_strictDelete ρ k) = k := by
  have hrec := 𝒰.strictInsert_strictDelete ρ k
  have happly := 𝒰.strictInsert_apply_position
    (𝒰.strictDelete k ρ) (ρ k)
    (𝒰.not_mem_strictSupport_strictDelete ρ k)
  rw [hrec] at happly
  apply ρ.injective
  exact happly

/-- Variant of `strictInsert_strictDelete` with the deleted value presented by an equal
external index. -/
theorem strictInsert_strictDelete_of_eq {n : ℕ} (ρ : 𝒰.StrictTuple (n + 1))
    (k : Fin (n + 2)) (i : Fin 𝒰.card)
    (hi : i ∉ 𝒰.strictSupport (𝒰.strictDelete k ρ)) (hki : ρ k = i) :
    𝒰.strictInsert (𝒰.strictDelete k ρ) i hi = ρ := by
  let hcard :
      (insert i (𝒰.strictSupport (𝒰.strictDelete k ρ))).card = n + 2 := by
    rw [Finset.card_insert_of_notMem hi, 𝒰.card_strictSupport]
  calc
    𝒰.strictInsert (𝒰.strictDelete k ρ) i hi =
        (𝒰.strictSupport ρ).orderEmbOfFin (𝒰.card_strictSupport ρ) := by
      change
        (insert i (𝒰.strictSupport (𝒰.strictDelete k ρ))).orderEmbOfFin hcard =
          (𝒰.strictSupport ρ).orderEmbOfFin (𝒰.card_strictSupport ρ)
      apply Finset.orderEmbOfFin_unique'
      intro j
      have hj :
          (insert i (𝒰.strictSupport (𝒰.strictDelete k ρ))).orderEmbOfFin hcard j ∈
            insert i (𝒰.strictSupport (𝒰.strictDelete k ρ)) :=
        Finset.orderEmbOfFin_mem _ _ _
      rcases Finset.mem_insert.mp hj with hj | hj
      · rw [hj, ← hki]
        exact (𝒰.mem_strictSupport_iff ρ (ρ k)).2 ⟨k, rfl⟩
      · rw [𝒰.mem_strictSupport_iff] at hj ⊢
        obtain ⟨l, hl⟩ := hj
        exact ⟨k.succAbove l, hl⟩
    _ = ρ := (strictTuple_eq_orderEmbOfSupport 𝒰 ρ).symm

/-- Variant of `strictInsertPosition_strictDelete` with an equal external index. -/
theorem strictInsertPosition_strictDelete_of_eq {n : ℕ}
    (ρ : 𝒰.StrictTuple (n + 1)) (k : Fin (n + 2)) (i : Fin 𝒰.card)
    (hi : i ∉ 𝒰.strictSupport (𝒰.strictDelete k ρ)) (hki : ρ k = i) :
    𝒰.strictInsertPosition (𝒰.strictDelete k ρ) i hi = k := by
  have hinsert := 𝒰.strictInsert_strictDelete_of_eq ρ k i hi hki
  have happly :=
    𝒰.strictInsert_apply_position (𝒰.strictDelete k ρ) i hi
  apply ρ.injective
  calc
    ρ (𝒰.strictInsertPosition (𝒰.strictDelete k ρ) i hi) =
        𝒰.strictInsert (𝒰.strictDelete k ρ) i hi
          (𝒰.strictInsertPosition (𝒰.strictDelete k ρ) i hi) :=
      congrArg
        (fun θ : 𝒰.StrictTuple (n + 1) ↦
          θ (𝒰.strictInsertPosition (𝒰.strictDelete k ρ) i hi))
        hinsert.symm
    _ = i := happly
    _ = ρ k := hki.symm

/-- Deleting a noninserted position from an inserted tuple is the same as first deleting the
corresponding old position and then inserting. -/
theorem strictDelete_strictInsert_succAbove {n : ℕ} (σ : 𝒰.StrictTuple (n + 1))
    (i : Fin 𝒰.card) (hi : i ∉ 𝒰.strictSupport σ) (j : Fin (n + 2)) :
    let ρ := 𝒰.strictInsert σ i hi
    let k := 𝒰.strictInsertPosition σ i hi
    let l := k.succAbove j
    let τ := 𝒰.strictDelete l ρ
    let m := j.predAbove k
    𝒰.strictDelete m τ = 𝒰.strictDelete j σ := by
  dsimp only
  ext a
  simp only [strictDelete, OrderEmbedding.coe_comp, Function.comp_apply,
    Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_succAbove_succAbove_predAbove]
  have h := congrArg
    (fun θ : 𝒰.StrictTuple (n + 1) ↦ θ (j.succAbove a))
    (𝒰.strictDelete_strictInsert σ i hi)
  exact congrArg Fin.val (by
    simpa only [strictDelete, OrderEmbedding.coe_comp, Function.comp_apply,
      Fin.succAboveOrderEmb_apply] using h)

/-- The inserted value occupies the predicted position after deleting a different position. -/
theorem strictDelete_strictInsert_value {n : ℕ} (σ : 𝒰.StrictTuple (n + 1))
    (i : Fin 𝒰.card) (hi : i ∉ 𝒰.strictSupport σ) (j : Fin (n + 2)) :
    let ρ := 𝒰.strictInsert σ i hi
    let k := 𝒰.strictInsertPosition σ i hi
    let l := k.succAbove j
    let τ := 𝒰.strictDelete l ρ
    τ (j.predAbove k) = i := by
  dsimp only
  simp only [strictDelete, OrderEmbedding.coe_comp, Function.comp_apply,
    Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_succAbove_predAbove]
  exact 𝒰.strictInsert_apply_position σ i hi

/-- A noninserted deletion commutes with canonical insertion. -/
theorem strictDelete_strictInsert_eq_insert {n : ℕ} (σ : 𝒰.StrictTuple (n + 1))
    (i : Fin 𝒰.card) (hi : i ∉ 𝒰.strictSupport σ) (j : Fin (n + 2)) :
    let k := 𝒰.strictInsertPosition σ i hi
    let hi' := 𝒰.not_mem_strictSupport_strictDelete_of_not_mem σ i hi j
    𝒰.strictDelete (k.succAbove j) (𝒰.strictInsert σ i hi) =
      𝒰.strictInsert (𝒰.strictDelete j σ) i hi' := by
  dsimp only
  let ρ := 𝒰.strictInsert σ i hi
  let k := 𝒰.strictInsertPosition σ i hi
  let l := k.succAbove j
  let τ := 𝒰.strictDelete l ρ
  let m := j.predAbove k
  have hdelete : 𝒰.strictDelete m τ = 𝒰.strictDelete j σ :=
    𝒰.strictDelete_strictInsert_succAbove σ i hi j
  have hvalue : τ m = i :=
    𝒰.strictDelete_strictInsert_value σ i hi j
  let hi' := 𝒰.not_mem_strictSupport_strictDelete_of_not_mem σ i hi j
  let hcard :
      (insert i (𝒰.strictSupport (𝒰.strictDelete j σ))).card = n + 2 := by
    rw [Finset.card_insert_of_notMem hi', 𝒰.card_strictSupport]
  change τ =
    (insert i (𝒰.strictSupport (𝒰.strictDelete j σ))).orderEmbOfFin hcard
  apply Finset.orderEmbOfFin_unique'
  intro a
  refine Fin.succAboveCases m ?_ (fun b ↦ ?_) a
  · rw [hvalue]
    exact Finset.mem_insert_self _ _
  · have hb := congrArg (fun θ : 𝒰.StrictTuple n ↦ θ b) hdelete
    rw [show τ (m.succAbove b) = 𝒰.strictDelete j σ b by
      simpa only [strictDelete, OrderEmbedding.coe_comp, Function.comp_apply,
        Fin.succAboveOrderEmb_apply] using hb]
    exact Finset.mem_insert_of_mem
      ((𝒰.mem_strictSupport_iff _ _).2 ⟨b, rfl⟩)

/-- The insertion position after a noninserted deletion is obtained with `Fin.predAbove`. -/
theorem strictInsertPosition_after_strictDelete {n : ℕ} (σ : 𝒰.StrictTuple (n + 1))
    (i : Fin 𝒰.card) (hi : i ∉ 𝒰.strictSupport σ) (j : Fin (n + 2)) :
    let k := 𝒰.strictInsertPosition σ i hi
    let hi' := 𝒰.not_mem_strictSupport_strictDelete_of_not_mem σ i hi j
    𝒰.strictInsertPosition (𝒰.strictDelete j σ) i hi' = j.predAbove k := by
  dsimp only
  let ρ := 𝒰.strictInsert σ i hi
  let k := 𝒰.strictInsertPosition σ i hi
  let l := k.succAbove j
  let τ := 𝒰.strictDelete l ρ
  let m := j.predAbove k
  have hvalue : τ m = i :=
    𝒰.strictDelete_strictInsert_value σ i hi j
  let hi' := 𝒰.not_mem_strictSupport_strictDelete_of_not_mem σ i hi j
  have heq : τ = 𝒰.strictInsert (𝒰.strictDelete j σ) i hi' :=
    𝒰.strictDelete_strictInsert_eq_insert σ i hi j
  have happly :=
    𝒰.strictInsert_apply_position (𝒰.strictDelete j σ) i hi'
  apply τ.injective
  calc
    τ (𝒰.strictInsertPosition (𝒰.strictDelete j σ) i hi') =
        𝒰.strictInsert (𝒰.strictDelete j σ) i hi'
          (𝒰.strictInsertPosition (𝒰.strictDelete j σ) i hi') :=
      congrArg
        (fun θ : 𝒰.StrictTuple (n + 1) ↦
          θ (𝒰.strictInsertPosition (𝒰.strictDelete j σ) i hi'))
        heq
    _ = i := happly
    _ = τ m := hvalue.symm

end Presheaf.Family

end Rigid.Cech
