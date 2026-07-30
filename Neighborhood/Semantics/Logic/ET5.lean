module

public import Neighborhood.Semantics.Logic.ENT4
public import Neighborhood.Semantics.Logic.E5

/-!
# The neighborhood logic `LogicET5`

Soundness, consistency and completeness of `LogicET5`, the classical modal logic axiomatised by
the reflexivity axiom `T` and the euclideanness axiom `Five` over `LogicE`, with respect to the
neighborhood frames that are both reflexive and euclidean. Also proves the strict inclusions of
`LogicENT4` and `LogicE5` in `LogicET5`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicET5.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive] [F.IsEuclidean] :
    A ∈ LogicET5 → F ⊧ A :=
  Hilbert.sound (by
    rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact valid_axiomT_of_isReflexive
    · exact valid_axiomFive_of_isEuclidean)

theorem LogicET5.consistent : (@LogicET5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicET5.sound Frame.simple_blackhole hC

instance : (@LogicET5 α).HasAxiomN :=
  ⟨have hiff : (⊤ : Formula α) 🡘 ◇⊤ ∈ (@LogicET5 α) :=
      Logic.E_intro Logic.diaTc (Logic.C_of_conseq Logic.verum)
   Logic.C_of_E_mpr (Logic.re hiff) ⨀ (Logic.axiomFive ⨀ (Logic.diaTc ⨀ Logic.verum))⟩

instance : Nonempty (MaximalConsistentSet (@LogicET5 α)) :=
  MaximalConsistentSet.nonempty LogicET5.consistent

section

variable [DecidableEq α]

omit [DecidableEq α] in
theorem LogicET5.hasAxiomFour : Axioms.Four A ∈ (@LogicET5 α) :=
  have h1 : (□A : Formula α) 🡒 ◇□A ∈ (@LogicET5 α) := Logic.diaTc
  have h2 : ◇□A 🡒 (□A : Formula α) ∈ (@LogicET5 α) :=
    (Logic.hasAxiomGeachSwap (L := @LogicET5 α) (g := ⟨1, 1, 0, 1⟩)).Geach A
  have hiff : (□A : Formula α) 🡘 ◇□A ∈ (@LogicET5 α) := Logic.E_intro h1 h2
  Logic.C_trans (Logic.C_trans h1 Logic.axiomFive)
    (Logic.C_of_E_mp (Logic.re (Logic.E_symm hiff)))

instance : (basicCanonicity (@LogicET5 α)).toModel.IsEuclidean := by
  apply Canonicity.isEuclidean'
  intro X hX
  have hbox : (basicCanonicity (@LogicET5 α)).toModel.box X = ∅ := by
    ext Ω
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hΩ => basicCanonicity.not_isNonproofset_of_mem_box hΩ hX
  rw [hbox]
  simp [Frame.dia, Frame.contains_unit]

theorem LogicET5.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → [F.IsEuclidean] → F ⊧ A) :
    A ∈ @LogicET5 α :=
  (basicCanonicity LogicET5).mem_of_valid
    (h (basicCanonicity LogicET5).toModel.toFrame (basicCanonicity LogicET5).toModel.Val)

end

theorem LogicENT4_ssubset_LogicET5 : @LogicENT4 ℕ ⊂ LogicET5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact Logic.axiomN
    · exact Logic.axiomT
    · exact LogicET5.hasAxiomFour
  · intro h
    have hFive : Axioms.Five (.atom 0) ∈ @LogicENT4 ℕ := h Logic.axiomFive
    let F : Frame (Fin 3) := ⟨fun x => {{x}, Set.univ}⟩
    haveI : F.ContainsUnit := ⟨by
      ext x
      simp only [Frame.box, F, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      right; rfl⟩
    have hbox_univ : F.box (Set.univ : Set (Fin 3)) = Set.univ := F.contains_unit
    have hbox_singleton : ∀ a : Fin 3, F.box ({a} : Set (Fin 3)) = {a} := by
      intro a
      have hne : ({a} : Set (Fin 3)) ≠ Set.univ := by
        obtain ⟨b, hb⟩ := exists_ne a
        intro heq
        exact hb (show b ∈ ({a} : Set (Fin 3)) by rw [heq]; exact Set.mem_univ b)
      ext y
      simp only [Frame.box, F, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.singleton_eq_singleton_iff]
      constructor
      · rintro (h | h)
        · exact h.symm
        · exact absurd h hne
      · rintro rfl
        left; rfl
    haveI : F.IsReflexive := ⟨by
      intro X x hx
      simp only [Frame.box, F, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rfl
      · trivial⟩
    haveI : F.IsTransitive := ⟨by
      intro X x hx
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      simp only [Frame.box, F, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp [hbox_singleton]
      · simp [hbox_univ]⟩
    have hE : F.IsEuclidean := isEuclidean_of_valid_axiomFive (LogicENT4.sound F hFive)
    have hdia : F.dia ({0, 1} : Set (Fin 3)) = {0, 1} := by
      simp only [Set.ext_iff, Frame.dia, Frame.box, F, Set.mem_compl_iff, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      decide
    have hbox : F.box ({0, 1} : Set (Fin 3)) = ∅ := by
      simp only [Set.ext_iff, Frame.box, F, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, Set.mem_empty_iff_false]
      decide
    have h2 := hE.eucl {0, 1}
    rw [hdia, hbox] at h2
    exact (Set.nonempty_of_mem (Set.mem_insert 0 {1})).ne_empty (Set.subset_empty_iff.mp h2)

theorem LogicE5_ssubset_LogicET5 : @LogicE5 ℕ ⊂ LogicET5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hT : Axioms.T (.atom 0) ∈ @LogicE5 ℕ := h Logic.axiomT
    haveI : (⟨fun _ => Set.univ⟩ : Frame (Fin 1)).IsEuclidean :=
      ⟨fun X => by simp [Frame.box, Frame.dia]⟩
    have hR := isReflexive_of_valid_axiomT
      (LogicE5.sound (⟨fun _ => Set.univ⟩ : Frame (Fin 1)) hT)
    have := hR.refl (∅ : Set (Fin 1)) (show (0 : Fin 1) ∈ _ by simp [Frame.box])
    simp at this

end
