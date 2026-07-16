module

public import ModalLogicArchive.Modal.Modality.Basic
public import ModalLogicArchive.Modal.Kripke.Logic.S5

@[expose] public section

namespace LO.Modal


namespace S5

set_option linter.style.multiGoal false

variable {m m₁ m₂ : Modality} {n}

open Entailment
open Modality
open Formula
open Kripke
open Modalities

protected abbrev modalities : Modalities := {-, ∼, □, ◇, ∼□, ∼◇}

lemma modal_reduction_0 : ModalReduction Modal.S5 0 Modal.S5.modalities := ModalReduction.reducible_0_of_mem $ by simp;

lemma modal_reduction_1 : ModalReduction Modal.S5 1 Modal.S5.modalities := ModalReduction.reducible_1_of_mem (by simp) (by simp) (by simp)

instance : Entailment.S5 Modal.S5 where
instance : Entailment.S4 Modal.S5 where
  Four _ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Entailment.WeakerThan.pbl (𝓢 := Modal.S4);
    simp;

instance : (□□) ≅[Modal.S5] (□) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0); simp;
  . apply translation_of_axiomInstance (a := 0);
    apply Entailment.WeakerThan.pbl (𝓢 := Modal.S4);
    simp;
instance : (□◇) ≅[Modal.S5] (◇) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0); simp;
  . apply translation_of_axiomInstance (a := 0); simp;
instance : (◇◇) ≅[Modal.S5] (◇) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0);
    exact axiomFourDual;
  . apply translation_of_axiomInstance (a := 0);
    simp;
instance : (◇□) ≅[Modal.S5] (□) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0); simp;
  . apply translation_of_axiomInstance (a := 0); simp;

lemma modal_reduction_2 : ModalReduction Modal.S5 2 S5.modalities := by
  apply ModalReduction.of_allOfSize;
  intro m hm;
  simp only [
    allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union,
    Finset.mem_image, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left
  ] at hm;
  rcases hm with (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl);
  . reduce_to (-);
  . reduce_to (∼□);
  . reduce_to (∼◇);
  . reduce_to (∼◇);
  . reduce_to (□);
  . reduce_to (◇);
  . reduce_to (∼□);
  . reduce_to (□);
  . reduce_to (◇);

instance : (∼□∼) ≅[Modal.S5] (◇)  := by trans (∼∼◇); exact equivalence_expand_left (□∼) (∼◇) (∼); exact equivalence_expand_right (∼∼) (-) (◇)
instance : (∼□□) ≅[Modal.S5] (∼□) := equivalence_expand_left (□□) (□) (∼)
instance : (∼◇◇) ≅[Modal.S5] (∼◇) := equivalence_expand_left (◇◇) (◇) (∼)
instance : (∼□◇) ≅[Modal.S5] (∼◇) := equivalence_expand_left (□◇) (◇) (∼)
instance : (∼◇□) ≅[Modal.S5] (∼□) := equivalence_expand_left (◇□) (□) (∼)
instance : (◇∼∼) ≅[Modal.S5] (◇)  := by trans (∼□∼); exact equivalence_expand_right (◇∼) (∼□) (∼); infer_instance;
instance : (◇∼□) ≅[Modal.S5] (∼□) := by trans (∼□□); exact equivalence_expand_right (◇∼) (∼□) (□); exact equivalence_expand_left (□□) (□) (∼)
instance : (◇∼◇) ≅[Modal.S5] (∼◇) := by trans (∼□◇); exact equivalence_expand_right (◇∼) (∼□) (◇); infer_instance;
instance : (◇□□) ≅[Modal.S5] (□)  := by trans (◇□); exact equivalence_expand_left (□□) (□) (◇); infer_instance;
instance : (◇□◇) ≅[Modal.S5] (◇)  := by trans (◇◇); exact equivalence_expand_left (□◇) (◇) (◇);  infer_instance;
instance : (◇□∼) ≅[Modal.S5] (∼◇) := by trans (□∼); exact equivalence_expand_right (◇□) (□) (∼); infer_instance;
instance : (◇◇∼) ≅[Modal.S5] (∼□) := by trans (◇∼); exact equivalence_expand_right (◇◇) (◇) (∼); infer_instance;
instance : (◇◇□) ≅[Modal.S5] (◇□) := by trans (◇□); exact equivalence_expand_right (◇◇) (◇) (□); infer_instance;
instance : (◇◇◇) ≅[Modal.S5] (◇)  := by trans (◇◇); exact equivalence_expand_left (◇◇) (◇) (◇); infer_instance;

lemma modal_reduction_3 : ModalReduction Modal.S5 3 S5.modalities := by
  intro m hm;
  rcases split_left₁' hm with ⟨m₂, hm₂, (rfl | rfl | rfl)⟩;
  . obtain ⟨m', _, _⟩ := modal_reduction_2 m₂ hm₂;
    use m';
    constructor;
    . assumption;
    . trans m₂;
      . apply translation_expand_right (□) (-);
      . assumption;
  . rcases split_left₁' hm₂ with ⟨m₂, hm₂', (rfl | rfl | rfl)⟩;
    . rcases iff_size_1.mp hm₂' with (rfl | rfl | rfl);
      . reduce_to (□);
      . reduce_to (◇);
      . reduce_to (∼◇);
    . obtain ⟨m', _, _⟩ := modal_reduction_2 (◇m₂) (by simpa);
      use m';
      constructor;
      . assumption;
      . trans (◇m₂)
        . apply translation_expand_right (◇◇) (◇);
        . assumption;
    . rcases iff_size_1.mp hm₂' with (rfl | rfl | rfl);
      . reduce_to (∼□);
      . reduce_to (∼◇);
      . reduce_to (◇);
  . obtain ⟨m₁, m₂, hm₁, hm₂', rfl⟩ := split_left₁ hm₂;
    rcases iff_size_1.mp hm₁ with (rfl | rfl | rfl);
    . rcases iff_size_1.mp hm₂' with (rfl | rfl | rfl);
      . reduce_to (∼□);
      . reduce_to (∼◇);
      . reduce_to (◇);
    . rcases iff_size_1.mp hm₂' with (rfl | rfl | rfl);
      . reduce_to (∼□);
      . reduce_to (∼◇);
      . reduce_to (□);
    . use m₂;
      constructor;
      . rcases iff_size_1.mp hm₂' with (rfl | rfl | rfl) <;> tauto;
      . apply translation_expand_right (∼∼) (-);

theorem modal_reduction : ∀ n, ModalReduction Modal.S5 n S5.modalities := ModalReduction.forall_of_reducible_to_max (by simp) $ by
  intro n hn;
  match n with
  | 0 => exact modal_reduction_0;
  | 1 => exact modal_reduction_1;
  | 2 => exact modal_reduction_2;
  | 3 => exact modal_reduction_3;

end S5

end LO.Modal
end
