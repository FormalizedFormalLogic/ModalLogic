module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev frame_2_72 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {Set.univ}
    | 1 => {{1}}⟩

instance : frame_2_72.IsReflexive := ⟨by
  intro X x
  match x with
  | 0 => intro hx; simp_all [Frame.box]
  | 1 => intro hx; simp_all [Frame.box]⟩

lemma frame_2_72.not_isTransitive : ¬frame_2_72.IsTransitive := fun hT => by
  have h0 : (0 : Fin 2) ∈ frame_2_72.box Set.univ := by simp [Frame.box]
  have h1 := hT.trans Set.univ h0
  simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id_eq,
    Frame.box, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.ext_iff] at h1
  have h2 := h1 1
  simp at h2
  have h3 : (0 : Fin 2) ∈ ({1} : Set (Fin 2)) := h2 ▸ Set.mem_univ 0
  simp at h3

end
