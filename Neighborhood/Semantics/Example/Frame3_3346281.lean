module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach
import Mathlib.Tactic.FinCases

@[expose] public section

variable {α : Type u}
variable {a b : α}

abbrev frame_3_3346281 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {∅, {0, 1}, {0, 2}, {1, 2}}
    | 1 => {∅, {0}, {1}, {0, 1}}
    | 2 => {∅, {0}, {2}, {0, 2}}⟩

lemma frame_3_3346281.box_empty :
    frame_3_3346281.box (∅ : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_3346281]

/-- Boxing a literal subset of the frame is decided by whether `w`'s neighbourhood set contains
that literal subset; the tail tactic discharges the cases where it does not, by comparing the
two sides pointwise. -/
lemma frame_3_3346281.box_zero :
    frame_3_3346281.box ({0} : Set (Fin 3)) = {1, 2} := by
  apply Set.Subset.antisymm <;>
    (intro w hw; fin_cases w <;> simp_all [Frame.box, frame_3_3346281] <;>
      (simp only [Set.ext_iff] at hw; revert hw; decide))

lemma frame_3_3346281.box_one :
    frame_3_3346281.box ({1} : Set (Fin 3)) = {1} := by
  apply Set.Subset.antisymm <;>
    (intro w hw; fin_cases w <;> simp_all [Frame.box, frame_3_3346281] <;>
      (simp only [Set.ext_iff] at hw; revert hw; decide))

lemma frame_3_3346281.box_two :
    frame_3_3346281.box ({2} : Set (Fin 3)) = {2} := by
  apply Set.Subset.antisymm <;>
    (intro w hw; fin_cases w <;> simp_all [Frame.box, frame_3_3346281] <;>
      (simp only [Set.ext_iff] at hw; revert hw; decide))

lemma frame_3_3346281.box_zero_one :
    frame_3_3346281.box ({0, 1} : Set (Fin 3)) = {0, 1} := by
  apply Set.Subset.antisymm <;>
    (intro w hw; fin_cases w <;> simp_all [Frame.box, frame_3_3346281] <;>
      (simp only [Set.ext_iff] at hw; revert hw; decide))

lemma frame_3_3346281.box_zero_two :
    frame_3_3346281.box ({0, 2} : Set (Fin 3)) = {0, 2} := by
  apply Set.Subset.antisymm <;>
    (intro w hw; fin_cases w <;> simp_all [Frame.box, frame_3_3346281] <;>
      (simp only [Set.ext_iff] at hw; revert hw; decide))

lemma frame_3_3346281.box_one_two :
    frame_3_3346281.box ({1, 2} : Set (Fin 3)) = {0} := by
  apply Set.Subset.antisymm <;>
    (intro w hw; fin_cases w <;> simp_all [Frame.box, frame_3_3346281] <;>
      (simp only [Set.ext_iff] at hw; revert hw; decide))

lemma frame_3_3346281.box_univ :
    frame_3_3346281.box (Set.univ : Set (Fin 3)) = ∅ := by
  apply Set.Subset.antisymm <;>
    (intro w hw; fin_cases w <;> simp_all [Frame.box, frame_3_3346281] <;>
      (simp only [Set.ext_iff] at hw; revert hw; decide))

instance : frame_3_3346281.IsSerial := ⟨fun X w hw => by
  simp only [Frame.dia, Frame.box, frame_3_3346281, Set.mem_compl_iff, Set.mem_setOf_eq]
  simp only [Frame.box, frame_3_3346281, Set.mem_setOf_eq] at hw
  fin_cases w <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢ <;>
    rcases hw with rfl | rfl | rfl | rfl <;>
      (rintro h; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.ext_iff] at h;
        revert h; decide)⟩

lemma frame_3_3346281.compl_zero : ({0} : Set (Fin 3))ᶜ = {1, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_3346281.compl_one : ({1} : Set (Fin 3))ᶜ = {0, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_3346281.compl_two : ({2} : Set (Fin 3))ᶜ = {0, 1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_3346281.compl_zero_one : ({0, 1} : Set (Fin 3))ᶜ = {2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_3346281.compl_zero_two : ({0, 2} : Set (Fin 3))ᶜ = {1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_3346281.compl_one_two : ({1, 2} : Set (Fin 3))ᶜ = {0} := by
  ext i; fin_cases i <;> simp

instance : frame_3_3346281.IsSymmetric := ⟨fun X => by
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [Frame.dia, frame_3_3346281.box_empty]
  · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [Frame.dia, frame_3_3346281.compl_zero_one, frame_3_3346281.box_two,
      frame_3_3346281.compl_two, frame_3_3346281.box_zero_one]
  · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [Frame.dia, frame_3_3346281.compl_zero_two, frame_3_3346281.box_one,
      frame_3_3346281.compl_one, frame_3_3346281.box_zero_two]
  · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [Frame.dia, frame_3_3346281.compl_zero, frame_3_3346281.box_one_two]
  · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [Frame.dia, frame_3_3346281.compl_one_two, frame_3_3346281.box_zero]
  · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [Frame.dia, frame_3_3346281.compl_one, frame_3_3346281.box_zero_two,
      frame_3_3346281.compl_zero_two, frame_3_3346281.box_one]
  · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [Frame.dia, frame_3_3346281.compl_two, frame_3_3346281.box_zero_one,
      frame_3_3346281.compl_zero_one, frame_3_3346281.box_two]
  · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [Frame.dia, frame_3_3346281.box_univ]⟩

lemma frame_3_3346281.not_isRegular :
    ¬frame_3_3346281.IsRegular := by
  intro hR
  have h := hR.regular ({0, 1} : Set (Fin 3)) ({0, 2} : Set (Fin 3))
  have h0 : (0 : Fin 3) ∈ frame_3_3346281.box {0, 1} ∩ frame_3_3346281.box {0, 2} := by
    rw [frame_3_3346281.box_zero_one, frame_3_3346281.box_zero_two]; simp
  have hmem := h h0
  have heq : ({0, 1} : Set (Fin 3)) ∩ {0, 2} = {0} := by ext i; fin_cases i <;> simp
  rw [heq, frame_3_3346281.box_zero] at hmem
  simp at hmem

lemma frame_3_3346281.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_3346281 ⊧ (Axioms.C #a #b : Formula α) := by
  intro hv
  apply frame_3_3346281.not_isRegular
  constructor
  rintro X Y x ⟨hX, hY⟩
  have h₂ := hv (fun c => if c = a then X else if c = b then Y else ∅) x
  rw [forces_imp, forces_and, forces_box, forces_box, forces_box, Model.truthset.eq_and] at h₂
  simp only [Model.truthset.eq_atom, if_neg (Ne.symm hab)] at h₂
  exact h₂ ⟨hX, hY⟩

end
