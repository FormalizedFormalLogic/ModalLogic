module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Semantics.Completeness
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Hilbert.Logics
public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.EK
import Mathlib.Tactic.FinCases

/-!
# The neighborhood logic `LogicEMC`

Soundness, consistency and completeness of `LogicEMC`, the classical modal logic axiomatised by
the monotonicity axiom `M` and the regularity axiom `C`, with respect to the neighborhood frames
that are both monotonic and regular, and its strict inclusion of `LogicEM`, `LogicEC` and
`LogicEK`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

/-! ### Soundness, consistency and completeness -/

/-- `LogicEMC` is sound with respect to every monotonic and regular neighborhood frame. -/
theorem LogicEMC.sound (h : A ∈ LogicEMC) {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] : F ⊧ A :=
  Hilbert.sound (by
    rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomC_of_isRegular) h

instance : (@LogicEMC α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole) (by
    rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomC_of_isRegular)

variable [DecidableEq α]

/-- `LogicEMC` is complete with respect to all monotonic and regular neighborhood frames. -/
theorem LogicEMC.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsMonotonic → F.IsRegular → F ⊧ A) :
    A ∈ @LogicEMC α :=
  (supplementedBasicCanonicity LogicEMC).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMC).toModel.toFrame inferInstance inferInstance
      (supplementedBasicCanonicity LogicEMC).toModel.Val)

/-! ### Strict inclusion of `LogicEM` -/

/-- A monotonic frame on two worlds that refutes the regularity axiom `C`. -/
abbrev Frame.counterframe_axiomC₁ : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}, {1}, {0, 1}}
    | 1 => {{1}, {0, 1}}⟩

lemma Frame.counterframe_axiomC₁.box_mono {X Y : Set (Fin 2)} (h : X ⊆ Y) :
    Frame.counterframe_axiomC₁.box X ⊆ Frame.counterframe_axiomC₁.box Y := by
  intro w hw
  fin_cases w <;>
    simp only [Frame.box, Frame.counterframe_axiomC₁, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢ <;>
    rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
    simp_all; grind

instance : Frame.counterframe_axiomC₁.IsMonotonic where
  mono _ _ := Set.subset_inter
    (Frame.counterframe_axiomC₁.box_mono Set.inter_subset_left)
    (Frame.counterframe_axiomC₁.box_mono Set.inter_subset_right)

@[simp]
lemma Frame.counterframe_axiomC₁.not_valid_axiomC :
    ¬Frame.counterframe_axiomC₁ ⊧ (Axioms.C (.atom 0) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0} | 1 => {1} | _ => Set.univ, 0, by
      unfold NotForces Forces; simp [Frame.box, Frame.counterframe_axiomC₁, Set.ext_iff]⟩

theorem LogicEM_ssubset_LogicEMC : @LogicEM ℕ ⊂ LogicEMC := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hC : Axioms.C (.atom 0) (.atom 1) ∈ @LogicEM ℕ :=
      h (ProvableHilbert.axm (Or.inr ⟨_, _, rfl⟩))
    exact Frame.counterframe_axiomC₁.not_valid_axiomC (LogicEM.sound hC Frame.counterframe_axiomC₁)

/-! ### Strict inclusion of `LogicEC` -/

/-- A regular frame on three worlds that refutes the monotonicity axiom `M`. -/
abbrev Frame.counterframe_axiomM₁ : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{1}}
    | 1 => {{0}, {0, 1}}
    | 2 => {{0}, {1, 2}, ∅}⟩

instance : Frame.counterframe_axiomM₁.IsRegular where
  regular X Y w hw := by
    fin_cases w <;>
      simp only [Frame.box, Frame.counterframe_axiomM₁, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      grind

@[simp]
lemma Frame.counterframe_axiomM₁.not_valid_axiomM :
    ¬Frame.counterframe_axiomM₁ ⊧ (Axioms.M (.atom 0) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {1, 2} | _ => Set.univ, 0, by
      unfold NotForces Forces; simp [Frame.box, Frame.counterframe_axiomM₁, Set.ext_iff]; decide⟩

theorem LogicEC_ssubset_LogicEMC : @LogicEC ℕ ⊂ LogicEMC := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M (.atom 0) (.atom 1) ∈ @LogicEC ℕ :=
      h (ProvableHilbert.axm (Or.inl ⟨_, _, rfl⟩))
    exact Frame.counterframe_axiomM₁.not_valid_axiomM (LogicEC.sound hM Frame.counterframe_axiomM₁)

/-! ### Strict inclusion of `LogicEK` -/

/-- A frame on four worlds satisfying the `K`-property, refuting both the monotonicity axiom `M`
and the regularity axiom `C`. -/
abbrev Frame.EK_counterframe_for_M_and_C : Frame (Fin 4) := ⟨fun _ => {{0, 1}, {0, 2}}⟩

instance : Frame.EK_counterframe_for_M_and_C.HasPropertyK where
  K X Y := by
    rintro w ⟨hw₁, hw₂⟩
    simp only [Frame.box, Frame.EK_counterframe_for_M_and_C, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hw₁ hw₂
    exfalso
    rcases hw₂ with rfl | rfl <;>
      rcases hw₁ with h | h <;>
      · have h3 := Set.ext_iff.mp h 3
        simp at h3

@[simp]
lemma Frame.EK_counterframe_for_M_and_C.not_valid_axiomC :
    ¬Frame.EK_counterframe_for_M_and_C ⊧ (Axioms.C (.atom 0) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {0, 2} | _ => ∅, 0, by
      unfold NotForces Forces
      simp [Frame.box, Frame.EK_counterframe_for_M_and_C, Set.ext_iff]⟩

@[simp]
lemma Frame.EK_counterframe_for_M_and_C.not_valid_axiomM :
    ¬Frame.EK_counterframe_for_M_and_C ⊧
      (Axioms.M ((.atom 0) ⋎ (.atom 1)) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {0, 2} | _ => ∅, 0, by
      unfold NotForces Forces
      simp [Frame.box, Frame.EK_counterframe_for_M_and_C, Set.ext_iff]
      decide⟩

theorem LogicEK_ssubset_LogicEMC : @LogicEK ℕ ⊂ LogicEMC := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ⟨A, B, rfl⟩
    exact Logic.axiomK_of_MC
  · intro h
    have hC : Axioms.C (.atom 0) (.atom 1) ∈ @LogicEK ℕ :=
      h (ProvableHilbert.axm (Or.inr ⟨_, _, rfl⟩))
    exact Frame.EK_counterframe_for_M_and_C.not_valid_axiomC
      (LogicEK.sound hC Frame.EK_counterframe_for_M_and_C)

end
