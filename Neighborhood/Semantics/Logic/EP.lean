module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomGeach
public import Neighborhood.Hilbert.Logics
public import Neighborhood.Semantics.Logic.E

/-!
# The neighborhood logic `LogicEP`

Soundness and consistency of `LogicEP`, the classical modal logic axiomatised by the
possibility axiom `P := ∼□⊥`, with respect to the neighborhood frames in which no world has the
empty set as one of its neighborhoods (`Frame.NotContainsEmpty`). Also its strict inclusion in
`LogicE`, and that `D` is not among its theorems.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

/-- `LogicEP` is sound with respect to every frame in which no world has the empty set as one
of its neighborhoods. -/
theorem LogicEP.sound (h : A ∈ LogicEP) {κ} [Nonempty κ] (F : Frame κ) [F.NotContainsEmpty] :
    F ⊧ A :=
  Hilbert.sound
    (fun B hB => by
      simp only [Set.mem_singleton_iff] at hB; subst hB
      exact valid_axiomP_of_notContainsEmpty) h

instance : (@LogicEP α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (fun B hB => by
      simp only [Set.mem_singleton_iff] at hB; subst hB
      exact valid_axiomP_of_notContainsEmpty)

/-! ### Strict inclusion in `LogicE`, and unprovability of `D` -/

theorem LogicE_ssubset_LogicEP : @LogicE ℕ ⊂ LogicEP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hP : (Axioms.P : Formula ℕ) ∈ @LogicE ℕ := h (ProvableHilbert.axm rfl)
    have := notContainsEmpty_of_valid_axiomP
      (F := (⟨fun _ => {∅}⟩ : Frame (Fin 1))) (LogicE.sound hP _)
    simpa using this.not_contains_empty (x := 0)

/-- A two-world frame with no empty neighborhood that is not serial: witnesses that `D` is not a
theorem of `LogicEP`. -/
abbrev Frame.trivial_nonserial : Frame (Fin 2) :=
  ⟨fun w => match w with | 0 => {{0}} | 1 => {{0}, {1}, {0, 1}}⟩

instance : Frame.trivial_nonserial.NotContainsEmpty :=
  ⟨fun x => by match x with | 0 => simp | 1 => simp; tauto_set⟩

lemma Frame.trivial_nonserial.not_isSerial : ¬Frame.trivial_nonserial.IsSerial := by
  intro hS
  have h1 : (1 : Fin 2) ∈ Frame.trivial_nonserial.box {1} := by simp [Frame.box]
  have h2 : (1 : Fin 2) ∉ Frame.trivial_nonserial.dia {1} := by simp [Frame.dia, Frame.box]
  exact h2 (hS.serial {1} h1)

theorem LogicEP.not_mem_axiomD {a : ℕ} : Axioms.D (.atom a) ∉ @LogicEP ℕ :=
  Hilbert.not_mem_of_not_valid (F := Frame.trivial_nonserial)
    (fun B hB => by
      simp only [Set.mem_singleton_iff] at hB; subst hB
      exact valid_axiomP_of_notContainsEmpty)
    (fun h => Frame.trivial_nonserial.not_isSerial (isSerial_of_valid_axiomD h))

end
