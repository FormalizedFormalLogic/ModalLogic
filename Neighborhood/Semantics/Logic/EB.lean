module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Semantics.AxiomGeach
public import Neighborhood.Hilbert.Logics
public import Neighborhood.Semantics.Logic.E

/-!
# The neighborhood logic `LogicEB`

Soundness and consistency of `LogicEB`, the classical modal logic axiomatised by the symmetry
axiom `B`, with respect to the symmetric neighborhood frames, and its strict inclusion in
`LogicE`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

/-- The one-world frame `Frame.simple_blackhole` is symmetric. -/
instance : Frame.simple_blackhole.IsSymmetric := by
  constructor
  intro X x hx
  have hne : Xᶜ ≠ Set.univ := by
    simp only [ne_eq, Set.compl_univ_iff]
    rintro rfl
    simp at hx
  simp [Frame.box, Frame.dia, hne]

/-- `LogicEB` is sound with respect to every symmetric neighborhood frame. -/
theorem LogicEB.sound (h : A ∈ LogicEB) {κ} [Nonempty κ] (F : Frame κ) [F.IsSymmetric] : F ⊧ A :=
  Hilbert.sound (fun _ hB => by obtain ⟨_, rfl⟩ := hB; exact valid_axiomB_of_isSymmetric) h

instance : (@LogicEB α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (fun _ hB => by obtain ⟨_, rfl⟩ := hB; exact valid_axiomB_of_isSymmetric)

/-! ### Strict inclusion of `LogicE` -/

theorem LogicE_ssubset_LogicEB : (@LogicE ℕ) ⊂ LogicEB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hB : Axioms.B (.atom 0) ∈ (@LogicE ℕ) := h (ProvableHilbert.axm ⟨_, rfl⟩)
    have hS : Frame.simple_whitehole.IsSymmetric := isSymmetric_of_valid_axiomB (LogicE.sound hB _)
    have := hS.symm {()} (show () ∈ _ by simp)
    simp [Frame.box] at this

end
