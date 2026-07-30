module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.Logic.EMNP
public import Neighborhood.Semantics.Example.Frame2_238

/-!
# The neighborhood logic `LogicEMND`

Soundness, consistency and completeness of `LogicEMND`, the classical modal logic axiomatised by
the monotonicity axiom `M`, `N := □⊤` and the seriality axiom `D` over `LogicE`, with respect to
the monotonic and serial neighborhood frames that contain their unit. Also its strict inclusion of
`LogicEMNP`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMND.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.ContainsUnit]
    [F.IsSerial] :
    A ∈ LogicEMND → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMND.consistent : (@LogicEMND α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMND.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMND α)) :=
  MaximalConsistentSet.nonempty LogicEMND.consistent

variable [DecidableEq α]

theorem LogicEMND.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicEMND α :=
  (supplementedBasicCanonicity LogicEMND).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMND).toModel.toFrame
      (supplementedBasicCanonicity LogicEMND).toModel.Val)

theorem LogicEMNP_ssubset_LogicEMND : @LogicEMNP ℕ ⊂ LogicEMND := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomP_of_ND
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEMNP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_238.not_valid_axiomD (LogicEMNP.sound frame_2_238 hD)

end
