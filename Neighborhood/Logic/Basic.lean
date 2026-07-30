module

public import Neighborhood.Axioms

/-!
# Logics

A logic is a set of formulas, and provability in a logic is membership. This file sets up the
provability notation, closure under substitution, consistency, and the comparison relations
`⪯`, `⪱`, `≊` and `Incomparable` between logics.
-/

@[expose] public section

namespace LO.Modal

/-- A logic, i.e. a set of formulas regarded as the set of its theorems. -/
abbrev Logic := Set Formula

namespace Logic

/-- `φ` is provable in `L`. -/
def Provable (L : Logic) (φ : Formula) : Prop := φ ∈ L

/-- `φ` is not provable in `L`. -/
abbrev Unprovable (L : Logic) (φ : Formula) : Prop := ¬L.Provable φ

end Logic

@[inherit_doc] infix:45 " ⊢ " => Logic.Provable
@[inherit_doc] infix:45 " ⊬ " => Logic.Unprovable

namespace Logic

/-- Every formula of `T` is provable in `L`. -/
def ProvableSet (L : Logic) (T : Set Formula) : Prop := ∀ {φ}, φ ∈ T → L ⊢ φ

end Logic

@[inherit_doc] infix:45 " ⊢* " => Logic.ProvableSet

namespace Logic

variable {L L₁ L₂ L₃ : Logic} {φ ψ : Formula} {T : Set Formula}

@[grind =] lemma iff_provable : L ⊢ φ ↔ φ ∈ L := Iff.rfl

@[grind =] lemma iff_unprovable : L ⊬ φ ↔ φ ∉ L := Iff.rfl

@[grind =] lemma iff_provableSet : L ⊢* T ↔ T ⊆ L := Iff.rfl

/-- Closure of a logic under substitution. -/
protected class Substitution (L : Logic) where
  subst : ∀ {φ : Formula} (s : Modal.Substitution), L ⊢ φ → L ⊢ φ⟦s⟧

export LO.Modal.Logic.Substitution (subst)
attribute [grind <=] Logic.Substitution.subst

/-! ### Provability strength -/

/-- Everything provable in `L₁` is provable in `L₂`. -/
class WeakerThan (L₁ L₂ : Logic) : Prop where
  subset : L₁ ⊆ L₂

@[inherit_doc] infix:40 " ⪯ " => Logic.WeakerThan

/-- `L₁` is weaker than `L₂` and not conversely. -/
class StrictlyWeakerThan (L₁ L₂ : Logic) : Prop where
  weakerThan : L₁ ⪯ L₂
  notWT : ¬L₂ ⪯ L₁

@[inherit_doc] infix:40 " ⪱ " => Logic.StrictlyWeakerThan

/-- `L₁` and `L₂` prove the same formulas. -/
class Equiv (L₁ L₂ : Logic) : Prop where
  eq : L₁ = L₂

@[inherit_doc] infix:40 " ≊ " => Logic.Equiv

/-- Neither of `L₁` and `L₂` is weaker than the other. -/
class Incomparable (L₁ L₂ : Logic) where
  notWT₁ : ¬L₁ ⪯ L₂
  notWT₂ : ¬L₂ ⪯ L₁

section

@[instance, simp, refl] protected lemma WeakerThan.refl (L : Logic) : L ⪯ L := ⟨Set.Subset.refl _⟩

lemma WeakerThan.wk (h : L₁ ⪯ L₂) : L₁ ⊢ φ → L₂ ⊢ φ := @h.subset φ

lemma WeakerThan.pbl [h : L₁ ⪯ L₂] : L₁ ⊢ φ → L₂ ⊢ φ := @h.subset φ

@[trans]
lemma WeakerThan.trans : L₁ ⪯ L₂ → L₂ ⪯ L₃ → L₁ ⪯ L₃ :=
  fun h₁ h₂ => ⟨Set.Subset.trans h₁.subset h₂.subset⟩

instance : Trans (α := Logic) (· ⪯ ·) (· ⪯ ·) (· ⪯ ·) := ⟨WeakerThan.trans⟩

lemma weakerThan_iff : L₁ ⪯ L₂ ↔ (∀ {φ}, L₁ ⊢ φ → L₂ ⊢ φ) :=
  ⟨fun h _ hφ => h.subset hφ, fun h => ⟨fun _ hφ => h hφ⟩⟩

lemma not_weakerThan_iff : ¬L₁ ⪯ L₂ ↔ (∃ φ, L₁ ⊢ φ ∧ L₂ ⊬ φ) := by
  simp [weakerThan_iff, Unprovable];

lemma strictlyWeakerThan_iff :
    L₁ ⪱ L₂ ↔ (∀ {φ}, L₁ ⊢ φ → L₂ ⊢ φ) ∧ (∃ φ, L₁ ⊬ φ ∧ L₂ ⊢ φ) := by
  constructor;
  . rintro ⟨wt, nwt⟩;
    refine ⟨weakerThan_iff.mp wt, ?_⟩;
    obtain ⟨φ, ht, hs⟩ := not_weakerThan_iff.mp nwt;
    exact ⟨φ, hs, ht⟩;
  . rintro ⟨h, φ, hs, ht⟩;
    exact ⟨weakerThan_iff.mpr h, not_weakerThan_iff.mpr ⟨φ, ht, hs⟩⟩;

lemma swt_of_swt_of_wt : L₁ ⪱ L₂ → L₂ ⪯ L₃ → L₁ ⪱ L₃ := by
  rintro ⟨h₁, nh₁⟩ h₂;
  exact ⟨h₁.trans h₂, fun h => nh₁ (h₂.trans h)⟩;

lemma swt_of_wt_of_swt : L₁ ⪯ L₂ → L₂ ⪱ L₃ → L₁ ⪱ L₃ := by
  rintro h₁ ⟨h₂, nh₂⟩;
  exact ⟨h₁.trans h₂, fun h => nh₂ (h.trans h₁)⟩;

instance [L₁ ⪱ L₂] : L₁ ⪯ L₂ := StrictlyWeakerThan.weakerThan

lemma StrictlyWeakerThan.trans : L₁ ⪱ L₂ → L₂ ⪱ L₃ → L₁ ⪱ L₃ :=
  fun h₁ h₂ => swt_of_swt_of_wt h₁ h₂.weakerThan

instance : Trans (α := Logic) (· ⪱ ·) (· ⪯ ·) (· ⪱ ·) := ⟨swt_of_swt_of_wt⟩
instance : Trans (α := Logic) (· ⪯ ·) (· ⪱ ·) (· ⪱ ·) := ⟨swt_of_wt_of_swt⟩
instance : Trans (α := Logic) (· ⪱ ·) (· ⪱ ·) (· ⪱ ·) := ⟨StrictlyWeakerThan.trans⟩

lemma weakening (h : L₁ ⪯ L₂) : L₁ ⊢ φ → L₂ ⊢ φ := weakerThan_iff.mp h

lemma StrictlyWeakerThan.of_unprovable_provable [L₁ ⪯ L₂] (hS : L₁ ⊬ φ) (hT : L₂ ⊢ φ) :
    L₁ ⪱ L₂ := ⟨inferInstance, fun h => hS (h.wk hT)⟩

lemma Equiv.iff : L₁ ≊ L₂ ↔ (∀ φ, L₁ ⊢ φ ↔ L₂ ⊢ φ) :=
  ⟨fun e => by simpa [Set.ext_iff, Provable] using e.eq,
   fun e => ⟨by simpa [Set.ext_iff, Provable] using e⟩⟩

@[instance, simp, refl] protected lemma Equiv.refl (L : Logic) : L ≊ L := ⟨rfl⟩

@[symm, grind .] lemma Equiv.symm : L₁ ≊ L₂ → L₂ ≊ L₁ := fun e => ⟨e.eq.symm⟩

@[trans] lemma Equiv.trans : L₁ ≊ L₂ → L₂ ≊ L₃ → L₁ ≊ L₃ := fun e₁ e₂ => ⟨e₁.eq.trans e₂.eq⟩

@[grind =]
lemma Equiv.antisymm_iff : L₁ ≊ L₂ ↔ L₁ ⪯ L₂ ∧ L₂ ⪯ L₁ := by
  constructor;
  . intro e;
    exact ⟨⟨Set.Subset.antisymm_iff.mp e.eq |>.1⟩, ⟨Set.Subset.antisymm_iff.mp e.eq |>.2⟩⟩;
  . rintro ⟨w₁, w₂⟩;
    exact ⟨Set.Subset.antisymm w₁.subset w₂.subset⟩;

alias ⟨_, Equiv.antisymm⟩ := Equiv.antisymm_iff

@[grind ->] lemma Equiv.le : L₁ ≊ L₂ → L₁ ⪯ L₂ := fun e => ⟨by rw [e.eq]⟩

instance : Trans (α := Logic) (· ≊ ·) (· ≊ ·) (· ≊ ·) := ⟨Equiv.trans⟩
instance : Trans (α := Logic) (· ≊ ·) (· ⪯ ·) (· ⪯ ·) := ⟨fun h₁ h₂ => h₁.le.trans h₂⟩
instance : Trans (α := Logic) (· ⪯ ·) (· ≊ ·) (· ⪯ ·) := ⟨fun h₁ h₂ => h₁.trans h₂.le⟩
instance : Trans (α := Logic) (· ≊ ·) (· ⪱ ·) (· ⪱ ·) := ⟨fun h₁ h₂ => swt_of_wt_of_swt h₁.le h₂⟩
instance : Trans (α := Logic) (· ⪱ ·) (· ≊ ·) (· ⪱ ·) := ⟨fun h₁ h₂ => swt_of_swt_of_wt h₁ h₂.le⟩

@[grind =]
lemma iff_strictlyWeakerThan_weakerThan_not_equiv : L₁ ⪱ L₂ ↔ L₁ ⪯ L₂ ∧ ¬(L₁ ≊ L₂) := by
  constructor;
  . rintro ⟨_, _⟩; grind;
  . rintro ⟨_, _⟩; constructor <;> grind;

lemma Incomparable.of_unprovable (h₁ : ∃ φ, L₁ ⊢ φ ∧ L₂ ⊬ φ) (h₂ : ∃ ψ, L₂ ⊢ ψ ∧ L₁ ⊬ ψ) :
    Incomparable L₁ L₂ := by
  constructor <;>
  . apply not_weakerThan_iff.mpr;
    assumption;

end

/-! ### Consistency -/

/-- Every formula is provable in `L`. -/
def Inconsistent (L : Logic) : Prop := ∀ φ, L ⊢ φ

/-- Some formula is unprovable in `L`. -/
class Consistent (L : Logic) : Prop where
  not_inconsistent : ¬Inconsistent L

section

@[simp]
lemma not_inconsistent_iff_consistent : ¬Inconsistent L ↔ Consistent L :=
  ⟨fun h => ⟨h⟩, fun ⟨h⟩ => h⟩

alias ⟨_, Consistent.not_inc⟩ := not_inconsistent_iff_consistent

@[simp]
lemma not_consistent_iff_inconsistent : ¬Consistent L ↔ Inconsistent L := by
  simp [← not_inconsistent_iff_consistent];

alias ⟨_, Inconsistent.not_con⟩ := not_consistent_iff_inconsistent

lemma consistent_iff_exists_unprovable : Consistent L ↔ ∃ φ, L ⊬ φ := by
  simp [← not_inconsistent_iff_consistent, Inconsistent];

alias ⟨Consistent.exists_unprovable, _⟩ := consistent_iff_exists_unprovable

lemma exists_unprovable [Consistent L] : ∃ φ, L ⊬ φ := Consistent.exists_unprovable inferInstance

lemma Consistent.of_unprovable (h : L ⊬ φ) : Consistent L := ⟨fun hp => h (hp φ)⟩

lemma Inconsistent.of_ge (h₁ : Inconsistent L₁) (h : L₁ ⪯ L₂) : Inconsistent L₂ :=
  fun φ => h.subset (h₁ φ)

end

/-! ### Comparison via inclusion -/

section

lemma weakerThan_of_provable (h : ∀ φ, L₁ ⊢ φ → L₂ ⊢ φ) : L₁ ⪯ L₂ := ⟨fun _ hφ => h _ hφ⟩

lemma weakerThan_of_subset (h : L₁ ⊆ L₂) : L₁ ⪯ L₂ := ⟨h⟩

lemma equiv_of_provable (h : ∀ φ, L₁ ⊢ φ ↔ L₂ ⊢ φ) : L₁ ≊ L₂ := Equiv.iff.mpr h

@[simp, grind .] lemma subset_of_weakerThan [h : L₁ ⪯ L₂] : L₁ ⊆ L₂ := h.subset

instance [L₁ ≊ L₂] : L₁ ⪯ L₂ := Equiv.le inferInstance
instance [L₁ ≊ L₂] : L₂ ⪯ L₁ := Equiv.le <| .symm inferInstance

@[grind .] lemma eq_of_equiv [h : L₁ ≊ L₂] : L₁ = L₂ := h.eq

lemma iff_equal_provable_equiv : L₁ = L₂ ↔ L₁ ≊ L₂ := ⟨fun h => ⟨h⟩, fun h => h.eq⟩

lemma strictWeakerThan_of_ssubset (h : L₁ ⊂ L₂) : L₁ ⪱ L₂ := by
  apply strictlyWeakerThan_iff.mpr;
  obtain ⟨h₁, ⟨ψ, hψ⟩⟩ := Set.ssubset_iff_exists.mp h;
  constructor;
  . intro φ hφ; exact weakerThan_of_subset h.1 |>.wk hφ;
  . use ψ;
    grind;

end

end Logic

section

variable {L : Logic}

instance : (∅ : Logic) ⪯ L := Logic.weakerThan_of_subset <| Set.empty_subset _

instance : L ⪯ (Set.univ : Logic) := Logic.weakerThan_of_subset <| Set.subset_univ _

instance [Logic.Consistent L] : L ⪱ (Set.univ : Logic) := by
  apply Logic.strictWeakerThan_of_ssubset;
  apply Set.ssubset_iff_exists.mpr;
  constructor;
  . simp;
  . obtain ⟨φ, hφ⟩ := Logic.exists_unprovable (L := L);
    use φ;
    grind;

end

end LO.Modal

end
