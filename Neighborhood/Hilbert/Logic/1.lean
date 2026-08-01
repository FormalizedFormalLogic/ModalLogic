module

public import Neighborhood.Hilbert.Basic

@[expose] public section

variable {α : Type u}

abbrev LogicEM : Logic α := Hilbert { Axioms.M A B | (A) (B) }
instance : (@LogicEM α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;

abbrev LogicEC : Logic α := Hilbert { Axioms.C A B | (A) (B) }
instance : (@LogicEC α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;

abbrev LogicEN : Logic α := Hilbert { Axioms.N }
instance : (@LogicEN α).HasAxiomN := Hilbert.hasAxiomN_of rfl

abbrev LogicEK : Logic α := Hilbert { Axioms.K A B | (A) (B) }
instance : (@LogicEK α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;

abbrev LogicET : Logic α := Hilbert { Axioms.T A | (A) }
instance : (@LogicET α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;

abbrev LogicED : Logic α := Hilbert { Axioms.D A | (A) }
instance : (@LogicED α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicEP : Logic α := Hilbert { Axioms.P }
instance : (@LogicEP α).HasAxiomP := Hilbert.hasAxiomP_of rfl

abbrev LogicEB : Logic α := Hilbert { Axioms.B A | (A) }
instance : (@LogicEB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicE4 : Logic α := Hilbert { Axioms.Four A | (A) }
instance : (@LogicE4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicE5 : Logic α := Hilbert { Axioms.Five A | (A) }
instance : (@LogicE5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

end
