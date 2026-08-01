module

public import Neighborhood.Hilbert.Basic

@[expose] public section

variable {α : Type u}

abbrev LogicEMCNTDB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMCNTDB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTDB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTDB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTDB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNTDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMCNTD4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCNTD4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTD4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTD4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTD4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNTD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCNTD5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNTD5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTD5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTD5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTD5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNTD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCNTB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCNTB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNTB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCNTB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNTB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNTB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCNT45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNT45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNT45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNT45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNT45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNT45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCNT45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCNDB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCNDB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNDB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNDB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCNDB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNDB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNDB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNDB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCND45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCND45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCND45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCND45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCND45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCND45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCND45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCNB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCNB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCTDB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCTDB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTDB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTDB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCTDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCTDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCTDB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCTDB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTDB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTDB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCTDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCTDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCTD45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCTD45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTD45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTD45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCTD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCTD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCTB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCTB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCTB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCTB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCDB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCDB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCDB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNTDB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMNTDB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTDB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTDB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNTDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNTDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMNTDB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNTDB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTDB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTDB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNTDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNTDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNTD45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNTD45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTD45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTD45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNTD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMNTD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNTB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNTB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNTB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMNTB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNDB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNDB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNDB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMNDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMTDB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMTDB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTDB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMTDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMTDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMTDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNTDB4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECNTDB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTDB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTDB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNTDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNTDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECNTDB5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNTDB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTDB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTDB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNTDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNTDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNTD45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNTD45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTD45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTD45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNTD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECNTD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNTB45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNTB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNTB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECNTB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNDB45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNDB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNDB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECNDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECTDB45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECTDB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTDB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECTDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECTDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECTDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENTDB45 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENTDB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTDB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENTDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENTDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicENTDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

end
