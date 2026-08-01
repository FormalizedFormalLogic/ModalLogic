module

public import Neighborhood.Hilbert.Basic

@[expose] public section

variable {α : Type u}

abbrev LogicEMCNP : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.P }
instance : (@LogicEMCNP α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNP α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNP α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicEMNT4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMNT4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNT4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNT4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNT4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCN4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCN4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCN4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCN4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCN4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCNT : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) }
instance : (@LogicEMCNT α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNT α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNT α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNT α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;

abbrev LogicEMCND : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMCND α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCND α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCND α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCND α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicEMCNB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMCNB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMCN5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCN5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCN5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCN5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCN5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCTB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMCTB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMNTB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMNTB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECNTB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECNTB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMCT4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCT4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCT4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCT4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCT4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECNT4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECNT4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNT4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNT4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNT4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCT5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCT5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCT5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCT5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCT5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNT5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNT5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNT5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNT5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNT5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNT5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNT5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNT5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNT5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNT5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCDB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMCDB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCDB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMNDB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMNDB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNDB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECNDB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECNDB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNDB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMCD4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCD4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCD4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMND4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMND4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMND4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMND4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMND4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECND4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECND4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECND4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECND4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECND4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCD5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCD5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCD5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMND5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMND5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMND5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMND5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMND5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECND5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECND5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECND5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECND5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECND5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMD45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMD45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECD45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECD45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEND45 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEND45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEND45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEND45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEND45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMC45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMC45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMC45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMC45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMC45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMN45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMN45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMN45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMN45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMN45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECN45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECN45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECN45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECN45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECN45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMNB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMNB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECNB4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECNB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCTD : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMCTD α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTD α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTD α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicEMCB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNTD : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMNTD α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTD α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTD α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicEMNB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMTDB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMTDB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTDB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMTDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMTD4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMTD4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTD4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMTD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMTD5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMTD5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTD5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMTD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMTB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMTB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMTB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMTB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMTB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMTB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMT45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMT45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMT45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMT45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMT45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMDB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMDB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMDB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMDB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNTD : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) }
instance : (@LogicECNTD α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTD α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTD α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicECNB5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECTDB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECTDB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTDB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECTDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECTD4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECTD4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTD4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECTD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECTD5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECTD5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTD5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECTD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECTB4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECTB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECTB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECTB5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECTB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECTB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECT45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECT45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECT45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECT45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECT45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECDB4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECDB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECDB5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECDB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECB45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENTDB : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicENTDB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTDB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENTDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicENTD4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENTD4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTD4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENTD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicENTD5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENTD5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTD5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENTD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENTB4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENTB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENTB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicENTB5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENTB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENTB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENT45 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENT45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENT45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENT45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicENT45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENDB4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENDB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicENDB5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENDB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENB45 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicENB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicETDB4 : Logic α := Hilbert $
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicETDB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicETDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicETDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicETDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicETDB5 : Logic α := Hilbert $
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicETDB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicETDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicETDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicETDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicETD45 : Logic α := Hilbert $
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicETD45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicETD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicETD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicETD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicETB45 : Logic α := Hilbert $
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicETB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicETB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicETB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicETB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEDB45 : Logic α := Hilbert $
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

end
