module

public import Neighborhood.Hilbert.Basic

@[expose] public section

variable {α : Type u}

abbrev LogicEMCN : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N }
instance : (@LogicEMCN α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMCN α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEMCN α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;

abbrev LogicEMCK : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) }
instance : (@LogicEMCK α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMCK α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEMCK α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;

abbrev LogicEMNP : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.P }
instance : (@LogicEMNP α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMNP α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEMNP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicECNP : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.P }
instance : (@LogicECNP α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECNP α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicECNP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicEMCP : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.P }
instance : (@LogicEMCP α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMCP α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEMCP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicENTB : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicENTB α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENTB α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicENTB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicEMN4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMN4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMN4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEMN4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicENT4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENT4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENT4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicENT4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEND4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEND4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEND4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicEND4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEMT4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMT4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMT4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicEMT4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEMC4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMC4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMC4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEMC4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEMCT : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) }
instance : (@LogicEMCT α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMCT α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEMCT α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;

abbrev LogicEMNT : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) }
instance : (@LogicEMNT α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMNT α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEMNT α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;

abbrev LogicECNT : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) }
instance : (@LogicECNT α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECNT α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicECNT α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;

abbrev LogicEMCD : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMCD α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMCD α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEMCD α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicEMND : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMND α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMND α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEMND α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicECND : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) }
instance : (@LogicECND α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECND α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicECND α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicEMCB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMCB α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMCB α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEMCB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicEMNB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMNB α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMNB α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEMNB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicECNB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) }
instance : (@LogicECNB α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECNB α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicECNB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicECN4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECN4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECN4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicECN4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEMC5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMC5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMC5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEMC5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEMN5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMN5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMN5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEMN5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicECN5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECN5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECN5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicECN5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEMTB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMTB α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMTB α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicEMTB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicECTB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECTB α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECTB α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicECTB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicECT4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECT4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECT4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicECT4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEMT5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMT5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMT5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicEMT5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicECT5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECT5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECT5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicECT5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicENT5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENT5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENT5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicENT5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEMDB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMDB α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicEMDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicECDB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECDB α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicECDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicENDB : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicENDB α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicENDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicEMD4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMD4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicEMD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicECD4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECD4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicECD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEMD5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMD5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicEMD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicECD5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECD5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicECD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEND5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEND5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEND5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicEND5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicED45 : Logic α := Hilbert $
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicED45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicED45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;
instance : (@LogicED45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEM45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEM45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEM45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;
instance : (@LogicEM45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEC45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEC45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEC45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;
instance : (@LogicEC45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEN45 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEN45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEN45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;
instance : (@LogicEN45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEMB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;
instance : (@LogicEMB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicECB4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;
instance : (@LogicECB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicENB4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;
instance : (@LogicENB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

end
