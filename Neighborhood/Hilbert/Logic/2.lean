module

public import Neighborhood.Hilbert.Basic

@[expose] public section

variable {α : Type u}

abbrev LogicEMC : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) }
instance : (@LogicEMC α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMC α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;

abbrev LogicEMN : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N }
instance : (@LogicEMN α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMN α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;

abbrev LogicECN : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N }
instance : (@LogicECN α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECN α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;

abbrev LogicEMK : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) }
instance : (@LogicEMK α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMK α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;

abbrev LogicEMT : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) }
instance : (@LogicEMT α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMT α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;

abbrev LogicENT : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) }
instance : (@LogicENT α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENT α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;

abbrev LogicEND : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) }
instance : (@LogicEND α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEND α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicECP : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.P }
instance : (@LogicECP α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicEMP : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.P }
instance : (@LogicEMP α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicENP : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.P }
instance : (@LogicENP α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicETB : Logic α := Hilbert $
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicETB α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicETB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicENB : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.B A | (A) }
instance : (@LogicENB α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicEN4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEN4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEN4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicET4 : Logic α := Hilbert $
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicET4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicET4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEM4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEM4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEM4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicET5 : Logic α := Hilbert $
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicET5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicET5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicECT : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) }
instance : (@LogicECT α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECT α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;

abbrev LogicEMD : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMD α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMD α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicECD : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) }
instance : (@LogicECD α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECD α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicEMB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMB α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEMB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicECB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECB α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicEC4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEC4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEC4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEM5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEM5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by grind;
instance : (@LogicEM5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEC5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEC5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicEC5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEN5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEN5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEN5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEDB : Logic α := Hilbert $
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicEDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicED4 : Logic α := Hilbert $
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicED4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicED4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicED5 : Logic α := Hilbert $
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicED5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicED5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicE45 : Logic α := Hilbert $
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicE45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;
instance : (@LogicE45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEB4 : Logic α := Hilbert $
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;
instance : (@LogicEB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicECK : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) }
instance : (@LogicECK α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECK α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;

abbrev LogicENK : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.K A B | (A) (B) }
instance : (@LogicENK α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENK α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;

abbrev LogicEKT : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.T A | (A) }
instance : (@LogicEKT α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEKT α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;

abbrev LogicEKD : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.D A | (A) }
instance : (@LogicEKD α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEKD α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicEKP : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.P }
instance : (@LogicEKP α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEKP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicEKB : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEKB α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEKB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicEK4 : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEK4 α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEK4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEK5 : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEK5 α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEK5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicETD : Logic α := Hilbert $
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) }
instance : (@LogicETD α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicETD α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicETP : Logic α := Hilbert $
  { Axioms.T A | (A) } ∪
  { Axioms.P }
instance : (@LogicETP α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicETP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicEDP : Logic α := Hilbert $
  { Axioms.D A | (A) } ∪
  { Axioms.P }
instance : (@LogicEDP α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicEDP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicEPB : Logic α := Hilbert $
  { Axioms.P } ∪
  { Axioms.B A | (A) }
instance : (@LogicEPB α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;
instance : (@LogicEPB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicEP4 : Logic α := Hilbert $
  { Axioms.P } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEP4 α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;
instance : (@LogicEP4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEP5 : Logic α := Hilbert $
  { Axioms.P } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEP5 α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;
instance : (@LogicEP5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEB5 : Logic α := Hilbert $
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;
instance : (@LogicEB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

end
