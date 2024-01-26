Require Import Undecidability.FOL.ModelTheory.LogicalPrinciples.
Require Import Undecidability.FOL.ModelTheory.HenkinEnv.
Require Import Undecidability.FOL.ModelTheory.ReverseLS. 
Require Import Undecidability.FOL.ModelTheory.Core.

Section LSiffDC.

    Corollary LS_iff_DC_under_AC00_LEM: 
        AC00 -> LEM -> DLS <-> DC.
    Proof.
        intros H1 H2; split.
        - eapply LS_CC_impl_DC; eauto.
        - intros DC. eapply LS_correct, LS_downward_with_DC_LEM; eauto.
    Qed.

    Corollary LS_iff_DC_BDP_BEP_under_AC00:
        AC00 -> DLS <-> DC /\ BDP /\ BEP.
    Proof.
        intros H1; split.
        - intros HLS. repeat split.
          now apply LS_CC_impl_DC.
          now apply LS_impl_BDP.
          now apply LS_impl_BEP.
        - intros (h1 & h2 & h3).
          now apply LS_correct, LS_downward_with_BDP_BEP_DC.
    Qed.

    Corollary LS_iff_DDC_BDP_BEP_BCC:
        DLS <-> DDC /\ BDP /\ BEP /\ BCC.
    Proof.
        split.
        - intros HLS. repeat split.
          assert (OBDC) as HO. now  apply LS_impl_OBDC.
          assert (BDC2) as H2. intros X. now apply OBDC_impl_BDC2_on.
          now apply BDC2_iff_DDC_BCC.
          now apply LS_impl_BDP. now apply LS_impl_BEP.
          now eapply BDC_impl_BCC, LS_impl_BDC. 
        - intros (h1 & h2 & h3 & h4).
          now apply LS_correct, LS_downward.
    Qed.

End LSiffDC.
