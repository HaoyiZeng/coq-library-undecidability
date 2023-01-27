Require Import Undecidability.FOL.ModelTheory.Core.
Require Import Undecidability.FOL.ModelTheory.HenkinModel.
Require Import Undecidability.FOL.Syntax.BinSig.
Require Import Undecidability.FOL.ModelTheory.SearchNat.

Section DC.

    Hypothesis XM:
        forall P, P \/ ~ P.

    Variable A: Type.
    Variable R: A -> A -> Prop.

    Lemma classical_logic:
        forall X (P: X -> Prop), (exists x, P x) <-> ~ (forall x, ~ P x).
    Proof using XM.
        firstorder.
        destruct (XM (exists x, P x)).
        easy.
        exfalso. apply H. intros x Px. apply H0. 
        now exists x.
    Qed.

    Definition LS_countable :=
        forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
            exists (N: model), a_coutable_model N /\ (exists h: N -> M, elementary_homomorphism h /\ exists n: N, h n = m).

    Instance interp__A : interp A :=
    {
        i_func := fun F v => match F return A with end;
        i_atom := fun P v => R (hd v) (last v)
    }.

    Instance Model__A: model :=
    {
        domain := A;
        interp' := interp__A
    }.

    Definition total_form :=
        ∀ (¬ ∀ ¬ (atom _ _ _ _ tt (cons _ ($1) _ (cons _ ($0) _ (nil _))))).

    Definition forfor_form :=
        (atom _ _ _ _ tt (cons _ ($1) _ (cons _ ($0) _ (nil _)))).

    Lemma total_sat:
        forall h, total_rel R -> Model__A ⊨[h] total_form.
    Proof.
        cbn; intros.
        destruct (H d) as [e P].
        eapply H0; exact P.
    Qed.

    Definition p {N} (α β: N): env N :=
        fun n => match n with
            | 0 => β
            | _ => α end.

    Lemma forfor_sat {N} (h: N -> A) (α β: N):
        R (h α) (h β) <-> Model__A ⊨[(p α β) >> h] forfor_form.
    Proof.
        unfold ">>"; now cbn.
    Qed.

    Lemma total_ex:
    (forall x: A, exists y: A, R x y) <-> forall x, ~ (forall y, ~ R x y).
    Proof using XM.
        firstorder.
        now apply classical_logic.
    Qed.

    (* Since we need a powerful version of bijective for definiing the predicate over the coutable type *)
    Definition bijective_comp {X Y} :=
        exists f g, (forall x: X, g (f x) = x) /\ forall y: Y, f (g y) = y.

    Definition LS_countable_comp :=
    forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
        exists (N: model), @bijective_comp N nat /\ (exists h: N -> M, elementary_homomorphism h /\ exists n: N, h n = m).

    Lemma LS_imples_DC_pred: LS_countable_comp -> (@DC_pred _ R).
    Proof using XM.
        intros LS total a.
        destruct (LS _ _ Model__A a) as [N [(f & g & bij_l & bij_r) [h [ele_el__h [n Eqan]]]]].
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        apply ele_el__h in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. apply classical_logic.
        now specialize(total' x).
        intros α β. rewrite forfor_sat.
        unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h. now cbn.
        destruct H as [R' [P1 P2]].
        assert (forall x : N, logical_decidable (R' x)) by (intros x y; apply XM).
        edestruct (@DC_pred_ω N R' _ _ bij_r bij_l H P1 n) as [P [case0 Choice]].
        unshelve eexists.
        exact (fun n' a' => exists n, h n = a' /\ P n' n); cbn.
        split.
        (* Proof of functional property*)
        - intro x; destruct (case0 x) as [n' [P1' P2']].
          exists (h n'); constructor.
          now exists n'.    
          intros a' [nn [Pa' Pa'']]. now rewrite (P2' nn).
        (* Proof of spec of the dependent choice predicate *)
        - split.
          + now exists n.
          + intro nA.
            destruct Choice as [_ Choice], (Choice nA) as [x [y Choice']].
            exists (h x), (h y).
            split. now exists x.
            split. now exists y. now rewrite <- P2.
    Qed.


    Section dec_R.

    Hypothesis dec__R: forall x y, dec (R x y).

    Lemma LS_imples_DC: LS_countable -> @DC_func A R.
    Proof using XM dec__R.
        intros LS total a.
        destruct (LS _ _ Model__A a) as [N [[f sur] [h [ele_el__h [n Eqan]]]]].
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        apply ele_el__h in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. apply classical_logic.
        now specialize(total' x).
        intros α β. rewrite forfor_sat.
        unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h. now cbn.
        destruct H as [R' [P1 P2]].
        assert (forall x, decidable (fun y => R' x y)) as dec__R'.
        intros x y. destruct (dec__R (h x) (h y)); firstorder.
        destruct (DC_ω _ _ f sur dec__R' P1 n) as [g [case0 Choice]].
        exists (g >> h); unfold ">>"; split.
        now rewrite case0.
        intro n'; now rewrite <- (P2 (g n') (g (S n'))).
    Qed.

    End dec_R.

End DC.
