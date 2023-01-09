Require Import Undecidability.FOL.ModelTheory.Core.
Require Import Undecidability.FOL.ModelTheory.HenkinModel.


Section DC.

    Hypothesis classical_logic: 
        forall X (P: X -> Prop), (exists x, P x) <-> ~ (forall x, ~ P x).

    Variable A: Type.
    Variable R: A -> A -> Prop.

    Definition LS_countable :=
        forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
            exists (N: model), a_coutable_model N /\ (exists h: N -> M, elementary_homomorphism h /\ exists n: N, h n = m).

    Definition FunctionalDependentChoice_on:=
        (forall x, exists y, R x y) -> forall w,
            (exists f : nat -> A, f 0 = w /\ forall n, R (f n) (f (S n))).


    Definition sys_func := False.
    Inductive sys_pred := lt: sys_pred.

    Instance Σf: funcs_signature :=
        {|
            syms := sys_func;
            ar_syms := fun _ => 0
        |}.

    Instance Σp: preds_signature :=
        {|
            preds := sys_pred;
            ar_preds := fun _ => 2
        |}.

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
        ∀ (¬ ∀ ¬ (atom _ _ _ _ lt (cons _ ($1) _ (cons _ ($0) _ (nil _))))).

    Definition forfor_form :=
        (atom _ _ _ _ lt (cons _ ($1) _ (cons _ ($0) _ (nil _)))).

    Lemma total_ex:
        (forall x: A, exists y: A, R x y) <-> forall x, ~ (forall y, ~ R x y).
    Proof using classical_logic.
        firstorder.
        now apply classical_logic.
    Qed.

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

    Hypothesis FunctionalDependentChoice_on_fin: 
        forall B (R': B -> B -> Prop), a_coutable_model B -> 
            (forall x, exists y, R' x y) -> forall w,
                (exists f : nat -> B,  f 0 = w /\ forall n, R' (f n) (f (S n))).

   Lemma LS_imples_DC: LS_countable -> FunctionalDependentChoice_on.
    Proof.
        intros LS total a.
        destruct (LS _ _ Model__A a) as [N [C__N [h [ele_el__h [n Eqan]]]]].
        unfold elementary_homomorphism in ele_el__h.
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        rewrite <- (ele_el__h total_form (fun _ => n)) in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => lt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. apply classical_logic.
        now specialize(total' x).
        intros α β. rewrite forfor_sat.
        rewrite <- ele_el__h. now cbn.
        destruct H as [R' [P1 P2]].
        destruct (FunctionalDependentChoice_on_fin C__N P1 n) as [f [case0 Choice]].
        exists (f >> h); unfold ">>"; split.
        now rewrite case0.
        intro n'; now rewrite <- (P2 (f n') (f (S n'))).
    Qed.

    Lemma exists_next: 
        forall B (R': B -> B -> Prop), a_coutable_model B -> 
            (forall x, exists y, R' x y) -> exists f: nat -> B,
                forall b, exists n, R' b (f n).
    Proof.
        intros B R' [f sur] total.
        exists f. intro b. 
        destruct (total b) as [c Rbc].
        destruct (sur c) as [m p].
        exists m. now rewrite p.
    Qed.

    Lemma search_next: 
        forall B (R': B -> B -> Prop),
            (exists f: nat -> B, forall b, exists n, R' b (f n))
                -> exists choice, forall n, R' (choice n) (choice (S n)).
    Proof.
        intros B R' [f P].
    Admitted.




   Lemma FunctionalDependentChoice_on_rel: 
    forall B (R': B -> B -> Prop), a_coutable_model B -> 
        (forall x, exists y, R' x y) -> forall w,
            (exists f : nat -> B,  f 0 = w /\ forall n, R' (f n) (f (S n))).
    Proof.
        intros B R' [f sur] total w.
    Admitted.


End DC.
