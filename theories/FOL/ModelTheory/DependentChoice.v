Require Import Undecidability.FOL.ModelTheory.Core.
Require Import Undecidability.FOL.ModelTheory.HenkinModel.

Definition dec (X: Type) : Type := X + (X -> False).
Notation decidable p := (forall x, dec (p x)).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.

Section WO.

    Implicit Types n k: nat.
    Variable p: nat -> Prop.
    Variable p_dec: decidable p.

    Inductive T (n: nat) : Prop := C (phi: ~p n -> T (S n)).

    Lemma T_base n :
        p n -> T n.
    Proof.
        intros H. constructor. intros H1. destruct (H1 H).
    Qed.

    Lemma T_step n :
        T (S n) -> T n.
    Proof.
        intros H. constructor. intros _. exact H.
    Qed.

    Lemma T_zero n :
        T n -> T 0.
    Proof.
        induction n as [|n IH].
        - auto.
        - intros H. apply IH. apply T_step, H.
    Qed.

    Lemma V n :
        p n -> T 0.
    Proof.
        intros H. eapply T_zero, T_base, H.
    Qed.

    Lemma W' :
        forall n, T n -> sig p.
    Proof.
        refine (fix F n a {struct a} := let (phi) := a in
                            match p_dec n with
                            inl H => _ | inr H => _
                            end).
        - exact (Sig p n H).
        - exact (F (S n) (phi H)).
    Qed.

    Theorem W :
        ex p -> sig p.
    Proof.
        intros H. apply W' with 0.
        destruct H as [n H].
        apply V with n, H.
    Qed.

End WO.


Section DC.

    Hypothesis classical_logic:
        forall X (P: X -> Prop), (exists x, P x) <-> ~ (forall x, ~ P x).

    Variable A: Type.
    Variable R: A -> A -> Prop.
    Hypothesis dec__R: forall x y, dec (R x y).

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
    Proof using classical_logic dec__R.
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

    Lemma exists_next:
    forall B (R': B -> B -> Prop), a_coutable_model B ->
        (forall x, exists y, R' x y) -> exists f: nat -> B,
            forall b, exists n, R' b (f n).
    Proof.
        intros B R' [f sur] total.
        exists f. intro b.
        destruct (total b) as [c Rbc], (sur c) as [m p].
        exists m. now rewrite p.
    Qed.

    Lemma DC_countable:
        forall B (R': B -> B -> Prop), a_coutable_model B ->
            (forall x, exists y, R' x y) -> (forall x y, dec (R' x y)) ->
                forall b: B, exists choice, choice 0 = b /\ forall n, R' (choice n) (choice (S n)).
    Proof.
        intros B R' C__B total dec__R' root.
        destruct (@exists_next B R' C__B total) as [f P].
        assert(forall b, decidable (fun n : nat => R' b (f n))) as dec__R'' by easy.
        specialize (fun b => (@W (fun n => R' b (f n)) (dec__R'' b) (P b))) as WO.
        exists (fix g n := match n with O => root | S n => f (pi1 (WO (g n))) end).
        split; try easy; intro n; cbn.
        destruct (WO ((fix g n:= match n with 0 => root |S n' => f (pi1 (WO (g n'))) end) n)); easy.
    Qed.

   Lemma LS_imples_DC: LS_countable -> FunctionalDependentChoice_on.
   Proof using classical_logic dec__R.
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
        assert (forall x, decidable (fun y => R' x y)) as dec__R'.
        intros x y. destruct (dec__R (h x) (h y)); firstorder.
        destruct (DC_countable C__N P1 dec__R' n) as [f [case0 Choice]].
        exists (f >> h); unfold ">>"; split.
        now rewrite case0.
        intro n'; now rewrite <- (P2 (f n') (f (S n'))).
    Qed.


End DC.
