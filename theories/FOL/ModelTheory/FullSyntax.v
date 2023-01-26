Require Import Undecidability.FOL.FullSyntax.
Require Export Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.BinSig.


Require Export Vector.

Local Set Implicit Arguments.
Notation vec := t.
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
        auto. intros H. apply IH. apply T_step, H.
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
        exact (Sig p n H). exact (F (S n) (phi H)).
    Qed.

    Theorem W :
        ex p -> sig p.
    Proof.
        intros H. apply W' with 0.
        destruct H as [n H]. apply V with n, H.
    Qed.

End WO.

Section model.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Class model := 
    {
    domain : Type;
    interp' : interp domain
    }.
    Coercion domain : model >-> Sortclass.
End model.

Arguments sat {_ _ _ _ _} _ _, {_ _ _} _ {_} _ _.
Arguments interp' {_ _} _, {_ _ _}.
Arguments i_atom {_ _} _ _ _ _.

Notation "pred ₚ[ M ] v" := (i_atom _ (interp' M) pred v) (at level 19).
Notation "Model ⊨[_] phi" := (forall p, sat (interp' Model) p phi) (at level 21).
Notation "Model ⊨[ ρ ] phi" := (sat (interp' Model) ρ phi) (at level 21).

Section Elementary.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Definition elementary_equivalence M N :=
        forall phi, closed phi -> (M ⊨[_] phi) <-> (N ⊨[_] phi).

    Definition elementary_homomorphism {M N: model} (h: M -> N) :=
        forall phi ρ, M ⊨[ρ] phi <-> N ⊨[ρ >> h] phi.

End Elementary.
Notation "N ⪳ M"  := (exists h: N -> M, elementary_homomorphism h) (at level 30).

Section DC.

    Variable A: Type.
    Variable R: A -> A -> Prop.
    Hypothesis dec__R: forall x y, dec (R x y).

    Definition surjective {M N} (f: M -> N) :=
        forall n: N, exists m: M, f m = n.

    Definition a_coutable_model M :=
        exists f: nat -> M, surjective f.

    Definition LS_countable :=
        forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
            exists (N: model), a_coutable_model N /\ (exists h: N -> M, elementary_homomorphism h /\ exists n: N, h n = m).

    Definition FunctionalDependentChoice_on:=
        (forall x, exists y, R x y) -> forall w,
            (exists f : nat -> A, f 0 = w /\ forall n, R (f n) (f (S n))).

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
        ∀ (∃ (atom _ _ _ _ tt (cons _ ($1) _ (cons _ ($0) _ (nil _))))).
    Definition forfor_form :=
        (atom _ _ _ _ tt (cons _ ($1) _ (cons _ ($0) _ (nil _)))).

    Lemma total_sat:
        forall h, (forall x, exists y, R x y) -> Model__A ⊨[h] total_form.
    Proof.
        cbn; intros.
        destruct (H d) as [e P].
        now exists e.
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
    Proof using dec__R.
        intros LS total a.
        destruct (LS _ _ Model__A a) as [N [C__N [h [ele_el__h [n Eqan]]]]].
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        unfold elementary_homomorphism in ele_el__h.
        apply ele_el__h in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h.
        destruct H as [R' [P1 P2]].
        assert (forall x, decidable (fun y => R' x y)) as dec__R'.
        intros x y. destruct (dec__R (h x) (h y)); firstorder.
        destruct (DC_countable C__N P1 dec__R' n) as [f [case0 Choice]].
        exists (f >> h); unfold ">>"; split.
        now rewrite case0.
        intro n'; now rewrite <- (P2 (f n') (f (S n'))).
    Qed.

End DC.









