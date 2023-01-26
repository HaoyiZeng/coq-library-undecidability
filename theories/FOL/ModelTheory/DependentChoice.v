Require Import Undecidability.FOL.ModelTheory.Core.
Require Import Undecidability.FOL.ModelTheory.HenkinModel.
Require Import Undecidability.FOL.Syntax.BinSig.
From Coq Require Import Arith Lia.

Definition dec (X: Type) : Type := X + (X -> False).
Notation decidable p := (forall x, dec (p x)).
Definition eqdec X := forall x y: X, dec (x = y).
Notation decider p := (forall x, dec (p x)).
Notation unique p := (forall x y, p x -> p y -> x = y).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.

Section Least_witness.

    Definition nat_eqdec : eqdec nat.
    Proof.
    intros x y.
    destruct (Nat.eq_dec x y) as [H|H].
    - left. exact H.
    - right. exact H.
    Defined.

    Implicit Types (n k: nat).

    Definition safe (p: nat -> Prop) n := forall k, p k -> k >= n.
    Definition least (p: nat -> Prop) n := p n /\ safe p n.

    Fact least_unique (p: nat -> Prop) :
    unique (least p).
    Proof.
    intros x y [H1 H2] [H3 H4].
    enough (x <= y /\ y <= x) by lia. split.
    - apply H2, H3.
    - apply H4, H1.
    Qed.

    Fact safe_O p :
    safe p 0.
    Proof.
    intros k _. lia.
    Qed.

    Fact safe_S p n :
    safe p n -> ~p n -> safe p (S n).
    Proof.
    intros H1 H2 k H3.
    specialize (H1 k H3).
    enough (k <> n) by lia.
    intros ->. easy.
    Qed.

    (*** Step-Indexed Linear Search *)


    Section Step_indexed_linear_search.
    Variable p: nat -> Prop.
    Variable p_dec: decider p.

    Fixpoint L n k : nat :=
    match n with
    | 0 => k
    | S n' => if p_dec k then k else L n' (S k)
    end.

    Lemma L_correct' :
    forall n k, p (n + k) -> safe p k -> least p (L n k).
    Proof.
    induction n as [|n IH]; cbn; intros k H1 H2.
    - easy.
    - destruct (p_dec k) as [H|H].
        + easy.
        + apply IH. 
        * replace (n + S k) with (S n + k) by lia. exact H1.
        * apply safe_S; assumption.
    Qed.

    Lemma L_correct n :
    p n -> least p (L n 0).
    Proof.
    intros H. apply L_correct'.
    - replace (n + 0) with n by lia. exact H.
    - apply safe_O.
    Qed.

    Lemma least_linear_sigma' :
    forall n k, p (n + k) -> safe p k -> sig (least p).
    Proof.
    induction n as [|n IH]; intros k H1 H2.
    - exists k. easy.
    - destruct (p_dec k) as [H|H].
        + exists k. easy.
        + apply (IH (S k)).
        * replace (n + S k) with (S n + k) by lia. exact H1.
        * apply safe_S; assumption.
    Qed.

    Lemma least_linear_sigma :
    sig p -> sig (least p).
    Proof.
    intros [n H].
    apply (@least_linear_sigma' n 0).
    - replace (n + 0) with n by lia. exact H.
    - apply safe_O.
    Qed.

    End Step_indexed_linear_search.

    (*** Direct Search *)

    Section Direct_search.
    Variable p: nat -> Prop.

    (** Certifying version *)

    Variable p_dec: decider p.

    Lemma least_direct_sigma' :
    forall n, safe p n + sig (least p).
    Proof.
    induction n as [|n IH].
    - left. apply safe_O.
    - destruct IH as [IH|IH].
        + destruct (p_dec n) as [H|H].
        * right. exists n. easy.
        * left. apply safe_S; assumption.
        + right. exact IH.
    Qed.

    Lemma least_direct_sigma :
    sig p -> sig (least p).
    Proof.
    intros [n H].
    destruct (least_direct_sigma' n) as [H1|H1].
    - exists n. easy.
    - exact H1.
    Qed.

    Fact least_ex :
    ex p -> ex (least p).
    Proof.
    intros [n H].
    edestruct least_direct_sigma as [k H1].
    - exists n. exact H.
    - exists k. exact H1.
    Qed. 

    End Direct_search.

    Definition XM := forall P, P \/ ~P.

    Fact xm_least_safe :
    XM -> forall p n, ex (least p) \/ safe p n.
    Proof.
    intros H p.
    induction n as [|n IH].
    - right. apply safe_O.
    - destruct IH as [IH|IH].
        + left. exact IH.
        + specialize (H (p n)) as [H|H].
        * left. exists n. easy.
        * right. apply safe_S; assumption.
    Qed.

    Fact least_safe_ex_least :
    (forall p n, ex (least p) \/ safe p n) -> forall p, ex p -> ex (least p).
    Proof.
    intros H p [n H1].
    specialize (H p n) as [H|H].
    * exact H.
    * exists n. easy.
    Qed.

    Fact XM_ex_least:
        XM -> forall p, ex p -> ex (least p).
    Proof.
        intro; now apply least_safe_ex_least, xm_least_safe.
    Qed.


End Least_witness.

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


Section DC.

    Hypothesis XM:
        forall P, P \/ ~ P.

    Variable A: Type.
    Variable R: A -> A -> Prop.

    Lemma XM__R :
        forall x y, (R x y) \/ ~ (R x y).
    Proof using XM.
        easy.
    Qed.

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

    Lemma total_ex:
    (forall x: A, exists y: A, R x y) <-> forall x, ~ (forall y, ~ R x y).
    Proof using XM.
        firstorder.
        now apply classical_logic.
    Qed.


    Section dec_R.
    Hypothesis dec__R: forall x y, dec (R x y).

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
   Proof using XM dec__R.
        intros LS total a.
        destruct (LS _ _ Model__A a) as [N [C__N [h [ele_el__h [n Eqan]]]]].
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
        destruct (DC_countable C__N P1 dec__R' n) as [f [case0 Choice]].
        exists (f >> h); unfold ">>"; split.
        now rewrite case0.
        intro n'; now rewrite <- (P2 (f n') (f (S n'))).
    Qed.

    End dec_R.

    Section DC_pred_coutable.

    Definition function_rel' {X Y} (P: X -> Y -> Prop) :=
        forall x, exists !y, P x y.

    Definition DC_pred D (R__d: D -> D -> Prop):= 
        total_rel R__d -> forall w,
            exists P: nat -> D -> Prop, function_rel' P /\ P 0 w /\ forall n, exists x y,  P n x /\ P (S n) y /\ R__d x y.

    Variable B: Type.
    Variable R':  B -> B -> Prop.
    Variable f: nat -> B.
    Variable g: B -> nat.
    Hypothesis bij_l: forall n, g (f n) = n.
    Hypothesis bij_r: forall b, f (g b) = b.

    Fixpoint least_pred w n b :=
        match n with
        | O => b = w
        | S n => exists! bn, least_pred w n bn /\ least (fun x => R' bn (f x)) (g b)
        end.

    Lemma exists_next_pred:
        total_rel R' -> forall b, exists n, least (fun n => R' b (f n)) n. 
    Proof.
        intros.
        destruct (H b) as [next Rbnext].
        apply XM_ex_least. { easy. }
        exists (g next).
        now rewrite bij_r.
    Qed.

    Lemma functional_least_pred root:
        total_rel R' ->
        forall n, exists! v, least_pred root n v.
    Proof.
        induction n. 
        - exists root; constructor; cbn; try easy.
        - destruct IHn as [v [p1 p2]].
          destruct (exists_next_pred H v) as [next Rrn].
          exists (f next); split; try easy; cbn.
          exists v; constructor; try easy. 
          split; try easy.
          now rewrite bij_l.
          intros v' [p _]; now apply p2.
          intros fnext' (p1' & p2' & p3).
          enough (g (f next) = g fnext').
          rewrite bij_l in H0. rewrite H0. easy.
          specialize(p3 p1' p2').
          unshelve eapply least_unique.
          exact (fun x : nat => R' p1' (f x)).
          destruct p2' as [H1 H2].
          rewrite (p2 _ H1) in Rrn.
          now rewrite bij_l. easy.
    Qed.


    Lemma exists_next_pred':
        total_rel R' -> forall w,
                (least_pred w O w)  /\ (forall n, exists x y, least_pred w n x /\ least_pred w (S n) y /\ R' x y).
    Proof.
        intros total root.
        unfold total_rel in total.
        split; try easy; intros; cbn.
        induction n; cbn.
        - exists root.
          destruct (exists_next_pred total root) as [next Rrn].
          exists (f next); split; try easy; split.
          rewrite bij_l. exists root; constructor.
          split; easy.
          intros x'.
          all: now destruct Rrn as (a_name & _).
        - destruct IHn as (x & y & nx & [bn [P1 P2]] & R'xy).
          exists y.
          destruct (exists_next_pred total y) as [next Rrn].
          exists (f next); split; try easy.
          exists bn; constructor.
          split; intros; easy.
          apply P2.
          split. 2: { now destruct Rrn. }
          exists y; constructor.
          split. exists bn; now constructor.
          now rewrite bij_l.
          intros y' ([b' [P1' P1'']] & P2').
          rewrite bij_l in P2'.
          enough (g y = g y').
          rewrite <- (bij_r y), <- (bij_r y').
          now f_equal.
          unshelve eapply least_unique.
          exact  (fun x : nat => R' b' (f x)).
          destruct P1. destruct P1'.
          destruct (functional_least_pred root total n) as [x_n [_ uni_x]].
          enough (bn = b') as re. now rewrite <- re. 
          now rewrite <- (uni_x bn), <- (uni_x b').
          easy.
    Qed.

    Theorem DC_pred_ω: (DC_pred R').
    Proof.
        intros total w.
        exists (least_pred w).
        split.
        - exact (functional_least_pred w total).
        - exact (exists_next_pred' total w).
    Qed.
    
    End DC_pred_coutable.

    


End DC.




(* Full Syntax
   Pred version *)

(* 
   Definition FunctionalDependentChoice_on:=
    (forall x, exists y, R x y) -> forall w,
        (exists f : nat -> A, f 0 = w /\ forall n, R (f n) (f (S n))). *)
