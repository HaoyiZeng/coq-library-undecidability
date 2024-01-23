Require Export Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.BinSig.
Require Import Undecidability.FOL.ModelTheory.Core.
Require Import Undecidability.FOL.ModelTheory.DCPre.

Section DC.

    Variable A: Type.
    Variable a: A.
    Variable R: A -> A -> Prop.

    Instance interp__A : interp A :=
    {
        i_func := fun F v => match F return A with end;
        i_atom := fun P v => R (hd v) (last v)
    }.

    Definition Model__A: model :=
    {|
        domain := A;
        interp' := interp__A
    |}.

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

    Section dec__R_full.

    Definition dec_R := forall x y, dec (R x y).

    Definition DC_on' {X} (R: X -> X -> Prop) :=
        X -> total R ->
            exists f: nat -> X, forall n, R (f n) (f (S n)).

    Lemma LS_impl_DC: LS_root -> dec_R -> DC_on' R.
    Proof using a.
        intros LS DecR _ total.
        destruct (LS Model__A a) as [N [[f sur] [h [ele_el__h [n Eqan]]]]].
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        unfold elementary_homomorphism in ele_el__h.
        apply ele_el__h in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h.
        destruct H as [R' [P1 P2]].
        assert (forall x y, dec (R' x y)) as dec__R'.
        { intros x y. destruct (DecR (h x) (h y)); firstorder. }
        destruct (@DC_ω _ _ f sur dec__R' P1 n) as [g [case0 Choice]].
        exists (g >> h); unfold ">>". 
        intro n'; now rewrite <- (P2 (g n') (g (S n'))).
    Qed.

    End dec__R_full.

    Section DC_pred_full.

    Definition PDC₀_root_on B (R: B -> B -> Prop) :=
        total R -> forall w, exists F : nat -> nat -> B, 
            (forall n, F 0 n  = w) /\ forall n a, exists b, R (F n a) (F (S n) b).

    Lemma LS_imples_PDC₀_root: LS_root' -> (PDC₀_root_on R).
    Proof.
        intros LS total w.
        destruct (LS _ _ Model__A w) as [N [(f & g & bij_l & bij_r) [h [ele_el__h [n Eqan]]]]].
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        apply ele_el__h in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h.
        destruct H as [R' [P1 P2]].
        exists (fun a b => match a, b with | O, b => w | S n, b => h (g b) end); split; [easy|].
        intros [|x] y.
        + rewrite <- Eqan.  
          destruct (P1 n) as [w' Hw'].
          rewrite P2 in Hw'.
          exists (f w'). now rewrite bij_l.
        + destruct (P1 (g y)) as [w' Hw'].
          rewrite P2 in Hw'.
          exists (f w'). now rewrite bij_l.
    Qed.

    Definition logical_dec_R := forall x y, logical_dec (R x y).

    Lemma LS_imples_DC_pred:  LS_root' -> logical_dec_R -> PDC_root_on R.
    Proof.
        intros LS  DecR total w.
        destruct (LS _ _ Model__A w) as [N [(f & g & bij_l & bij_r) [h [ele_el__h [n Eqan]]]]].
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        apply ele_el__h in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h.
        destruct H as [R' [P1 P2]].
        assert (forall x : N, logical_decidable (R' x)).
        intros x y. destruct (DecR (h x) (h y)); now try (left + right; rewrite P2).
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

    End DC_pred_full.

End DC.

















