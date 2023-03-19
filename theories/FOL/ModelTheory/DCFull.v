Require Import Undecidability.FOL.FullSyntax.
Require Export Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.BinSig.
Require Import Undecidability.FOL.ModelTheory.SearchNat.


Require Export Vector.
Notation vec := t.

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

    Definition DC:=
        (forall x, exists y, R x y) -> forall w,
            (exists f : nat -> A, f 0 = w /\ forall n, R (f n) (f (S n))).

    Definition surjective {M N} (f: M -> N) :=
        forall n: N, exists m: M, f m = n.

    Definition a_coutable_model M :=
        exists f: nat -> M, surjective f.

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

    Hypothesis dec__R: forall x y, dec (R x y).

    Lemma LS_imples_DC: LS_countable -> DC.
    Proof using dec__R.
        intros LS total a.
        destruct (LS _ _ Model__A a) as [N [[f sur] [h [ele_el__h [n Eqan]]]]].
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
        destruct (@DC_ω _ _ f sur dec__R' P1 n) as [g [case0 Choice]].
        exists (g >> h); unfold ">>"; split.
        now rewrite case0.
        intro n'; now rewrite <- (P2 (g n') (g (S n'))).
    Qed.

    End dec__R_full.

    Section DC_pred_full.

    Hypothesis definiteness__R: forall x y,  (R x y) \/ ~ (R x y).

    Definition PDC:= 
        (forall x, exists y, R x y) -> forall w,
            exists P: nat -> A -> Prop, (forall x, exists! y, P x y) /\ P 0 w /\ forall n, exists x y,  P n x /\ P (S n) y /\ R x y. 

    Definition bijective_comp {X Y} :=
        exists f g, (forall x: X, g (f x) = x) /\ forall y: Y, f (g y) = y.

    Definition LS_countable_comp :=
        forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
            exists (N: model), @bijective_comp N nat /\ (exists h: N -> M, elementary_homomorphism h /\ exists n: N, h n = m).


    (* Definition OmniscientDependentChoiceP_on {A} (R: A -> A -> Prop) :=
        forall w,
        exists P : nat -> A -> Prop,
            (forall x, exists y, R x y) -> forall n : nat, function_rel P /\ P 0 w /\ forall n, exists x y,  P n x /\ P (S n) y /\ R x y.   

    Hypothesis IP_pred':
        forall (A' : Prop) X (P : (nat -> X -> Prop) -> Prop),
            (A' -> { R | P R }) -> { R | A' -> P R }.

    Lemma LS_imples_DC_pred': LS_countable_comp -> (@OmniscientDependentChoiceP_on _ R).
    Proof.
        intros LS m.
        destruct (LS _ _ Model__A m) as [N [(f & g & bij_l & bij_r) [h [ele_el__h [n Eqan]]]]].
        destruct(@IP_pred' (forall x, exists y, R x y) A
        (fun P => forall n : nat, function_rel P /\ P 0 m /\ forall n, exists x y,  P n x /\ P (S n) y /\ R x y)).
        intro total.
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        apply ele_el__h in total'.
        assert (Σ R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h.
        destruct X as [R' [P1 P2]].
        assert (forall x : N, logical_decidable (R' x)).
        intros x y. destruct (logical_dec__R (h x) (h y)); now try (left + right; rewrite P2).
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
        - now exists x.
    Qed. *)

    Lemma LS_imples_DC_pred: LS_countable_comp -> PDC.
    Proof using definiteness__R.
        intros LS total a.
        destruct (LS _ _ Model__A a) as [N [(f & g & bij_l & bij_r) [h [ele_el__h [n Eqan]]]]].
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        apply ele_el__h in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h.
        destruct H as [R' [P1 P2]].
        assert (forall x : N, logical_decidable (R' x)).
        intros x y. destruct (definiteness__R (h x) (h y)); now try (left + right; rewrite P2).
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










