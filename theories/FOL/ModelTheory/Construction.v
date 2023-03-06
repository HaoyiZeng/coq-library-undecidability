Require Import Undecidability.FOL.ModelTheory.Core.
Require Import Coq.Arith.Compare_dec.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Lia.

Notation "'Σ' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Section Construction.
    Context {Σf : funcs_signature} {Σp : preds_signature} {M: model}. 
    Existing Instance falsity_on.

    Section im_incl.

    Definition im_incl (ρ ρ': nat -> M) := forall x, Σ y, ρ x = ρ' y.
    Definition im_incl_k (ρ ρ': nat -> M) k := forall x, x < k -> Σ y, ρ x = ρ' y.

    End im_incl.

    Notation "ρ ≼ ρ'" := (im_incl ρ ρ') (at level 25).
    Notation "ρ ≼[ k ] ρ'" := (im_incl_k ρ ρ' k) (at level 25).

    Section incl_prop.

    Lemma incl_sat ρ ρ': ρ ≼ ρ' -> forall φ, exists ψ, M ⊨[ρ] φ <-> M ⊨[ρ'] ψ.
    Proof.
        intros H φ.
        unshelve eexists.
        exact (φ[fun x => $ (projT1 (H x))]).
        rewrite sat_comp.
        apply sat_ext.
        intro x; cbn.
        now destruct (H x).
    Qed.

    Lemma bound_incl ρ ρ': forall φ k, bounded k φ -> ρ ≼[k] ρ' -> exists ψ, M ⊨[ρ] φ <-> M ⊨[ρ'] ψ.
    Proof.
        intros.
        unshelve eexists.
        exact (let σ x := match (lt_dec x k) with
                | left cp =>  $ (projT1 (H0 x cp)) 
                | right _ =>  $ x 
                end in φ[σ]).
        rewrite sat_comp.
        apply bound_ext with k. exact H.
        intros; cbn.
        destruct (lt_dec n k); cbn.
        now destruct (H0 n l).
        congruence.
    Qed.
        

    Definition wit_env (ρ ρ_s: env M) φ := exists w, M ⊨[ρ_s w .: ρ] φ -> M ⊨[ρ] (∀ φ).

    Goal forall ρ ρ' ρ_s, ρ ≼ ρ' -> (forall φ, wit_env ρ' ρ_s φ) -> (forall φ, wit_env ρ ρ_s φ).
    Proof.
        intros.
        enough (forall w, ((ρ_s w) .: ρ) ≼ ((ρ_s w) .: ρ')).
        (* intros w x.
        exists (projT1 (H x)); cbn.
        destruct (H x); cbn.
        induction x; try easy. *)
        destruct (incl_sat H (∀ φ)) as [fψ fH].
        destruct (H0 fψ) as[w wit_ψ].
        destruct (incl_sat (H1 w) φ) as [ψ pH].
        Admitted.

    (* Definition wit_rel ρ ρ_s: Prop := (forall φ, next_env ρ ρ_s φ) /\ (ρ ≼ ρ_s). *)

    End incl_prop.


    Hypothesis dis_M: forall x y: M, (x = y) + (~ (x = y)).

    Lemma change (ρ ρ': env M): (forall x, exists y, ρ x = ρ' y) -> ρ ≼ ρ'.
    Proof.
        intros H x.
        apply W.
        intro x'.
        apply dis_M.
        exact (H x).
    Qed.

    Variable F: nat -> nat -> M.
    Hypothesis prop_F: forall n, (F n) ≼ (F (S n)).

    Lemma refl_incl: forall e, e ≼ e.
    Proof.
        intros n x.
        now exists x.
    Qed.

    Lemma trans_incl: forall a b c, a ≼ b -> b ≼ c -> a ≼ c.
    Proof.
        unfold "≼"; intros.
        destruct (H x) as [ny H'], (H0 ny) as [my H''].
        exists my; congruence.
    Qed.



    Lemma nil_F:
        forall n, F 0 ≼ F n.
    Proof.
        induction n. 
        - apply refl_incl.
        - eapply trans_incl.
          apply IHn.
          easy.
    Qed.

    Lemma succ_F: forall a b, a <= b -> F a ≼ F b -> F (S a) ≼ F (S b).
    Proof.
        intros a b; induction (b - a) eqn: E.
        - intros. assert (a = b) as -> by lia. apply refl_incl.
    Admitted.

    Lemma mono_F: forall a b, a <= b -> F a ≼ F b.
    Proof.
        intros a b; revert a; induction b.
        - intros a H. assert (a = 0) as -> by lia.
          apply refl_incl.
        - destruct a.
          intro; apply nil_F.
          intro H.
          cbn in H.
    Admitted.

    Definition wit_rel ρ ρ' :=
        forall φ, wit_env ρ ρ' φ /\ forall x, exists y, ρ x = ρ' y.


    Hypothesis depandent_path:
        forall root, exists F: nat -> nat -> M, F 0 = root /\ forall n, wit_rel (F n) (F (S n)).

    Variable init_ρ: nat -> M. 

    Definition next a : nat * nat :=
    match a with
    | (0,y) => (S y, 0)
    | (S x, y) => (x, S y)
    end.

    Fixpoint decode n : nat * nat :=
    match n with
    | 0 => (0,0)
    | S n' => next (decode n')
    end.

    Fixpoint sum n : nat :=
    match n with
    | 0 => 0
    | S n' => S n' + sum n'
    end.

    Definition encode x y : nat :=
    sum (x + y) + y.

    Definition π__1 x:= (fst (decode x)).
    Definition π__2 x:= (snd (decode x)).

    Hypothesis cantor_paring: forall x, encode (π__1 x) (π__2 x) = x.
    Hypothesis cantor_left: forall x y, π__1 (encode x y) = x.
    Hypothesis cantor_right: forall x y, (π__2 (encode x y)) = y.

    Definition fixed x := F (π__1 x) (π__2 x).

    Lemma le_encode: forall x, π__1 x <= x /\ π__2 x <= x.
    Proof.
        induction x.
        - easy.
        - unfold π__1, π__2; destruct IHx. split.
          destruct (decode (S x)).
    Admitted.
    


    Lemma incl_bound: forall bound, exists m, forall x, x < bound -> exists k, F m k = fixed x.
    Proof.
        intro bound.
        exists bound.
        intros x lb.
        assert (x <= bound) as lb' by lia.
        specialize (@mono_F x bound lb') as incl_x.
        enough (π__1 x <= x).
        specialize (@mono_F (π__1 x) x H) as incl_px.
        destruct (trans_incl incl_px incl_x (π__2 x)) as [y py].
        now exists y.
        induction x; cbn.
        easy.
    Admitted.


End Construction.