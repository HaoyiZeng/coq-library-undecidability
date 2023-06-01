Require Import Undecidability.FOL.FullSyntax.
Require Export Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.BinSig.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Undecidability.FOL.ModelTheory.FullModelNotation.


Section joint.

Definition forall_times {Σ_funcs : funcs_signature} 
{Σ_preds : preds_signature} {ff : falsity_flag} n (phi : form) := 
    iter (fun psi => ∀ psi) n phi.

Fixpoint join {X n} (v : t X n) (rho : nat -> X) :=
    match v with
    | Vector.nil _ => rho
    | Vector.cons _ x n w => join w (x.:rho)
    end.

Fixpoint join' {X n} (v : t X n) (rho : nat -> X) :=
    match v with
    | Vector.nil _ => rho
    | Vector.cons _ x n w => x.:(join' w rho)
    end.

End joint.

 Notation "v '∗' rho" := (join v rho) (at level 20).
 Notation "v '∗r' rho" := (join' v rho) (at level 20).

Require Import Coq.Program.Equality.
Require Import Coq.Vectors.VectorDef.

Section facts_joint.

    Lemma joint_cons {A: Type} {n: nat} (v: vec A n) h rho: v ∗r (h .: rho) = 
        (append v (cons _ h _ (nil _))) ∗r rho.
    Proof.
        induction v; cbn. { easy. }
        now rewrite IHv.
    Qed.
    

    Lemma forall_joint `{ interp} n phi ρ:
        ρ ⊨ forall_times n phi <-> forall v : vec _ n, (v ∗ ρ) ⊨ phi.
    Proof.
        split.
        - intros Hp v; revert Hp; revert ρ. 
        dependent induction v; cbn. {easy. }
        + intros rho HI.
            specialize (HI h).
            now apply IHv in HI.
        - revert ρ; induction n; cbn.
        + intros ρ Hp; now specialize (Hp (nil _)).
        + intros ρ Hp d.
            apply IHn; intro v.
            now specialize (Hp (cons _ d _ v)).
    Qed.

    Definition S_add_1 n:
        S n = n + 1.
    Proof.
        induction n; try apply eq_refl; cbn.
        rewrite IHn; apply eq_refl.
    Qed.

    Definition S_add_1' n:
    n + 1 = S n.
    Proof.
        induction n; try apply eq_refl; cbn.
        rewrite IHn; apply eq_refl.
    Defined.

    Lemma cast_refl X n (v : Vector.t X n) : cast v (Logic.eq_refl) = v. 
    Proof.
        induction v; cbn; trivial. now rewrite IHv.
    Qed.

    Fixpoint vec_rev {X n} (v: vec X n): vec X n
    :=
        match v with
        | nil _ => nil _ 
        | cons _ x _ v => cast (append (vec_rev v) (cons _ x _ (nil _))) (S_add_1' _)
        end.

    Lemma rev_rev_eq {X n} (v: vec X n):
        vec_rev (vec_rev v) = v.
    Proof.
        dependent induction v. {easy. }
        cbn. 
    Admitted.
    

    Definition append_joint {X n} h (t: vec X n) ρ:
        append t (cons X h 0 (nil X)) ∗ ρ = (h .: t ∗ ρ).
    Proof.
        revert ρ; induction t; cbn. { easy. }
        intro ρ. now rewrite IHt.
    Qed.

    Lemma joint_eq_rev_joint' {X n} (v: vec X n) ρ: 
        (v ∗r ρ) = (vec_rev v) ∗ ρ.
    Proof.
        induction v; cbn. { reflexivity. }
        destruct S_add_1'. 
        rewrite cast_refl, append_joint.
        rewrite IHv.
        reflexivity.
    Qed.

    Lemma rev_joint_eq_joint {X n} (v: vec X n) ρ: 
        (vec_rev v ∗r ρ) = v ∗ ρ.
    Proof.
        induction v; cbn. { reflexivity. }
        destruct S_add_1'.
        rewrite cast_refl.
    Admitted.


    

    Lemma join_joint'_eq `{ interp} n phi ρ:
        (forall v : vec _ n, (v ∗ ρ) ⊨ phi) <-> (forall v : vec _ n, (v ∗r ρ) ⊨ phi) .
    Proof.
        split.
        - intros H' v.
          specialize (H' (vec_rev v)).
          now rewrite joint_eq_rev_joint'.
        - intros H' v. 
          specialize (H' (vec_rev v)).
          now rewrite <- rev_joint_eq_joint.
    Qed.
    

    Lemma forall_joint'  `{interp} n phi ρ:
    ρ ⊨ forall_times n phi <-> forall v : vec _ n, (v ∗r ρ) ⊨ phi.
    Proof.
        rewrite <- join_joint'_eq.
        apply forall_joint.
    Qed.
    
End facts_joint.


    

Section BDP.

    Variable A: Type.
    Variable R: forall {n}, vec A n -> A -> Prop.
    Variable a: A.
    Hypothesis total_A: forall n (v: vec A n), exists w, R v w.

    Instance sig_A : preds_signature | 0 :=
        {| preds := nat; ar_preds := fun n => S n |}.

    Definition tl {A n} (v: vec A (S n)): vec A n :=
        match v with
        | cons _ _ _ w => w
        end.

    Definition hd {A n} (v: vec A (S n)): A :=
        match v with
        | cons _ x _ _ => x
        end.

    Instance interp__A : interp A :=
    {
        i_func := fun F v => match F return A with end;
        i_atom := fun n (v: vec A (S n)) => R  (tl v) (hd v)
    }.

(*

    Definition add_1_r_red (n : nat) : S n = n + 1.
    Proof.
        induction n; [easy | simpl].
        rewrite IHn. reflexivity.
    Defined.


    Definition var_n_vec (n: nat): vec term n.
    Proof.
        induction n.
        exact (nil _).
        rewrite add_1_r_red.
        refine (append (IHn) (cons _ ($ n) _ (nil _))).
    Defined. *)

    Fixpoint var_n' {X} (f: nat -> X) (n m: nat)  :=
        match m with
        | 0 => nil _
        | S m => cons _ (f n) _ (var_n' f (S n) m) 
        end.
    Definition var_n_vec n := var_n' var 0 n.

    Lemma test1 X (w: X) {n: nat} (v: vec X n) ρ:
        (w .: (v ∗ ρ)) = (append v (cons _ w _ (nil _))) ∗ ρ.
    Proof.
        revert ρ; induction v; cbn.
        easy. intro ρ.
        now rewrite (IHv (h .: ρ)).
    Qed.
    
    Lemma test2 X (w: X) {n: nat} (v: vec X n) ρ:
        v ∗ (w .: ρ) = (cons _ w _ v) ∗ ρ.
    Proof.
        reflexivity.
    Qed.
    
    Lemma var_n_vec_rec n m (w: vec _ m)  (v: vec _ n) ρ:
        map (eval A interp__A (w ∗ (v ∗ ρ))) (var_n' var m n) = vec_rev v.
    Proof.
        revert m w; induction v. 
        - cbn. easy.  
        - cbn. dependent induction v.
    Admitted.

    Lemma var_n_vec_rec' n w v ρ:
        (Vector.map (eval A interp__A (w .: v ∗r ρ)) (var_n' var 1 n)) = v.
    Proof.
    revert ρ w. dependent induction v.
    - easy.
    - cbn. intros ρ w. f_equal. 
      rewrite <- (IHv ρ w) at 2.
      destruct n.
      + easy.
Admitted.
    

    Instance model__A: model := 
    {
        domain := A;
        interp' := interp__A 
    }.

    Fixpoint Fin n : Type :=
        match n with
        | 0 => False
        | S x => option (Fin x)
        end.

    Lemma For_M_test ρ:
        model__A ⊨[ρ] forall_times 2 (∃ (atom _ _ _ _  2 (var_n_vec (S 2)))).
    Proof.
        rewrite forall_joint'.
        intro v. 
        destruct (total_A v) as [w Jw].
        exists w.
        cbn.
        now do 3 dependent induction v.
    Qed.

    Lemma For_M' n ρ:
        model__A ⊨[ρ] forall_times n (∃ (atom _ _ _ _  n (var_n_vec (S n)))).
    Proof.
        rewrite forall_joint'; intro v.
        destruct (total_A v) as [w Hw].
        exists w; cbn.
        now rewrite var_n_vec_rec'.
    Qed.

    Definition LS_term :=
        forall M (i_M: interp M),
            exists (N: interp term), exists h: term -> M, (forall phi (ρ: env term), ρ ⊨ phi <-> (ρ >> h) ⊨ phi).

    Variable t_: nat -> term.
    Variable nth_: term -> nat.
    Hypothesis Ht: forall t, t_ (nth_ t) = t.

    Lemma dc_under_LS:
         LS_term-> exists f: nat -> A, forall n (v: vec nat n), exists m, R (map f v) (f m).
    Proof.
        intros ls.
        destruct (ls A (interp' model__A)) as [iterm [h Ph]].
        assert (forall (ρ: nat -> term) n, ρ ⊨ forall_times n (∃ (atom _ _ _ _  n (var_n_vec (S n))))) as H1.
        - intros ρ n.
          specialize (Ph (forall_times n (∃ (atom _ _ _ _  n (var_n_vec (S n))))) ρ) as ->.
          apply For_M'.
         - assert (forall (ρ: nat -> term) n (v: vec term n), exists m, (m.:( v ∗r ρ)) ⊨ ((atom _ _ _ _  n (var_n_vec (S n))))) as H2.
           intros ρ n v.
           specialize (H1 ρ n) as H1'.
          rewrite forall_joint' in H1'.
          now apply H1'.
          assert (forall (ρ : nat -> term) (n : nat) (v : vec term n),
          exists m : term, model__A ⊨[(m .: v ∗r ρ) >> h] atom n (var_n_vec (S n))) as H3.
          intros ρ n v.
          specialize (H2 ρ n v) as [m Hm].
          exists m. now rewrite <- Ph.
          assert (forall {n} m (v: vec _ n) ρ, model__A ⊨[ (m .: v ∗r ρ) >> h] atom n (var_n_vec (S n)) <-> R (map h v) (h m)).
          intros n m v ρ. cbn.
          admit.
          exists (fun n => h (t_ n)).
          intros n v.
          destruct (H3 (fun _ => $0) n (map t_ v)) as [m Hm].
          exists (nth_ m).
          rewrite Ht.
         rewrite H in Hm.
         now rewrite map_map in Hm. 
    Admitted.

End BDP.
