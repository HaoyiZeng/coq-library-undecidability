Require Import Undecidability.FOL.FullSyntax.
Require Export Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.BinSig.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Undecidability.FOL.ModelTheory.FullModelNotation.
Require Import Coq.Logic.EqdepFacts Coq.Logic.FinFun.


Locate Vector.t.
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


Fixpoint vec_snoc {X n} (v: vec X n) (x:X) : vec X (S n) := match v with
  nil _ => cons _ x _ (nil _)
| cons _ y _ v => cons _ y _ (vec_snoc v x) end.

Fixpoint vec_rev {X n} (v: vec X n): vec X n
:= match v with
    | nil _ => nil _ 
    | cons _ x _ v => vec_snoc (vec_rev v) x
    end.

Lemma vec_rev_snoc {X n} (v : vec X n) (x : X) :
  vec_rev (vec_snoc v x) = cons _ x _ (vec_rev v).
Proof.
  induction v in x|-*.
  - easy.
  - cbn. rewrite IHv. cbn. reflexivity.
Qed.

Lemma rev_rev_eq {X n} (v: vec X n):
    vec_rev (vec_rev v) = v.
Proof.
  induction v.
  - easy.
  - cbn. rewrite vec_rev_snoc, IHv. easy.
Qed.

    Lemma joint_cons {A: Type} {n: nat} (v: vec A n) h rho: 
    v ∗r (h .: rho) =  (append v (cons _ h _ (nil _))) ∗r rho.
    Proof.
        induction v; cbn. { easy. }
        now rewrite IHv.
    Qed.

    Lemma snoc_joint_rev {A: Type} {n: nat} (v: vec A n) h ρ:
        vec_snoc v h ∗r ρ = v ∗r (h .: ρ) .
    Proof.
        induction v. 
        - cbn. easy.
        - cbn. now rewrite IHv.
    Qed.

    Lemma snoc_joint {A: Type} {n: nat} (v: vec A n) (h: A) ρ:
        (vec_snoc v h) ∗ ρ = (h .: (v ∗ ρ)).
    Proof.
        induction v in ρ |-*; cbn.
        - easy.
        - now rewrite IHv.
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

    Lemma join_join_rev {A n} (v: vec A n) ρ: v ∗ ρ = vec_rev v ∗r ρ .
    Proof.
        dependent induction v.
        - cbn. easy.
        - cbn. rewrite IHv.
          now rewrite snoc_joint_rev.
    Qed.

    Lemma join_rev_join {A n} (v: vec A n) ρ: (vec_rev v) ∗ ρ = v ∗r ρ .
    Proof.
        dependent induction v.
        - cbn. easy.
        - cbn. rewrite <- IHv.
          rewrite snoc_joint.
          reflexivity.
    Qed.

    Definition append_joint {X n} h (t: vec X n) ρ:
        append t (cons X h 0 (nil X)) ∗ ρ = (h .: t ∗ ρ).
    Proof.
        revert ρ; induction t; cbn. { easy. }
        intro ρ. now rewrite IHt.
    Qed.

    Variable A: Type.
    Lemma lookup_join m n (w : vec _ m) (ρ : nat  -> A) : 
        (w ∗r ρ) (m + n) = ρ n.
    Proof.
    induction w in ρ,n|-*.
    - cbn. easy.
    - cbn. apply IHw.
    Qed.

    Lemma lookup_join_actually X n (v : vec X n) ρ p2 : 
        (v ∗r ρ) (FinFun.Fin2Restrict.f2n p2) = VectorDef.nth v p2.
    Proof.
    induction p2 in v,ρ|-*.
    - cbn. dependent induction v; easy.
    - unfold FinFun.Fin2Restrict.f2n in *.
        dependent induction v.
        cbn. destruct (Fin.to_nat p2) as [p2n Hp2].
        cbn in *. apply IHp2.
    Qed.

    Lemma lookup_join_actually_h {B: Type} n (v : vec A n) ρ p2 (h: A -> B): 
    ((v ∗r ρ) >> h) (FinFun.Fin2Restrict.f2n p2) = (VectorDef.nth (map h v) p2).
    Proof.
    induction p2 in v,ρ|-*.
    - cbn. dependent induction v; easy.
    - unfold FinFun.Fin2Restrict.f2n in *.
        dependent induction v.
        cbn. destruct (Fin.to_nat p2) as [p2n Hp2].
        cbn in *. apply IHp2.
    Qed.

    Lemma forall_joint' `{interp} n phi ρ:
    ρ ⊨ forall_times n phi <-> forall v : vec _ n, (v ∗r ρ) ⊨ phi.
    Proof.
        split; intros.
        - rewrite <- join_rev_join.
          now rewrite forall_joint in H0.
        - rewrite forall_joint.
          intros v.
          specialize (H0 (vec_rev v)).
          now rewrite join_join_rev.
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

    Fixpoint var_n' {X} (f: nat -> X) (n m: nat)  :=
        match m with
        | 0 => nil _
        | S m => cons _ (f n) _ (var_n' f (S n) m) 
        end.
    Definition var_n_vec n := var_n' var 0 n.

    Lemma nth_var X m n p2 (f:nat -> X) : 
        (VectorDef.nth (var_n' f m n) p2) = f (m + FinFun.Fin2Restrict.f2n p2).
    Proof.
    induction p2 in m|-*.
    - cbn. f_equal. apply plus_n_O.
    - cbn. unfold FinFun.Fin2Restrict.f2n in *.
        cbn. destruct (Fin.to_nat p2) as [p2n Hp2]. cbn.
        specialize (IHp2 (S m)). cbn in *. rewrite plus_n_Sm in IHp2. easy.
    Qed.

    Lemma foo n m (w : vec _ m) v ρ :
    Vector.map (@eval _ _ A interp__A (w ∗r (v ∗r ρ))) (var_n' var m n) = v.
    Proof.
    apply VectorSpec.eq_nth_iff. intros p1 p2 ->.
    erewrite nth_map. 2:reflexivity.
    rewrite nth_var. cbn.
    rewrite lookup_join.
    rewrite lookup_join_actually. easy.
    Qed.

    Lemma var_n_vec_rec' n w v ρ:
        (Vector.map (eval A interp__A (w .: v ∗r ρ)) (var_n' var 1 n)) =  v.
    Proof.
        exact (@foo n 1 (cons _ w _ (nil _)) v ρ).
    Qed.

    Instance model__A: model := 
    {
        domain := A;
        interp' := interp__A 
    }.

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

    Lemma decoding n m (v: vec term n) ρ (h: term -> A):
        R (Vector.map (eval A interp__A ((m .: v ∗r ρ) >> h)) (var_n' var 1 n)) 
          (((m .: v ∗r ρ) >> h) 0) 
        =
        R (map h v) (h m) .
    Proof.
        f_equal.
        apply VectorSpec.eq_nth_iff. intros p1 p2 ->.
        erewrite nth_map. 2:reflexivity.
        rewrite nth_var. cbn.
        change ((v ∗r ρ >> h) (Fin2Restrict.f2n p2) = nth (map h v) p2).
        rewrite lookup_join_actually_h. easy.
    Qed.
    

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
          now rewrite decoding.
          exists (fun n => h (t_ n)).
          intros n v.
          destruct (H3 (fun _ => $0) n (map t_ v)) as [m Hm].
          exists (nth_ m).
          rewrite Ht.
         rewrite H in Hm.
         now rewrite map_map in Hm. 
    Qed.

End BDP.

Section Result.

Variable t_: nat -> term.
Variable nth_: term -> nat.
Hypothesis Ht: forall t, t_ (nth_ t) = t.

Definition BDC:=
    forall (A: Type) (R: forall {n}, vec A n -> A -> Prop), 
        A -> (forall n (v: vec A n), exists w, R v w) ->
        (exists f: nat -> A, forall n (v: vec nat n), exists m, R (map f v) (f m)).

Theorem LS_implies_BDC: 
    LS_term -> BDC.
Proof.
    intros ls A R a total_R.
    now apply (dc_under_LS total_R Ht).
Qed.

End Result.

