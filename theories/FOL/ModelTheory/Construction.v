Require Import Undecidability.FOL.ModelTheory.Core.
Require Import Coq.Arith.Compare_dec.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Undecidability.FOL.ModelTheory.HenkinModel.


Notation "'Σ' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Section Construction.

    Context {Σf : funcs_signature} {Σp : preds_signature} {M: model}. 

    Section incl_def.

    Definition im_incl (ρ ρ': nat -> M) := forall x, Σ y, ρ x = ρ' y.
    Definition im_incl_k (ρ ρ': nat -> M) k := forall x, x < k -> Σ y, ρ x = ρ' y.

    End incl_def.

    Notation "ρ ≼ ρ'" := (im_incl ρ ρ') (at level 25).
    Notation "ρ ≼[ k ] ρ'" := (im_incl_k ρ ρ' k) (at level 25).

    Section incl_prop.

    Lemma sat_incl ρ ρ': ρ ≼ ρ' -> forall φ, 
        exists σ, (M ⊨[ρ] φ <-> M ⊨[ρ'] φ[σ]) /\ (forall x, (σ >> (eval M interp' ρ')) x = ρ x).
    Proof.
        intros H φ.
        exists (fun x => $ (projT1 (H x))).
        rewrite sat_comp.
        split.
        apply sat_ext.
        all: intro x; cbn; now destruct (H x).
    Qed.

    Lemma bounded_incl ρ ρ' φ k: bounded k φ -> ρ ≼[k] ρ' -> 
        exists σ, (M ⊨[ρ] φ <-> M ⊨[ρ'] φ[σ]) /\ 
            (forall x, x < k -> (σ >> (eval M interp' ρ')) x = ρ x).
    Proof.
        intros.
        exists (fun x => match (lt_dec x k) with
                | left cp =>  $ (projT1 (H0 x cp)) 
                | right _ =>  $ x 
                end).
        rewrite sat_comp.
        split.
        apply bound_ext with k. exact H.
        intros; cbn.
        destruct (lt_dec n k); cbn.
        now destruct (H0 n l).
        congruence.
        intros x l; cbn.
        destruct (lt_dec x k); cbn.
        now destruct (H0 x l0).
        congruence.
    Qed.

    Lemma map_cons_w (ρ ρ': env M) w  {n} (v: vec term n): 
        (forall t : term, In t v -> t ₜ[ M] ρ' = t`[fun x : nat => $(S x)] ₜ[ M] (w .: ρ') )
            -> map (eval M interp' ρ') v = map (eval M interp' (w .: ρ')) (map (subst_term (fun x : nat => $(S x))) v).
    Proof.
        intro H.
        induction v; cbn. {constructor. }
        rewrite IHv, (H h). {easy. }
        constructor.
        intros t H'; apply H.
        now constructor.
    Qed.

    Lemma cons_w (ρ ρ': env M) (σ: nat -> term) w:
        forall x, (σ >> eval M interp' ρ') x = (σ >> subst_term ↑) x ₜ[ M] (w .: ρ').
    Proof.
        unfold ">>".
        intro x; induction (σ x); cbn; try easy.
        now rewrite map_cons_w with (w := w).
    Qed.

    Definition wit_env (ρ ρ_s: env M) φ := exists w, M ⊨[ρ_s w .: ρ] φ -> M ⊨[ρ] (∀ φ).

    Lemma incl_impl_wit_env ρ ρ' ρ_s: ρ ≼ ρ' 
        -> (forall φ, wit_env ρ' ρ_s φ) -> (forall φ, wit_env ρ ρ_s φ).
    Proof.
        intros.
        destruct (sat_incl H (∀ φ)) as (σ & fH & EH).
        destruct (H0 (φ[up σ])) as [ws P].
        exists ws.
        intro Hp; rewrite fH. 
        apply P; revert Hp.
        rewrite sat_comp.
        apply sat_ext'.
        destruct x; cbn. { easy. }
        rewrite <- EH.
        apply (cons_w ρ ρ' σ (ρ_s ws)).
    Qed.

    Lemma bounded_incl_impl_wit_env ρ ρ' ρ_s: (forall φ, wit_env ρ' ρ_s φ) 
        -> (forall φ k, bounded k φ -> ρ ≼[k] ρ' -> wit_env ρ ρ_s φ).
    Proof.
        intros Rρ' φ k H Ink.
        assert (bounded k (∀ φ)) as HS.
        apply bounded_S_quant.
        apply (bounded_up H); lia.
        destruct (bounded_incl HS Ink ) as (σ & fH & EH).
        destruct (Rρ' (φ[up σ])) as [ws P].
        exists ws.
        intro Hp; rewrite fH. 
        apply P; revert Hp.
        rewrite sat_comp.
        apply (bound_ext _ H); intros n Ln. 
        destruct n; cbn. {easy. }
        rewrite <- EH.
        - now rewrite (cons_w ρ ρ' σ (ρ_s ws)).
        - lia.
    Qed.  

    End incl_prop.

    Section incl_Path.
(*     


    Hypothesis dis_M: forall x y: M, (x = y) + (~ (x = y)).

    Lemma change (ρ ρ': env M): (forall x, exists y, ρ x = ρ' y) -> ρ ≼ ρ'.
    Proof.
        intros H x.
        apply W.
        intro x'.
        apply dis_M.
        exact (H x).
    Qed.

    Lemma change_k (ρ ρ': env M) k: (forall x, x < k -> exists y, ρ x = ρ' y) -> ρ ≼[k] ρ'.
    Proof.
        intros H x Lx.
        apply W.
        intro x'.
        apply dis_M.
        exact (H x Lx).
    Qed. *)

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

    Lemma mono_F' a b: F a ≼ F (a + b) .
    Proof.
        induction b.
        - assert (a + 0 = a) as -> by lia; apply refl_incl.
        - assert (a + S b = S(a + b)) as -> by lia.
          eapply trans_incl. exact IHb. exact (prop_F (a + b)).
    Qed.

    Lemma mono_F a b: a < b -> F a ≼ F b.
    Proof.
        assert (a < b -> Σ c, a + c = b) .
        intro H; exists (b - a); lia.
        intro aLb.
        destruct (H aLb) as [c Pc].
        specialize (mono_F' a c).
        now rewrite Pc. 
    Qed.

    End incl_Path.

    Section Fixed_point.

    Variable F: nat -> nat -> M.

    Definition wit_rel ρ ρ' :=
        (forall φ, wit_env ρ ρ' φ) /\ forall x, exists y, ρ x = ρ' y.

    Definition wit_rel_comp ρ ρ' :=
        (forall φ, wit_env ρ ρ' φ) /\ forall x, ρ x = ρ' (2 * x).

    Variable init_ρ: nat -> M.

    Hypothesis depandent_path:
        F 0 = init_ρ /\ forall n, wit_rel_comp (F n) (F (S n)).

    Lemma wit_rel_comp_implies_incl ρ ρ':
        wit_rel_comp ρ ρ' -> ρ ≼ ρ'.
    Proof.
        intros H x; exists (2 * x).
        now destruct H as [_ P].
    Qed.

    Lemma depandent_path_comp:
        forall n, F n ≼ F (S n) .
    Proof.
        destruct depandent_path as [_ H].
        now intro n; eapply wit_rel_comp_implies_incl.
    Qed.

    Variable encode: nat -> nat -> nat.
    Variable π__1: nat -> nat.
    Variable π__2: nat -> nat.

    Hypothesis cantor_paring: forall x, encode (π__1 x) (π__2 x) = x.
    Hypothesis cantor_left: forall x y, π__1 (encode x y) = x.
    Hypothesis cantor_right: forall x y, (π__2 (encode x y)) = y.

    Definition fixed x := F (π__1 x) (π__2 x).


    Lemma union_incl n: (F n) ≼ fixed.
    Proof.
        intro x; exists (encode n x); cbn.
        unfold fixed.
        now rewrite cantor_left, cantor_right.
    Qed.

    Lemma union_fixed n: wit_rel (F n) fixed.
    Proof.
        split; intros.
        - unfold wit_env. 
          destruct depandent_path as [_ H].
          destruct (H n) as [H_ H_'].
          destruct (H_ φ) as [w H'].
          (* destruct (H'' w) as [w' Pw]. *)
          destruct (union_incl (S n) w) as [ws Pws].
          exists ws.
          intro; apply H'.
          now rewrite Pws.
        - exists (encode n x); cbn.
          unfold fixed.
          now rewrite cantor_left, cantor_right.
    Qed.

    (** Here we prove the principle of strong induction, induction on the natural
numbers where the inductive hypothesis includes all smaller natural numbers. *)


    Lemma bounded_cantor b:
        Σ E, forall x, x < b -> π__1 x < E.
    Proof.
        clear; strong induction b.
        specialize (H (pred b)).
        destruct b; [exists 0; intros; lia| ].
        destruct H as [Ep EP]; [lia |].
        destruct (lt_dec Ep ((π__1 b))); 
        exists (S (π__1 b)) + exists (S Ep); 
        intros x H'; destruct (lt_dec x b); specialize (EP x); 
        lia || now assert (x = b) as -> by lia; lia.
    Qed.


    Lemma bounded_rel b: 
        Σ E: nat, forall x, x < b -> Σ y, fixed x = F E y.
    Proof.
        intros.
        destruct (bounded_cantor b) as [E PE].
        exists E; intros.
        unfold fixed.
        specialize (PE _ H).
        specialize (mono_F depandent_path_comp PE) as H1.
        exists (projT1 (H1 (π__2 x))).
        now destruct (projT2 (H1 (π__2 x))).
    Qed.


    Theorem Fixed_point:
        wit_rel fixed fixed .
    Proof.
        split; intros.
        - destruct (find_bounded φ) as [b bφ].
          destruct (bounded_rel b) as [E P].
          (* enough (exists E: nat, forall x, x < b -> exists y, fixed x = F E y) as [E P]. *)
          unshelve eapply bounded_incl_impl_wit_env; [exact (F E) |exact b | |easy |..].
          + now destruct (union_fixed E) as [HB _].
          + intros x Lxb; apply (P x Lxb). 
        - now exists x.
    Qed.


    Definition path root:
        exists F, F O = root /\ forall n, wit_rel_comp (F n) (F (S n)).
    Proof.
    
    Admitted.



    End Fixed_point.

End Construction.



Section Result.

    (* For any model *)
    Context {Σf : funcs_signature} {Σp : preds_signature} {M: model}.

    (* If such path exists *)
    Variable root: env M.
    Hypothesis path:
        exists F, F O = root /\ forall n, wit_rel_comp (F n) (F (S n)).

    (* Consider a Cantor pairing *)
    Variable encode: nat -> nat -> nat.
    Variable π__1: nat -> nat.
    Variable π__2: nat -> nat.
    Hypothesis cantor_paring: forall x, encode (π__1 x) (π__2 x) = x.
    Hypothesis cantor_left: forall x y, π__1 (encode x y) = x.
    Hypothesis cantor_right: forall x y, (π__2 (encode x y)) = y.

    (* If the signature is countable *)
    Variable phi_ : nat -> form.
    Hypothesis Hphi : forall phi, exists n, phi_ n = phi.

    Theorem LS_downward: exists (N: model), N ⪳ M.
    Proof.
        destruct path as [F Pp'].
        specialize (depandent_path_comp Pp') as Incl. 
        specialize (Fixed_point  Pp'  cantor_left cantor_right) as N.
        unshelve eapply Tarski_Vaught_Test'.
        exact (fixed F π__1 π__2).
        all: try easy.
        now destruct N.
    Qed.

End Result.

