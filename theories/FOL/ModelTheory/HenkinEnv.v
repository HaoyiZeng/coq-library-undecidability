Require Import Undecidability.FOL.Completeness.TarskiCompleteness.
Require Import Undecidability.FOL.ModelTheory.FullModelNotation.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Undecidability.FOL.ModelTheory.FullHenkinModel.
Require Import Undecidability.FOL.ModelTheory.DCFull.
Require Import Lia Peano_dec.

Definition directed {X} (R: X -> X -> Prop) :=
    forall x y, exists z, R x z /\ R y z.
Definition total {X Y} (R: X -> Y -> Prop) := forall x, exists y, R x y.
Notation "R ∘ g" := (fun x y => R (g x) (g y)) (at level 30).

Definition DDC := forall X (R: X -> X -> Prop),
    X -> directed R -> exists f: nat -> X, directed (R ∘ f).
Definition BCC := forall X (R: nat -> X -> Prop),
    X -> total R -> exists f: nat -> X, forall n, exists w, R n (f w).
Definition BDP := forall X (P: X -> Prop),
    X -> exists f: nat -> X,
        (forall n, P (f n)) -> (forall x, P x).
Definition BEP := forall X (P: X -> Prop),
    X -> exists f: nat -> X,
        (exists x, P x) -> (exists n, P (f n)).

Section Incl_im.
    Variables A B C: Type.
    Definition im_sub (ρ: A -> C) (ρ': B -> C)  := forall x, exists y, ρ x = ρ' y.
    Definition im_sub_k (ρ: nat -> C) (ρ': B -> C)  k := forall x, x < k -> exists y, ρ x = ρ' y.
End Incl_im.

Notation "ρ ⊆ ρ'" := (im_sub ρ ρ') (at level 25).
Notation "ρ ⊆[ k ] ρ'" := (im_sub_k ρ ρ' k) (at level 25).

Section Incl_facts.

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

    Lemma refl_sub {A B} (e: A -> B): e ⊆ e.
    Proof.
        intros x.
        now exists x.
    Qed.

    Lemma trans_sub  {A B} (a b c: A -> B): a ⊆ b -> b ⊆ c -> a ⊆ c.
    Proof.
        unfold "⊆"; intros.
        destruct (H x) as [ny H'], (H0 ny) as [my H''].
        exists my; congruence.
    Qed.

End Incl_facts.

Section FixedModel.
    Context {Σf : funcs_signature} {Σp : preds_signature} {M: model} {nonempty: M}. 

    (* Definition of Henkin condition *)
    Section Henkin_condition.
        Definition succ (ρ: env M) (ρ_s: env M) (φ: form): Prop :=
            ((forall n: nat, M ⊨[ρ_s n .: ρ] φ) -> M ⊨[ρ] (∀ φ)) 
                /\ 
            (M ⊨[ρ] (∃ φ) -> exists m, M ⊨[ρ_s m .: ρ] φ).
    End Henkin_condition.

    Notation "ρ ⇒ ρ_s" := (forall φ, succ ρ ρ_s φ) (at level 25).
    Notation "ρ ⇒[ phi ] ρ_s" := (succ ρ ρ_s phi) (at level 25).

    (* Some technical lemmas about bounded *)
    Section TechnicalLemmas.

        Lemma map_eval_cons (ρ ρ': env M) w  {n} (v: vec term n): 
        (forall t : term, In t v -> t ₜ[ M] ρ' = t`[fun x : nat => $(S x)] ₜ[ M] (w .: ρ') ) -> 
            map (eval M interp' ρ') v = map (eval M interp' (w .: ρ')) (map (subst_term (fun x : nat => $(S x))) v).
        Proof.
            intro H.
            induction v; cbn. {constructor. }
            rewrite IHv, (H h); [easy|constructor|].
            intros t H'; apply H.
            now constructor.
        Qed.

        Lemma comp_cons (ρ ρ': env M) (σ: nat -> term) w:
            forall x, (σ >> eval M interp' ρ') x = (σ >> subst_term ↑) x ₜ[ M] (w .: ρ').
        Proof.
            unfold ">>".
            intro x; induction (σ x); cbn; try easy.
            now rewrite map_eval_cons with (w := w).
        Qed.

        Lemma im_bounded_sub (ρ ρ': env M) b:
            ρ ⊆[b] ρ' -> exists (ξ : nat -> nat), forall x, x < b -> (ρ x) = (ρ' (ξ x)).
        Proof.
            induction b; cbn; [intros |].
            - exists (fun _ => O); lia.
            - intros. destruct IHb as [ξ Pξ].
            intros x Hx; apply (H x); lia. 
            destruct (H b) as [w Hw]; [lia|].
            exists (fun i => if (eq_nat_dec i b) then w else (ξ i)).
            intros; destruct (eq_nat_dec x b) as [->| eH]; [easy|].
            eapply Pξ; lia.  
        Qed.

        Lemma im_bounded_sub_form ρ ρ' φ k: bounded k φ -> ρ ⊆[k] ρ' -> 
            exists σ, (M ⊨[ρ] φ <-> M ⊨[ρ'] φ[σ]) /\ (forall x, x < k -> (σ >> (eval M interp' ρ')) x = ρ x).
        Proof.
            intros H H'.
            destruct (@im_bounded_sub _ _ _ H') as [ξ Hξ].
            exists (fun x => $ (ξ x)); split.
            - rewrite sat_comp.  
            apply bound_ext with k. exact H.
            intros. cbn. now apply Hξ.
            -  cbn. intros x Hx. now rewrite Hξ.
        Qed.

        Lemma bounded_sub_impl_henkin_env ρ ρ' ρ_s: 
            ρ' ⇒ ρ_s -> forall φ k, bounded k φ -> ρ ⊆[k] ρ' -> ρ ⇒[φ] ρ_s.
        Proof.
            intros Rρ' φ k H Ink.
            assert (bounded k (∀ φ)) as HS.
            apply bounded_S_quant, (bounded_up H); lia.
            destruct (im_bounded_sub_form HS Ink ) as (σ & fH & EH).
            destruct (Rρ' (φ[up σ])) as [P _]. split.
            + intro Hp; rewrite fH. apply P; revert Hp.
            intros H' n'; rewrite sat_comp.
            unshelve eapply (bound_ext _ H). exact (ρ_s n' .: ρ). 
            intros n Ln. destruct n; cbn; [easy|]. rewrite <- EH.
            now rewrite (comp_cons ρ ρ' σ (ρ_s n')). lia. apply H'.
            + assert (bounded k (∃ φ)) as HS'. apply bounded_S_quant, (bounded_up H); lia.
            destruct (im_bounded_sub_form HS' Ink ) as (σ' & fH' & EH').
            specialize (Rρ' (φ[up σ'])) as [_ P']. rewrite fH'; intro Hp.
            destruct (P' Hp) as [w Hw]. apply P' in Hp. 
            exists w; revert Hw; rewrite sat_comp.
            apply (bound_ext _ H). intros x HL.
            induction x; cbn. easy. rewrite <- EH'.
            now rewrite (comp_cons ρ ρ' σ' (ρ_s w)). lia.
        Qed.

        Lemma incl_impl_wit_env ρ ρ' ρ_s: 
            ρ' ⇒ ρ_s -> ρ ⊆ ρ' -> ρ ⇒ ρ_s.
        Proof.
            intros H IN φ.
            destruct (find_bounded φ) as [k Hk].
            apply (@bounded_sub_impl_henkin_env ρ ρ' ρ_s H φ k Hk).
            intros x _; apply IN.
        Qed.

    End TechnicalLemmas.

    (* Some facts about merging two countable set *)
    Section Merge.

        Definition merge {A: Type} (f1 f2: nat -> A): nat -> A :=
            fun n => match EO_dec n with 
                | inl L => f1 (projT1 L)
                | inr R => f2 (projT1 R)
            end.
        
        Fact merge_even {A: Type} (f1 f2: nat -> A):
            forall n, (merge f1 f2) (2 * n) = f1 n. 
        Proof.
            intros n. 
            unfold merge.
            destruct (EO_dec (2*n)).
            f_equal. destruct e. cbn; lia.
            destruct o. lia.
        Qed.
        
        Fact merge_odd {A: Type} (f1 f2: nat -> A):
            forall n, (merge f1 f2) (2 * n + 1) = f2 n. 
        Proof.
            intros n. 
            unfold merge.
            destruct (EO_dec (2*n + 1)).
            destruct e. lia.
            f_equal. destruct o. cbn; lia.
        Qed.
        
        Fact merge_l: forall {A: Type} (f1 f2: nat -> A), (f1 ⊆ merge f1 f2).
        Proof.
            intros A f1 f2 x; exists (2*x).
            assert (even (2*x)) by (exists x; lia).
            unfold merge; destruct (EO_dec (2*x)).
            enough (pi1 e = x) as -> by easy; destruct e; cbn; lia.
            exfalso; apply (@EO_false (2*x)); split; easy.
        Qed.
        
        Fact merge_r: forall {A: Type} (f1 f2: nat -> A), (f2 ⊆ merge f1 f2).
        Proof.
            intros A f1 f2 x; exists (2*x + 1).
            assert (odd (2*x + 1)) by (exists x; lia).
            unfold merge; destruct (EO_dec (2*x + 1)).
            exfalso; apply (@EO_false (2*x + 1)); split; easy.
            enough (pi1 o = x) as -> by easy; destruct o; cbn; lia.
        Qed.
        
        Fact merge_ex: forall {A: Type} (f1 f2: nat -> A), 
            forall x, exists y, f1 y = merge f1 f2 x \/ f2 y = merge f1 f2 x.
        Proof.
            intros A f1 f2 x; unfold merge.
            destruct (EO_dec x) as [[i Hi]|[i Hi]]; now exists i; (left + right). 
        Qed.

    End Merge.

    Definition henkin_next A B := A ⇒ B /\ A ⊆ B.
    Notation "A '~>' B" := (henkin_next A B) (at level 60).

    Section Next_env.
        Lemma trans_succ a b c:
        (a ~> b) -> (b ~> c) -> (a ~> c).
        Proof.
            intros [H1 S1] [H2 S2]; split; [intro φ| ].
            destruct (H1 φ) as [H11 H12], (H2 φ) as [H21 H22];
            split; intro H.
            - apply H11. intro n. destruct (S2 n) as [w ->]. apply H.
            - destruct (H12 H) as [w Hw].
            destruct (S2 w) as [w' Hw'].
            exists w'. rewrite <- Hw'; easy.
            - eapply (trans_sub S1 S2).
        Qed.

    End Next_env.

    (* This section shows that countable directed F implies a fixpoint of ~> *)
    Section direcred_fixpoint.

        Variable F: nat -> env M.
        Hypothesis F_hypo: forall x y, exists k,  F x ~> F k /\ F y ~> F k.

        (* Since ~> is a transitive relation *)
        Lemma domain: forall (l: list nat), exists k, 
            forall x, List.In x l -> F x ~> F k.
        Proof.
            intro l; induction l as [|a l [k Hk]].
            - exists 42. intros x [].
            - destruct (F_hypo a k) as [w [Haw Hkw]].
            exists w; intros x [<-|Hx].
            + apply Haw.
            + eapply trans_succ.
                now apply Hk. apply Hkw. 
        Qed.

        Opaque encode_p.

        Definition fixpont_env: env M := fun x => F (π__1 x) (π__2 x).

        Require Import List.
        Import ListNotations.

        Lemma fixpont_env_incl n: F n ⊆ fixpont_env.
        Proof.
            intro x; exists (encode n x); cbn.
            unfold fixpont_env.
            now rewrite cantor_left, cantor_right.
        Qed.

        Lemma fixpoint_succ n: F n ⇒ fixpont_env.
        Proof.
            intro φ.
            destruct (find_bounded φ) as [y Hy].
            unshelve eapply bounded_sub_impl_henkin_env.
            exact (F n).
            exact y. destruct (@domain [n]) as [k [Pk _]].
            firstorder.
            intro phi; destruct (Pk phi) as [H1 H2].
            split; intro H.
            - apply H1. intro x; destruct (fixpont_env_incl k x) as [w ->]; apply H.
            - destruct (H2 H) as [w Hw]. destruct (fixpont_env_incl k w) as [w' Hw'].
            exists w'. now rewrite <- Hw'.
            - trivial.
            - intros x' _. now exists x'.
        Qed.    

        Fixpoint n_lsit n :=
            match n with
            | O => []
            | S n => n::n_lsit n
            end.

        Lemma In_n_list n:
            forall a, a < n <-> In a (n_lsit n).
        Proof.
            induction n; cbn.
            - lia.
            - intro x; split. 
            + intros Hx. 
                assert (x = n \/ x < n) as [->| H1] by lia.
                now constructor. right. apply IHn; lia.
            + intros [->|H]; [lia|]. rewrite <- (IHn x) in H. lia.
        Qed.

        Lemma new_bounded b: 
            exists E: nat, fixpont_env ⊆[b] (F E).
        Proof.
            destruct (bounded_cantor b) as [E PE].
            destruct(@domain (n_lsit E)) as [K HK].
            exists K; intros x H.
            unfold fixpont_env.
            specialize (PE _ H).
            enough (In (π__1 x) (n_lsit E)) as H1.
            destruct (HK (π__1 x) H1) as [_ H3].
            exact (H3 (π__2 x)).
            now apply In_n_list.
        Qed.

        Theorem fixpoint_env_Fixed_point: fixpont_env ⇒ fixpont_env.
        Proof.
            intros.
            destruct (find_bounded φ) as [b bφ].
            destruct (new_bounded b) as [E P].
            unshelve eapply bounded_sub_impl_henkin_env; [exact (F E) |exact b|..]; try easy.
            apply (fixpoint_succ E).
        Qed.

        Opaque encode_p. 

    End direcred_fixpoint.

    (* This sectiob shows that ~> is directed *)
    Section Next_env_directed.
        Hypothesis bdp: BDP.
        Hypothesis bep: BEP.
        Hypothesis bcc : BCC.
        Variable phi_ : nat -> form.
        Variable nth_ : form -> nat.
        Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.

        Lemma BCC_term: forall B (R: form -> B -> Prop), 
            B -> (forall x, exists y, R x y) -> 
                exists f: (nat -> B),  forall n, exists w, R n (f w).
        Proof.
            intros B R b totalR.
            destruct (@bcc B (fun n => R (phi_ n)) b) as [g Pg].
            intro x. apply (totalR (phi_ x)).
            exists g. intro n. 
            specialize (Pg (nth_ n)).
            now rewrite Hphi in Pg.
        Qed.

        Definition universal_witness:
            forall ρ, exists (W: nat -> M), forall φ, (forall w, M ⊨[W w.:ρ] φ) -> M ⊨[ρ] ∀ φ.
        Proof.
            intros ρ.
            destruct (@BCC_term (nat -> M) (fun phi h => (forall w, M ⊨[(h w) .: ρ] phi) -> M ⊨[ρ] (∀ phi))) as [F PF].
            { exact (fun n => nonempty). }
            - intro φ; destruct (bdp (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
            exact (ρ (nth_ φ)). exists w; intro Hx; cbn; now apply Hw.
            - exists (fun (n: nat) => F (π__1 n) (π__2 n)).
            intro φ; specialize (PF φ).
            intro H'. destruct PF as [[] PF]; apply PF.
            intro w.
            specialize (H' (encode 0 w)).
            now rewrite cantor_left, cantor_right in H'.
            intro w. specialize (H' (encode (S n) w)).
            now rewrite cantor_left, cantor_right in H'.
        Qed.

        Definition existential_witness:
            forall ρ, exists (W: nat -> M), forall φ, M ⊨[ρ] (∃ φ) -> (exists w, M ⊨[W w.:ρ] φ).
        Proof.
            intros ρ.
            destruct (@BCC_term (nat -> M) (fun phi h =>  M ⊨[ρ] (∃ phi) -> (exists w, M ⊨[(h w) .: ρ] phi))) as [F PF].
            { exact (fun n => nonempty). }
            - intro φ; destruct (bep (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
            exact (ρ O). exists w; intro Hx; cbn; now apply Hw.
            - exists (fun (n: nat) => F (π__1 n) (π__2 n)).
            intro φ; specialize (PF φ).
            intro H'. destruct PF as [[] PF]. 
            destruct (PF H') as [w Pw].
            exists (encode 0 w).
            now rewrite cantor_left, cantor_right.
            destruct (PF H') as [w Pw].
            exists (encode (S n) w).
            now rewrite cantor_left, cantor_right.
        Qed.

        Lemma Henkin_witness:
            forall ρ, exists (W: nat -> M), ρ ⇒ W.
        Proof.
            intros ρ.
            destruct (universal_witness ρ) as [Uw PUw].
            destruct (existential_witness ρ) as [Ew PEw].
            exists (merge Uw Ew); intros φ; split; intro Hφ.
            - apply PUw; intro w.
            destruct (merge_l Uw Ew w) as [key ->].
            apply (Hφ key). 
            - destruct (PEw _ Hφ) as [w Pw].
            destruct (merge_r Uw Ew w) as [key Hk].
            exists key. now rewrite <- Hk.
        Qed.

        Lemma Next_env:
            forall ρ, exists (W: nat -> M), ρ ~> W.
        Proof.
            intros ρ.
            destruct (Henkin_witness ρ) as [W' HW].
            exists (merge W' ρ); split.
            - intros φ; destruct (HW φ) as [H1 H2]; split; intro Hφ.
            apply H1. intro n. specialize (Hφ (2 * n)).
            now rewrite merge_even in Hφ.
            destruct (H2 Hφ) as [w Hw].
            exists (2 * w). now rewrite merge_even.
            - apply merge_r.
        Qed.

        Definition directed_Henkin_env: forall ρ1 ρ2, exists ρ, (ρ1 ~> ρ) /\ (ρ2 ~> ρ).
        Proof.
            intros ρ1 ρ2.
            pose (σ := merge ρ1 ρ2).
            destruct (Next_env σ) as [ρ [H1 H2]].
            exists ρ; split; split.
            + eapply incl_impl_wit_env. exact H1. apply merge_l.
            + eapply trans_sub. apply merge_l. apply H2.
            + eapply incl_impl_wit_env. exact H1. apply merge_r.
            + eapply trans_sub. apply merge_r. apply H2.
        Qed.
    End Next_env_directed.

End FixedModel.

Section Result.

    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Variable phi_: nat -> form.
    Variable nth_: form -> nat.
    Hypothesis Hphi: forall phi, phi_ (nth_ phi) = phi.

    Definition LS_on (M: model) := 
        exists (N: interp term) (h: term -> M), 
            forall phi (ρ: env term), ρ ⊨ phi <-> M ⊨[ρ >> h] phi.

    Definition LS := forall M: model, M -> LS_on M.

    Theorem LS_downward:
        BDP -> BEP -> DDC -> BCC -> LS.
    Proof.
        intros BDP BEP DDC BCC M m.
        destruct (DDC _ (henkin_next)) as [F PF].
        { exact (fun n => m). }
        { intros A B. unshelve eapply directed_Henkin_env; eauto. }
        pose (fixpoint_env_Fixed_point PF) as Succ.
        specialize Henkin_env_el with (phi_ := phi_)  (h := fixpont_env F) as [N PN].
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        split; intros φ; [apply (Succ φ)| apply (Succ φ)].
        now exists N, (morphism (fixpont_env F)).
    Qed.

End Result.