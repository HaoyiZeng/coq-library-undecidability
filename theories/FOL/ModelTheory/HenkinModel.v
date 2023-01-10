From Undecidability Require Import Synthetic.EnumerabilityFacts Synthetic.ListEnumerabilityFacts Shared.ListAutomation.
Require Import Undecidability.FOL.Completeness.TarskiCompleteness.
Require Import Undecidability.FOL.ModelTheory.Core.
Local Set Implicit Arguments.


(* Gives the proof that any model with term as domain is countable. 
   It may be possible to generalize to arbitrary cardinality depandent
   on signature. *)
Section TermModelIsCountable.
    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Existing Instance falsity_on.

    (* Proof of countable *)
    Context {HdF : eq_dec Σf} {HdP : eq_dec Σp}.
    Variable eF : nat -> option Σf.
    Context {HeF : enumerator__T eF Σf}.
    Variable eP : nat -> option Σp.
    Context {HeP : enumerator__T eP Σp}.

    Variable list_Funcs : nat -> list syms.
    Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

    Definition injects X Y := exists f : X -> Y, forall x x', f x = f x' -> x = x'.
    Definition infinite X := injects nat X.
    Definition same_cardinality X Y := injects X Y /\ injects Y X.

    Definition a_coutable_model M :=
        exists f: nat -> M, surjective f.

    Lemma term_model_countable: a_coutable_model term.
    Proof.
        destruct (enumT_term enum_Funcs') as [f H]. 
        exists (fun n => match f n with None => var n | Some t => t end).
        intro t. destruct (H t) as [n eq].
        exists n. now rewrite eq.
    Qed.


    (* 
    Variable eP : nat -> option Σp.
    Context {HeP : enumerator__T eP Σp}.

    Lemma term_model_card:
        same_cardinality Σ_f term.
    *)

(* 
   In the section, the Löwenheim–Skolem theorem downward part is shown 
   by henkin construction. We assume that the model M is non-empty and 
   classical, so this is basically a simple application of the model 
   existing Lemma.

   Result:
   ∀ M: model, ∃ N: model, M ≡ N and N is countable
*)
Section HenkinModel.
    (* Consider a nonempty classical model *)
    Variable M: model.
    Hypothesis classical_model: classical interp'.
    Hypothesis noempty: M.

    Definition input_theory: theory := theory_of_model M.

    Definition output_theory: theory := 
        Out_T (construct_construction (input_bot (closed_theory_of_model M))).

    Instance term_model M: model := 
    {
        domain := term;
        interp' := model_bot (closed_theory_of_model M)
    }.


    Lemma Hcon_in_M: consistent class input_theory.
    Proof.
        intros H. 
        enough (M ⊨[_] ⊥).
        exact (H0 (fun _ => noempty)).
        destruct H as [L [InL InCon]].
        intro rho; eapply sound_for_classical_model.
        exact classical_model. exact InCon.
        intros s h%(InL s).
        destruct h as [_ hpo]. 
        exact (hpo _).
    Qed.
    (* By Soundness of classical model *)

    Corollary Hcon_out_M: consistent class output_theory.
    Proof.
        intro H; apply Hcon_in_M.
        apply Out_T_econsistent with 
        (construct_construction (input_bot (closed_theory_of_model _))); assumption.
    Qed.

    Lemma classical_model': forall p φ, (M ⊨[p] ((¬ ¬ φ) → φ)).
    Proof.
        intros; cbn; intros.
        apply classical_model with ⊥.
        intro; exfalso.
        now apply H.
    Qed.
    (* A classical proof :) *)

    Lemma contain_out_in:
        forall phi, closed phi -> 
            phi ∈ output_theory -> phi ∈ input_theory.
    Proof.
        intros φ closed_φ H.
        split. { assumption. }
        intro p.
        apply classical_model'; intros nphisat.
        assert (¬ φ ∈ output_theory).
        assert (closed (¬ φ)).
        constructor; eauto; constructor.
        apply Out_T_sub; split; eauto.
        intro p'; apply (sat_closed _ p p').
        all: try easy.
        apply Hcon_out_M.
        exists [φ; ¬ φ]; split.
        intros phi [<-|[<-|]]; easy.
        eapply IE with (phi := φ).
        eapply Ctx; now right.
        eapply Ctx; now left.
    Qed.

    (*  For any noempty and classical model M, there exists a countable term
        model which is elementary equivalence to M, whenever the signature is 
        at most countable. 
    *)
    Theorem LS_downward_weaker: 
        exists N: model, a_coutable_model N /\ M ≡ N.
    Proof.
        exists (term_model M).
        split. {apply term_model_countable. }
        split; intros.
        - apply (sat_closed _ p var). { assumption. }
          apply valid_T_model_bot. apply Hcon_in_M.
          unfold "∈", theory_of_model; eauto.
        - apply contain_out_in. { assumption. }
          setoid_rewrite <- subst_var.
          apply model_bot_correct.
          apply Hcon_in_M.
          eauto.
    Qed.

End HenkinModel.


(* 
    In this section, a stronger version of the Löwenheim–Skolem theorem downward part
    is shown based on the model satisfying the witness property, and the elementary 
    embedding from the henkin model to the original model is constructible.

   Result:
   ∀ M: model, M satisfy the witness property → ∃ N: model, N ⪳ M and N is countable.
*)

Section TheWitness.

    Definition closed_term t := bounded_t 0 t.
    Existing Instance falsity_on.    

    (* A nonempty model *)
    Variable M: model. 
    Hypothesis nonempty: M.

    (* which satify the witness property *)
    Variable phi_ : nat -> form.
    Hypothesis Hphi : forall phi, exists n, phi_ n = phi.
    Variable wit_: nat -> term.
    Definition witness_prop_ n := 
         M ⊨[_] (((phi_ n)[(wit_ n)..]) → ∀ (phi_ n)).
    Hypothesis Hwitness_prop: 
        forall n, closed_term (wit_ n) /\ witness_prop_ n.

    Definition h: env M := fun _ => nonempty.
    Definition morphism: term -> M := eval M interp' h.
    Definition theory_under h: theory :=
        fun phi => M ⊨[h] phi.

    Instance interp_term: interp term :=
        {| i_func := func; i_atom := fun P v => atom P v ∈ theory_under h|}.
    Instance N: model :=
        { domain := term; interp' := interp_term }.


    Lemma eval_eval (ρ: env term) (t: term):
        (t ₜ[N] ρ) ₜ[M] h =
                 t ₜ[M] (fun x => (ρ x) ₜ[M] h).
    Proof.
          induction t; try easy; cbn.
          apply f_equal; rewrite map_map; apply map_ext_in.
          now apply IH.
    Qed.

    Lemma map_eval_eval (ρ: env term) {n} (v: t term n):
            map (fun t => (t ₜ[N] ρ) ₜ[M] h) v =
            map (fun t => t ₜ[M] (fun x => (ρ x) ₜ[M] h)) v.
    Proof.
        apply map_ext, eval_eval.
    Qed.

    Theorem LS_downward_under_witness: 
        exists (N: model), a_coutable_model N /\ N ⪳ M.
    Proof.
        exists N. split. {apply term_model_countable. }
        exists morphism; intros φ.
        induction φ using form_ind_falsity; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval.
        - destruct b0; cbn; intuition.
        - destruct q; split.
          + intros H d; destruct (Hphi φ) as [i phi].
            specialize (H (wit_ i)); destruct (@Hwitness_prop i) as [witness_closed witness_prop__i].
            apply IHφ in H; unfold witness_prop_ in witness_prop__i; rewrite phi in witness_prop__i.
            eapply witness_prop__i.
            revert H; setoid_rewrite sat_comp; cbn.
            eapply sat_ext; induction x; cbn. 2: trivial.
            now apply bounded_eval_t with 0, witness_closed.
          + intros H d; rewrite (IHφ (d.:ρ)).
            specialize (H (morphism d)).
            revert H; apply sat_ext.
            induction x; easy.
    Qed.

End TheWitness.


(* Section DC.
    Variable M: model. 
    Hypothesis nonempty: M.
    (* A nonempty model *)


    Variable phi_ : nat -> form.
    Hypothesis Hphi : forall phi, exists n, phi_ n = phi.
    Variable wit_: nat -> option term.
    (* Maybe with the countable choice? We have *)
    Hypothesis choiceWit:
        forall n, match wit_ n with
          | None => forall t, ~ (bounded_t 0 t /\ M ⊨[_] (∀ (phi_ n) → ((phi_ n)[t..])))
          | Some t => bounded_t 0 t /\ M ⊨[_] (((phi_ n)[t..]) → ∀ (phi_ n))
        end.

    Variable inaccessible: M.
    Hypothesis inaccessible_prop: forall t, 
        bounded_t 0 t -> ~ forall ρ, (t ₜ[M] ρ) = inaccessible.

    Definition h': env M :=
        fun n => match wit_ n with
            | None => inaccessible
            | Some t => t ₜ[M] (fun _ => nonempty)
            end.
    Definition morphism': term -> M := eval M interp' h'.

    Instance interp_term': interp term :=
        {| i_func := func; i_atom := fun P v => atom P v ∈ theory_under h'|}.
    Instance N': model :=
        { domain := term; interp' := interp_term' }.

    Lemma eval_eval' (ρ: env term) (t: term):
        (t ₜ[N'] ρ) ₜ[M] h' = 
                 t ₜ[M] (fun x => (ρ x) ₜ[M] h'). 
    Proof.
          induction t; try easy; cbn. 
          apply f_equal; rewrite map_map; apply map_ext_in.
          now apply IH.
    Qed.

    Lemma map_eval_eval' (ρ: env term) {n} (v: t term n):
        map (fun t => (t ₜ[N'] ρ) ₜ[M] h') v =
        map (fun t => t ₜ[M] (fun x => (ρ x) ₜ[M] h')) v.
    Proof.
    apply map_ext, eval_eval'.
    Qed.


    Theorem LS_downward'':
        exists (N: model) (h: N -> M), elementary_homomorphism h.
    Proof.
        exists N', morphism'; intros φ. 
        induction φ using form_ind_falsity; intro; try easy. 
        - cbn; now rewrite map_map, map_eval_eval'.
        - destruct b0; cbn; intuition.
        - destruct q; split. 
          + intros H d; destruct (Hphi φ) as [i phi].
            specialize (H (var i)); specialize (@choiceWit i).
            apply IHφ in H; rewrite phi in choiceWit.
            destruct (wit_ i) eqn: E.
            ++ eapply choiceWit; cbn.
               revert H; setoid_rewrite sat_comp; cbn.
               eapply sat_ext; induction x; cbn. 2: trivial.
               destruct choiceWit as [witness_closed _].
               unfold h'. rewrite E. 
               now apply bounded_eval_t with 0, witness_closed.
            ++ admit.
          + intros H d; rewrite (IHφ (d.:ρ)).
            specialize (H (morphism' d)).
            revert H; apply sat_ext.
            induction x; easy.
    Admitted.

End DC. *)

Section WithoutWitness.

    Existing Instance falsity_on.    

    (* A nonempty model *)
    Variable M: model. 
    Hypothesis nonempty: M.

    (* which satify the witness property *)
    Variable phi_ : nat -> form.
    Hypothesis Hphi : forall phi, exists n, phi_ n = phi.
    Variable dep: nat -> M.
    Hypothesis witness_prop_ : 
        forall n ρ, M ⊨[(dep n).:ρ] (((phi_ n)) → ((∀ phi_ n)[↑])).

    Definition morphism__d: term -> M := eval M interp' dep.

    Instance interp_term__d: interp term :=
        {| i_func := func; i_atom := fun P v => atom P v ∈ theory_under dep|}.
    Instance N__d: model :=
        { domain := term; interp' := interp_term__d }.


    Lemma eval_eval__d (ρ: env term) (t: term):
        (t ₜ[N__d] ρ) ₜ[M] dep =
                 t ₜ[M] (fun x => (ρ x) ₜ[M] dep).
    Proof.
          induction t; try easy; cbn.
          apply f_equal; rewrite map_map; apply map_ext_in.
          now apply IH.
    Qed.

    Lemma map_eval_eval__d (ρ: env term) {n} (v: t term n):
            map (fun t => (t ₜ[N__d] ρ) ₜ[M] dep) v =
            map (fun t => t ₜ[M] (fun x => (ρ x) ₜ[M] dep)) v.
    Proof.
        apply map_ext, eval_eval__d.
    Qed.


    Theorem LS_downward_under_witness: 
        exists (N: model), a_coutable_model N /\ N ⪳ M.
    Proof.
        exists N__d. split. {apply term_model_countable. }
        exists morphism__d; intros φ.
        induction φ using form_ind_falsity; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval__d.
        - destruct b0; cbn; intuition.
        - destruct q; split.
          + intros H d; destruct (Hphi φ) as [i phi].
            cbn in H. 
          specialize (@witness_prop_ i (ρ >> morphism__d)).
          cbn in witness_prop_.
          rewrite phi in witness_prop_.
          cbn in witness_prop_.
         

          destruct (@Hwitness_prop i) as [witness_closed witness_prop__i].

            specialize (H (wit_ i)). 
            apply IHφ in H; unfold witness_prop_ in witness_prop__i; rewrite phi in witness_prop__i.
            eapply witness_prop__i.
            revert H; setoid_rewrite sat_comp; cbn.
            eapply sat_ext; induction x; cbn. 2: trivial.
            now apply bounded_eval_t with 0, witness_closed.
          + intros H d; rewrite (IHφ (d.:ρ)).
            specialize (H (morphism d)).
            revert H; apply sat_ext.
            induction x; easy.
    Qed.

End TheWitness.

End TermModelIsCountable.


(* Section Final.

    (* 
        Upward will change the signature 
        Then given the model over this new signature
        Downward can provide the term model over term
        wich has the same cardinality as X.
    *)

    Context {Σf : funcs_signature} {Σp : preds_signature}.

    Hypothesis LS_weaker: 
        forall (M: model) X (f: X -> M), infinite X -> injective f ->
            exists N: model, N ≡ M /\ same_cardinality N X.

    Hypothesis LS_stronger: 
        DC <-> forall (M: model) X (f: X -> M), 
                infinite X -> injective f -> exists N: model, N ⪳ M /\ same_cardinality N X.

End Final. *)
