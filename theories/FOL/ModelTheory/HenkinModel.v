From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation.
Require Import Undecidability.FOL.Completeness.TarskiCompleteness.
Require Import Undecidability.FOL.Deduction.FragmentND.
Require Import Undecidability.FOL.ModelTheory.Core.
Local Set Implicit Arguments.


(* 
   In the section, the Löwenheim–Skolem theorem downward part is shown 
   by henkin construction. We assume that the model M is non-empty and 
   classical, so this is basically a simple application of the model 
   existing Lemma.

   Result:
   ∀ M: model, ∃ N: model, M ≡ N and N is countable
*)

Section HenkinModel.
    Context {Σf : funcs_signature} {Σp : preds_signature}.

    (* Proof of countable *)
    Context {HdF : eq_dec Σf} {HdP : eq_dec Σp}.
    Variable eF : nat -> option Σf.
    Context {HeF : enumerator__T eF Σf}.
    Variable eP : nat -> option Σp.
    Context {HeP : enumerator__T eP Σp}.

    Variable list_Funcs : nat -> list syms.
    Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

    Definition countable_model M :=
        exists f: nat -> M, surjective f.

    Instance term_model M: model := 
    {
        domain := term;
        interp' := model_bot (closed_theory_of_model M)
    }.

    Lemma term_model_countable: countable_model term.
    Proof.
        destruct (enumT_term enum_Funcs') as [f H]. 
        exists (fun n => match f n with None => var n | Some t => t end).
        intro t. destruct (H t) as [n eq].
        exists n. now rewrite eq.
    Qed.

    (* Proof of elementary equivalence *)
    Existing Instance falsity_on.

    (* Consider a noemoty classical model *)
    Variable M: model.
    Hypothesis classical_model: classical interp'.
    Hypothesis noempty: M.

    Definition input_theory: theory := theory_of_model M.
    Definition output_theory: theory := 
        Out_T (construct_construction (input_bot (closed_theory_of_model M))).

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

    Corollary  Hcon_out_M: consistent class output_theory.
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
        exists N: model, countable_model N /\ M ≡ N.
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
   ∀ M: model, M satisfy the witness property → ∃ N: model, N ⪳ M.
*)

Section TheWitness.
    Context {Σf : funcs_signature} {Σp : preds_signature}.

    Existing Instance falsity_on.    

    (* A nonempty model *)
    Variable M: model. 
    Hypothesis nonempty: M.

    (* which satify the witness property *)
    Variable phi_ : nat -> form.
    Hypothesis Hphi : forall phi, exists n, phi_ n = phi.
    Variable wit_: nat -> term.
    Hypothesis witness_prop: 
        forall n σ, M ⊨[σ] (((phi_ n)[(wit_ n)..]) → ∀ (phi_ n)).
    Hypothesis witness_closed:
        forall n, bounded_t 0 (wit_ n).

    (* 
      Consider the env that map $n to the witness of φ_n
      This env existst when the model satify the witness property
    *)
    Definition h: env M :=
        fun n => (wit_ n) ₜ[M] (fun _ => nonempty).
    Definition morphism: term -> M := eval M interp' h.
    Definition theory_under h: theory :=
        fun phi => M ⊨[h] phi.

    (* The henkin model which (h n) ≡ ($ n) for working without closed *)
    Instance interp_term: interp term :=
        {| i_func := func; i_atom := fun P v => atom P v ∈ theory_under h|}.
    Instance N: model :=
        { domain := term; interp' := interp_term }.


    Lemma eval_eval (ρ: env term) (tm: term):
        (tm ₜ[N] ρ) ₜ[M] h = 
                 tm ₜ[M] (fun x => (ρ x) ₜ[M] h). 
    Proof.
          induction tm; try easy. 
          cbn. apply f_equal; rewrite map_map; apply map_ext_in.
          intro a. now apply IH.
    Qed.

    Lemma map_eval_eval (ρ: env term) {n} (v: t term n):
            map (fun tm => (tm ₜ[N] ρ) ₜ[M] h) v =
            map (fun tm => tm ₜ[M] (fun x => (ρ x) ₜ[M] h)) v.
    Proof.
        apply map_ext. apply eval_eval.
    Qed.

    Theorem LS_downward_under_witness: 
        exists (N: model), N ⪳ M.
    Proof.
        exists N, morphism; intros φ. 
        induction φ using form_ind_falsity; intro; try easy. 
        - cbn; rewrite map_map; now rewrite map_eval_eval.
        - destruct b0; cbn; intuition.
        - destruct q; split. 
          + intros H d; destruct (Hphi φ) as [i phi].
            specialize (H (var i)); specialize (@witness_prop i).
            apply IHφ in H; rewrite phi in witness_prop.
            eapply witness_prop; cbn.
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

    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Existing Instance falsity_on.

    Variable M: model. 
    Hypothesis classical_model: classical (interp' M).
    Hypothesis nonempty: M.
    (* A classical and nonempty model *)

    
    Variable enum_phi : nat -> form.
    Hypothesis He : forall phi, exists n, enum_phi n = phi.
    Variable index_wit: nat -> option term.
    (* Maybe with the countable choice? We have *)
    Hypothesis withDC:
        forall n, match index_wit n with
            | None => True
            | Some t => forall h n, M ⊨[h] (henkin_axiom (enum_phi n))[t..]
            end.
    Variable inaccessible: M.
    Definition homo': env M :=
        fun n => match index_wit n with
            | None => inaccessible
            | Some t => t t[M] (fun _ => nonempty)
            end.

    Theorem LS_downward'':
        exists (N: model) (h: N -> M), elementary_homormophism h.
    Proof.
    Admitted.

    
End DC. *)


(* Section Final.

    (* 
        Upward will change the signature 
        Then given the model over this new signature
        Downward can provide the term model over term
        wich has the same cardinality as X.
    *)

    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Existing Instance falsity_on.
    Definition has_same_card N M := exists g: N -> M, bijective g.
    Definition infinite X := exists f: nat -> X, injective f. 
    Hypothesis LS_weaker: 
        forall (M: model) X (f: X -> M), injective f -> infinite X ->
            exists N: model, N ≡ M /\ has_same_card N X.

    Hypothesis LS_stronger: 
        forall (M: model) X (f: X -> M), injective f -> infinite X ->
            exists N: model, N ⪳ M /\ has_same_card N X.

End Final. *)

