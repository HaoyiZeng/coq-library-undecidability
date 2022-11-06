Require Import Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.Facts.
Require Export Undecidability.FOL.Syntax.Core.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Vector.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Require Export Undecidability.FOL.Semantics.Tarski.FragmentCore.

Section Isomorphism.

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Class model := 
    {
        domain : Type;
        interp' : interp domain
    }.

    Coercion domain : model >-> Sortclass.

    Arguments i_func {_ _ _} _ _ _.
    Arguments i_atom {_ _ _} _ _ _.

    Definition preserve_func {M N: model} (h: M -> N) := 
        forall func v, 
        h (i_func interp' func v) = i_func interp' func (map h v).
        
    Definition preserve_pred {M N: model} (h: M -> N) :=
        forall pred v,
        i_atom interp' pred v -> i_atom interp' pred (map h v).
        
    Definition strong_preserve_pred {M N: model} (h: M -> N) :=
        forall pred v,
            i_atom interp' pred v <-> i_atom interp' pred (map h v). 

    Definition injective {M N} (f: M -> N) :=
        forall n m, f n = f m -> n = m.

    Definition surjective {M N} (f: M -> N) :=
        forall n: N, exists m: M, f m = n.

    Definition bijective {M N} (f: M -> N) :=
        injective f /\ surjective f. 

    Class homorphism {M N: model} (h: M -> N) :=
    {
        func_preserved : preserve_func h;
        pred_preserved : preserve_pred h;
    }.

    Class strong_homorphism {M N: model} (h: M -> N) :=
    {
        homorphism' :> homorphism h;
        pred_strong_preserved : strong_preserve_pred h
    }.

    Class embedding {M N: model} (h: M -> N) :=
    {
        strong_homorphism' :> strong_homorphism h;
        morphism_injectived : injective h
    }.

    Class isomorphism {M N: model} (h: M -> N) :=
    {
        embedding' :> embedding h;
        morphism_surjective : surjective h 
    }.


    Goal forall (M N: model) (h: M -> N), isomorphism h -> embedding h.
    Proof.
        intros M N h iso.
        constructor. constructor. constructor.
        apply func_preserved.
        apply pred_preserved.
        apply pred_strong_preserved.
        apply morphism_injectived.
    Qed.

End Isomorphism.

Section Elementary.

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Definition theory_model `(model): theory :=
        fun phi => closed phi /\ interp' ⊨= phi.

    Fact closed_theory_of_model M: closed_T (theory_model M).
    Proof.
        intros phi [closed sat].
        exact closed.
    Qed.

    Definition elementary M N :=
        forall φ, theory_model M φ <-> theory_model N φ.

End Elementary.


Notation "M ≡ N" := (elementary M N) (at level 30).
Notation "M ⋍ N" := (exists h: M -> N, isomorphism h) (at level 30).

Arguments closed_theory_of_model {_ _ _} _.
(* closed_theory_of_model : ∀ M: model, closed_T (theory_model M) *)


Section ModelFacts.

    Require Export Undecidability.FOL.Semantics.Tarski.FragmentFacts.

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Arguments eval {_ _ _}.

    Lemma term_preserved {M N: model} {ρ ρ'} (h: M -> N) : 
           (forall x: nat, h (ρ x) = ρ' x)
        -> preserve_func h
        -> forall t: term, h (eval interp' ρ t) = eval interp' ρ' t.
    Proof.
        intros Heq pf.
        induction t; cbn. easy.
        rewrite <- (map_ext_in _ _ _ _ _ v IH).
        rewrite (pf _ (map (eval _ ρ) v)).
        now rewrite map_map.
    Qed.

    (* 
         ∀ x, h (ρ x) = ρ' x  
         func_preserved h
        ----------------------
         ∀ t, h (Ρ t) = Ρ' t
    *)

    Lemma iso_impl_elementary' {M N: model} (h: M -> N): 
           isomorphism h 
        -> forall φ ρ ρ', (forall x, h (ρ x) = ρ' x)
        -> sat interp' ρ φ <-> sat interp' ρ' φ.
    Proof.
        intros iso.
        induction φ; cbn; intros. { easy. }
        - rewrite (pred_strong_preserved (map (eval _ ρ) t)), map_map.
          now rewrite (map_ext _ _ _ _ (term_preserved H func_preserved)).
        - destruct b0. rewrite (IHφ1 _ _ H), (IHφ2 _ _ H). easy.
        - destruct q. split; intros hp d. 
          + destruct (morphism_surjective d) as [m heq].
            apply (IHφ (m .: ρ) (d .: ρ')).
            induction x; cbn; easy.
            exact (hp m).
          + apply (IHφ (d .: ρ) (h d .: ρ')).
            induction x; cbn; easy.
            exact (hp (h d)).
    Qed.

    (* 
        ∀ x, h (ρ x) = ρ' x 
        M ⋍ N 
        -------------------------
        ∀ φ, ρ ⊨ φ <-> ρ' ⊨ φ
    *)

    Arguments iso_impl_elementary' {_ _ _ _ _}.

    Theorem iso_impl_elementary {M N: model}: 
        M ⋍ N -> M ≡ N.
    Proof.
        intros [h iso] phi; split; intros [cphi satphi]; split; try easy; intro env.
        - destruct (morphism_surjective (env O)) as [m _].
          apply (sat_closed _ _ (fun n => h m) cphi).
          now apply (iso_impl_elementary' (fun n => m) (fun n => h m)).
        - now apply (iso_impl_elementary' env (fun n => h (env n))).
    Qed.

End ModelFacts.


Section CountableModel.

    Require Import Undecidability.FOL.Completeness.TarskiCompleteness.
    Require Import Undecidability.Synthetic.EnumerabilityFacts.
    From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.

    Context {ff : falsity_flag}.
    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Context {HdF : eq_dec Σf} {HdP : eq_dec Σp}.
    Variable eF : nat -> option Σf.
    Context {HeF : enumerator__T eF Σf}.
    Variable eP : nat -> option Σp.
    Context {HeP : enumerator__T eP Σp}.

    Definition countable_model M :=
        exists f: nat -> M, surjective f.

    Instance term_model M: model := 
    {
        domain := term;
        interp' := model_bot (closed_theory_of_model M)
    }.

    Variable list_Funcs : nat -> list syms.
    Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

    Lemma term_model_countable M: countable_model (term_model M).
    Proof.
        destruct (enumT_term enum_Funcs') as [f H]. 
        exists (fun n => match f n with None => var n | Some t => t end).
        intro t. destruct (H t) as [n eq].
        exists n. now rewrite eq.
    Qed.

(* 
    Theorem LS_downward (M: model): 
        exists N: model, countable_model N /\ M ≡ N.
    Proof.
        exists (term_model M).
        split. apply term_model_countable.
        intro φ; split; intros [cphi satphi]; split; try easy; intro env.
        induction φ.
        - admit.
        - apply Out_T_sub. admit.
        - admit.
        - admit.
    Admitted.  
*)

End CountableModel.

