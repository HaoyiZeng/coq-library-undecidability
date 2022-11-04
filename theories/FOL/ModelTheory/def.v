Require Import Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.Facts.
Require Export Undecidability.FOL.Syntax.Core.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Vector.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Require Export Undecidability.FOL.Semantics.Tarski.FullCore.

Section Isomorphism.

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Record model := 
        {
        domain :> Type;
        interp_md :> interp domain
        }.


    Arguments i_func {_ _ _} _ _ _.
    Arguments i_atom {_ _ _} _ _ _.

    Definition preserve_func {M N: model} (h: M -> N) := 
        forall func v, 
            i_func (interp_md N) func (map h v) = h (i_func (interp_md M) func v).

    (*  Failed

    Definition preserve_func {M N: model} (h: M -> N) :=  
        forall func v, 
            i_func _ func (map h v) = h (i_func _ func v).

    Definition preserve_func'' {M N: Type} `{interp M} `{interp N} (h: M -> N) := 
        forall func v, 
          i_func _ func (map h v) = h (i_func _ func v).

    *)

    Definition preserve_pred {M N: model} (h: M -> N) :=
        forall pred v,
            i_atom (interp_md N) pred (map h v) <-> i_atom (interp_md M) pred v.

    Definition injective {M N} (f: M -> N) :=
        forall n m, f n = f m -> n = m.

    Definition surjective {M N} (f: M -> N) :=
        forall n: N, exists m: M, f m = n.

    Definition bijective {M N} (f: M -> N) :=
        injective f /\ surjective f. 

    Class isomorphism {M N: model} (h: M -> N) := 
    {
        func_preserved : preserve_func h;
        pred_preserved : preserve_pred h;
        morphism_bijective : bijective h;
    }.

    Definition theory_model (M: model): theory :=
        fun phi => closed phi /\ (interp_md M) ⊨= phi.

    Fact closed_theory_of_model M: closed_T (theory_model M).
    Proof.
        intros phi [closed sat].
        exact closed.
    Qed.

    Definition elementary M N :=
        forall φ, theory_model M φ <-> theory_model N φ.
    
    Notation "M ≡ N" := (elementary M N) (at level 30).
    Notation "M ⋍ N" := (exists h: M -> N, isomorphism h) (at level 30).

    Fact isomorphism_implies_elementary (M N: model): 
        M ⋍ N -> M ≡ N.
    Proof.
    Admitted.

    Definition countable_model (M: model) :=
        exists f: nat -> domain M, surjective f.

    Lemma model_exists M: exists N: model, countable_model N /\ elementary M N.
    Proof.
    Admitted.

End Isomorphism.