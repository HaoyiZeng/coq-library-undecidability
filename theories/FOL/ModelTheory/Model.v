Require Import Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.Facts.
Require Export Undecidability.FOL.Syntax.Core.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Vector.

Local Set Implicit Arguments.
(* Local Unset Strict Implicit. *)

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

    Class homomorphism {M N: model} (h: M -> N) :=
    {
        func_preserved : preserve_func h;
        pred_preserved : preserve_pred h;
    }.

    Class strong_homomorphism {M N: model} (h: M -> N) :=
    {
        homomorphism' :> homomorphism h;
        pred_strong_preserved : strong_preserve_pred h
    }.

    Class embedding {M N: model} (h: M -> N) :=
    {
        strong_homomorphism' :> strong_homomorphism h;
        morphism_injectived : injective h
    }.

    Class isomorphism {M N: model} (h: M -> N) :=
    {
        embedding' :> embedding h;
        morphism_surjective : surjective h 
    }.

    Definition isomorphic {M N: model} :=
        exists h: M -> N, isomorphism h.

    (* 
    Test the definition
    Goal forall (M N: model) (h: M -> N), isomorphism h -> embedding h.
    Proof.
        intros M N h iso.
        constructor. constructor. constructor.
        apply func_preserved.
        apply pred_preserved.
        apply pred_strong_preserved.
        apply morphism_injectived.
    Qed. 
    *)

End Isomorphism.

Notation "M ≅ N" := (exists h: M -> N, isomorphism h) (at level 30).

Arguments sat {_ _ _ _ _} _ _, {_ _ _} _ {_} _ _.
Arguments interp {_ _} _, _ _ _.

Notation "M ⊨[_] phi" := (forall p, sat (@interp' _ _ M) p phi) (at level 21).
Notation "M ⊨[ ρ ] phi" := (sat (@interp' _ _ M) ρ phi) (at level 21).

Notation "h ∘ ρ" := (funcomp h ρ) (at level 20).

Section Elementary.

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Definition theory_of_model (M: model): theory :=
        fun φ => closed φ /\ M ⊨[_] φ.

    Fact closed_theory_of_model M: closed_T (theory_of_model M).
    Proof.
        now intros phi [closed sat].
    Qed.

    Definition elementary_equivalence M N :=
        forall phi, closed phi -> (M ⊨[_] phi) <-> (N ⊨[_] phi).

    Definition elementary_homormophism {M N: model} (h: M -> N) :=
        forall phi ρ, M ⊨[ρ] phi <-> N ⊨[h ∘ ρ] phi.


End Elementary.


Notation "M ≡ N" := (elementary_equivalence M N) (at level 30).


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
        M ≅ N -> M ≡ N.
    Proof.
        intros [h iso] phi cphi. split; try easy; intros asup env.
        - destruct (morphism_surjective (env O)) as [m _].
          apply (sat_closed _ _ (fun n => h m) cphi).
          now apply (iso_impl_elementary' (fun n => m) (fun n => h m)).
        - now apply (iso_impl_elementary' env (fun n => h (env n))).
    Qed.

End ModelFacts.


Section relation.

    Import Coq.Vectors.Vector.
    Local Notation vec := t.

    Definition total_rel (X Y : Type) (R : X -> Y -> Prop) :=
        forall x, exists y, R x y.

    Definition functional_rel X Y (R : X -> Y -> Prop) :=
        forall x y y', R x y -> R x y' -> y = y'.

    Definition function_rel {X Y} (R: X -> Y -> Prop) := 
        functional_rel R /\ total_rel R. 

    Definition rev {X Y} (R: X -> Y -> Prop) x y := R y x.

    Definition injective_rel X Y (R : X -> Y -> Prop) :=
        functional_rel (rev R).

    Definition surjective_rel (X Y : Type) (R : X -> Y -> Prop) :=
        total_rel (rev R).

    Definition bijective_rel X Y (R : X -> Y -> Prop) :=
        function_rel R /\ function_rel (rev R).

    Inductive map_rel {X Y: Type} (R: X -> Y -> Prop): forall n: nat, vec X n -> vec Y n -> Prop :=
        | nil_rel: map_rel R (nil _) (nil _)
        | cons_rel n x y (vx: vec X n) (vy: vec Y n): 
            map_rel R vx vy -> R x y -> map_rel R (cons _ x n vx) (cons _ y n vy).


(* Definition hd {X : Type} {n} (v : vec X (S n)) : X :=
  match v with
  | cons _ h _ _ => h
  end.

Definition tl {X : Type} {n} (v : vec X (S n)) : vec X n :=
  match v with
  | cons _ _ _ tl => tl
  end.

Fixpoint map_rel {X Y} (R: X -> Y -> Prop) n (v1: vec X n) (v2: vec Y n): Prop :=
    match v1 in vec _ n return vec _ n -> Prop with
    | nil _ => fun _ => True 
    | cons _ x _ v1 => 
        fun v2 => (R x (hd v2)) /\ (map_rel R v1 (tl v2))
    end v2. *)

(* Lemma map_rel' {X Y} (R: X -> Y -> Prop) n: 
    total_rel R -> forall v: vec X n, exists v', map_rel R v v'.
Proof.
    intros Tt v. 
    induction v as [|e n v Hv].
    - now exists (nil _).
    - destruct Hv. destruct (Tt e) as [ne re].
      exists (cons _ ne _ x); cbn.
      split; eassumption.
Qed. *)

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Arguments i_func {_ _ _} _ _ _.
    Arguments i_atom {_ _ _} _ _ _.

    Definition preserve_func_rel {M N: model} (R: M -> N -> Prop) := 
        forall func v, exists v', 
            R (i_func interp' func v) (i_func interp' func v') /\ map_rel R v v'.

    Definition preserve_pred_rel {M N: model} (R: M -> N -> Prop) :=
        forall pred v, exists v',
            ((i_atom interp' pred v) <-> (i_atom interp' pred v')) /\ map_rel R v v'.

    Class isomorphism_rel {M N: model} (R: M -> N -> Prop) :=
        {
            func_preserved_rel: preserve_func_rel R;
            pred_preserved_rel: preserve_pred_rel R;
            morphism_biject_rel: bijective_rel R
        }.


End relation.

Notation "M ≅ᵣ N" := (exists R: M -> N -> Prop, isomorphism_rel R) (at level 30).

Section rel_facts.

    Require Export Undecidability.FOL.Semantics.Tarski.FragmentFacts.

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.
    Arguments eval {_ _ _}.

(*

    Lemma term_preserved_rel {M N: model} {ρ ρ'} (R: M -> N -> Prop) : 
       (forall x: nat, R (ρ x) (ρ' x))
    -> preserve_func_rel R
    -> forall t: term, R (eval interp' ρ t) (eval interp' ρ' t).
    Proof.
      intros Heq pf.
      induction t; cbn. easy.
      destruct (pf _ (map (eval interp' ρ) v)) as [v' [H Rvv']].
      admit.
    Admitted.

    Lemma iso_impl_elementary_rel' {M N: model} (R: M -> N -> Prop): 
        isomorphism_rel R 
        -> forall φ ρ ρ', (forall x, R (ρ x) (ρ' x))
        -> sat interp' ρ φ <-> sat interp' ρ' φ.
    Proof.
    intros iso.
    induction φ; cbn; intros. { easy. }
    (* - rewrite (pred_strong_preserved (map (eval _ ρ) t)), map_map.
      now rewrite (map_ext _ _ _ _ (term_preserved H func_preserved)). *)
    - destruct (pred_preserved_rel (map (eval interp' ρ) t) ) as [t' [IH Rt]]. 
      enough (t' = (map (eval interp' ρ') t)).
      rewrite <- H0.
      assumption.
      admit.
    - destruct b0. rewrite (IHφ1 _ _ H), (IHφ2 _ _ H). easy.
    - destruct q. split; intros hp d. 
    + destruct morphism_biject_rel as [[fu total] [inj sur]].
      destruct (sur d) as [m Rmd].
      apply (IHφ (m .: ρ) (d .: ρ')).
      induction x; cbn. assumption.
      exact (H x).
      exact (hp m).
    + destruct morphism_biject_rel as [[fu total] [inj sur]].
      destruct (total d) as [n Rmn].
      apply (IHφ (d .: ρ) (n .: ρ')).
      induction x; cbn.
      assumption.
      exact (H x).
      exact (hp n).
Admitted.


    Arguments iso_impl_elementary_rel' {_ _ _ _ _}.

    Theorem iso_impl_elementary_rel {M N: model}: 
    M ≅ᵣ N -> M ≡ N.
    Proof.
      intros [R iso] phi; split; intros [cphi satphi]; split; try easy; intro env.
    - destruct morphism_biject_rel as [[func total] [inj sur]].
      destruct (sur (env O)) as [m _].
      destruct (total m) as [n Rmn].
      apply (sat_closed _ _ (fun _ => n) cphi).
      now apply (iso_impl_elementary_rel' (fun _ => m) (fun _ => n)).
    - destruct morphism_biject_rel as [[func total] [inj sur]].
      destruct (total (env O)) as [n _].
      destruct (sur n) as [m Rnm].
      apply (sat_closed _ _ (fun _ => m) cphi).
      now apply (iso_impl_elementary_rel' (fun _ => m) (fun _ => n)).
Qed.
*)

End rel_facts.

Section CountableModel.
Require Import Undecidability.FOL.Completeness.TarskiCompleteness.
Require Import Undecidability.Synthetic.EnumerabilityFacts.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.




(* Context {ff : falsity_flag}. *)
Context {Σf : funcs_signature} {Σp : preds_signature}.
Context {HdF : eq_dec Σf} {HdP : eq_dec Σp}.
Variable eF : nat -> option Σf.
Context {HeF : enumerator__T eF Σf}.
Variable eP : nat -> option Σp.
Context {HeP : enumerator__T eP Σp}.

Definition countable_model M :=
    exists f: nat -> M, surjective f.

Existing Instance falsity_on.

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

Require Import Undecidability.FOL.Deduction.FragmentND.

Hypothesis Hcon_M: forall M: model, consistent class (theory_of_model M).


(* Theorem LS_downward (M: model): 
    exists N: model, countable_model N /\ M ≡ N.
Proof.
    exists (term_model M).
Admitted. *)

End CountableModel.



      









