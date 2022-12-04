Require Import Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.Facts.
Require Export Undecidability.FOL.Syntax.Core.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Vector.

Local Set Implicit Arguments.
(* Local Unset Strict Implicit. *)

Require Export Undecidability.FOL.Semantics.Tarski.FragmentCore.


(* New notatiob so far, for supporting model
    f[ Model ]
    p[ Model ]
    t[ Model ]
    Model ⊨[_]
    Model ⊨[ ]
*)

Section model.

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Class model := 
    {
    domain : Type;
    interp' : interp domain
    }.

    Coercion domain : model >-> Sortclass.

End model.


Arguments i_func {_ _} _ _ _ _.
Arguments i_atom {_ _} _ _ _ _.
Arguments interp' {_ _} _, {_ _ _}.
(* A interface s.t. interp' can be used as interp *)
Arguments eval {_ _}.
Notation "func f[ M ] v" := (i_func M (interp' M) func v) (at level 19).
(* 
   func: Σ_funcs 
   M: model
   v: vec M (sys_ar func) 
    : M
*)

Notation "pred p[ M ] v" := (i_atom M (interp' M) pred v) (at level 19).
(* 
   pred: Σ_preds
   M: model
   v: vec M (sys_ar [pred]) 
    : Prop
*)

Notation "term t[ M ] env" := (eval M (interp' M) env term) (at level 19).



Section Isomorphism.

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Definition preserve_func {M N: model} (h: M -> N) := 
        forall func v, 
            h (func f[M] v) = func f[N] (map h v).

    Definition preserve_pred {M N: model} (h: M -> N) :=
        forall pred v,
            pred p[M] v -> pred p[N] (map h v).
        
    Definition strong_preserve_pred {M N: model} (h: M -> N) :=
        forall pred v,
            pred p[M] v <-> pred p[N] (map h v).

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


Notation "M ⊨[_] phi" := (forall p, sat (interp' M) p phi) (at level 21).
(* 
    M : model
    phi: form
        : (nat -> M) -> Prop
    ∀ env, Model ⊨[env] formula
*)
Notation "M ⊨[ ρ ] phi" := (sat (interp' M) ρ phi) (at level 21).
(* 
    M: model
    ρ: nat -> M
    phi: form
        : Prop
    Model ⊨[env] formula
*)

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
        -> forall term: term, h (term t[M] ρ) = term t[N] ρ'.
    Proof.
        intros Heq pf.
        induction term; cbn. easy.
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
        -> M ⊨[ρ] φ <-> N ⊨[ρ'] φ.
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

    Definition preserve_func_rel {M N: model} (R: M -> N -> Prop) := 
        forall func v, exists v', 
            R (func f[M] v) (func f[N] v') /\ map_rel R v v'.

    Definition preserve_pred_rel {M N: model} (R: M -> N -> Prop) :=
        forall pred v, exists v',
            (pred p[M] v <-> pred p[N] v') /\ map_rel R v v'.

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
    Import Coq.Vectors.Vector.
    Local Notation vec := t.


    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.
    Arguments eval {_ _ _}.
    Require Import Coq.Program.Equality.

    Fact function_rel_map {X Y} (R: X -> Y -> Prop) {n: nat} (v1: vec X n) (v2 v2': vec Y n):
        function_rel R -> map_rel R v1 v2 -> map_rel R v1 v2' -> v2 = v2'.
    Proof.
        intros H1 H2.
        dependent induction H2; dependent destruction v2'; try easy.
        - intros.
          specialize (IHmap_rel v2').
          rewrite IHmap_rel.
          enough (y = h).
          rewrite H3. easy.
          dependent destruction H0.
          eapply H1 . exact H. easy.
          dependent destruction H0; eassumption.
    Qed.


    Lemma term_preserved_rel {M N: model} {ρ ρ'} (R: M -> N -> Prop) : 
       (forall x: nat, R (ρ x) (ρ' x))
    -> isomorphism_rel R 
    -> preserve_func_rel R
    -> forall t: term, R (t t[M] ρ) (t t[N] ρ').
    Proof.
      intros Heq iso pf.
      induction t; cbn. easy.
      destruct (pf _ (map (eval interp' ρ) v)) as [v' [H Rvv']]; cbn.
      assert (v' = (map (eval interp' ρ') v)).
      eapply function_rel_map.
      destruct iso as [_ _ [h _]].
      exact h.
      exact Rvv'.
      admit.
      rewrite <- H0; easy.
    Admitted.

    Lemma iso_impl_elementary_rel' `{falsity_flag} {M N: model} (R: M -> N -> Prop): 
        isomorphism_rel R 
        -> forall φ ρ ρ', (forall x, R (ρ x) (ρ' x))
        -> M ⊨[ρ] φ <-> N ⊨[ρ'] φ.
    Proof.
      intros iso.
      induction φ; cbn; intros. { easy. }
    (* - rewrite (pred_strong_preserved (map (eval _ ρ) t)), map_map.
      now rewrite (map_ext _ _ _ _ (term_preserved H func_preserved)). *)
    - destruct (pred_preserved_rel (map (eval interp' ρ) t) ) as [v' [IH Rt]]. 
      enough (v' = (map (eval interp' ρ') t)).
      rewrite <- H0; assumption.
      eapply function_rel_map.
      destruct iso as [_ _ [h _]].
      exact h.
      exact Rt.
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
      intros [h iso] phi cphi. split; try easy; intros asup env.
    - destruct morphism_biject_rel as [[func total] [inj sur]].
      destruct (sur (env O)) as [m _].
      destruct (total m) as [n Rmn].
      apply (sat_closed _ _ (fun _ => n) cphi).
      admit.
      (* now apply (iso_impl_elementary_rel' (fun _ => m) (fun _ => n)). *)
    - destruct morphism_biject_rel as [[func total] [inj sur]].
      destruct (total (env O)) as [n _].
      destruct (sur n) as [m Rnm].
      apply (sat_closed _ _ (fun _ => m) cphi).
      admit. 
      (* now apply (iso_impl_elementary_rel' (fun _ => m) (fun _ => n)). *)
Admitted.


End rel_facts.


(* Will be put in another Doc *)
Section CountableModel.

    Require Import Undecidability.FOL.Completeness.TarskiCompleteness.
    Require Import Undecidability.Synthetic.EnumerabilityFacts.
    From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
    Require Import Undecidability.FOL.Deduction.FragmentND.
    Require Import Undecidability.FOL.Semantics.Tarski.FragmentSoundness.

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

    Lemma term_model_countable M: countable_model (term_model M).
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
    Theorem LS_downward: 
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

End CountableModel.

Section HenkinModel.
    Require Import Undecidability.FOL.Syntax.Facts.

    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Existing Instance falsity_on.

    Variable M: model. 
    Hypothesis classical_model: classical (interp' M).
    Hypothesis nonempty: M.
    (* A classical and nonempty model *)

    Variable enum_phi : nat -> form.
    Hypothesis He : forall phi, exists n, enum_phi n = phi.
    Variable index_wit: env term.
    Hypothesis ρ_henkin_sat: 
        forall h n, M ⊨[h] (henkin_axiom (enum_phi n))[(index_wit n)..].
    (* which satify the henkin axioms for any formulas (in syntax level) *)

    Definition homo: env M :=
        fun n => (index_wit n) t[M] (fun _ => nonempty).
    (* 
        Consider then env that map $0 to the witness of φ_n
        This env existst when the model satify the witness property
    *)

    Definition theory_under_homo: theory :=
        fun phi => M ⊨[homo] phi.

    Instance interp_bot: interp term :=
        {| i_func := func; i_atom := fun P v => atom P v ∈ theory_under_homo|}.

    Instance model_bot: model :=
        {| domain := term; interp' := interp_bot|}.

    (* The henkin model which (h n) ≡ ($ n) for working without closed *)

    Theorem LS_downward':
        exists (N: model) (h: N -> M), elementary_homormophism h.
    Proof.
        exists model_bot, (eval _ (interp' M) homo); cbn.
        unfold elementary_homormophism; cbn.
        intros φ ρ.
        induction φ.
        - easy.
        - admit.
        - destruct b0; cbn. firstorder.
        - destruct q. admit.
    Admitted.
End HenkinModel.

Section DC.

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

    
End DC.


    




      









