Require Export Undecidability.FOL.FullSyntax.
Require Export Undecidability.FOL.Syntax.Theories.
Require Export Vector.

Local Set Implicit Arguments.

Declare Scope modelNotation.
Open Scope modelNotation.

Notation vec := t.

Section model.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Record model :=
    {
        domain : Type;
        interp' : interp domain
    }.

    Coercion domain : model >-> Sortclass.

End model.

Arguments eval {_ _}.
Arguments i_func {_ _} _ _ _ _.
Arguments i_atom {_ _} _ _ _ _.
Arguments sat {_ _ _ _ _} _ _, {_ _ _} _ {_} _ _.

(* A interface s.t. interp' can be used as interp *)
Arguments interp' {_ _} _, {_ _ _}.

(* Declare some notation that distinguishes the different models *)

    (* Evaluate function in model M with argument v
    func: Σ_funcs 
    M: model
    v: vec M (sys_ar func) 
        : M
    *)
    Notation "func ₕ[ M ] v" := (i_func _ (interp' M) func v) (at level 19).

    (* Evaluate predicate in model M with argument v
    pred: Σ_preds
    M: model
    v: vec M (sys_ar [pred]) 
        : Prop
    *)
    Notation "pred ₚ[ M ] v" := (i_atom _ (interp' M) pred v) (at level 19).

    (* Evaluate term in model M under environment env
    term: term
    M: model
    env: nat → M
        : Prop
    *)
    Notation "term ₜ[ M ] env" := (eval _ (interp' M) env term) (at level 19).

    (* 
        M : model
        phi: form
            : (nat -> M) -> Prop
        ∀ env, Model ⊨[env] formula
    *)
    Notation "Model ⊨[_] phi" := (forall p, sat (interp' Model) p phi) (at level 21).

    (* 
        M: model
        ρ: nat -> M
        phi: form
            : Prop
        Model ⊨[env] formula
    *)
    Notation "Model ⊨[ ρ ] phi" := (sat (interp' Model) ρ phi) (at level 21).


Section Elementary.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Definition elementary_equivalence M N :=
        forall phi, closed phi -> (M ⊨[_] phi) <-> (N ⊨[_] phi).

    Definition elementary_homomorphism (M N: model) (h: M -> N) :=
        forall phi ρ, M ⊨[ρ] phi <-> N ⊨[ρ >> h] phi.

End Elementary.

Notation "M ≡ N"  := (elementary_equivalence M N) (at level 30).
Notation "N ⪳[ h ] M"  := (@elementary_homomorphism _ _ _ N M h) (at level 30).
Notation "N ⪳ M"  := (exists h: N -> M, N ⪳[ h ] M) (at level 30).

Section LöwenheimSkolemTheorem.

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Definition syntatic_model_on (M: model) :=  
        exists (N: interp term) (h: term -> M), 
            forall φ ρ, Build_model N ⊨[ρ] φ <-> M ⊨[ρ >> h] φ.

    Definition surjective {M N} (f: M -> N) :=
        forall n: N, exists m: M, f m = n.

    Definition a_coutable_model M :=
        exists f: nat -> M, surjective f.

    Definition LöwenheimSkolemTheorem :=
       forall M: model, M -> exists N: model, a_coutable_model N /\ N ⪳ M.

    Definition LS := forall M: model, M -> syntatic_model_on M.

    Hypothesis surjective_term: exists f: nat -> term, surjective f.

    Fact LS_correct: LS -> LöwenheimSkolemTheorem.
    Proof.
        intros H M m.
        destruct (H M m) as (I & h & HI).
        unshelve eexists. { econstructor. exact I. }
        split. apply surjective_term.
        exists h. intros ??; apply HI.
    Qed.

    Definition LS_root :=
        forall (M: model), forall m,
            exists (N: model), a_coutable_model N /\ 
                (exists h: N -> M, N ⪳[h] M /\ exists n: N, h n = m).

    Definition bijective_comp {X Y} :=
        exists f g, (forall x: X, g (f x) = x) /\ forall y: Y, f (g y) = y.

    Definition LS_root' :=
        forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
            exists (N: model), @bijective_comp N nat /\ (exists h: N -> M, elementary_homomorphism h /\ exists n: N, h n = m).

End LöwenheimSkolemTheorem.
