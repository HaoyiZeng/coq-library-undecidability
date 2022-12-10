Require Export Undecidability.FOL.FragmentSyntax.
Require Export Vector.

Local Set Implicit Arguments.

Declare Scope modelNotation.
Open Scope modelNotation.

Notation vec := t.

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
