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

    Definition elementary_homomorphism {M N: model} (h: M -> N) :=
        forall phi ρ, M ⊨[ρ] phi <-> N ⊨[ρ >> h] phi.

    Definition elementary_syntactic_homomorphism {M: model} (i_term: interp term) (h: term -> M) :=
        forall phi (ρ: env term), ρ ⊨ phi <-> M ⊨[ρ >> h] phi.



End Elementary.


(* closed_theory_of_model : ∀ M: model, closed_T (theory_model M) *)
Arguments closed_theory_of_model {_ _ _} _.

Notation "M ≡ N"  := (elementary_equivalence M N) (at level 30).
Notation "N ⪳ M"  := (exists h: N -> M, elementary_homomorphism h) (at level 30).
Notation "N ⪳[ h ] M"  := (@elementary_homomorphism _ _ _ N M h) (at level 30).

Notation "𝕋 ⪳[ h ] M" := (exists i_term, @elementary_syntactic_homomorphism _ _ _ M i_term h) (at level 30).
Notation "𝕋 ⪳ M" := (exists i_term h, @elementary_syntactic_homomorphism _ _ _ M i_term h) (at level 30).